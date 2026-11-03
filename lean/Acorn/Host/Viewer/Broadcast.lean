/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Sensed
import Acorn.Host.Viewer.IdentityHandshake
import Acorn.Host.Viewer.ControlTelemetry
import Std.Sync.Mutex
import Acorn.Host.Forever

/-!
# Serialized observer delivery

Replay publication, generation admission and subscriber registration share one
mutex. A publisher never waits for a network reader. Each subscriber has a
bounded application queue and one wake promise; promises carry no frame payload.
One delivery task owns each subscription. Native mutex/promise scheduling and
allocator overhead remain trusted infrastructure, without a liveness guarantee.

The broadcaster decides nothing about the process lifecycle. It holds a copy of the
lifecycle that the supervisor's step decided (`Acorn.Host.Viewer.Supervision`), which
the supervisor installs, with the observer changes that go with it, in one serialized
operation (`Broadcast.settle`); frame admission reads that copy. The step's state is
authoritative, and the copy lags it only between a step and the settlement that the
actor performs next.
-/
namespace Acorn.Host.Viewer

/-- Bound on simultaneous retained subscriber queues. -/
def connectionCapacity : Nat := 16

private structure Subscriber where
  id : UInt64
  queue : Buffer WireText subscriberCapacity
  wake : IO.Promise Unit

private structure IdentityWait where
  generation : UInt64
  candidate : Option CoreIdentity := none
  refused : Bool := false
  frames : Buffer WireText replayCapacity := .empty
  dropped : Nat := 0

/-- An observer change that a supervisor transition installs together with its lifecycle. -/
inductive Change where
  /-- The retiring process's buffered output may be lost: mark the retained map partial. -/
  | loseTail
  /-- A new process: hold its output until its identity is persisted; it has refused no
  checkpoint yet. -/
  | await (generation : UInt64)
  /-- Refuse the identity the waiting process reported, with every output it holds. -/
  | refuseIdentity (generation : UInt64)
  /-- The joined stderr of the last process reported a refused checkpoint. -/
  | refuseCheckpoint
  /-- A new run: drop the old run's replay, map, queued frames, pending identity and control. -/
  | newRun

private structure BroadcastState where
  lifecycle : Lifecycle
  checkpointRefused : Bool := false
  control : Option WireText := none
  waiting : Option IdentityWait := none
  adopted : Option (UInt64 × CoreIdentity) := none
  world : Option ((key : MapKey) × WorldMemory key) := none
  worldPartial : Bool := false
  worldRevision : Nat := 0
  replay : Buffer WireText replayCapacity := .empty
  subscribers : Buffer Subscriber connectionCapacity := .empty
  sequence : UInt64 := 0

/-- Native observation capability; callers cannot replace its queue or generation state. -/
structure Broadcast where
  private mk ::
  private state : Std.Mutex BroadcastState

/-- Each supervisor owns an independent serialized observer domain. -/
def Broadcast.new (identity : Identity) (desired : Desired) (historyMayBeMissing : Bool := false) : BaseIO Broadcast := do
  return ⟨← Std.Mutex.new { lifecycle := .initial identity desired, worldPartial := historyMayBeMissing }⟩

private def sameWorldRevision : Option ((key : MapKey) × WorldMemory key) →
    Option ((key : MapKey) × WorldMemory key) → Bool
  | none, none => true
  | some ⟨leftKey, left⟩, some ⟨rightKey, right⟩ =>
    if same : leftKey = rightKey then
      let left := same ▸ left
      left.changeCount == right.changeCount && left.isIncomplete == right.isIncomplete
    else false
  | _, _ => false

private def BroadcastState.withWorld (state : BroadcastState)
    (world : Option ((key : MapKey) × WorldMemory key)) : BroadcastState :=
  { state with
    world := world
    worldRevision := state.worldRevision + (if sameWorldRevision state.world world then 0 else 1) }

private def BroadcastState.loseWorldTail (state : BroadcastState) : BroadcastState :=
  { state.withWorld (state.world.map fun ⟨key, memory⟩ => ⟨key, memory.markPartial⟩) with
    worldPartial := true }

/-- Read-only lifecycle snapshot, without an observer-state write capability. -/
def Broadcast.lifecycle (broadcast : Broadcast) : BaseIO Lifecycle :=
  broadcast.state.atomically do return (← get).lifecycle

/-- Read a complete map under the publication lock for later atomic disk publication. -/
def Broadcast.world (broadcast : Broadcast) : BaseIO (Option ((key : MapKey) × WorldMemory key)) :=
  broadcast.state.atomically do return (← get).world

/-- Map contents and their mutation revision are captured together, before asynchronous disk IO. -/
def Broadcast.worldForWrite (broadcast : Broadcast) :
    BaseIO (Nat × Option ((key : MapKey) × WorldMemory key)) :=
  broadcast.state.atomically do
    let state ← get
    return (state.worldRevision, state.world)

/-- Startup restore cannot replace an observed map or attach a foreign identity. -/
def Broadcast.restoreWorld (broadcast : Broadcast) {key : MapKey} (memory : WorldMemory key) :
    BaseIO Bool :=
  broadcast.state.atomically do
    let state ← get
    if state.world.isSome || state.lifecycle.phaseValue != .idle ||
        key.run != state.lifecycle.identityValue.run || key.seed != state.lifecycle.identityValue.seed then
      return false
    set { state.withWorld (some ⟨key, memory.markPartial⟩) with worldPartial := true }
    return true

/-- The current process may complete attribution while its readers drain,
without restoring that reaped process's observation rights. -/
def Broadcast.pendingIdentity (broadcast : Broadcast) : BaseIO (Option (UInt64 × CoreIdentity)) :=
  broadcast.state.atomically do
    let state ← get
    let some waiting := state.waiting | return none
    if waiting.refused || !state.lifecycle.ownsIdentity waiting.generation then return none
    return waiting.candidate.map (waiting.generation, ·)

/-- A checkpoint-refusal diagnostic is admitted under its actual process generation. -/
def Broadcast.refuseCheckpoint (broadcast : Broadcast) (generation : UInt64) : BaseIO Unit :=
  broadcast.state.atomically (modify fun state =>
    if state.lifecycle.phaseValue.accepts generation then { state with checkpointRefused := true }
    else state)

private def Subscriber.enqueue (subscriber : Subscriber) (text : WireText) : Subscriber :=
  match subscriber.queue.offer text with
  | none => subscriber
  | some queue => { subscriber with queue }

private def Subscriber.enqueueControl (subscriber : Subscriber) (text : WireText) : Subscriber :=
  { subscriber with queue := subscriber.queue.retain text }

private def BroadcastState.publish (state : BroadcastState) (text : WireText) : BroadcastState :=
  { state with
    replay := state.replay.retain text
    subscribers := ⟨state.subscribers.values.map (·.enqueue text), by
      simpa using state.subscribers.bounded⟩ }

private def BroadcastState.observe (state : BroadcastState) (text : WireText) : BroadcastState :=
  let next := state.publish text
  match (SensedEnvelope.parse text).toOption.map (·.sensed) with
  | none => next
  | some sensed =>
    if sensed.key.run == state.lifecycle.identityValue.run &&
        sensed.key.seed == state.lifecycle.identityValue.seed then
      let ⟨key, memory⟩ := sensed.absorb state.world
      next.withWorld (some ⟨key, if state.worldPartial then memory.markPartial else memory⟩)
    else next

private def BroadcastState.observation (state : BroadcastState) : ControlObservation :=
  ⟨state.checkpointRefused, state.worldPartial⟩

/-- The actor calls this only after publishing the selected identity to state.json.
The candidate, active generation, identity update, control update, queued suffix
and subscriber wakeups share one serialization boundary. The lifecycle installed is the one
the supervisor's step decided, with the identity adopted, and the control record encodes it
with the step's detail. Pending overflow is reported to the caller and conservatively marks
any retained map partial. -/
def Broadcast.commitIdentity (broadcast : Broadcast) (generation : UInt64) (actual : CoreIdentity)
    (lifecycle : Lifecycle) (detail : ControlDetail) : BaseIO (Except String Nat) := do
  let result : Except String (Nat × List (IO.Promise Unit)) ← broadcast.state.atomically do
    let state ← get
    let some waiting := state.waiting | return .error "no identity handshake is pending"
    if waiting.generation != generation || waiting.candidate != some actual ||
        !state.lifecycle.ownsIdentity generation then return .error "identity handshake is stale"
    let forwarding := state.lifecycle.phaseValue.accepts generation
    let control ← match controlTelemetryLine lifecycle state.observation detail with
      | .error reason => return .error reason
      | .ok text => pure text
    let changed := state.lifecycle.identityValue != actual.identity
    let subscribers := state.subscribers.values.map fun subscriber =>
      let subscriber := if changed then { subscriber with queue := .empty } else subscriber
      subscriber.enqueueControl control
    let newWorld := state.lifecycle.identityValue.run != actual.identity.run ||
      state.lifecycle.identityValue.seed != actual.identity.seed
    let base := if newWorld then { state.withWorld none with worldPartial := false } else state
    let mut next : BroadcastState := { base with
      lifecycle, waiting := none, adopted := some (generation, actual), control := some control
      replay := if changed then .empty else state.replay
      subscribers := ⟨subscribers, by simpa [subscribers] using state.subscribers.bounded⟩ }
    if forwarding then
      for frame in waiting.frames.values do next := next.observe frame
    let dropped := waiting.dropped + if forwarding then 0 else waiting.frames.values.length
    if dropped > 0 then
      next := next.loseWorldTail
    set next
    return .ok (dropped, next.subscribers.values.map (·.wake))
  match result with
  | .error reason => return .error reason
  | .ok (dropped, wakes) =>
    for wake in wakes do wake.resolve ()
    return .ok dropped

private def BroadcastState.change (state : BroadcastState) : Change → BroadcastState
  | .loseTail => state.loseWorldTail
  | .await generation =>
    { state with
      waiting := some ⟨generation, none, false, .empty, 0⟩, adopted := none
      checkpointRefused := false }
  | .refuseIdentity generation =>
    match state.waiting with
    | some waiting =>
      if waiting.generation == generation then
        { state with waiting := some { waiting with candidate := none, refused := true, frames := .empty } }
      else state
    | none => state
  | .refuseCheckpoint => { state with checkpointRefused := true }
  | .newRun =>
    let subscribers := state.subscribers.values.map fun subscriber =>
      { subscriber with queue := .empty }
    { state.withWorld none with
      replay := .empty, worldPartial := false, control := none, waiting := none, adopted := none
      checkpointRefused := false
      subscribers := ⟨subscribers, by simpa [subscribers] using state.subscribers.bounded⟩ }

/-- Install the lifecycle the supervisor's step decided, apply the observer changes that go
with it, in order, and publish the control record of that lifecycle with the step's detail,
all in one serialized operation. Supervisor records bypass process-generation admission while
retaining the same serialized subscriber boundary. They have a dedicated current snapshot and
do not consume process replay slots; an unchanged record is not sent again. -/
def Broadcast.settle (broadcast : Broadcast) (lifecycle : Lifecycle) (changes : List Change)
    (detail : ControlDetail) : BaseIO (Except String Unit) := do
  let result : Except String (List (IO.Promise Unit)) ← broadcast.state.atomically do
    let state := { (changes.foldl BroadcastState.change (← get)) with lifecycle }
    set state
    match controlTelemetryLine lifecycle state.observation detail with
    | .error reason => return .error reason
    | .ok text =>
      if state.control.map (·.val) == some text.val then return .ok []
      let subscribers := state.subscribers.values.map (·.enqueueControl text)
      set { state with control := some text, subscribers := ⟨subscribers, by
        simpa [subscribers] using state.subscribers.bounded⟩ }
      return .ok (subscribers.map (·.wake))
  match result with
  | .error reason => return .error reason
  | .ok wakes =>
    for wake in wakes do wake.resolve ()
    return .ok ()

private def Broadcast.notice (broadcast : Broadcast) (fields : Lifecycle → List TelemetryField) :
    BaseIO (Except String Unit) := do
  let result : Except String (List (IO.Promise Unit)) ← broadcast.state.atomically do
    let state ← get
    let some text := wireText (emitTelemetryFields (fields state.lifecycle))
      | return .error "supervisor notice exceeds its physical line bound"
    let subscribers := state.subscribers.values.map (·.enqueueControl text)
    set { state with subscribers := ⟨subscribers, by
      simpa [subscribers] using state.subscribers.bounded⟩ }
    return .ok (subscribers.map (·.wake))
  match result with
  | .error reason => return .error reason
  | .ok wakes =>
    for wake in wakes do wake.resolve ()
    return .ok ()

/-- The Clear acknowledgement names the already-installed world and never enters replay. -/
def Broadcast.announceCleared (broadcast : Broadcast) : BaseIO (Except String Unit) :=
  broadcast.notice fun lifecycle =>
    [⟨"cleared", .flag, true⟩, ⟨"seed", .natural, lifecycle.identityValue.seed.toNat⟩]

/-- An observed process exit supplies the existing browser fault surface, without adding a replay frame. -/
def Broadcast.announceExit (broadcast : Broadcast) (reason : String) : BaseIO (Except String Unit) :=
  broadcast.notice fun _ =>
    [⟨"eos", .flag, true⟩, ⟨"kind", .text, "exit"⟩, ⟨"reason", .text, controlDiagnostic reason⟩]

/-- Admit generation and mutate all queues in one serialized operation.
Every slow subscriber keeps its queued prefix and refuses the new frame. -/
def Broadcast.publish (broadcast : Broadcast) (generation : UInt64) (text : WireText) : BaseIO Bool := do
  let identity := (coreIdentity text).toOption
  let wakes ← broadcast.state.atomically do
    let state ← get
    if let some waiting := state.waiting then
      if waiting.generation == generation then
        if waiting.refused || !state.lifecycle.ownsIdentity generation || identity.isNone then return none
        if waiting.candidate.isSome && waiting.candidate != identity then return none
        let waiting := { waiting with
          candidate := waiting.candidate.or identity
          dropped := waiting.dropped + if waiting.frames.values.length == replayCapacity then 1 else 0
          frames := waiting.frames.retain text }
        set { state with waiting := some waiting }
        return some []
    if !state.lifecycle.phaseValue.accepts generation then return none
    if let some (owner, actual) := state.adopted then
      if owner == generation && identity != some actual then return none
    let next := state.observe text
    set next
    return some (next.subscribers.values.map (·.wake))
  match wakes with
  | none => return false
  | some wakes =>
    for wake in wakes do wake.resolve ()
    return true

/-- A subscription is bound to its creating broadcast instance and nonreused sequence. -/
structure Subscription where
  private mk ::
  private broadcast : Broadcast
  private id : UInt64

/-- Replay and map snapshot are captured at the same serialized stream position. -/
structure ReplaySnapshot where
  /-- Current durable identity at registration. -/
  identity : Identity
  /-- Last supervisor record at this same registration boundary. -/
  control : Option WireText
  /-- Run-owned sensed observations, independent of the browser's history ring. -/
  world : Option ((key : MapKey) × WorldMemory key)
  /-- Bounded replay preceding all subsequently queued live frames. -/
  frames : Buffer WireText replayCapacity

/-- Registration and replay snapshot share the publication mutex, closing their handover gap.
Capacity or sequence exhaustion refuses registration before it retains a queue. -/
def Broadcast.subscribe (broadcast : Broadcast) : BaseIO (Option (Subscription × ReplaySnapshot)) := do
  let wake ← IO.Promise.new
  broadcast.state.atomically do
    let state ← get
    if state.sequence == 18446744073709551615 then return none
    let id := state.sequence + 1
    let subscriber : Subscriber := ⟨id, .empty, wake⟩
    match state.subscribers.offer subscriber with
    | none => return none
    | some subscribers =>
      set { state with subscribers, sequence := id }
      return some (⟨broadcast, id⟩, ⟨state.lifecycle.identityValue, state.control, state.world, state.replay⟩)

/-- Disconnect removes the queue before waking any blocked delivery task. -/
def Subscription.close (subscription : Subscription) : BaseIO Unit := do
  let wake ← subscription.broadcast.state.atomically do
    let state ← get
    let wake := (state.subscribers.values.find? (·.id == subscription.id)).map (·.wake)
    let remaining := state.subscribers.values.filter (·.id != subscription.id)
    set { state with subscribers := ⟨remaining,
      Nat.le_trans (List.length_filter_le _ _) state.subscribers.bounded⟩ }
    return wake
  if let some wake := wake then wake.resolve ()

/-- A subscriber read either consumes one bounded frame or supplies a payload-free wake task. -/
inductive SubscriptionRead where
  /-- The registration no longer exists. -/
  | closed
  /-- Exactly one queued frame was consumed. -/
  | item (text : WireText)
  /-- Wait outside the publication lock, then poll again. -/
  | wait (task : Task (Option Unit))

/-- One serialized dequeue or wake registration for the subscription's sole reader. -/
def Subscription.poll (subscription : Subscription) : BaseIO SubscriptionRead := do
  let wake ← IO.Promise.new
  subscription.broadcast.state.atomically do
    let state ← get
    let some subscriber := state.subscribers.values.find? (·.id == subscription.id) | return .closed
    let (result, next) : SubscriptionRead × Subscriber := match subscriber.queue.pop with
      | some (text, queue) => (.item text, { subscriber with queue })
      | none => (.wait wake.result?, { subscriber with wake })
    let subscribers := state.subscribers.values.map fun current =>
      if current.id == subscription.id then next else current
    set { state with subscribers := ⟨subscribers, by simpa [subscribers] using state.subscribers.bounded⟩ }
    return result

/-- Wait outside the publication lock; only the subscriber delivery task can block here.
Dropped promises and explicit disconnect both terminate this subscription reader. -/
def Subscription.receive (subscription : Subscription) : BaseIO (Option WireText) := do
  for _ in forever do
    match ← subscription.poll with
    | .closed => return none
    | .item text => return some text
    | .wait task =>
      if (← IO.wait task).isNone then return none
  -- The loop has no `break`, so it ends only by returning.
  return none

end Acorn.Host.Viewer
