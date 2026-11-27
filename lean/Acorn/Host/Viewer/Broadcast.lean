import Acorn.Host.Viewer.Sensed
import Acorn.Host.Viewer.IdentityHandshake
import Acorn.Host.Viewer.ControlTelemetry
import Acorn.Host.Viewer.ServerFrame
import Std.Sync.Mutex
import Acorn.Host.Forever

namespace Acorn.Host.Viewer

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

inductive Change where
  | loseTail
  | await (generation : UInt64)
  | refuseIdentity (generation : UInt64)
  | refuseCheckpoint
  | newRun

private structure BroadcastState where
  lifecycle : Lifecycle
  checkpointRefused : Bool := false
  control : Option WireText := none
  detail : Option ControlDetail := none
  waiting : Option IdentityWait := none
  adopted : Option (UInt64 × CoreIdentity) := none
  world : Option ((key : MapKey) × WorldMemory key) := none
  worldPartial : Bool := false
  worldRevision : Nat := 0
  replay : Buffer WireText replayCapacity := .empty
  observer : ServerObserverState
  subscribers : Buffer Subscriber connectionCapacity := .empty
  sequence : UInt64 := 0

structure BroadcastSnapshot where
  lifecycle : Lifecycle
  observation : ControlObservation
  detail : Option ControlDetail
  world : Option ((key : MapKey) × WorldMemory key)
  observer : ServerObserverState

structure Broadcast where
  private mk ::
  private state : Std.Mutex BroadcastState

def Broadcast.new (identity : Identity) (desired : Desired) (historyMayBeMissing : Bool := false) : BaseIO Broadcast := do
  return ⟨← Std.Mutex.new {
    lifecycle := .initial identity desired
    worldPartial := historyMayBeMissing
    observer := .empty identity
  }⟩

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

def Broadcast.lifecycle (broadcast : Broadcast) : BaseIO Lifecycle :=
  broadcast.state.atomically do return (← get).lifecycle

def Broadcast.world (broadcast : Broadcast) : BaseIO (Option ((key : MapKey) × WorldMemory key)) :=
  broadcast.state.atomically do return (← get).world

def Broadcast.worldForWrite (broadcast : Broadcast) :
    BaseIO (Nat × Option ((key : MapKey) × WorldMemory key)) :=
  broadcast.state.atomically do
    let state ← get
    return (state.worldRevision, state.world)

def Broadcast.restoreWorld (broadcast : Broadcast) {key : MapKey} (memory : WorldMemory key) :
    BaseIO Bool :=
  broadcast.state.atomically do
    let state ← get
    if state.world.isSome || state.lifecycle.phaseValue != .idle ||
        key.run != state.lifecycle.identityValue.run || key.seed != state.lifecycle.identityValue.seed then
      return false
    set { state.withWorld (some ⟨key, memory.markPartial⟩) with worldPartial := true }
    return true

def Broadcast.pendingIdentity (broadcast : Broadcast) : BaseIO (Option (UInt64 × CoreIdentity)) :=
  broadcast.state.atomically do
    let state ← get
    let some waiting := state.waiting | return none
    if waiting.refused || !state.lifecycle.ownsIdentity waiting.generation then return none
    return waiting.candidate.map (waiting.generation, ·)

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

private def BroadcastState.observe (state : BroadcastState) (text : WireText)
    (parsed : Option Json.Value) (nowMonoMs : Nat) : BroadcastState :=
  let next := state.publish text
  let observer := match parsed with
    | some value => next.observer.observe value nowMonoMs
    | none => next.observer
  let next := { next with observer }
  match parsed.bind fun value => (sensedFromJson value).toOption with
  | none => next
  | some sensed =>
    if sensed.key.run == state.lifecycle.identityValue.run &&
        sensed.key.seed == state.lifecycle.identityValue.seed then
      let ⟨key, memory⟩ := sensed.absorb state.world
      next.withWorld (some ⟨key, if state.worldPartial then memory.markPartial else memory⟩)
    else next

private def BroadcastState.observation (state : BroadcastState) : ControlObservation :=
  ⟨state.checkpointRefused, state.worldPartial⟩

def Broadcast.snapshot (broadcast : Broadcast) : BaseIO BroadcastSnapshot :=
  broadcast.state.atomically do
    let state ← get
    return ⟨state.lifecycle, state.observation, state.detail, state.world, state.observer⟩

def Broadcast.commitIdentity (broadcast : Broadcast) (generation : UInt64) (actual : CoreIdentity)
    (lifecycle : Lifecycle) (detail : ControlDetail) : BaseIO (Except String Nat) := do
  let nowMonoMs ← IO.monoMsNow
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
      lifecycle, detail := some detail, waiting := none, adopted := some (generation, actual),
      control := some control
      replay := if changed then .empty else state.replay
      observer := if changed then .empty actual.identity else state.observer.resetIdentity actual.identity
      subscribers := ⟨subscribers, by simpa [subscribers] using state.subscribers.bounded⟩ }
    if forwarding then
      for frame in waiting.frames.values do
        next := next.observe frame (Json.parse frame.val).toOption nowMonoMs
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

def Broadcast.settle (broadcast : Broadcast) (lifecycle : Lifecycle) (changes : List Change)
    (detail : ControlDetail) : BaseIO (Except String Unit) := do
  let isNewRun := changes.any fun change => match change with | .newRun => true | _ => false
  let result : Except String (List (IO.Promise Unit)) ← broadcast.state.atomically do
    let changed := changes.foldl BroadcastState.change (← get)
    let observer := if isNewRun then .empty lifecycle.identityValue
      else changed.observer.resetIdentity lifecycle.identityValue
    let state := { changed with lifecycle, detail := some detail, observer }
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

def Broadcast.announceCleared (broadcast : Broadcast) : BaseIO (Except String Unit) :=
  broadcast.notice fun lifecycle =>
    [⟨"cleared", .flag, true⟩, ⟨"seed", .natural, lifecycle.identityValue.seed.toNat⟩]

def Broadcast.announceExit (broadcast : Broadcast) (reason : String) : BaseIO (Except String Unit) :=
  broadcast.notice fun _ =>
    [⟨"eos", .flag, true⟩, ⟨"kind", .text, "exit"⟩, ⟨"reason", .text, controlDiagnostic reason⟩]

def Broadcast.publish (broadcast : Broadcast) (generation : UInt64) (text : WireText) : BaseIO Bool := do
  let parsed := (Json.parse text.val).toOption
  let identity := parsed.bind fun value => (coreIdentityFromJson value).toOption
  let nowMonoMs ← IO.monoMsNow
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
    let next := state.observe text parsed nowMonoMs
    set next
    return some (next.subscribers.values.map (·.wake))
  match wakes with
  | none => return false
  | some wakes =>
    for wake in wakes do wake.resolve ()
    return true

structure Subscription where
  private mk ::
  private broadcast : Broadcast
  private id : UInt64

structure ReplaySnapshot where
  identity : Identity
  control : Option WireText
  world : Option ((key : MapKey) × WorldMemory key)
  frames : Buffer WireText replayCapacity

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

def Subscription.close (subscription : Subscription) : BaseIO Unit := do
  let wake ← subscription.broadcast.state.atomically do
    let state ← get
    let wake := (state.subscribers.values.find? (·.id == subscription.id)).map (·.wake)
    let remaining := state.subscribers.values.filter (·.id != subscription.id)
    set { state with subscribers := ⟨remaining,
      Nat.le_trans (List.length_filter_le _ _) state.subscribers.bounded⟩ }
    return wake
  if let some wake := wake then wake.resolve ()

inductive SubscriptionRead where
  | closed
  | item (text : WireText)
  | wait (task : Task (Option Unit))

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

def Subscription.receive (subscription : Subscription) : BaseIO (Option WireText) := do
  for _ in forever do
    match ← subscription.poll with
    | .closed => return none
    | .item text => return some text
    | .wait task =>
      if (← IO.wait task).isNone then return none
  return none

end Acorn.Host.Viewer
