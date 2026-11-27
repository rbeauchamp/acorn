import Acorn.Host.Viewer.Sensed
import Acorn.Host.Viewer.IdentityHandshake
import Acorn.Host.Viewer.ControlTelemetry
import Acorn.Host.Viewer.ServerFrame
import Std.Sync.Mutex

namespace Acorn.Host.Viewer

def connectionCapacity : Nat := 16

def pollVersionState (seen current : Nat) : Bool × Nat :=
  if seen < current then (true, current) else (false, seen)

theorem pollVersionState_catches_up (seen current : Nat) (h : seen < current) :
    pollVersionState seen current = (true, current) := by
  simp [pollVersionState, h]

theorem pollVersionState_idle (seen current : Nat) (h : current ≤ seen) :
    pollVersionState seen current = (false, seen) := by
  have hnot : ¬ (seen < current) := Nat.not_lt.mpr h
  simp [pollVersionState, hnot]

theorem pollVersionState_coalesces (seen current : Nat) :
    (pollVersionState (pollVersionState seen current).2 current).1 = false := by
  unfold pollVersionState
  split <;> simp [*]

private structure Subscriber where
  id : UInt64
  seenVersion : Nat
  wake : IO.Promise Unit

private structure IdentityWait where
  generation : UInt64
  candidate : Option CoreIdentity := none
  refused : Bool := false
  frames : Buffer (DecodedTelemetry × Nat) replayCapacity := .empty
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
  detail : Option ControlDetail := none
  waiting : Option IdentityWait := none
  adopted : Option (UInt64 × CoreIdentity) := none
  world : Option ((key : MapKey) × WorldMemory key) := none
  worldPartial : Bool := false
  worldRevision : Nat := 0
  observer : ServerObserverState
  subscribers : Buffer Subscriber connectionCapacity := .empty
  sequence : UInt64 := 0
  version : Nat := 0

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

private def BroadcastState.observe (state : BroadcastState) (decoded : DecodedTelemetry)
    (nowMonoMs : Nat) : BroadcastState :=
  let next := { state with
    observer := state.observer.observe decoded nowMonoMs
    version := state.version + 1 }
  match decoded.sensed with
  | none => next
  | some sensed =>
    if sensed.key.run == state.lifecycle.identityValue.run &&
        sensed.key.seed == state.lifecycle.identityValue.seed then
      let ⟨key, memory⟩ := sensed.absorb state.world
      next.withWorld (some ⟨key, if state.worldPartial then memory.markPartial else memory⟩)
    else next

private def BroadcastState.observation (state : BroadcastState) : ControlObservation :=
  ⟨state.checkpointRefused, state.worldPartial⟩

private def sameControlState (prevLifecycle nextLifecycle : Lifecycle)
    (prevObs nextObs : ControlObservation)
    (prevDetail : Option ControlDetail) (nextDetail : ControlDetail) : Bool :=
  match prevDetail with
  | none => false
  | some prev =>
    prevLifecycle.identityValue == nextLifecycle.identityValue &&
      prevLifecycle.phaseValue == nextLifecycle.phaseValue &&
      prevLifecycle.desiredValue == nextLifecycle.desiredValue &&
      prevLifecycle.failureCount == nextLifecycle.failureCount &&
      prevObs.checkpointRefused == nextObs.checkpointRefused &&
      prevObs.mapPartial == nextObs.mapPartial &&
      prev.transition == nextDetail.transition &&
      prev.reason == nextDetail.reason &&
      prev.clearDisabled == nextDetail.clearDisabled &&
      prev.abnormalExit == nextDetail.abnormalExit &&
      prev.log.checkpoint == nextDetail.log.checkpoint &&
      controlTail prevLifecycle prev == controlTail nextLifecycle nextDetail

def Broadcast.snapshot (broadcast : Broadcast) : BaseIO BroadcastSnapshot :=
  broadcast.state.atomically do
    let state ← get
    return ⟨state.lifecycle, state.observation, state.detail, state.world, state.observer⟩

def Broadcast.commitIdentity (broadcast : Broadcast) (generation : UInt64) (actual : CoreIdentity)
    (lifecycle : Lifecycle) (detail : ControlDetail) : BaseIO (Except String Nat) := do
  let result : Except String (Nat × List (IO.Promise Unit)) ← broadcast.state.atomically do
    let state ← get
    let some waiting := state.waiting | return .error "no identity handshake is pending"
    if waiting.generation != generation || waiting.candidate != some actual ||
        !state.lifecycle.ownsIdentity generation then return .error "identity handshake is stale"
    let forwarding := state.lifecycle.phaseValue.accepts generation
    let changed := state.lifecycle.identityValue != actual.identity
    let newWorld := state.lifecycle.identityValue.run != actual.identity.run ||
      state.lifecycle.identityValue.seed != actual.identity.seed
    let base := if newWorld then { state.withWorld none with worldPartial := false } else state
    let mut next : BroadcastState := { base with
      lifecycle, detail := some detail, waiting := none, adopted := some (generation, actual)
      observer := if changed then .empty actual.identity else state.observer.resetIdentity actual.identity
      version := state.version + 1 }
    if forwarding then
      for (decoded, capturedMs) in waiting.frames.values do
        next := next.observe decoded capturedMs
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
    { state.withWorld none with
      worldPartial := false, waiting := none, adopted := none, checkpointRefused := false }

def Broadcast.settle (broadcast : Broadcast) (lifecycle : Lifecycle) (changes : List Change)
    (detail : ControlDetail) : BaseIO (Except String Unit) := do
  let isNewRun := changes.any fun change => match change with | .newRun => true | _ => false
  let wakes : List (IO.Promise Unit) ← broadcast.state.atomically do
    let prev ← get
    let changed := changes.foldl BroadcastState.change prev
    let observer := if isNewRun then .empty lifecycle.identityValue
      else changed.observer.resetIdentity lifecycle.identityValue
    let nextObs := changed.observation
    let modified := !changes.isEmpty ||
      !sameControlState prev.lifecycle lifecycle prev.observation nextObs prev.detail detail
    let state := { changed with
      lifecycle, detail := some detail, observer
      version := if modified then changed.version + 1 else changed.version }
    set state
    return if modified then state.subscribers.values.map (·.wake) else []
  for wake in wakes do wake.resolve ()
  return .ok ()

private def Broadcast.notify (broadcast : Broadcast) : BaseIO (Except String Unit) := do
  let wakes ← broadcast.state.atomically do
    let state ← get
    let next := { state with version := state.version + 1 }
    set next
    return next.subscribers.values.map (·.wake)
  for wake in wakes do wake.resolve ()
  return .ok ()

def Broadcast.announceCleared (broadcast : Broadcast) : BaseIO (Except String Unit) :=
  broadcast.notify

def Broadcast.announceExit (broadcast : Broadcast) (_reason : String) : BaseIO (Except String Unit) :=
  broadcast.notify

def Broadcast.recordIngressDrop (broadcast : Broadcast) (generation : UInt64) (count : Nat) :
    BaseIO Unit := do
  if count == 0 then return
  broadcast.state.atomically do
    let state ← get
    if let some waiting := state.waiting then
      if waiting.generation == generation then
        set { state with waiting := some { waiting with dropped := waiting.dropped + count } }
        return
    if state.lifecycle.phaseValue.accepts generation then
      set state.loseWorldTail

def Broadcast.publishDecoded (broadcast : Broadcast) (generation : UInt64)
    (decoded : DecodedTelemetry) (nowMonoMs : Nat) : BaseIO Bool := do
  let wakes ← broadcast.state.atomically do
    let state ← get
    if let some waiting := state.waiting then
      if waiting.generation == generation then
        if waiting.refused || !state.lifecycle.ownsIdentity generation || decoded.identity.isNone then
          return none
        if waiting.candidate.isSome && waiting.candidate != decoded.identity then return none
        let waiting := { waiting with
          candidate := waiting.candidate.or decoded.identity
          dropped := waiting.dropped + if waiting.frames.values.length == replayCapacity then 1 else 0
          frames := waiting.frames.retain (decoded, nowMonoMs) }
        set { state with waiting := some waiting }
        return some []
    if !state.lifecycle.phaseValue.accepts generation then return none
    if let some (owner, actual) := state.adopted then
      if owner == generation && decoded.identity != some actual then return none
    let next := state.observe decoded nowMonoMs
    set next
    return some (next.subscribers.values.map (·.wake))
  match wakes with
  | none => return false
  | some wakes =>
    for wake in wakes do wake.resolve ()
    return true

def Broadcast.publish (broadcast : Broadcast) (generation : UInt64) (text : WireText) : BaseIO Bool := do
  let decoded := decodeTelemetry text
  let nowMonoMs ← IO.monoMsNow
  broadcast.publishDecoded generation decoded nowMonoMs

structure Subscription where
  private mk ::
  private broadcast : Broadcast
  private id : UInt64

def Broadcast.subscribe (broadcast : Broadcast) : BaseIO (Option Subscription) := do
  let wake ← IO.Promise.new
  broadcast.state.atomically do
    let state ← get
    if state.sequence == 18446744073709551615 then return none
    let id := state.sequence + 1
    let subscriber : Subscriber := ⟨id, state.version, wake⟩
    match state.subscribers.offer subscriber with
    | none => return none
    | some subscribers =>
      set { state with subscribers, sequence := id }
      return some ⟨broadcast, id⟩

def Subscription.close (subscription : Subscription) : BaseIO Unit := do
  let wake ← subscription.broadcast.state.atomically do
    let state ← get
    let wake := (state.subscribers.values.find? (·.id == subscription.id)).map (·.wake)
    let remaining := state.subscribers.values.filter (·.id != subscription.id)
    set { state with subscribers := ⟨remaining,
      Nat.le_trans (List.length_filter_le _ _) state.subscribers.bounded⟩ }
    return wake
  if let some wake := wake then wake.resolve ()

def Subscription.snapshot (subscription : Subscription) : BaseIO (Option BroadcastSnapshot) :=
  subscription.broadcast.state.atomically do
    let state ← get
    if !(state.subscribers.values.any (·.id == subscription.id)) then return none
    let subscribers := state.subscribers.values.map fun current =>
      if current.id == subscription.id then { current with seenVersion := state.version } else current
    set { state with subscribers := ⟨subscribers, by simpa [subscribers] using state.subscribers.bounded⟩ }
    return some ⟨state.lifecycle, state.observation, state.detail, state.world, state.observer⟩

inductive SubscriptionRead where
  | closed
  | updated
  | wait (task : Task (Option Unit))

def Subscription.poll (subscription : Subscription) : BaseIO SubscriptionRead := do
  let wake ← IO.Promise.new
  subscription.broadcast.state.atomically do
    let state ← get
    let some subscriber := state.subscribers.values.find? (·.id == subscription.id) | return .closed
    let (changed, nextVersion) := pollVersionState subscriber.seenVersion state.version
    let (result, next) : SubscriptionRead × Subscriber :=
      if changed then
        (.updated, { subscriber with seenVersion := nextVersion })
      else
        (.wait wake.result?, { subscriber with wake })
    let subscribers := state.subscribers.values.map fun current =>
      if current.id == subscription.id then next else current
    set { state with subscribers := ⟨subscribers, by simpa [subscribers] using state.subscribers.bounded⟩ }
    return result

end Acorn.Host.Viewer
