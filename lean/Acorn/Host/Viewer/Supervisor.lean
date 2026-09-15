/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.SupervisedProcess
import Acorn.Host.Viewer.ControlTelemetry
import Acorn.Host.Viewer.MapCodec
import Acorn.Host.Viewer.HttpServer

/-!
# Durable native supervisor actor

One actor owns state publication, launch preparation, process polling, and
whole-run replacement. HTTP only appends to a bounded command queue. Start
requires successful state publication before spawn; Stop still raises wind-up
when persistence fails, reporting that restart intent could not be saved.
A moved directory is never reused through its retired capability. Replacement
publication must complete before a new identity or process can be installed.
-/
namespace Acorn.Host.Viewer

/-- Complete identity arguments selected before the actual checkpoint outcome. -/
structure CoreLaunch where
  /-- Durable run and world identity; the checkpoint selects its logical epoch. -/
  identity : Identity
  /-- Logical epoch supplied for missing/refused checkpoint construction. -/
  newEpoch : UInt64
  /-- Source of fresh construction. -/
  origin : NewAgentOrigin

/-- Launch preparation refuses epoch reuse at exhaustion. -/
def PersistedState.launch (state : PersistedState) : Except String CoreLaunch := do
  unless state.identity.browserSafe do throw "viewer identity exceeds browser integer precision"
  if state.processStarted && state.identity.agentEpoch.toNat ≥ browserIntegerMax then
    throw "logical agent epoch exhausted"
  return ⟨state.identity,
    if state.processStarted then state.identity.agentEpoch + 1 else state.identity.agentEpoch,
    if state.processStarted then .fresh else state.origin⟩

/-- Native bootstrap supplies fixed executable configuration and a fresh seed source.
Only launch identity and the owned checkpoint path vary between processes. -/
structure SupervisorConfig where
  /-- Actual executable, resolved before supervision. -/
  executable : System.FilePath
  /-- Pure argument construction from the admitted launch and run-owned path. -/
  arguments : CoreLaunch → System.FilePath → Array String
  /-- A configuration that cannot preserve whole-run ownership disables Clear. -/
  clearDisabled : Option String
  /-- Actual native source of new terrain seeds, called only for Clear. -/
  freshSeed : IO UInt64

private structure SupervisorState where
  directory : RunDirectory
  persisted : PersistedState
  detail : ControlDetail
  replacement : Option PersistedState := none
  publicationReady : Bool := true
  mapWrittenAt : Nat := 0
  mapWrittenRevision : Option Nat := none
  operatorStopped : Bool := false
  failure : Option String := none

/-- Bounded lifecycle mailbox; there is one actor consumer. -/
def commandCapacity : Nat := 4

/-- Native supervisor owns its command queue and serializes complete actor steps. -/
structure Supervisor where
  private mk ::
  private config : SupervisorConfig
  private broadcast : Broadcast
  private process : SupervisedProcess
  private queue : Std.Mutex (Buffer Command commandCapacity)
  private state : Std.Mutex SupervisorState

/-- Construct only after the bootstrap has admitted and published the initial state. -/
def Supervisor.new (config : SupervisorConfig) (directory : RunDirectory)
    (persisted : PersistedState) : IO Supervisor := do
  unless persisted.identity.browserSafe do
    throw (IO.userError "viewer identity exceeds browser integer precision; retained state is unchanged")
  directory.writeState persisted
  let mapRead ← directory.readMap persisted.identity
  let mapRefused := match mapRead with | .refused _ => true | _ => false
  let broadcast ← Broadcast.new persisted.identity persisted.desired (persisted.processStarted || mapRefused)
  let mapReason ← match mapRead with
    | .missing => pure "viewer initialized"
    | .refused reason => pure s!"viewer initialized; retained map refused: {reason}"
    | .restored _ memory =>
      let _ ← broadcast.restoreWorld memory
      pure "viewer initialized; retained map restored as partial"
  let detail : ControlDetail := {
    transition := .initialized
    reason := mapReason
    clearDisabled := config.clearDisabled
    log := {}
    mapPartial := ← broadcast.worldIsPartial }
  match ← broadcast.publishControl (controlTelemetryLine · detail) with
  | .error reason => throw (IO.userError reason)
  | .ok () => pure ()
  return ⟨config, broadcast, ← SupervisedProcess.new broadcast, ← Std.Mutex.new .empty,
    ← Std.Mutex.new { directory, persisted, detail }⟩

/-- HTTP may retain only four closed lifecycle commands, with no process handle. -/
def Supervisor.submit (supervisor : Supervisor) (command : Command) : BaseIO ControlResult := do
  if command == .clear && supervisor.config.clearDisabled.isSome then return .clearUnavailable
  supervisor.queue.atomically do
    match (← get).offer command with
    | none => return .busy
    | some queue => set queue; return .accepted

/-- One consistent registration snapshot supplies control, map and subsequent replay. -/
def supervisorInitial (snapshot : ReplaySnapshot) : BaseIO InitialFrames := do
  let map := snapshot.world.bind fun ⟨_, memory⟩ => memory.frame.toOption
  return ⟨snapshot.control, map⟩

/-- HTTP and process output use this actor's exact same broadcaster. -/
def Supervisor.http (supervisor : Supervisor) (assets : ViewerAssets) : IO HttpViewer :=
  HttpViewer.new supervisor.broadcast assets supervisorInitial supervisor.submit

private def Supervisor.publish (supervisor : Supervisor) (state : SupervisorState)
    (transition : ControlTransition) (reason : String) : IO SupervisorState := do
  let state := { state with
    detail.transition := transition, detail.reason := controlDiagnostic reason
    failure := if transition == .failed then some (controlDiagnostic reason) else state.failure
    detail.mapPartial := ← supervisor.broadcast.worldIsPartial }
  match ← supervisor.broadcast.publishControl (controlTelemetryLine · state.detail) with
  | .error reason => throw (IO.userError reason)
  | .ok () => return state

private def saveIntent (state : SupervisorState) (desired : Desired) : IO SupervisorState := do
  let persisted := { state.persisted with desired }
  state.directory.writeState persisted
  return { state with persisted, publicationReady := true }

private def Supervisor.command (supervisor : Supervisor) (state : SupervisorState)
    (command : Command) : IO SupervisorState := do
  let state := { state with operatorStopped := command != .start }
  if let some replacement := state.replacement then
    if command == .clear then
      return ← supervisor.publish state .failed "replacement state publication is pending; Clear refused"
    let desired := if command == .stop then Desired.stopped else .running
    return { state with replacement := some { replacement with desired } }
  let desired := match command with | .start => Desired.running | .stop | .clear => .stopped
  let saved : Except String SupervisorState ← try pure (.ok (← saveIntent state desired))
    catch error => pure (.error error.toString)
  match saved with
  | .error reason =>
    -- Stop/Clear must still wind up the live process; failed persistence cannot start or archive.
    supervisor.broadcast.request .stop
    return ← supervisor.publish { state with publicationReady := false } .failed
      s!"intent could not be saved; process wind-up requested: {reason}"
  | .ok state =>
    supervisor.broadcast.request command
    let (transition, reason) := match command with
      | .start => (ControlTransition.startRequested, "operator requested Start")
      | .stop => (.stopRequested, "operator requested Stop")
      | .clear => (.clearRequested, "operator requested whole-run Clear")
    return ← supervisor.publish state transition reason

private def Supervisor.finishReplacement (supervisor : Supervisor) (state : SupervisorState) :
    IO SupervisorState := do
  let some replacement := state.replacement | return state
  try
    state.directory.writeState replacement
  catch error =>
    return ← supervisor.publish state .failed s!"old run archived; replacement state not published: {error}"
  supervisor.broadcast.replacementIntent replacement.desired
  if !(← supervisor.broadcast.archived replacement.identity) then
    return ← supervisor.publish state .failed "replacement identity could not be installed"
  let state ← supervisor.publish
    { state with
      persisted := replacement, replacement := none, publicationReady := true
      detail.log := {}, detail.abnormalExit := false, failure := none
      mapWrittenAt := 0, mapWrittenRevision := none } .cleared "previous run archived; new zero-knowledge identity installed"
  match ← supervisor.broadcast.announceCleared with
  | .error reason => return ← supervisor.publish state .failed reason
  | .ok () => return state

private def Supervisor.clear (supervisor : Supervisor) (state : SupervisorState) : IO SupervisorState := do
  let lifecycle ← supervisor.broadcast.lifecycle
  let some intended := lifecycle.archiveIntent | return state
  if !state.publicationReady then return state
  if state.persisted.identity.agentEpoch.toNat ≥ browserIntegerMax then
    supervisor.broadcast.request .stop
    return ← supervisor.publish state .failed "Clear refused: logical agent epoch exhausted"
  let seed ← try supervisor.config.freshSeed
    catch error =>
      supervisor.broadcast.request .stop
      return ← supervisor.publish state .failed s!"Clear refused before archival: {error}"
  if seed.toNat > browserIntegerMax then
    supervisor.broadcast.request .stop
    return ← supervisor.publish state .failed "Clear refused before archival: seed exceeds browser integer precision"
  let identity : Identity := ⟨state.persisted.identity.run + 1, seed,
    state.persisted.identity.agentEpoch + 1⟩
  let stamp := (min (← IO.monoMsNow) (2 ^ 64 - 1)).toUInt64
  let some outcome ← supervisor.process.archive state.directory stamp (do
    let _ ← supervisor.publish state .archiving "archiving the complete run directory"
    pure ()) | return state
  match outcome with
  | .unchanged reason =>
    return ← supervisor.publish state .failed s!"Clear failed; old run remains: {reason}"
  | .moved archive reason =>
    return ← supervisor.publish { state with publicationReady := false } .failed
      s!"old run archived at {archive}; replacement directory unavailable: {reason}"
  | .ready archive =>
    let directory ← try RunDirectory.open state.directory.rootPath
      catch error =>
        return ← supervisor.publish { state with publicationReady := false } .failed
          s!"old run archived at {archive}; replacement owner unavailable: {error}"
    let replacement : PersistedState := ⟨identity, intended, .cleared, false⟩
    supervisor.finishReplacement { state with
      directory, replacement := some replacement, publicationReady := false }

private def Supervisor.launch (supervisor : Supervisor) (state : SupervisorState) : IO SupervisorState := do
  if !state.publicationReady || state.replacement.isSome then return state
  let lifecycle ← supervisor.broadcast.lifecycle
  let now := (min (← IO.monoMsNow) (2 ^ 64 - 1)).toUInt64
  if (lifecycle.reserve now).isNone then return state
  let launch ← match state.persisted.launch with
    | .ok launch => pure launch
    | .error reason =>
      supervisor.broadcast.request .stop
      return ← supervisor.publish state .failed reason
  -- Persist the attempted launch before spawn; checkpoint outcome still owns the actual epoch.
  let persisted := { state.persisted with processStarted := true }
  try state.directory.writeState persisted
  catch error =>
    supervisor.broadcast.request .stop
    return ← supervisor.publish { state with publicationReady := false } .failed
      s!"launch intent publication failed: {error}"
  let state := { state with persisted }
  match ← supervisor.process.launch state.directory supervisor.config.executable
      (supervisor.config.arguments launch (state.directory.path .weights)) with
  | .occupied | .deferred => return state
  | .refused reason =>
    let state ← supervisor.publish state .failed s!"spawn refused: {reason}"
    match ← supervisor.broadcast.announceExit state.detail.reason with
    | .error reason => return ← supervisor.publish state .failed reason
    | .ok () => return state
  | .started _ =>
    return ← supervisor.publish { state with
      detail.log := {}, detail.abnormalExit := false
      operatorStopped := false, failure := none }
      .coreStarted "core process started"

private def Supervisor.flushMap (supervisor : Supervisor) (state : SupervisorState)
    (force : Bool := false) : IO SupervisorState := do
  if !state.publicationReady || state.replacement.isSome then return state
  let now ← IO.monoMsNow
  if !force && now - state.mapWrittenAt < 10000 then return state
  let state := { state with mapWrittenAt := now }
  let (revision, world) ← supervisor.broadcast.worldForWrite
  if state.mapWrittenRevision == some revision then return state
  if let some ⟨_, memory⟩ := world then
    try
      state.directory.writeMap memory
      return { state with mapWrittenRevision := some revision }
    catch error => return ← supervisor.publish state .failed s!"retained map publication refused: {error}"
  return state

private def exitReason (exit : ProcessExit) : String :=
  s!"core exited with status {exit.code}" ++
    if exit.code != 0 then "; abnormal termination; learning since the last successful checkpoint may be lost" else ""

private def pipeReason (name : String) (result : PipeResult) : String :=
  match result with
  | .eof => ""
  | .refused reason => s!"; {name} read refused: {controlDiagnostic reason}"

private def outputReason (output : OutputStatus) (stderr : PipeResult) (log : LogStatus) : String :=
  (log.checkpoint.map (fun status => "; " ++ status.line)).getD
    "; final checkpoint status unavailable" ++
  (match output.completion with
    | none => "; stdout completion unavailable"
    | some result => pipeReason "stdout" result) ++ pipeReason "stderr" stderr ++
  s!"; stdout refused oversized={output.oversized}, malformed={output.malformed}, stale={output.stale}" ++
  s!"; stderr log dropped={log.dropped}, oversized={log.oversized}, write failures={log.failures}" ++
  (log.lastFailure.map (fun reason => s!"; last log error: {controlDiagnostic reason}")).getD ""

private def terminationFailed (exit : ProcessExit) (output : OutputStatus)
    (stderr : PipeResult) (log : LogStatus) : Bool :=
  let pipesFailed := match output.completion, stderr with
    | some .eof, .eof => false
    | _, _ => true
  exit.code != 0 || log.checkpoint == some .failed || pipesFailed || log.failures != 0

private def exitTransition (exit : ProcessExit) (lifecycle : Lifecycle) : ControlTransition :=
  if exit.stopRequested then .coreStopped
  else if lifecycle.desiredValue == .running then .restartScheduled else .failed

private def Supervisor.identity (supervisor : Supervisor) (state : SupervisorState) : IO SupervisorState := do
  let some (generation, actual) ← supervisor.broadcast.pendingIdentity | return state
  unless actual.identity.browserSafe do
    supervisor.broadcast.refuseIdentity generation
    return ← supervisor.publish { state with publicationReady := false } .failed
      "core identity exceeds browser integer precision; preserving durable identity and refusing observation"
  let persisted := state.persisted.adopt actual
  try state.directory.writeState persisted
  catch error =>
    supervisor.broadcast.request .stop
    return ← supervisor.publish { state with publicationReady := false } .failed
      s!"core identity could not be persisted; observation release refused: {error}"
  let detail := { state.detail with
    reason := "core reported the identity selected by checkpoint loading" }
  match ← supervisor.broadcast.commitIdentity generation actual (controlTelemetryLine · detail) with
  | .error reason =>
    supervisor.broadcast.request .stop
    return ← supervisor.publish { state with persisted, publicationReady := false } .failed reason
  | .ok dropped =>
    let state := { state with persisted, detail, publicationReady := true }
    if dropped > 0 then
      return ← supervisor.publish state detail.transition
        s!"checkpoint-selected identity persisted; {dropped} pending observer records dropped"
    return state

/-- One actor step never waits for pipe EOF. Native state/map IO can block this
actor but cannot block HTTP queue admission or the core's output pipe readers. -/
def Supervisor.step (supervisor : Supervisor) : IO Unit :=
  supervisor.state.atomically do
    let mut state ← get
    state ← supervisor.identity state
    let command ← supervisor.queue.atomically do
      match (← get).pop with
      | none => return none
      | some (command, queue) => set queue; return some command
    if let some command := command then state ← supervisor.command state command
    match ← supervisor.process.poll with
    | .finished exit stdout stderr log =>
      let reason := exitReason exit ++ outputReason stdout stderr log
      state := { state with
        detail.log := log, detail.abnormalExit := exit.code != 0
        failure := if terminationFailed exit stdout stderr log then some reason else state.failure }
      state ← supervisor.flushMap state true
      let lifecycle ← supervisor.broadcast.lifecycle
      state ← supervisor.publish state (exitTransition exit lifecycle)
        reason
      if !exit.stopRequested && !state.operatorStopped then
        match ← supervisor.broadcast.announceExit state.detail.reason with
        | .error reason => state ← supervisor.publish state .failed reason
        | .ok () => pure ()
      try state ← saveIntent state lifecycle.desiredValue
      catch error =>
        state ← supervisor.publish { state with publicationReady := false } .failed
          s!"process exited; intent publication failed: {error}"
    | .refused reason => state ← supervisor.publish state .failed reason
    | .draining exit =>
      state := { state with detail.abnormalExit := exit.code != 0 }
      let lifecycle ← supervisor.broadcast.lifecycle
      state ← supervisor.publish state (exitTransition exit lifecycle)
        (exitReason exit ++ "; process readers are draining")
    | .empty | .running _ _ => pure ()
    -- Reaping cannot strand a candidate delivered during the first identity check.
    -- Once joins finish, no further pipe callback can race this final attribution.
    state ← supervisor.identity state
    state ← if state.replacement.isSome then supervisor.finishReplacement state else supervisor.clear state
    state ← supervisor.flushMap state
    state ← supervisor.launch state
    -- Includes generation-admitted checkpoint refusals without repeating unchanged frames.
    state ← supervisor.publish state state.detail.transition state.detail.reason
    set state

/-- Graceful viewer shutdown retains the process slot until reap and pipe drain.
The original durable run intent is preserved for the next viewer start. Host
signal delivery and eventual pipe closure remain native liveness assumptions.
Publication errors cannot skip wind-up; terminal failures are reported after it. -/
def Supervisor.shutdown (supervisor : Supervisor) : IO Unit := do
  let failed ← IO.mkRef false
  let report : String → IO Unit := fun reason => do
    failed.set true
    try IO.eprintln s!"viewer shutdown: {reason}" catch _ => pure ()
  let update : IO Unit → IO Unit := fun action => do
    try action catch error => report error.toString
  supervisor.broadcast.request .stop
  update do
    supervisor.state.atomically do
      if let some reason := (← get).failure then report reason
      let state ← supervisor.publish (← get) .stopRequested
        "viewer closing; finishing the current attempt and checkpoint"
      set state
  repeat
    update do
      supervisor.state.atomically do set (← supervisor.identity (← get))
    let outcome ← try supervisor.process.poll catch error => pure (.refused error.toString)
    let finished ← match outcome with
      | .empty => pure true
      | .finished exit stdout stderr log =>
        let reason := exitReason exit ++ outputReason stdout stderr log
        update (IO.println reason)
        if terminationFailed exit stdout stderr log then
          failed.set true
        update do
          supervisor.state.atomically do
            let previous ← get
            let state := { previous with
              detail.log := log, detail.abnormalExit := exit.code != 0
              failure := if terminationFailed exit stdout stderr log then some reason else previous.failure }
            -- Retain observations even if publishing the final frame fails.
            set state
            set (← supervisor.publish state .coreStopped reason)
        pure true
      | .refused reason => report s!"retaining process ownership: {reason}"; pure false
      | .running _ _ | .draining _ => pure false
    if finished then
      update do
        supervisor.state.atomically do
          let state ← supervisor.identity (← get)
          let state ← supervisor.flushMap state true
          set state
          if let some reason := state.failure then report reason
      if ← failed.get then throw (IO.userError "viewer closed with failures; see the diagnostics above")
      return
    IO.sleep 50

end Acorn.Host.Viewer
