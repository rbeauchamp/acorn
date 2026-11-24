import Acorn.Host.Viewer.PipePump
import Acorn.Host.Viewer.IdentityHandshake

namespace Acorn.Host.Viewer

def healthyRunMs : Nat := 30000

def mapInterval : Nat := 10000

structure CoreLaunch where
  identity : Identity
  newEpoch : UInt64
  origin : NewAgentOrigin

def PersistedState.launch (state : PersistedState) : Except String CoreLaunch := do
  unless state.identity.browserSafe do throw "viewer identity exceeds browser integer precision"
  if state.processStarted && state.identity.agentEpoch.toNat ≥ browserIntegerMax then
    throw "logical agent epoch exhausted"
  return ⟨state.identity,
    if state.processStarted then state.identity.agentEpoch + 1 else state.identity.agentEpoch,
    if state.processStarted then .fresh else state.origin⟩

def Command.desired : Command → Desired
  | .start => .running
  | .stop | .clear => .stopped

def clockWord (now : Nat) : UInt64 := (min now (2 ^ 64 - 1)).toUInt64

inductive Slot where
  | empty
  | live (generation : UInt64)
  | draining (generation : UInt64) (code : UInt32) (requested : Bool)
  deriving DecidableEq

inductive Owner where
  | current
  | retired (reason : String)
  deriving DecidableEq

inductive Closing where
  | open
  | closing (failed : Bool)
  | closed (failed : Bool)
  deriving DecidableEq

structure ExitReport where
  detail : ControlDetail
  failure : Option String
  transition : ControlTransition
  reason : String
  announce : Bool

inductive Call where
  | writeState (state : PersistedState)
  | writeMap (skip : Option Nat)
  | spawn (generation : UInt64) (launch : CoreLaunch)
  | windUp (generation : UInt64)
  | commit (generation : UInt64) (actual : CoreIdentity) (lifecycle : Lifecycle)
      (detail : ControlDetail)
  | seed
  | archive (stamp : UInt64)
  | reopen

def Call.Result : Call → Type
  | .writeState _ => Except String Unit
  | .writeMap _ => Except String (Option Nat)
  | .spawn _ _ => Except String Unit
  | .windUp _ => Except String Unit
  | .commit _ _ _ _ => Except String Nat
  | .seed => Except String UInt64
  | .archive _ => ArchiveResult
  | .reopen => Except String Unit

inductive Pending where
  | intent (command : Command) (state : PersistedState)
  | launch (state : PersistedState) (launch : CoreLaunch)
  | spawn (generation : UInt64) (launch : CoreLaunch)
  | windUp (generation : UInt64)
  | adopt (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
  | commit (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
      (detail : ControlDetail)
  | exitMap (report : ExitReport) (skip : Option Nat)
  | exitIntent (state : PersistedState)
  | map (skip : Option Nat)
  | closeMap (skip : Option Nat)
  | seed (intended : Desired)
  | archive (identity : Identity) (intended : Desired) (stamp : UInt64)
  | reopen (identity : Identity) (intended : Desired) (archive : System.FilePath)
  | replacement (state : PersistedState) (ackStop : Bool := false)

def Pending.call (pending : Pending) (lifecycle : Lifecycle) : Call :=
  match pending with
  | .intent _ state | .launch state _ | .adopt _ _ state | .exitIntent state
  | .replacement state _ => .writeState state
  | .spawn generation plan => .spawn generation plan
  | .windUp generation => .windUp generation
  | .commit generation actual _ detail =>
    .commit generation actual (lifecycle.adoptFinalIdentity generation actual.identity) detail
  | .exitMap _ skip | .map skip | .closeMap skip => .writeMap skip
  | .seed _ => .seed
  | .archive _ _ stamp => .archive stamp
  | .reopen _ _ _ => .reopen

def Pending.writes : Pending → Bool
  | .intent _ _ | .launch _ _ | .adopt _ _ _ | .exitIntent _ | .replacement _ _
  | .exitMap _ _ | .map _ | .closeMap _ | .archive _ _ _
  | .reopen _ _ _ => true
  | .spawn _ _ | .windUp _ | .commit _ _ _ _ | .seed _ => false

def Pending.clears : Pending → Bool
  | .intent command _ => command == .clear
  | .seed _ | .archive _ _ _ | .reopen _ _ _ | .replacement _ _ => true
  | _ => false

def Pending.serves : Pending → Bool
  | .intent _ _ | .exitIntent _ | .launch _ _ | .spawn _ _ | .map _ | .exitMap _ _ => true
  | pending => pending.clears

structure Core where
  lifecycle : Lifecycle
  slot : Slot
  persisted : PersistedState
  replacement : Option PersistedState
  owner : Owner
  detail : ControlDetail
  failure : Option String
  mapAt : Nat
  mapRevision : Option Nat
  closing : Closing
  last : Nat
  pending : Option Pending

inductive Follow where
  | announceExit (reason : String)
  | announceCleared
  | ackStop
  | refuseStop (reason : String)
  | attach (generation : UInt64)
  | say (text : String)
  | complain (text : String)

inductive Effect where
  | settle (lifecycle : Lifecycle) (changes : List Change) (detail : ControlDetail)
  | follow (follow : Follow)

structure Stepped where
  core : Core
  changes : List Change := []
  follows : List Follow := []

def Stepped.effects (stepped : Stepped) : List Effect :=
  .settle stepped.core.lifecycle stepped.changes stepped.core.detail ::
    stepped.follows.map .follow

def Stepped.at (stepped : Stepped) (now : Nat) : Stepped :=
  { stepped with core := { stepped.core with last := now } }

inductive Event where
  | command (command : Command)
  | candidate (generation : UInt64) (actual : CoreIdentity)
  | exited (code : UInt32) (uptimeMs : Nat)
  | finished (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus)
  | refused (reason : String)
  | tick
  | close

def exitReason (code : UInt32) : String :=
  s!"core exited with status {code}" ++
    if code != 0 then
      "; abnormal termination; learning since the last successful checkpoint may be lost"
    else ""

private def pipeReason (name : String) (result : PipeResult) : String :=
  match result with
  | .eof => ""
  | .refused reason => s!"; {name} read refused: {controlDiagnostic reason}"

def outputReason (output : OutputStatus) (stderr : PipeResult) (log : LogStatus) : String :=
  (log.checkpoint.map (fun status => "; " ++ status.line)).getD
    "; final checkpoint status unavailable" ++
  (match output.completion with
    | none => "; stdout completion unavailable"
    | some result => pipeReason "stdout" result) ++ pipeReason "stderr" stderr ++
  s!"; stdout refused oversized={output.oversized}, malformed={output.malformed}, stale={output.stale}" ++
  s!"; stderr log dropped={log.dropped}, oversized={log.oversized}, write failures={log.failures}" ++
  (log.lastFailure.map (fun reason => s!"; last log error: {controlDiagnostic reason}")).getD ""

def terminationFailed (code : UInt32) (output : OutputStatus) (stderr : PipeResult)
    (log : LogStatus) : Bool :=
  let pipesFailed := match output.completion, stderr with
    | some .eof, .eof => false
    | _, _ => true
  code != 0 || log.checkpoint == some .failed || pipesFailed || log.failures != 0

def exitTransition (requested : Bool) (lifecycle : Lifecycle) : ControlTransition :=
  if requested then .coreStopped
  else if lifecycle.desiredValue == .running then .restartScheduled else .failed

namespace Core

def report (core : Core) (transition : ControlTransition) (reason : String) : Core :=
  let reason := controlDiagnostic reason
  { core with
    detail := { core.detail with transition, reason }
    failure := if transition == .failed then some reason else core.failure }

def windUpTarget (slot : Slot) (before after : Lifecycle) : Option UInt64 :=
  match slot with
  | .live generation =>
    if after.phaseValue == .stopping generation && before.phaseValue != .stopping generation then
      some generation
    else none
  | .empty | .draining _ _ _ => none

def moveTo (core : Core) (lifecycle : Lifecycle) : Core :=
  { core with
    lifecycle
    pending := (windUpTarget core.slot core.lifecycle lifecycle).map .windUp }

def stop (core : Core) : Core := core.moveTo (core.lifecycle.request .stop)

def mapWritable (core : Core) : Bool := core.owner == .current && core.replacement.isNone

def intentFailed (core : Core) (reason : String) (refuseStop : Bool := false) : Stepped :=
  ⟨core.stop.report .failed
    s!"intent write failed (persistence unconfirmed); process wind-up requested: {reason}",
    [], if refuseStop then [.refuseStop reason] else []⟩

def command (core : Core) (clearDisabled : Option String) (command : Command) : Stepped :=
  if command == .clear && clearDisabled.isSome then ⟨core, [], []⟩
  else match core.replacement with
  | some replacement =>
    if command == .clear then
      ⟨core.report .failed "replacement state publication is pending; Clear refused", [], []⟩
    else if command == .stop then
      let next := { replacement with desired := .stopped }
      match core.owner with
      | .retired reason => core.intentFailed reason true
      | .current =>
        ⟨{ core with
          replacement := some next
          pending := some (.replacement next true) }, [], []⟩
    else ⟨{ core with replacement := some { replacement with desired := command.desired } }, [], []⟩
  | none =>
    match core.owner with
    | .retired reason => core.intentFailed reason (command == .stop)
    | .current =>
      ⟨{ core with
        pending := some (.intent command { core.persisted with desired := command.desired }) },
        [], []⟩

def intentSaved (core : Core) (command : Command) (state : PersistedState) : Stepped :=
  let (transition, reason, follows) := match command with
    | .start => (ControlTransition.startRequested, "operator requested Start", [])
    | .stop =>
      if state.desired == .stopped then
        (.stopRequested, "operator requested Stop", [.ackStop])
      else
        (.stopRequested, "operator requested Stop",
          [.refuseStop "stop intent did not record stopped"])
    | .clear => (.clearRequested, "operator requested whole-run Clear", [])
  ⟨({ core with persisted := state }.moveTo (core.lifecycle.request command)).report
    transition reason, [], follows⟩

def adoptFailed (core : Core) (reason : String) : Stepped :=
  ⟨core.stop.report .failed
    s!"core identity could not be persisted; observation release refused: {reason}", [], []⟩

def candidate (core : Core) (generation : UInt64) (actual : CoreIdentity) : Stepped :=
  if !core.lifecycle.ownsIdentity generation then ⟨core, [], []⟩
  else if !actual.identity.browserSafe then
    ⟨core.stop.report .failed
      "core identity exceeds browser integer precision; preserving durable identity and refusing observation",
      [.refuseIdentity generation], []⟩
  else match core.owner with
    | .retired reason => core.adoptFailed reason
    | .current =>
      ⟨{ core with pending := some (.adopt generation actual (core.persisted.adopt actual)) },
        [], []⟩

def adopted (core : Core) (generation : UInt64) (actual : CoreIdentity)
    (state : PersistedState) : Stepped :=
  let detail := { core.detail with
    reason := "core reported the identity selected by checkpoint loading" }
  ⟨{ core with pending := some (.commit generation actual state detail) }, [], []⟩

def committed (core : Core) (generation : UInt64) (actual : CoreIdentity)
    (state : PersistedState) (detail : ControlDetail) (dropped : Nat) : Stepped :=
  let core := { core with
    persisted := state, detail
    lifecycle := core.lifecycle.adoptFinalIdentity generation actual.identity }
  if dropped > 0 then
    ⟨core.report detail.transition
      s!"checkpoint-selected identity persisted; {dropped} pending observer records dropped",
      [], []⟩
  else ⟨core, [], []⟩

def exited (core : Core) (now : Nat) (code : UInt32) (uptime : Nat) : Stepped :=
  match core.slot with
  | .live generation =>
    let requested := core.lifecycle.phaseValue == .stopping generation
    let failed := if requested then core.lifecycle
      else core.lifecycle.failed generation (clockWord now) (decide (uptime > healthyRunMs))
    let lifecycle := failed.retire generation
    ⟨({ core with
      lifecycle, slot := .draining generation code requested
      detail := { core.detail with abnormalExit := code != 0 } }).report
      (exitTransition requested lifecycle)
      (exitReason code ++ "; process readers are draining"), [.loseTail], []⟩
  | .empty | .draining _ _ _ => ⟨core, [], []⟩

def closed (core : Core) : Stepped :=
  match core.closing with
  | .closing failed =>
    ⟨{ core with closing := .closed (failed || core.failure.isSome) }, [],
      (core.failure.map fun reason => [Follow.complain reason]).getD []⟩
  | .open | .closed _ => ⟨core, [], []⟩

def closeOut (core : Core) : Stepped :=
  if core.mapWritable then ⟨{ core with pending := some (.closeMap core.mapRevision) }, [], []⟩
  else core.closed

def exitReported (core : Core) (report : ExitReport) : Stepped :=
  let core := ({ core with detail := report.detail, failure := report.failure }).report
    report.transition report.reason
  let follows := if report.announce then [Follow.announceExit core.detail.reason] else []
  match core.owner with
  | .retired reason =>
    ⟨core.report .failed s!"process exited; intent publication failed: {reason}", [], follows⟩
  | .current =>
    ⟨{ core with
      pending := some (.exitIntent { core.persisted with desired := core.lifecycle.desiredValue }) },
      [], follows⟩

def finished (core : Core) (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus) :
    Stepped :=
  match core.slot with
  | .draining generation code requested =>
    let reason := exitReason code ++ outputReason stdout stderr log
    let changes := if log.checkpoint == some .refused && core.lifecycle.ownsIdentity generation
      then [Change.refuseCheckpoint] else []
    let detail := { core.detail with log, abnormalExit := code != 0 }
    let failed := terminationFailed code stdout stderr log
    let failure := if failed then some reason else core.failure
    let core := { core with slot := .empty }
    match core.closing with
    | .open =>
      let report : ExitReport :=
        ⟨detail, failure, exitTransition requested core.lifecycle, reason, !requested⟩
      if core.mapWritable then
        ⟨{ core with pending := some (.exitMap report core.mapRevision) }, changes, []⟩
      else
        let reported := core.exitReported report
        { reported with changes := changes ++ reported.changes }
    | .closing before =>
      ⟨({ core with detail, failure, closing := .closing (before || failed) }).report
        .coreStopped reason, changes, [Follow.say reason]⟩
    | .closed _ => ⟨core, [], []⟩
  | .empty | .live _ => ⟨core, [], []⟩

def refused (core : Core) (reason : String) : Stepped :=
  match core.closing with
  | .open => ⟨core.report .failed reason, [], []⟩
  | .closing _ =>
    ⟨{ core with closing := .closing true }, [],
      [.complain s!"retaining process ownership: {reason}"]⟩
  | .closed _ => ⟨core, [], []⟩

def launchCheck (core : Core) (now : Nat) : Stepped :=
  if core.replacement.isNone && core.slot == .empty && core.closing == .open then
    match core.lifecycle.reserve (clockWord now) with
    | none => ⟨core, [], []⟩
    | some _ =>
      match core.persisted.launch with
      | .error reason => ⟨core.stop.report .failed reason, [], []⟩
      | .ok launch =>
        match core.owner with
        | .retired reason =>
          ⟨core.stop.report .failed s!"launch intent publication failed: {reason}", [], []⟩
        | .current =>
          ⟨{ core with
            pending := some (.launch { core.persisted with processStarted := true } launch) },
            [], []⟩
  else ⟨core, [], []⟩

def mapOrLaunch (core : Core) (now : Nat) : Stepped :=
  if core.mapWritable && decide (mapInterval ≤ now - core.mapAt) then
    ⟨{ core with mapAt := now, pending := some (.map core.mapRevision) }, [], []⟩
  else core.launchCheck now

def clear (core : Core) (intended : Desired) : Stepped :=
  if core.persisted.identity.agentEpoch.toNat ≥ browserIntegerMax then
    ⟨core.stop.report .failed "Clear refused: logical agent epoch exhausted", [], []⟩
  else match core.owner with
    | .current => ⟨{ core with pending := some (.seed intended) }, [], []⟩
    | .retired _ => ⟨core, [], []⟩

def tick (core : Core) (now : Nat) : Stepped :=
  match core.closing with
  | .open =>
    match core.replacement with
    | some state =>
      match core.owner with
      | .current => ⟨{ core with pending := some (.replacement state) }, [], []⟩
      | .retired _ => ⟨core, [], []⟩
    | none =>
      match core.lifecycle.archiveIntent, core.slot with
      | some intended, .empty => core.clear intended
      | _, _ => core.mapOrLaunch now
  | .closing _ =>
    match core.slot with
    | .empty => core.closeOut
    | .live _ | .draining _ _ _ => ⟨core, [], []⟩
  | .closed _ => ⟨core, [], []⟩

def close (core : Core) : Stepped :=
  match core.closing with
  | .open =>
    let follows := (core.failure.map fun reason => [Follow.complain reason]).getD []
    let core := ({ core with closing := .closing core.failure.isSome }.stop).report .stopRequested
      "viewer closing; finishing the current attempt and checkpoint"
    if core.slot == .empty then
      let out := core.closeOut
      { out with follows := follows ++ out.follows }
    else ⟨core, [], follows⟩
  | .closing _ | .closed _ => ⟨core, [], []⟩

def seeded (core : Core) (now : Nat) (intended : Desired) (seed : UInt64) : Stepped :=
  if seed.toNat > browserIntegerMax then
    ⟨core.stop.report .failed
      "Clear refused before archival: seed exceeds browser integer precision", [], []⟩
  else
    let identity : Identity := ⟨core.persisted.identity.run + 1, seed,
      core.persisted.identity.agentEpoch + 1⟩
    match core.lifecycle.beginArchive, core.owner with
    | some lifecycle, .current =>
      ⟨({ core with
        lifecycle, pending := some (.archive identity intended (clockWord now)) }).report
        .archiving "archiving the complete run directory", [], []⟩
    | _, _ => ⟨core, [], []⟩

def replaced (core : Core) (state : PersistedState) : Stepped :=
  let lifecycle := core.lifecycle.replacementIntent state.desired
  match lifecycle.archived state.identity with
  | some installed =>
    ⟨({ core with
      lifecycle := installed, persisted := state, replacement := none
      detail := { core.detail with log := {}, abnormalExit := false }
      failure := none, mapAt := 0, mapRevision := none }).report .cleared
      "previous run archived; new zero-knowledge identity installed", [.newRun], [.announceCleared]⟩
  | none => ⟨({ core with lifecycle }).report .failed "replacement identity could not be installed",
      [], []⟩

def retiredReason (archive : System.FilePath) : String :=
  s!"the run directory moved to {archive} and no replacement directory is owned"

def resolve (core : Core) (now : Nat) :
    (pending : Pending) → (pending.call core.lifecycle).Result → Stepped
  | .intent command _, .error reason => core.intentFailed reason (command == .stop)
  | .intent command state, .ok () => core.intentSaved command state
  | .launch _ _, .error reason =>
    ⟨core.stop.report .failed s!"launch intent publication failed: {reason}", [], []⟩
  | .launch state plan, .ok () =>
    let core := { core with persisted := state }
    match core.lifecycle.reserve (clockWord now) with
    | some (generation, lifecycle) =>
      ⟨{ core with lifecycle, pending := some (.spawn generation plan) }, [], []⟩
    | none => ⟨core, [], []⟩
  | .spawn generation _, .error reason =>
    let core := ({ core with
      lifecycle := core.lifecycle.failed generation (clockWord now) false }).report .failed
      s!"spawn refused: {reason}"
    ⟨core, [.loseTail], [.announceExit core.detail.reason]⟩
  | .spawn generation _, .ok () =>
    let core := { core with
      slot := .live generation, failure := none
      detail := { core.detail with log := {}, abnormalExit := false } }
    ⟨(core.moveTo (core.lifecycle.started generation)).report .coreStarted "core process started",
      [.await generation], [.attach generation]⟩
  | .windUp _, .error reason => core.refused reason
  | .windUp _, .ok () => ⟨core, [], []⟩
  | .adopt _ _ _, .error reason => core.adoptFailed reason
  | .adopt generation actual state, .ok () => core.adopted generation actual state
  | .commit _ _ state _, .error reason =>
    ⟨{ core with persisted := state }.stop.report .failed reason, [], []⟩
  | .commit generation actual state detail, .ok dropped =>
    core.committed generation actual state detail dropped
  | .exitMap report _, .error reason =>
    let refusal := s!"retained map publication refused: {reason}"
    core.exitReported { report with
      reason := report.reason ++ "; " ++ refusal, failure := some (controlDiagnostic refusal) }
  | .exitMap report _, .ok revision =>
    { core with mapRevision := revision.or core.mapRevision }.exitReported report
  | .exitIntent _, .error reason =>
    ⟨core.report .failed s!"process exited; intent publication failed: {reason}", [], []⟩
  | .exitIntent state, .ok () => ⟨{ core with persisted := state }, [], []⟩
  | .map _, .error reason =>
    (core.report .failed s!"retained map publication refused: {reason}").launchCheck now
  | .map _, .ok revision => { core with mapRevision := revision.or core.mapRevision }.launchCheck now
  | .closeMap _, .error reason =>
    (core.report .failed s!"retained map publication refused: {reason}").closed
  | .closeMap _, .ok revision => { core with mapRevision := revision.or core.mapRevision }.closed
  | .seed _, .error reason =>
    ⟨core.stop.report .failed s!"Clear refused before archival: {reason}", [], []⟩
  | .seed intended, .ok seed => core.seeded now intended seed
  | .archive _ _ _, .unchanged reason =>
    ⟨({ core with lifecycle := core.lifecycle.archiveFailed }).report .failed
      s!"Clear failed; old run remains: {reason}", [], []⟩
  | .archive _ _ _, .moved archive reason =>
    ⟨({ core with
      lifecycle := core.lifecycle.archiveFailed, owner := .retired (retiredReason archive) }).report
      .failed s!"old run archived at {archive}; replacement directory unavailable: {reason}", [], []⟩
  | .archive identity intended _, .ready archive =>
    ⟨{ core with pending := some (.reopen identity intended archive) }, [], []⟩
  | .reopen _ _ archive, .error reason =>
    ⟨({ core with owner := .retired (retiredReason archive) }).report .failed
      s!"old run archived at {archive}; replacement owner unavailable: {reason}", [], []⟩
  | .reopen identity intended _, .ok () =>
    let state : PersistedState := ⟨identity, intended, .cleared, false⟩
    ⟨{ core with replacement := some state, pending := some (.replacement state) }, [], []⟩
  | .replacement _ ackStop, .error reason =>
    ⟨core.report .failed
      s!"old run archived; replacement state write failed (publication unconfirmed): {reason}", [],
      if ackStop then [.refuseStop reason] else []⟩
  | .replacement state ackStop, .ok () =>
    let stepped := core.replaced state
    if ackStop then
      if state.desired == .stopped then
        { stepped with follows := stepped.follows ++ [.ackStop] }
      else
        { stepped with follows := stepped.follows ++ [.refuseStop "stop intent did not record stopped"] }
    else stepped

def start (persisted : PersistedState) (clearDisabled : Option String) (reason : String)
    (reading : Nat) : Core where
  lifecycle := .initial persisted.identity persisted.desired
  slot := .empty
  persisted := persisted
  replacement := none
  owner := .current
  detail := { transition := .initialized, reason, clearDisabled, log := {} }
  failure := none
  mapAt := 0
  mapRevision := none
  closing := .open
  last := reading
  pending := none

def instant (core : Core) (reading : Nat) : Nat := max core.last reading

def stopRefusalFollow (reason : String) : Event → List Follow
  | .command .stop => [.refuseStop reason]
  | .command _ | .candidate _ _ | .exited _ _ | .finished _ _ _ | .refused _ | .tick | .close =>
    []

def dispatch (core : Core) (clearDisabled : Option String) (now : Nat) (event : Event) :
    Stepped :=
  match core.pending with
  | some _ => ⟨core, [], stopRefusalFollow "supervisor is busy with another operation" event⟩
  | none =>
    match core.closing, event with
    | .closed _, event => ⟨core, [], stopRefusalFollow "viewer is closed" event⟩
    | .open, .command command => core.command clearDisabled command
    | .closing _, .command command =>
      ⟨core, [], if command == .stop then [.refuseStop "viewer is closing"] else []⟩
    | _, .candidate generation actual => core.candidate generation actual
    | _, .exited code uptime => core.exited now code uptime
    | _, .finished stdout stderr log => core.finished stdout stderr log
    | _, .refused reason => core.refused reason
    | _, .tick => core.tick now
    | _, .close => core.close

def step (core : Core) (clearDisabled : Option String) (reading : Nat) (event : Event) : Stepped :=
  (core.dispatch clearDisabled (core.instant reading) event).at (core.instant reading)

def resume (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result) : Stepped :=
  ({ core with pending := none }.resolve (core.instant reading) pending result).at
    (core.instant reading)

end Core

inductive Ran (clearDisabled : Option String) : Core → Prop where
  | start (persisted : PersistedState) (reason : String) (reading : Nat) :
      Ran clearDisabled (Core.start persisted clearDisabled reason reading)
  | step {core : Core} (ran : Ran clearDisabled core) (reading : Nat) (event : Event) :
      Ran clearDisabled (core.step clearDisabled reading event).core
  | resume {core : Core} {pending : Pending} (ran : Ran clearDisabled core)
      (waiting : core.pending = some pending) (reading : Nat)
      (result : (pending.call core.lifecycle).Result) :
      Ran clearDisabled (core.resume reading pending result).core

structure Supervision (clearDisabled : Option String) where
  core : Core
  reached : Ran clearDisabled core

def Supervision.start (clearDisabled : Option String) (persisted : PersistedState)
    (reason : String) (reading : Nat) : Supervision clearDisabled × List Effect :=
  let core := Core.start persisted clearDisabled reason reading
  (⟨core, .start persisted reason reading⟩, ({ core } : Stepped).effects)

def Supervision.step {clearDisabled : Option String} (supervision : Supervision clearDisabled)
    (reading : Nat) (event : Event) : Supervision clearDisabled × List Effect :=
  let stepped := supervision.core.step clearDisabled reading event
  (⟨stepped.core, .step supervision.reached reading event⟩, stepped.effects)

def Supervision.resume {clearDisabled : Option String} (supervision : Supervision clearDisabled)
    {pending : Pending} (waiting : supervision.core.pending = some pending) (reading : Nat)
    (result : (pending.call supervision.core.lifecycle).Result) :
    Supervision clearDisabled × List Effect :=
  let stepped := supervision.core.resume reading pending result
  (⟨stepped.core, .resume supervision.reached waiting reading result⟩, stepped.effects)

namespace Core

theorem report_pending (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).pending = core.pending := rfl
theorem report_owner (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).owner = core.owner := rfl
theorem report_closing (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).closing = core.closing := rfl
theorem report_lifecycle (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).lifecycle = core.lifecycle := rfl
theorem report_replacement (core : Core) (transition : ControlTransition)
    (reason : String) : (core.report transition reason).replacement = core.replacement := rfl
theorem report_slot (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).slot = core.slot := rfl
theorem report_persisted (core : Core) (transition : ControlTransition)
    (reason : String) : (core.report transition reason).persisted = core.persisted := rfl
theorem report_transition (core : Core) (transition : ControlTransition)
    (reason : String) : (core.report transition reason).detail.transition = transition := rfl

theorem moveTo_pending (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).pending =
      (windUpTarget core.slot core.lifecycle lifecycle).map .windUp := rfl
theorem moveTo_owner (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).owner = core.owner := rfl
theorem moveTo_closing (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).closing = core.closing := rfl
theorem moveTo_lifecycle (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).lifecycle = lifecycle := rfl
theorem moveTo_replacement (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).replacement = core.replacement := rfl
theorem moveTo_slot (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).slot = core.slot := rfl
theorem moveTo_persisted (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).persisted = core.persisted := rfl

theorem stop_eq (core : Core) : core.stop = core.moveTo (core.lifecycle.request .stop) :=
  rfl

end Core

structure Core.Invariant (clearDisabled : Option String) (core : Core) : Prop where
  retired : ∀ pending, core.pending = some pending → pending.writes = true →
    core.owner = .current
  clearless : clearDisabled.isSome = true → core.lifecycle.Clearless ∧
    core.replacement = none ∧ ∀ pending, core.pending = some pending → pending.clears = false
  closing : core.closing ≠ .open → ∀ pending, core.pending = some pending →
    pending.serves = false
  launch : ∀ state plan, core.pending = some (.launch state plan) →
    state.processStarted = true ∧ state.identity = plan.identity
  spawn : ∀ generation plan, core.pending = some (.spawn generation plan) →
    core.persisted.processStarted = true ∧ core.persisted.identity = plan.identity

theorem PersistedState.launch_identity (state : PersistedState) (plan : CoreLaunch)
    (admitted : state.launch = .ok plan) : plan.identity = state.identity := by
  unfold PersistedState.launch at admitted
  by_cases safe : state.identity.browserSafe = true <;>
    by_cases exhausted : (state.processStarted && decide (state.identity.agentEpoch.toNat ≥ browserIntegerMax)) = true <;>
    simp_all [bind, Except.bind, pure, Except.pure]
  all_goals (subst admitted; rfl)

theorem Core.instant_later (core : Core) (reading : Nat) :
    core.last ≤ core.instant reading ∧ (core.last ≤ reading → core.instant reading = reading) :=
  ⟨Nat.le_max_left _ _, fun later => Nat.max_eq_right later⟩

theorem Core.step_last (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) : (core.step clearDisabled reading event).core.last = core.instant reading :=
  rfl

theorem Core.resume_last (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result) :
    (core.resume reading pending result).core.last = core.instant reading := rfl

theorem Stepped.effects_settle (stepped : Stepped) :
    stepped.effects = .settle stepped.core.lifecycle stepped.changes stepped.core.detail ::
      stepped.follows.map .follow := rfl

namespace Core

theorem command_beq (left right : Command) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

theorem desired_beq (left right : Desired) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

theorem phase_beq (left right : Phase) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> first
    | rfl
    | (rename_i first second; show (first == second) = _; rw [Bool.eq_iff_iff]; simp)

private theorem forall_map_some {α β : Type} (f : α → β) (value : Option α) (property : β → Prop) :
    (∀ mapped, value.map f = some mapped → property mapped) ↔
      ∀ inner, value = some inner → property (f inner) := by
  cases value <;> simp

theorem cleared_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) :
    ({ core with pending := none } : Core).Invariant clearDisabled :=
  ⟨fun _ h => (by cases h),
   fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, fun _ h => (by cases h)⟩,
   fun _ _ h => (by cases h),
   fun _ _ h => (by cases h),
   fun _ _ h => (by cases h)⟩

private theorem Invariant.report {clearDisabled : Option String} {core : Core}
    (invariant : core.Invariant clearDisabled) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).Invariant clearDisabled :=
  ⟨invariant.retired, invariant.clearless, invariant.closing, invariant.launch, invariant.spawn⟩

private theorem Invariant.of_none {clearDisabled : Option String} {core : Core}
    (hp : core.pending = none)
    (hcl : clearDisabled.isSome = true → core.lifecycle.Clearless ∧ core.replacement = none) :
    core.Invariant clearDisabled :=
  ⟨fun _ h => (by rw [hp] at h; cases h),
   fun hc => ⟨(hcl hc).1, (hcl hc).2, fun _ h => (by rw [hp] at h; cases h)⟩,
   fun _ _ h => (by rw [hp] at h; cases h),
   fun _ _ h => (by rw [hp] at h; cases h),
   fun _ _ h => (by rw [hp] at h; cases h)⟩

private theorem Invariant.of_some {clearDisabled : Option String} {core : Core} {p : Pending}
    (hp : core.pending = some p)
    (hret : p.writes = true → core.owner = .current)
    (hcl : clearDisabled.isSome = true →
      core.lifecycle.Clearless ∧ core.replacement = none ∧ p.clears = false)
    (hcls : core.closing ≠ .open → p.serves = false)
    (hlch : ∀ s pl, p = .launch s pl → s.processStarted = true ∧ s.identity = pl.identity)
    (hspn : ∀ g pl, p = .spawn g pl →
      core.persisted.processStarted = true ∧ core.persisted.identity = pl.identity) :
    core.Invariant clearDisabled :=
  ⟨fun q hq hw => (by rw [hp] at hq; cases Option.some.inj hq; exact hret hw),
   fun hc => ⟨(hcl hc).1, (hcl hc).2.1, fun q hq =>
     (by rw [hp] at hq; cases Option.some.inj hq; exact (hcl hc).2.2)⟩,
   fun hcl' q hq => (by rw [hp] at hq; cases Option.some.inj hq; exact hcls hcl'),
   fun s pl hq => (by rw [hp] at hq; exact hlch s pl (Option.some.inj hq)),
   fun g pl hq => (by rw [hp] at hq; exact hspn g pl (Option.some.inj hq))⟩

private theorem Invariant.moveTo {clearDisabled : Option String} {core : Core}
    (invariant : core.Invariant clearDisabled) {lifecycle : Lifecycle}
    (hcl : clearDisabled.isSome = true → lifecycle.Clearless) :
    (core.moveTo lifecycle).Invariant clearDisabled := by
  cases hw : windUpTarget core.slot core.lifecycle lifecycle with
  | none =>
    exact Invariant.of_none (by simp only [Core.moveTo, hw]; rfl)
      fun hc => ⟨hcl hc, (invariant.clearless hc).2.1⟩
  | some gen =>
    exact Invariant.of_some (p := .windUp gen) (by simp only [Core.moveTo, hw]; rfl)
      (fun h => by cases h)
      (fun hc => ⟨hcl hc, (invariant.clearless hc).2.1, rfl⟩)
      (fun _ => rfl)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)

private theorem Invariant.stop {clearDisabled : Option String} {core : Core}
    (invariant : core.Invariant clearDisabled) :
    core.stop.Invariant clearDisabled :=
  invariant.moveTo fun hc => Lifecycle.request_clearless _ .stop (by decide) (invariant.clearless hc).1

private theorem Invariant.withPersisted {clearDisabled : Option String} {core : Core}
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none)
    (state : PersistedState) :
    ({ core with persisted := state } : Core).Invariant clearDisabled :=
  Invariant.of_none ready fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩

private theorem mapWritable_eq {core : Core} (h : core.mapWritable = true) :
    core.owner = .current ∧ core.replacement = none := by
  unfold Core.mapWritable at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact h

theorem command_invariant (core : Core) (clearDisabled : Option String) (command : Command)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none)
    (serving : core.closing = .open) :
    (core.command clearDisabled command).core.Invariant clearDisabled := by
  unfold Core.command
  split
  · exact invariant
  · rename_i hdis
    cases hrep : core.replacement with
    | some replacement =>
      dsimp only
      split
      · exact invariant.report _ _
      · split
        · cases hown : core.owner with
          | retired reason => exact invariant.stop.report _ _
          | current =>
            dsimp only
            exact Invariant.of_some
              (p := .replacement { replacement with desired := .stopped } true)
              rfl
              (fun _ => rfl)
              (fun hc => by
                have := (invariant.clearless hc).2.1
                rw [hrep] at this; cases this)
              (fun hcl => absurd serving hcl)
              (fun _ _ h => by cases h)
              (fun _ _ h => by cases h)
        · exact Invariant.of_none ready fun hc => by
            have := (invariant.clearless hc).2.1
            rw [hrep] at this; cases this
    | none =>
      dsimp only
      cases hown : core.owner with
      | retired reason => exact invariant.stop.report _ _
      | current =>
        dsimp only
        exact Invariant.of_some
          (p := .intent command { core.persisted with desired := command.desired })
          rfl
          (fun _ => rfl)
          (fun hc => ⟨(invariant.clearless hc).1, rfl, by
            simp only [Pending.clears]
            cases command <;> simp_all [command_beq]⟩)
          (fun hcl => absurd serving hcl)
          (fun _ _ h => by cases h)
          (fun _ _ h => by cases h)

theorem candidate_invariant (core : Core) (clearDisabled : Option String) (generation : UInt64)
    (actual : CoreIdentity) (invariant : core.Invariant clearDisabled)
    (ready : core.pending = none) :
    (core.candidate generation actual).core.Invariant clearDisabled := by
  let _ := ready
  unfold Core.candidate
  split
  · exact invariant
  · split
    · exact invariant.stop.report _ _
    · cases core.owner with
      | retired reason => exact invariant.stop.report _ _
      | current =>
        dsimp only
        exact Invariant.of_some (p := .adopt generation actual (core.persisted.adopt actual)) rfl
          (fun _ => rfl)
          (fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, rfl⟩)
          (fun _ => rfl)
          (fun _ _ h => by cases h)
          (fun _ _ h => by cases h)

theorem exited_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (code : UInt32) (uptime : Nat) (invariant : core.Invariant clearDisabled)
    (ready : core.pending = none) :
    (core.exited now code uptime).core.Invariant clearDisabled := by
  unfold Core.exited
  cases core.slot with
  | empty | draining _ _ _ => exact invariant
  | live generation =>
    dsimp only
    apply Invariant.report
    refine Invariant.of_none ready fun hc => ⟨?_, (invariant.clearless hc).2.1⟩
    apply Lifecycle.retire_clearless
    split
    · exact (invariant.clearless hc).1
    · exact Lifecycle.failed_clearless _ _ _ _ (invariant.clearless hc).1

theorem refused_invariant (core : Core) (clearDisabled : Option String) (reason : String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.refused reason).core.Invariant clearDisabled := by
  unfold Core.refused
  cases core.closing with
  | «open» => exact invariant.report _ _
  | closed _ => exact invariant
  | closing _ =>
    exact Invariant.of_none ready fun hc =>
      ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩

theorem closed_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    core.closed.core.Invariant clearDisabled := by
  unfold Core.closed
  cases core.closing with
  | «open» | closed _ => exact invariant
  | closing _ =>
    exact Invariant.of_none ready fun hc =>
      ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩

theorem exitReported_invariant (core : Core) (clearDisabled : Option String)
    (report : ExitReport) (invariant : core.Invariant clearDisabled)
    (ready : core.pending = none) (serving : core.closing = .open) :
    (core.exitReported report).core.Invariant clearDisabled := by
  unfold Core.exitReported
  dsimp only
  cases core.owner with
  | retired reason =>
    apply Invariant.report
    apply Invariant.report
    exact Invariant.of_none ready fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩
  | current =>
    exact Invariant.of_some
      (p := .exitIntent { core.persisted with desired := core.lifecycle.desiredValue }) rfl
      (fun _ => rfl)
      (fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, rfl⟩)
      (fun hcl => absurd serving hcl)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)

theorem closeOut_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    core.closeOut.core.Invariant clearDisabled := by
  unfold Core.closeOut
  cases hmw : core.mapWritable with
  | false => exact core.closed_invariant clearDisabled invariant ready
  | true =>
    obtain ⟨hown, _⟩ := mapWritable_eq hmw
    exact Invariant.of_some (p := .closeMap core.mapRevision) rfl
      (fun _ => hown)
      (fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, rfl⟩)
      (fun _ => rfl)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)

theorem finished_invariant (core : Core) (clearDisabled : Option String)
    (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.finished stdout stderr log).core.Invariant clearDisabled := by
  unfold Core.finished
  cases core.slot with
  | empty | live _ => exact invariant
  | draining generation code requested =>
    dsimp only
    cases hcls : core.closing with
    | closed _ =>
      exact Invariant.of_none ready fun hc =>
        ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩
    | closing before =>
      dsimp only
      apply Invariant.report
      exact Invariant.of_none ready fun hc =>
        ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩
    | «open» =>
      dsimp only
      split
      · rename_i hmw
        obtain ⟨hown, _⟩ := mapWritable_eq hmw
        exact Invariant.of_some (p := .exitMap _ core.mapRevision) rfl
          (fun _ => hown)
          (fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, rfl⟩)
          (fun hcl => absurd rfl hcl)
          (fun _ _ h => by cases h)
          (fun _ _ h => by cases h)
      · have hslot : ({ core with slot := .empty, closing := .open } : Core).Invariant
            clearDisabled :=
          Invariant.of_none (core := { core with slot := .empty, closing := .open }) ready fun hc =>
            ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩
        exact Core.exitReported_invariant { core with slot := .empty, closing := .open }
          clearDisabled _ hslot ready rfl

theorem launchCheck_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.launchCheck now).core.Invariant clearDisabled := by
  let _ := ready
  unfold Core.launchCheck
  cases hcond : (core.replacement.isNone && (core.slot == .empty) && (core.closing == .open)) with
  | false => exact invariant
  | true =>
    dsimp only
    have hopen : core.closing = .open := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.2
    cases core.lifecycle.reserve (clockWord now) with
    | none => exact invariant
    | some _ =>
      dsimp only
      cases hlch : core.persisted.launch with
      | error _ => exact invariant.stop.report _ _
      | ok launch =>
        dsimp only
        cases core.owner with
        | retired _ => exact invariant.stop.report _ _
        | current =>
          dsimp only
          exact Invariant.of_some
            (p := .launch { core.persisted with processStarted := true } launch) rfl
            (fun _ => rfl)
            (fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, rfl⟩)
            (fun hcl => absurd hopen hcl)
            (fun s pl h => by
              cases h
              exact ⟨rfl, (PersistedState.launch_identity _ _ hlch).symm⟩)
            (fun _ _ h => by cases h)

private theorem mapOrLaunch_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none)
    (serving : core.closing = .open) :
    (core.mapOrLaunch now).core.Invariant clearDisabled := by
  unfold Core.mapOrLaunch
  cases hcond : (core.mapWritable && decide (mapInterval ≤ now - core.mapAt)) with
  | false => exact core.launchCheck_invariant clearDisabled now invariant ready
  | true =>
    have hmw : core.mapWritable = true := (Bool.and_eq_true _ _).mp hcond |>.1
    obtain ⟨hown, _⟩ := mapWritable_eq hmw
    exact Invariant.of_some (p := .map core.mapRevision) rfl
      (fun _ => hown)
      (fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, rfl⟩)
      (fun hcl => absurd serving hcl)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)

theorem tick_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.tick now).core.Invariant clearDisabled := by
  unfold Core.tick
  cases hcls : core.closing with
  | closed _ => exact invariant
  | closing _ =>
    cases core.slot with
    | empty => exact core.closeOut_invariant clearDisabled invariant ready
    | live _ | draining _ _ _ => exact invariant
  | «open» =>
    dsimp only
    cases hrep : core.replacement with
    | some state =>
      dsimp only
      cases core.owner with
      | retired _ => exact invariant
      | current =>
        dsimp only
        exact Invariant.of_some (p := .replacement state) rfl
          (fun _ => rfl)
          (fun hc => by have := (invariant.clearless hc).2.1; rw [hrep] at this; cases this)
          (fun hcl => absurd rfl hcl)
          (fun _ _ h => by cases h)
          (fun _ _ h => by cases h)
    | none =>
      dsimp only
      cases harch : core.lifecycle.archiveIntent with
      | none => exact core.mapOrLaunch_invariant clearDisabled now invariant ready hcls
      | some intended =>
        cases core.slot with
        | live _ | draining _ _ _ =>
          exact core.mapOrLaunch_invariant clearDisabled now invariant ready hcls
        | empty =>
          dsimp only
          unfold Core.clear
          split
          · exact invariant.stop.report _ _
          · cases core.owner with
            | retired _ => exact invariant
            | current =>
              dsimp only
              exact Invariant.of_some (p := .seed intended) rfl
                (fun _ => rfl)
                (fun hc => by
                  have := Lifecycle.clearless_archiveIntent _ (invariant.clearless hc).1
                  rw [harch] at this; cases this)
                (fun hcl => absurd hcls hcl)
                (fun _ _ h => by cases h)
                (fun _ _ h => by cases h)

theorem close_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    core.close.core.Invariant clearDisabled := by
  unfold Core.close
  cases core.closing with
  | closing _ | closed _ => exact invariant
  | «open» =>
    dsimp only
    have hstop : (({ core with closing := .closing core.failure.isSome }.stop).report
        .stopRequested "viewer closing; finishing the current attempt and checkpoint").Invariant
        clearDisabled :=
      ((Invariant.of_none (core := { core with closing := .closing core.failure.isSome }) ready
        fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩).stop).report _ _
    split
    · rename_i hemp
      have hemp' : core.slot = .empty := by
        simpa [Core.report, Core.stop, Core.moveTo] using hemp
      have hpend : (({ core with closing := .closing core.failure.isSome }.stop).report
          .stopRequested
          "viewer closing; finishing the current attempt and checkpoint").pending = none := by
        simp [Core.report, Core.stop, Core.moveTo, windUpTarget, hemp']
      exact Core.closeOut_invariant _ clearDisabled hstop hpend
    · exact hstop

theorem Invariant.serving {clearDisabled : Option String} {core : Core} {pending : Pending}
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some pending)
    (serves : pending.serves = true) : core.closing = .open := by
  cases closing : core.closing with
  | «open» => rfl
  | closing failed =>
    have refused := invariant.closing (by simp [closing]) pending waiting
    rw [serves] at refused; cases refused
  | closed failed =>
    have refused := invariant.closing (by simp [closing]) pending waiting
    rw [serves] at refused; cases refused

theorem resolve_intent_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (command : Command) (state : PersistedState)
    (result : ((Pending.intent command state).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.intent command state)) :
    ({ core with pending := none }.resolve now (.intent command state) result).core.Invariant
      clearDisabled := by
  have base := core.cleared_invariant clearDisabled invariant
  cases result with
  | error _ => exact base.stop.report _ _
  | ok _ =>
    simp only [Core.resolve, Core.intentSaved]
    apply Invariant.report
    refine (base.withPersisted rfl state).moveTo fun hc => ?_
    have hnotClear : command ≠ .clear := by
      have hcl := (invariant.clearless hc).2.2 _ waiting
      intro h; subst h; cases hcl
    exact Lifecycle.request_clearless _ command hnotClear (invariant.clearless hc).1

theorem resolve_launch_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (state : PersistedState) (plan : CoreLaunch)
    (result : ((Pending.launch state plan).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.launch state plan)) :
    ({ core with pending := none }.resolve now (.launch state plan) result).core.Invariant
      clearDisabled := by
  have base := core.cleared_invariant clearDisabled invariant
  cases result with
  | error _ => exact base.stop.report _ _
  | ok _ =>
    simp only [Core.resolve]
    cases hres : core.lifecycle.reserve (clockWord now) with
    | none => exact base.withPersisted rfl state
    | some pair =>
      obtain ⟨generation, lifecycle⟩ := pair
      have hserving := invariant.serving waiting rfl
      have hlaunch := invariant.launch state plan waiting
      exact Invariant.of_some (p := .spawn generation plan) rfl
        (fun h => by cases h)
        (fun hc => ⟨Lifecycle.reserve_clearless _ _ _ _ hres (invariant.clearless hc).1,
          (invariant.clearless hc).2.1, rfl⟩)
        (fun hcl => absurd hserving hcl)
        (fun _ _ h => by cases h)
        (fun _ _ h => by cases h; exact hlaunch)

theorem resolve_spawn_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (generation : UInt64) (plan : CoreLaunch)
    (result : ((Pending.spawn generation plan).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.spawn generation plan)) :
    ({ core with pending := none }.resolve now (.spawn generation plan) result).core.Invariant
      clearDisabled := by
  let _ := waiting
  cases result with
  | error _ =>
    simp only [Core.resolve]
    apply Invariant.report
    exact Invariant.of_none rfl fun hc =>
      ⟨Lifecycle.failed_clearless _ _ _ _ (invariant.clearless hc).1,
        (invariant.clearless hc).2.1⟩
  | ok _ =>
    simp only [Core.resolve]
    apply Invariant.report
    have hcore : ({ core with
        pending := none, slot := .live generation, failure := none,
        detail := { core.detail with log := {}, abnormalExit := false } } : Core).Invariant
        clearDisabled :=
      Invariant.of_none rfl fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1⟩
    exact hcore.moveTo fun hc =>
      Lifecycle.started_clearless _ _ (invariant.clearless hc).1

theorem resolve_adopt_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
    (result : ((Pending.adopt generation actual state).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.adopt generation actual state)) :
    ({ core with pending := none }.resolve now (.adopt generation actual state) result).core.Invariant
      clearDisabled := by
  let _ := waiting
  have base := core.cleared_invariant clearDisabled invariant
  cases result with
  | error _ => exact base.stop.report _ _
  | ok _ =>
    simp only [Core.resolve, Core.adopted]
    exact Invariant.of_some (p := .commit generation actual state _) rfl
      (fun h => by cases h)
      (fun hc => ⟨(invariant.clearless hc).1, (invariant.clearless hc).2.1, rfl⟩)
      (fun _ => rfl)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)

theorem resolve_commit_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (generation : UInt64) (actual : CoreIdentity) (state : PersistedState) (detail : ControlDetail)
    (result : ((Pending.commit generation actual state detail).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.commit generation actual state detail)) :
    ({ core with pending := none }.resolve now (.commit generation actual state detail)
        result).core.Invariant clearDisabled := by
  let _ := waiting
  have base := core.cleared_invariant clearDisabled invariant
  cases result with
  | error _ => exact (base.withPersisted rfl state).stop.report _ _
  | ok dropped =>
    simp only [Core.resolve, Core.committed]
    have hcore : ({ core with
        pending := none, persisted := state, detail := detail,
        lifecycle := core.lifecycle.adoptFinalIdentity generation actual.identity } :
        Core).Invariant clearDisabled :=
      Invariant.of_none rfl fun hc =>
        ⟨Lifecycle.adoptFinalIdentity_clearless _ _ _ (invariant.clearless hc).1,
          (invariant.clearless hc).2.1⟩
    split
    · exact hcore.report _ _
    · exact hcore

theorem resolve_exitIntent_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (state : PersistedState)
    (result : ((Pending.exitIntent state).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.exitIntent state)) :
    ({ core with pending := none }.resolve now (.exitIntent state) result).core.Invariant
      clearDisabled := by
  let _ := waiting
  have base := core.cleared_invariant clearDisabled invariant
  cases result with
  | error _ => exact base.report _ _
  | ok _ => exact base.withPersisted rfl state

theorem resolve_seed_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (intended : Desired)
    (result : ((Pending.seed intended).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.seed intended)) :
    ({ core with pending := none }.resolve now (.seed intended) result).core.Invariant
      clearDisabled := by
  have base := core.cleared_invariant clearDisabled invariant
  have hnotDis : clearDisabled.isSome = true → False := fun hc => by
    have := (invariant.clearless hc).2.2 _ waiting
    cases this
  have hserving := invariant.serving waiting rfl
  cases result with
  | error _ => exact base.stop.report _ _
  | ok seed =>
    simp only [Core.resolve, Core.seeded]
    split
    · exact base.stop.report _ _
    · cases core.lifecycle.beginArchive with
      | none => exact base
      | some lifecycle =>
        cases core.owner with
        | retired _ =>
          exact Invariant.of_none rfl fun hc => (hnotDis hc).elim
        | current =>
          dsimp only
          apply Invariant.report
          exact Invariant.of_some (p := .archive _ intended (clockWord now)) rfl
            (fun _ => rfl)
            (fun hc => (hnotDis hc).elim)
            (fun hcl => absurd hserving hcl)
            (fun _ _ h => by cases h)
            (fun _ _ h => by cases h)

theorem resolve_archive_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (identity : Identity) (intended : Desired) (stamp : UInt64)
    (result : ((Pending.archive identity intended stamp).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.archive identity intended stamp)) :
    ({ core with pending := none }.resolve now (.archive identity intended stamp)
        result).core.Invariant clearDisabled := by
  have hnotDis : clearDisabled.isSome = true → False := fun hc => by
    have := (invariant.clearless hc).2.2 _ waiting
    cases this
  have hown : core.owner = .current := invariant.retired _ waiting rfl
  have hserving := invariant.serving waiting rfl
  cases result with
  | unchanged _ =>
    apply Invariant.report
    exact Invariant.of_none rfl fun hc => (hnotDis hc).elim
  | moved _ _ =>
    apply Invariant.report
    exact Invariant.of_none rfl fun hc => (hnotDis hc).elim
  | ready archive =>
    exact Invariant.of_some (p := .reopen identity intended archive) rfl
      (fun _ => hown)
      (fun hc => (hnotDis hc).elim)
      (fun hcl => absurd hserving hcl)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)

theorem resolve_reopen_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (identity : Identity) (intended : Desired) (archive : System.FilePath)
    (result : ((Pending.reopen identity intended archive).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.reopen identity intended archive)) :
    ({ core with pending := none }.resolve now (.reopen identity intended archive)
        result).core.Invariant clearDisabled := by
  have hnotDis : clearDisabled.isSome = true → False := fun hc => by
    have := (invariant.clearless hc).2.2 _ waiting
    cases this
  have hown : core.owner = .current := invariant.retired _ waiting rfl
  have hserving := invariant.serving waiting rfl
  cases result with
  | error _ =>
    apply Invariant.report
    exact Invariant.of_none rfl fun hc => (hnotDis hc).elim
  | ok _ =>
    exact Invariant.of_some (p := .replacement ⟨identity, intended, .cleared, false⟩) rfl
      (fun _ => hown)
      (fun hc => (hnotDis hc).elim)
      (fun hcl => absurd hserving hcl)
      (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)

theorem resolve_replacement_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (state : PersistedState) (ackStop : Bool)
    (result : ((Pending.replacement state ackStop).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.replacement state ackStop)) :
    ({ core with pending := none }.resolve now (.replacement state ackStop)
        result).core.Invariant clearDisabled := by
  have hnotDis : clearDisabled.isSome = true → False := fun hc => by
    have := (invariant.clearless hc).2.2 _ waiting
    cases this
  cases result with
  | error _ => exact (core.cleared_invariant clearDisabled invariant).report _ _
  | ok _ =>
    simp only [Core.resolve, Core.replaced]
    repeat' split
    all_goals (
      apply Invariant.report
      exact Invariant.of_none rfl fun hc => (hnotDis hc).elim)

theorem resolve_windUp_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (generation : UInt64) (result : ((Pending.windUp generation).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) :
    ({ core with pending := none }.resolve now (.windUp generation) result).core.Invariant
      clearDisabled := by
  cases result
  · exact Core.refused_invariant _ clearDisabled _ (core.cleared_invariant clearDisabled invariant)
      rfl
  · exact core.cleared_invariant clearDisabled invariant

theorem resolve_exitMap_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (report : ExitReport) (skip : Option Nat)
    (result : ((Pending.exitMap report skip).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled)
    (waiting : core.pending = some (.exitMap report skip)) :
    ({ core with pending := none }.resolve now (.exitMap report skip) result).core.Invariant
      clearDisabled := by
  have serving := invariant.serving waiting rfl
  have base := core.cleared_invariant clearDisabled invariant
  cases result
  · exact Core.exitReported_invariant _ clearDisabled _ base rfl serving
  · exact Core.exitReported_invariant _ clearDisabled _
      ⟨base.retired, base.clearless, base.closing, base.launch, base.spawn⟩ rfl serving

theorem resolve_map_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (skip : Option Nat) (result : ((Pending.map skip).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) :
    ({ core with pending := none }.resolve now (.map skip) result).core.Invariant
      clearDisabled := by
  have base := core.cleared_invariant clearDisabled invariant
  cases result
  · exact Core.launchCheck_invariant _ clearDisabled _
      ⟨base.retired, base.clearless, base.closing, base.launch, base.spawn⟩ rfl
  · exact Core.launchCheck_invariant _ clearDisabled _
      ⟨base.retired, base.clearless, base.closing, base.launch, base.spawn⟩ rfl

theorem resolve_closeMap_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (skip : Option Nat) (result : ((Pending.closeMap skip).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) :
    ({ core with pending := none }.resolve now (.closeMap skip) result).core.Invariant
      clearDisabled := by
  have base := core.cleared_invariant clearDisabled invariant
  cases result
  · exact Core.closed_invariant _ clearDisabled
      ⟨base.retired, base.clearless, base.closing, base.launch, base.spawn⟩ rfl
  · exact Core.closed_invariant _ clearDisabled
      ⟨base.retired, base.clearless, base.closing, base.launch, base.spawn⟩ rfl

theorem resolve_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (pending : Pending) (result : (pending.call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some pending) :
    ({ core with pending := none }.resolve now pending result).core.Invariant clearDisabled := by
  cases pending with
  | intent => exact core.resolve_intent_invariant _ _ _ _ _ invariant waiting
  | launch => exact core.resolve_launch_invariant _ _ _ _ _ invariant waiting
  | spawn => exact core.resolve_spawn_invariant _ _ _ _ _ invariant waiting
  | windUp => exact core.resolve_windUp_invariant _ _ _ _ invariant
  | adopt => exact core.resolve_adopt_invariant _ _ _ _ _ _ invariant waiting
  | commit => exact core.resolve_commit_invariant _ _ _ _ _ _ _ invariant waiting
  | exitMap => exact core.resolve_exitMap_invariant _ _ _ _ _ invariant waiting
  | exitIntent => exact core.resolve_exitIntent_invariant _ _ _ _ invariant waiting
  | map => exact core.resolve_map_invariant _ _ _ _ invariant
  | closeMap => exact core.resolve_closeMap_invariant _ _ _ _ invariant
  | seed => exact core.resolve_seed_invariant _ _ _ _ invariant waiting
  | archive => exact core.resolve_archive_invariant _ _ _ _ _ _ invariant waiting
  | reopen => exact core.resolve_reopen_invariant _ _ _ _ _ _ invariant waiting
  | replacement => exact core.resolve_replacement_invariant _ _ _ _ _ invariant waiting

theorem dispatch_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (event : Event) (invariant : core.Invariant clearDisabled) :
    (core.dispatch clearDisabled now event).core.Invariant clearDisabled := by
  unfold dispatch
  split
  · exact invariant
  · rename_i ready
    split <;> first
      | exact invariant
      | exact core.command_invariant clearDisabled _ invariant ready (by assumption)
      | exact core.candidate_invariant clearDisabled _ _ invariant ready
      | exact core.exited_invariant clearDisabled _ _ _ invariant ready
      | exact core.finished_invariant clearDisabled _ _ _ invariant ready
      | exact core.refused_invariant clearDisabled _ invariant ready
      | exact core.tick_invariant clearDisabled _ invariant ready
      | exact core.close_invariant clearDisabled invariant ready

theorem step_invariant (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (invariant : core.Invariant clearDisabled) :
    (core.step clearDisabled reading event).core.Invariant clearDisabled :=
  let next := core.dispatch_invariant clearDisabled (core.instant reading) event invariant
  ⟨next.retired, next.clearless, next.closing, next.launch, next.spawn⟩

theorem resume_invariant (core : Core) (clearDisabled : Option String) (reading : Nat)
    (pending : Pending) (result : (pending.call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some pending) :
    (core.resume reading pending result).core.Invariant clearDisabled :=
  let next := core.resolve_invariant clearDisabled (core.instant reading) pending result invariant
    waiting
  ⟨next.retired, next.clearless, next.closing, next.launch, next.spawn⟩

theorem start_invariant (persisted : PersistedState) (clearDisabled : Option String)
    (reason : String) (reading : Nat) :
    (Core.start persisted clearDisabled reason reading).Invariant clearDisabled :=
  ⟨by simp [Core.start], fun _ => ⟨Lifecycle.initial_clearless _ _, rfl, by simp [Core.start]⟩,
    by simp [Core.start], by simp [Core.start], by simp [Core.start]⟩

end Core

theorem Ran.invariant {clearDisabled : Option String} {core : Core}
    (ran : Ran clearDisabled core) : core.Invariant clearDisabled := by
  induction ran with
  | start persisted reason reading => exact Core.start_invariant persisted _ reason reading
  | step _ reading event invariant => exact Core.step_invariant _ _ reading event invariant
  | resume _ waiting reading result invariant =>
    exact Core.resume_invariant _ _ reading _ result invariant waiting

theorem Supervision.retired_untouched {clearDisabled : Option String}
    (supervision : Supervision clearDisabled) (pending : Pending)
    (waiting : supervision.core.pending = some pending)
    (retired : supervision.core.owner ≠ .current) : pending.writes = false := by
  cases writes : pending.writes
  · rfl
  · exact absurd (supervision.reached.invariant.retired pending waiting writes) retired

theorem Supervision.clear_disabled {reason : String} (supervision : Supervision (some reason)) :
    supervision.core.lifecycle.Clearless ∧ supervision.core.replacement = none ∧
      ∀ pending, supervision.core.pending = some pending → pending.clears = false :=
  supervision.reached.invariant.clearless rfl

theorem Supervision.closing_starts_nothing {clearDisabled : Option String}
    (supervision : Supervision clearDisabled) (closing : supervision.core.closing ≠ .open)
    (pending : Pending) (waiting : supervision.core.pending = some pending) :
    pending.serves = false :=
  supervision.reached.invariant.closing closing pending waiting

theorem Supervision.spawn_recorded {clearDisabled : Option String}
    (supervision : Supervision clearDisabled) (generation : UInt64) (plan : CoreLaunch)
    (waiting : supervision.core.pending = some (.spawn generation plan)) :
    supervision.core.persisted.processStarted = true ∧
      supervision.core.persisted.identity = plan.identity :=
  supervision.reached.invariant.spawn generation plan waiting

namespace Core

theorem resume_launch (core : Core) (reading : Nat) (state : PersistedState) (plan : CoreLaunch)
    (result : ((Pending.launch state plan).call core.lifecycle).Result)
    (generation : UInt64) (spawned : CoreLaunch)
    (spawning : (core.resume reading (.launch state plan) result).core.pending =
      some (.spawn generation spawned)) :
    result = .ok () ∧ spawned = plan ∧
      (core.resume reading (.launch state plan) result).core.persisted = state ∧
      generation.toNat = core.lifecycle.lastGenerationValue.toNat + 1 ∧
      (core.resume reading (.launch state plan) result).core.lifecycle.lastGenerationValue =
        generation ∧
      core.lifecycle.retryReady (clockWord (core.instant reading)) = true ∧
      core.lifecycle.desiredValue = .running ∧ core.lifecycle.phaseValue = .idle ∧
      core.lifecycle.clearPendingValue = none := by
  cases result with
  | error reason =>
    simp [resume, Stepped.at, resolve, Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff] at spawning
  | ok =>
    simp only [resume, Stepped.at, resolve] at spawning ⊢
    split at spawning
    · rename_i reserved
      simp only [Option.some.injEq, Pending.spawn.injEq] at spawning
      obtain ⟨rfl, rfl⟩ := spawning
      have facts := Lifecycle.reserve_some _ _ _ _ reserved
      exact ⟨rfl, rfl, by simp, facts.2.2.2.2.1, by simp [facts.2.2.2.2.2.1], facts.2.2.2.1,
        facts.2.1, facts.1, facts.2.2.1⟩
    · simp at spawning

theorem stop_winds_up (core : Core) (clearDisabled : Option String) (reading : Nat)
    (generation : UInt64) (ready : core.pending = none) (serving : core.closing = .open)
    (noReplacement : core.replacement = none) (live : core.slot = .live generation)
    (running : core.lifecycle.phaseValue = .running generation) :
    (core.step clearDisabled reading (.command .stop)).core.pending = some (.windUp generation) ∨
      ∃ state, (core.step clearDisabled reading (.command .stop)).core.pending =
          some (.intent .stop state) ∧
        ∀ later result,
          ((core.step clearDisabled reading (.command .stop)).core.resume later
            (.intent .stop state) result).core.pending = some (.windUp generation) := by
  have stopping := core.lifecycle.request_stopping .stop generation (by decide) running
  have target : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) =
      some generation := by
    simp [windUpTarget, live, stopping, running, phase_beq, bne]
  cases owner : core.owner with
  | retired reason =>
    left
    simp [step, dispatch, Stepped.at, ready, serving, Core.command, command_beq, noReplacement, owner,
      intentFailed, Core.report, Core.moveTo, Core.stop, target]
  | current =>
    right
    refine ⟨{ core.persisted with desired := .stopped }, ?_, ?_⟩
    · simp [step, dispatch, Stepped.at, ready, serving, Core.command, command_beq, noReplacement, owner,
        Command.desired]
    · intro later result
      cases result <;>
        simp [step, dispatch, Stepped.at, ready, serving, Core.command, command_beq, noReplacement, owner,
          resume, resolve, intentFailed, intentSaved, Core.report, Core.moveTo, Core.stop, target]

theorem replaced_identity (core : Core) (state : PersistedState)
    (cleared : (core.replaced state).core.detail.transition = .cleared) :
    (core.replaced state).core.lifecycle.identityValue = state.identity ∧
      state.identity.run ≠ core.lifecycle.identityValue.run := by
  simp only [replaced] at cleared ⊢
  split at cleared
  · rename_i installed archived
    have facts := Lifecycle.archived_identity _ _ _ archived
    refine ⟨facts.1, ?_⟩
    rw [← Lifecycle.replacementIntent_identity core.lifecycle state.desired]
    exact facts.2
  · simp [Core.report] at cleared

theorem finished_defers (core : Core) (stdout : OutputStatus) (stderr : PipeResult)
    (log : LogStatus) :
    (∀ failed, (core.finished stdout stderr log).core.closing = .closed failed →
        core.closing = .closed failed) ∧
      ∀ skip, (core.finished stdout stderr log).core.pending = some (.closeMap skip) →
        core.pending = some (.closeMap skip) := by
  simp only [Core.finished, Core.exitReported]
  repeat' split
  all_goals simp_all [Core.report]

theorem step_finished_defers_close (core : Core) (clearDisabled : Option String) (reading : Nat)
    (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus) :
    (∀ failed, (core.step clearDisabled reading (.finished stdout stderr log)).core.closing =
        .closed failed → core.closing = .closed failed) ∧
      ∀ skip, (core.step clearDisabled reading (.finished stdout stderr log)).core.pending =
        some (.closeMap skip) → core.pending = some (.closeMap skip) := by
  have deferred := core.finished_defers stdout stderr log
  cases pending : core.pending with
  | some waiting => simp [step, dispatch, Stepped.at, pending]
  | none =>
    cases closing : core.closing with
    | closed failed => simp [step, dispatch, Stepped.at, pending, closing]
    | «open» => simpa [step, dispatch, Stepped.at, pending, closing] using deferred
    | closing failed => simpa [step, dispatch, Stepped.at, pending, closing] using deferred

end Core

namespace Core

structure Calm (before after : Core) : Prop where
  generation : after.lifecycle.lastGenerationValue = before.lifecycle.lastGenerationValue
  quiet : ∀ generation plan, after.pending ≠ some (.spawn generation plan)

theorem command_calm (core : Core) (clearDisabled : Option String) (command : Command)
    (ready : core.pending = none) :
    Calm core (core.command clearDisabled command).core := by
  simp only [Core.command, Core.intentFailed]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, command_beq, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])

theorem candidate_calm (core : Core) (generation : UInt64) (actual : CoreIdentity)
    (ready : core.pending = none) :
    Calm core (core.candidate generation actual).core := by
  simp only [Core.candidate, Core.adoptFailed]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])

theorem exited_calm (core : Core) (now : Nat) (code : UInt32) (uptime : Nat)
    (ready : core.pending = none) : Calm core (core.exited now code uptime).core := by
  simp only [Core.exited]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, phase_beq, Lifecycle.failed_lastGeneration,
      Lifecycle.retire_lastGeneration])

theorem refused_calm (core : Core) (reason : String) (ready : core.pending = none) :
    Calm core (core.refused reason).core := by
  simp only [Core.refused]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report])

theorem closed_calm (core : Core) (ready : core.pending = none) : Calm core core.closed.core := by
  simp only [Core.closed]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])

theorem closeOut_calm (core : Core) (ready : core.pending = none) :
    Calm core core.closeOut.core := by
  simp only [Core.closed, Core.closeOut]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])

theorem exitReported_calm (core : Core) (report : ExitReport) (ready : core.pending = none) :
    Calm core (core.exitReported report).core := by
  simp only [Core.exitReported]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report])

theorem launchCheck_calm (core : Core) (now : Nat) (ready : core.pending = none) :
    Calm core (core.launchCheck now).core := by
  simp only [Core.launchCheck]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])

theorem tick_calm (core : Core) (now : Nat) (ready : core.pending = none) :
    Calm core (core.tick now).core := by
  unfold Core.tick
  split
  · simp only [Core.launchCheck, Core.mapOrLaunch, Core.clear]
    repeat' split
    all_goals (
      (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
      (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
      constructor <;>
      simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])
  · cases core.slot with
    | empty => exact core.closeOut_calm ready
    | live _ | draining _ _ _ => (
      (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
      (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
      constructor <;>
      simp_all [])
  · (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])

theorem close_calm (core : Core) (ready : core.pending = none) : Calm core core.close.core := by
  simp only [Core.closed, Core.closeOut,
    Core.close]
  repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])

theorem Calm.through {before middle after : Core} (first : Calm before middle)
    (second : Calm middle after) : Calm before after :=
  ⟨second.generation.trans first.generation, second.quiet⟩

theorem finished_calm (core : Core) (stdout : OutputStatus) (stderr : PipeResult)
    (log : LogStatus) (ready : core.pending = none) :
    Calm core (core.finished stdout stderr log).core := by
  simp only [Core.finished]
  split
  · split
    · split
      · (
        (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
        (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
        constructor <;>
        simp_all [])
      · exact Calm.through (by (
        (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
        (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
        constructor <;>
        simp_all [])) (Core.exitReported_calm _ _ (by simpa using ready))
    · (
      (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
      (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
      constructor <;>
      simp_all [Core.report])
    · (
      (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
      (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
      constructor <;>
      simp_all [])
  · (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])
  · (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])

theorem step_calm (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (ready : core.pending = none) :
    Calm core (core.step clearDisabled reading event).core := by
  have calm : Calm core (core.dispatch clearDisabled (core.instant reading) event).core := by
    unfold dispatch
    split
    · simp_all
    · split <;> first
        | exact core.command_calm clearDisabled _ ready
        | exact core.candidate_calm _ _ ready
        | exact core.exited_calm _ _ _ ready
        | exact core.finished_calm _ _ _ ready
        | exact core.refused_calm _ ready
        | exact core.tick_calm _ ready
        | exact core.close_calm ready
        | (
          (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
          (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
          constructor <;>
          simp_all [])
  exact ⟨calm.generation, calm.quiet⟩

theorem step_waiting (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (pending : Pending) (waiting : core.pending = some pending) :
    (core.step clearDisabled reading event).core = { core with last := core.instant reading } := by
  simp [step, dispatch, Stepped.at, waiting]

end Core

namespace Core

theorem resolve_intent_calm (core : Core) (now : Nat) (command : Command) (state : PersistedState)
    (result : ((Pending.intent command state).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.intent command state) result).core := by
  cases result <;> simp only [Core.resolve, Core.intentFailed,
    Core.intentSaved] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])

theorem resolve_spawn_calm (core : Core) (now : Nat) (generation : UInt64) (plan : CoreLaunch)
    (result : ((Pending.spawn generation plan).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.spawn generation plan) result).core := by
  cases result <;> simp only [Core.resolve] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Option.map_eq_some_iff, Lifecycle.started_lastGeneration, Lifecycle.failed_lastGeneration])

theorem resolve_adopt_calm (core : Core) (now : Nat) (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
    (result : ((Pending.adopt generation actual state).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.adopt generation actual state) result).core := by
  cases result <;> simp only [Core.resolve, Core.adoptFailed, Core.adopted] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])

theorem resolve_commit_calm (core : Core) (now : Nat) (generation : UInt64) (actual : CoreIdentity) (state : PersistedState) (detail : ControlDetail)
    (result : ((Pending.commit generation actual state detail).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.commit generation actual state detail) result).core := by
  cases result <;> simp only [Core.resolve, Core.committed] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration,
      Lifecycle.adoptFinalIdentity_lastGeneration])

theorem resolve_exitIntent_calm (core : Core) (now : Nat) (state : PersistedState)
    (result : ((Pending.exitIntent state).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.exitIntent state) result).core := by
  cases result <;> simp only [Core.resolve] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report])

theorem resolve_seed_calm (core : Core) (now : Nat) (intended : Desired)
    (result : ((Pending.seed intended).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.seed intended) result).core := by
  cases result <;> simp only [Core.resolve, Core.seeded] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Core.moveTo, Core.stop, Option.map_eq_some_iff, Lifecycle.request_lastGeneration])

theorem resolve_archive_calm (core : Core) (now : Nat) (identity : Identity) (intended : Desired) (stamp : UInt64)
    (result : ((Pending.archive identity intended stamp).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.archive identity intended stamp) result).core := by
  cases result <;> simp only [Core.resolve] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Lifecycle.archiveFailed_lastGeneration])

theorem resolve_reopen_calm (core : Core) (now : Nat) (identity : Identity) (intended : Desired) (archive : System.FilePath)
    (result : ((Pending.reopen identity intended archive).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.reopen identity intended archive) result).core := by
  cases result <;> simp only [Core.resolve] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report])

theorem resolve_replacement_calm (core : Core) (now : Nat) (state : PersistedState) (ackStop : Bool)
    (result : ((Pending.replacement state ackStop).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.replacement state ackStop) result).core := by
  cases result <;> simp only [Core.resolve, Core.replaced] <;> repeat' split
  all_goals (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report, Lifecycle.replacementIntent_lastGeneration])

theorem resolve_windUp_calm (core : Core) (now : Nat) (generation : UInt64)
    (result : ((Pending.windUp generation).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.windUp generation) result).core := by
  cases result
  · exact Calm.through (by (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])) (Core.refused_calm _ _ rfl)
  · exact ⟨rfl, fun _ _ waiting => nomatch waiting⟩

theorem resolve_exitMap_calm (core : Core) (now : Nat) (report : ExitReport) (skip : Option Nat)
    (result : ((Pending.exitMap report skip).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.exitMap report skip) result).core := by
  cases result
  · exact Calm.through (by (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])) (Core.exitReported_calm _ _ rfl)
  · exact Calm.through (by (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])) (Core.exitReported_calm _ _ rfl)

theorem resolve_map_calm (core : Core) (now : Nat) (skip : Option Nat)
    (result : ((Pending.map skip).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.map skip) result).core := by
  cases result
  · exact Calm.through (by (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report])) (Core.launchCheck_calm _ _ rfl)
  · exact Calm.through (by (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])) (Core.launchCheck_calm _ _ rfl)

theorem resolve_closeMap_calm (core : Core) (now : Nat) (skip : Option Nat)
    (result : ((Pending.closeMap skip).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.closeMap skip) result).core := by
  cases result
  · exact Calm.through (by (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [Core.report])) (Core.closed_calm _ rfl)
  · exact Calm.through (by (
    (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
    (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
    constructor <;>
    simp_all [])) (Core.closed_calm _ rfl)

theorem resume_calm (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result)
    (notLaunch : ∀ state plan, pending ≠ .launch state plan) :
    Calm core (core.resume reading pending result).core := by
  have calm : Calm core
      ({ core with pending := none }.resolve (core.instant reading) pending result).core := by
    cases pending with
    | launch state plan => exact absurd rfl (notLaunch state plan)
    | intent => exact core.resolve_intent_calm _ _ _ _
    | spawn => exact core.resolve_spawn_calm _ _ _ _
    | windUp => exact core.resolve_windUp_calm _ _ _
    | adopt => exact core.resolve_adopt_calm _ _ _ _ _
    | commit => exact core.resolve_commit_calm _ _ _ _ _ _
    | exitMap => exact core.resolve_exitMap_calm _ _ _ _
    | exitIntent => exact core.resolve_exitIntent_calm _ _ _
    | map => exact core.resolve_map_calm _ _ _
    | closeMap => exact core.resolve_closeMap_calm _ _ _
    | seed => exact core.resolve_seed_calm _ _ _
    | archive => exact core.resolve_archive_calm _ _ _ _ _
    | reopen => exact core.resolve_reopen_calm _ _ _ _ _
    | replacement => exact core.resolve_replacement_calm _ _ _ _
  exact ⟨calm.generation, calm.quiet⟩

end Core

end Acorn.Host.Viewer
