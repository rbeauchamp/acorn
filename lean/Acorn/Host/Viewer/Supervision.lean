/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.PipePump
import Acorn.Host.Viewer.IdentityHandshake

/-!
# The viewer supervisor's pure core

The viewer supervises the core as a child process: it starts it, winds it up, restarts it after
an unexpected exit, replaces the whole run on Clear and publishes the lifecycle state the page
shows. This module makes every one of those decisions, with no effect: a state (`Core`), the
events the native actor hands it, and one step per event that returns the next state and the
effects to perform. The actor that reads the world and performs the effects is
`Acorn.Host.Viewer.Supervisor`.

**One operation at a time.** Some effects have an outcome the supervisor must know before it
goes on: a write of the state file, a spawn, the stop line, the identity handshake, a fresh
seed, the archival rename, the replacement directory and a map write. A step that needs one
ends with it as its `Pending` call, and the actor hands the call's outcome to `Core.resume`
before it reads anything else. So the state file is written before the spawn that relies on it,
and a reaction to a failed write is decided by the step that sees the failure.

**Every step ends with what it decided.** The effects of a result (`Stepped.effects`) begin
with the settlement of its lifecycle and detail: the broadcaster installs that lifecycle, with
the observer changes the transition makes, and publishes its control record in one serialized
operation (`Broadcast.settle`). The control record of every result is the one of its state.

**A supervision is sealed by its run.** A `Supervision` holds a state with a derivation (`Ran`)
from its start by steps and outcomes, for its Clear configuration. There is no other way to a
value, so every theorem about the states that `Ran` reaches holds of the supervisor the actor
drives. The instants of a supervision do not go back, whatever the clock reads
(`Supervision.at_later`). What the step decides is proved here; what the operating system does
with each effect is the trusted base the actor names.
-/
namespace Acorn.Host.Viewer

/-- A run longer than this many milliseconds resets the short-failure sequence. -/
def healthyRunMs : Nat := 30000

/-- The retained map is persisted at most this often, in milliseconds, between exits. -/
def mapInterval : Nat := 10000

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

/-- The intent an operator command saves. -/
def Command.desired : Command → Desired
  | .start => .running
  | .stop | .clear => .stopped

/-- A clock reading as a machine word, saturated at the largest word. -/
def clockWord (now : Nat) : UInt64 := (min now (2 ^ 64 - 1)).toUInt64

/-! ## The state -/

/-- The native process slot, as the step holds it. -/
inductive Slot where
  /-- No child and no reader owns the run. -/
  | empty
  /-- The child of this generation lives. -/
  | live (generation : UInt64)
  /-- The child exited with this status, its readers still drain, and whether the supervisor
  had asked it to wind up. -/
  | draining (generation : UInt64) (code : UInt32) (requested : Bool)
  deriving DecidableEq

/-- The run directory capability the actor holds. -/
inductive Owner where
  /-- The actor holds the capability of the run directory. -/
  | current
  /-- The run moved and no replacement capability exists; nothing writes again. -/
  | retired (reason : String)
  deriving DecidableEq

/-- How far the viewer has gone in closing. -/
inductive Closing where
  /-- The viewer serves. -/
  | open
  /-- The viewer winds the core up, then closes; and whether a failure was reported. -/
  | closing (failed : Bool)
  /-- The core is reaped and the map persisted; and whether a failure was reported. -/
  | closed (failed : Bool)
  deriving DecidableEq

/-- What an exit report holds while its map write is under way. -/
structure ExitReport where
  /-- The detail the exit publishes. -/
  detail : ControlDetail
  /-- The failure the exit records. -/
  failure : Option String
  /-- The transition of the exit. -/
  transition : ControlTransition
  /-- The reason of the exit. -/
  reason : String
  /-- Whether the exit was unexpected, so the page is told with an `eos` notice. -/
  announce : Bool

/-- A native operation whose outcome the step needs before it goes on. -/
inductive Call where
  /-- Publish the state file. -/
  | writeState (state : PersistedState)
  /-- Persist the retained map unless its revision is `skip`. -/
  | writeMap (skip : Option Nat)
  /-- Spawn the core for a reserved generation. -/
  | spawn (generation : UInt64) (launch : CoreLaunch)
  /-- Send the core its one stop line. -/
  | windUp (generation : UInt64)
  /-- Install a persisted identity in the observer and release the output it held. -/
  | commit (generation : UInt64) (actual : CoreIdentity) (lifecycle : Lifecycle)
      (detail : ControlDetail)
  /-- Draw a fresh terrain seed. -/
  | seed
  /-- Rename the whole run directory into the archive. -/
  | archive (stamp : UInt64)
  /-- Open the empty replacement run directory. -/
  | reopen

/-- The outcome of each call. -/
def Call.Result : Call → Type
  | .writeState _ => Except String Unit
  | .writeMap _ => Except String (Option Nat)
  | .spawn _ _ => Except String Unit
  | .windUp _ => Except String Unit
  | .commit _ _ _ _ => Except String Nat
  | .seed => Except String UInt64
  | .archive _ => ArchiveResult
  | .reopen => Except String Unit

/-- Why a step waits, with what it goes on with. -/
inductive Pending where
  /-- An operator command's intent is being saved. -/
  | intent (command : Command) (state : PersistedState)
  /-- The attempted launch is being saved before the spawn. -/
  | launch (state : PersistedState) (launch : CoreLaunch)
  /-- The reserved generation is being spawned. -/
  | spawn (generation : UInt64) (launch : CoreLaunch)
  /-- The stop line is being sent. -/
  | windUp (generation : UInt64)
  /-- A checkpoint-selected identity is being saved. -/
  | adopt (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
  /-- The saved identity is being installed in the observer, with this detail. -/
  | commit (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
      (detail : ControlDetail)
  /-- The map is persisted after a reap, before the exit is reported. -/
  | exitMap (report : ExitReport) (skip : Option Nat)
  /-- The intent is saved after an exit. -/
  | exitIntent (state : PersistedState)
  /-- The periodic map write. -/
  | map (skip : Option Nat)
  /-- The final map write of a closing viewer. -/
  | closeMap (skip : Option Nat)
  /-- Clear's fresh seed. -/
  | seed (intended : Desired)
  /-- Clear's archival. -/
  | archive (identity : Identity) (intended : Desired) (stamp : UInt64)
  /-- Clear's replacement directory. -/
  | reopen (identity : Identity) (intended : Desired) (archive : System.FilePath)
  /-- Clear's replacement state. -/
  | replacement (state : PersistedState)

/-- The call each pending operation makes, from the lifecycle of the state that waits: an
identity is installed with that lifecycle, the identity adopted. -/
def Pending.call (pending : Pending) (lifecycle : Lifecycle) : Call :=
  match pending with
  | .intent _ state | .launch state _ | .adopt _ _ state | .exitIntent state
  | .replacement state => .writeState state
  | .spawn generation plan => .spawn generation plan
  | .windUp generation => .windUp generation
  | .commit generation actual _ detail =>
    .commit generation actual (lifecycle.adoptFinalIdentity generation actual.identity) detail
  | .exitMap _ skip | .map skip | .closeMap skip => .writeMap skip
  | .seed _ => .seed
  | .archive _ _ stamp => .archive stamp
  | .reopen _ _ _ => .reopen

/-- Whether a pending operation acts on the run directory: through its capability, or by
opening its replacement. -/
def Pending.writes : Pending → Bool
  | .intent _ _ | .launch _ _ | .adopt _ _ _ | .exitIntent _ | .replacement _
  | .exitMap _ _ | .map _ | .closeMap _ | .archive _ _ _
  | .reopen _ _ _ => true
  | .spawn _ _ | .windUp _ | .commit _ _ _ _ | .seed _ => false

/-- Whether a pending operation belongs to a Clear, the saving of its intent included. -/
def Pending.clears : Pending → Bool
  | .intent command _ => command == .clear
  | .seed _ | .archive _ _ _ | .reopen _ _ _ | .replacement _ => true
  | _ => false

/-- Whether a pending operation starts or changes what the run intends: a command's or an
exit's intent, a launch, a spawn, a periodic map write or a Clear. A closing viewer begins
none of them. -/
def Pending.serves : Pending → Bool
  | .intent _ _ | .exitIntent _ | .launch _ _ | .spawn _ _ | .map _ | .exitMap _ _ => true
  | pending => pending.clears

/-- The supervisor's complete state. -/
structure Core where
  /-- The process lifecycle the broadcaster mirrors. -/
  lifecycle : Lifecycle
  /-- The native process slot. -/
  slot : Slot
  /-- The durable state as the supervisor last decided it. -/
  persisted : PersistedState
  /-- A Clear's replacement state, archived and opened but not yet published. -/
  replacement : Option PersistedState
  /-- The run directory capability. -/
  owner : Owner
  /-- The detail of the last transition. -/
  detail : ControlDetail
  /-- The last failure, reported when the viewer closes. -/
  failure : Option String
  /-- The instant of the last periodic map write. -/
  mapAt : Nat
  /-- The map revision last persisted. -/
  mapRevision : Option Nat
  /-- How far the viewer has gone in closing. -/
  closing : Closing
  /-- The instant of the last step, in milliseconds of the monotonic clock. -/
  last : Nat
  /-- The operation whose outcome the step waits for. -/
  pending : Option Pending

/-- A terminal or diagnostic line the actor prints, or a notice and reader start that follow
the settlement of a step. -/
inductive Follow where
  /-- The page's process-exit notice. -/
  | announceExit (reason : String)
  /-- The page's acknowledgement of Clear. -/
  | announceCleared
  /-- Start the readers of the spawned child. -/
  | attach (generation : UInt64)
  /-- A line on the viewer's standard output. -/
  | say (text : String)
  /-- A shutdown diagnostic on the viewer's standard error. -/
  | complain (text : String)

/-- An effect of a step, performed in order. -/
inductive Effect where
  /-- Install a lifecycle with its observer changes and publish its control record. -/
  | settle (lifecycle : Lifecycle) (changes : List Change) (detail : ControlDetail)
  /-- A notice, reader start or terminal line. -/
  | follow (follow : Follow)

/-- The result of a step: the next state, the observer changes installed with its lifecycle,
and what follows the settlement. -/
structure Stepped where
  /-- The next state. -/
  core : Core
  /-- Observer changes made with the lifecycle. -/
  changes : List Change := []
  /-- Notices, reader starts and lines after the settlement. -/
  follows : List Follow := []

/-- The effects of a result, in order: the settlement of its state, then what follows it. The
pending call of its state, if any, comes after them. -/
def Stepped.effects (stepped : Stepped) : List Effect :=
  .settle stepped.core.lifecycle stepped.changes stepped.core.detail ::
    stepped.follows.map .follow

/-- Record the instant of a step in its result. -/
def Stepped.at (stepped : Stepped) (now : Nat) : Stepped :=
  { stepped with core := { stepped.core with last := now } }

/-- What the native actor hands the step: an observation of the world or the operator. -/
inductive Event where
  /-- An operator command taken from the bounded queue. -/
  | command (command : Command)
  /-- The identity the process of this generation reported, held until it is persisted. -/
  | candidate (generation : UInt64) (actual : CoreIdentity)
  /-- The live child was reaped with this status after this many milliseconds. -/
  | exited (code : UInt32) (uptimeMs : Nat)
  /-- The readers of the reaped child finished, with what they observed. -/
  | finished (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus)
  /-- The native wait refused; the slot stays owned. -/
  | refused (reason : String)
  /-- Nothing else happened. -/
  | tick
  /-- The operator asked the viewer to close. -/
  | close

/-! ## Reasons -/

/-- The account of an exit status. -/
def exitReason (code : UInt32) : String :=
  s!"core exited with status {code}" ++
    if code != 0 then
      "; abnormal termination; learning since the last successful checkpoint may be lost"
    else ""

private def pipeReason (name : String) (result : PipeResult) : String :=
  match result with
  | .eof => ""
  | .refused reason => s!"; {name} read refused: {controlDiagnostic reason}"

/-- The account of what a reaped child's readers observed. -/
def outputReason (output : OutputStatus) (stderr : PipeResult) (log : LogStatus) : String :=
  (log.checkpoint.map (fun status => "; " ++ status.line)).getD
    "; final checkpoint status unavailable" ++
  (match output.completion with
    | none => "; stdout completion unavailable"
    | some result => pipeReason "stdout" result) ++ pipeReason "stderr" stderr ++
  s!"; stdout refused oversized={output.oversized}, malformed={output.malformed}, stale={output.stale}" ++
  s!"; stderr log dropped={log.dropped}, oversized={log.oversized}, write failures={log.failures}" ++
  (log.lastFailure.map (fun reason => s!"; last log error: {controlDiagnostic reason}")).getD ""

/-- A termination fails when the status is nonzero, the final save failed, a pipe did not end
cleanly or the log lost a write. -/
def terminationFailed (code : UInt32) (output : OutputStatus) (stderr : PipeResult)
    (log : LogStatus) : Bool :=
  let pipesFailed := match output.completion, stderr with
    | some .eof, .eof => false
    | _, _ => true
  code != 0 || log.checkpoint == some .failed || pipesFailed || log.failures != 0

/-- A requested exit stopped the core; an unexpected one schedules a restart while the run
intends to run, and fails otherwise. -/
def exitTransition (requested : Bool) (lifecycle : Lifecycle) : ControlTransition :=
  if requested then .coreStopped
  else if lifecycle.desiredValue == .running then .restartScheduled else .failed

namespace Core

/-! ## Transitions -/

/-- Record a transition with its capped reason; a failure is kept for the close report. -/
def report (core : Core) (transition : ControlTransition) (reason : String) : Core :=
  let reason := controlDiagnostic reason
  { core with
    detail := { core.detail with transition, reason }
    failure := if transition == .failed then some reason else core.failure }

/-- The generation that must receive the stop line after a lifecycle change: the live process
that the change moved into stopping. -/
def windUpTarget (slot : Slot) (before after : Lifecycle) : Option UInt64 :=
  match slot with
  | .live generation =>
    if after.phaseValue == .stopping generation && before.phaseValue != .stopping generation then
      some generation
    else none
  | .empty | .draining _ _ _ => none

/-- Move to a lifecycle. A live process that it moves into stopping is sent its stop line
next, and nothing else is pending. -/
def moveTo (core : Core) (lifecycle : Lifecycle) : Core :=
  { core with
    lifecycle
    pending := (windUpTarget core.slot core.lifecycle lifecycle).map .windUp }

/-- Stop without saving the intent: the lifecycle stops and a live process winds up. -/
def stop (core : Core) : Core := core.moveTo (core.lifecycle.request .stop)

/-- Whether the map may be written: the actor holds the run directory and no replacement
waits to be published. -/
def mapWritable (core : Core) : Bool := core.owner == .current && core.replacement.isNone

/-- A command's intent could not be saved: the core still winds up, and nothing starts. -/
def intentFailed (core : Core) (reason : String) : Stepped :=
  ⟨core.stop.report .failed s!"intent could not be saved; process wind-up requested: {reason}",
    [], []⟩

/-- An operator command from the bounded queue. A disabled Clear changes nothing. While a
replacement waits to be published, Start and Stop revise its intent and Clear is refused.
Otherwise the command's intent is saved first. -/
def command (core : Core) (clearDisabled : Option String) (command : Command) : Stepped :=
  if command == .clear && clearDisabled.isSome then ⟨core, [], []⟩
  else match core.replacement with
  | some replacement =>
    if command == .clear then
      ⟨core.report .failed "replacement state publication is pending; Clear refused", [], []⟩
    else ⟨{ core with replacement := some { replacement with desired := command.desired } }, [], []⟩
  | none =>
    match core.owner with
    | .retired reason => core.intentFailed reason
    | .current =>
      ⟨{ core with
        pending := some (.intent command { core.persisted with desired := command.desired }) },
        [], []⟩

/-- A command's intent was saved: the lifecycle follows the command. -/
def intentSaved (core : Core) (command : Command) (state : PersistedState) : Stepped :=
  let (transition, reason) := match command with
    | .start => (ControlTransition.startRequested, "operator requested Start")
    | .stop => (.stopRequested, "operator requested Stop")
    | .clear => (.clearRequested, "operator requested whole-run Clear")
  ⟨({ core with persisted := state }.moveTo (core.lifecycle.request command)).report
    transition reason, [], []⟩

/-- A checkpoint-selected identity could not be persisted: its output stays held and the
core winds up. -/
def adoptFailed (core : Core) (reason : String) : Stepped :=
  ⟨core.stop.report .failed
    s!"core identity could not be persisted; observation release refused: {reason}", [], []⟩

/-- The identity a process reported. An identity beyond the browser's integers is refused with
the output it holds, and the core winds up; any other is persisted first. -/
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

/-- The persisted identity is installed in the observer next, with this detail. -/
def adopted (core : Core) (generation : UInt64) (actual : CoreIdentity)
    (state : PersistedState) : Stepped :=
  let detail := { core.detail with
    reason := "core reported the identity selected by checkpoint loading" }
  ⟨{ core with pending := some (.commit generation actual state detail) }, [], []⟩

/-- The identity was installed and its held output released. -/
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

/-- The live child was reaped. An exit the supervisor did not ask for consumes the restart
budget; either way the generation is retired and its readers drain. -/
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

/-- A closing viewer has closed: its last failure is reported. -/
def closed (core : Core) : Stepped :=
  match core.closing with
  | .closing failed =>
    ⟨{ core with closing := .closed (failed || core.failure.isSome) }, [],
      (core.failure.map fun reason => [Follow.complain reason]).getD []⟩
  | .open | .closed _ => ⟨core, [], []⟩

/-- A closing viewer with no process persists its map and closes. -/
def closeOut (core : Core) : Stepped :=
  if core.mapWritable then ⟨{ core with pending := some (.closeMap core.mapRevision) }, [], []⟩
  else core.closed

/-- An exit is reported after its map write: the page hears of an unexpected one, and the
intent the exit leaves is saved. -/
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

/-- The readers of the reaped child finished. A serving viewer persists the map, then reports
the exit; a closing one reports it and closes at a later tick, after the identity the readers
delivered is attributed. -/
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

/-- The native wait or wind-up refused; a closing viewer reports it when it closes. -/
def refused (core : Core) (reason : String) : Stepped :=
  match core.closing with
  | .open => ⟨core.report .failed reason, [], []⟩
  | .closing _ =>
    ⟨{ core with closing := .closing true }, [],
      [.complain s!"retaining process ownership: {reason}"]⟩
  | .closed _ => ⟨core, [], []⟩

/-- Launch when the lifecycle admits a reservation now and nothing else owns the run: the
attempted launch is saved first. -/
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

/-- Persist the map when it is due, then consider a launch. -/
def mapOrLaunch (core : Core) (now : Nat) : Stepped :=
  if core.mapWritable && decide (mapInterval ≤ now - core.mapAt) then
    ⟨{ core with mapAt := now, pending := some (.map core.mapRevision) }, [], []⟩
  else core.launchCheck now

/-- Clear, once the process is reaped and its readers finished: a fresh seed comes first. -/
def clear (core : Core) (intended : Desired) : Stepped :=
  if core.persisted.identity.agentEpoch.toNat ≥ browserIntegerMax then
    ⟨core.stop.report .failed "Clear refused: logical agent epoch exhausted", [], []⟩
  else match core.owner with
    | .current => ⟨{ core with pending := some (.seed intended) }, [], []⟩
    | .retired _ => ⟨core, [], []⟩

/-- Nothing else happened: publish a replacement that waits, or go on with a Clear the reaped
process admits, or persist the map and consider a launch. A closing viewer with no process
closes. -/
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

/-- The operator closes the viewer: the core winds up without the intent being saved, and the
viewer closes once it is reaped. -/
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

/-- A Clear's fresh seed arrived: a seed beyond the browser's integers refuses the Clear, and
any other names the replacement identity, the next run with the next agent epoch, and the
archival begins. -/
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

/-- The replacement state was published: the new identity is installed, with the intent the
operator last chose, and the page is told. -/
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

/-- How a retired run directory is named in the failures it causes. -/
def retiredReason (archive : System.FilePath) : String :=
  s!"the run directory moved to {archive} and no replacement directory is owned"

/-- The outcome of the pending call, from a state with nothing pending. -/
def resolve (core : Core) (now : Nat) :
    (pending : Pending) → (pending.call core.lifecycle).Result → Stepped
  | .intent _ _, .error reason => core.intentFailed reason
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
  | .replacement _, .error reason =>
    ⟨core.report .failed s!"old run archived; replacement state not published: {reason}", [], []⟩
  | .replacement state, .ok () => core.replaced state

/-! ## The step -/

/-- The state the viewer starts from, after the bootstrap published `persisted`: no process,
nothing pending, the lifecycle of the durable identity and intent, and the reason the page is
shown first. -/
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

/-- The instant of a step at a reading of the clock: the reading, or the instant of the last
step when the reading is before it. -/
def instant (core : Core) (reading : Nat) : Nat := max core.last reading

/-- The step of an event, before the instant is recorded. A state that waits for a call's
outcome takes no event; a closed viewer takes none; a closing one takes no command. -/
def dispatch (core : Core) (clearDisabled : Option String) (now : Nat) (event : Event) :
    Stepped :=
  match core.pending with
  | some _ => ⟨core, [], []⟩
  | none =>
    match core.closing, event with
    | .closed _, _ => ⟨core, [], []⟩
    | .open, .command command => core.command clearDisabled command
    | .closing _, .command _ => ⟨core, [], []⟩
    | _, .candidate generation actual => core.candidate generation actual
    | _, .exited code uptime => core.exited now code uptime
    | _, .finished stdout stderr log => core.finished stdout stderr log
    | _, .refused reason => core.refused reason
    | _, .tick => core.tick now
    | _, .close => core.close

/-- One step on an event at a reading of the clock, at the instant `Core.instant` gives. -/
def step (core : Core) (clearDisabled : Option String) (reading : Nat) (event : Event) : Stepped :=
  (core.dispatch clearDisabled (core.instant reading) event).at (core.instant reading)

/-- The outcome of the pending call at a reading of the clock, at the instant `Core.instant`
gives. -/
def resume (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result) : Stepped :=
  ({ core with pending := none }.resolve (core.instant reading) pending result).at
    (core.instant reading)

end Core

/-! ## A run -/

/-- A state is reached from a start by steps and call outcomes, for a Clear configuration. -/
inductive Ran (clearDisabled : Option String) : Core → Prop where
  /-- The viewer starts from a published durable state. -/
  | start (persisted : PersistedState) (reason : String) (reading : Nat) :
      Ran clearDisabled (Core.start persisted clearDisabled reason reading)
  /-- A step on an event. -/
  | step {core : Core} (ran : Ran clearDisabled core) (reading : Nat) (event : Event) :
      Ran clearDisabled (core.step clearDisabled reading event).core
  /-- The outcome of the call the state waits for. -/
  | resume {core : Core} {pending : Pending} (ran : Ran clearDisabled core)
      (waiting : core.pending = some pending) (reading : Nat)
      (result : (pending.call core.lifecycle).Result) :
      Ran clearDisabled (core.resume reading pending result).core

/-- A supervision: its state, with a derivation from its start for its Clear configuration.
Every value is reached by `Supervision.start`, `Supervision.step` and `Supervision.resume`. -/
structure Supervision (clearDisabled : Option String) where
  /-- The state. -/
  core : Core
  /-- The state is reached from a start. -/
  reached : Ran clearDisabled core

/-- A supervision at its start, with the effects that publish its first control record. -/
def Supervision.start (clearDisabled : Option String) (persisted : PersistedState)
    (reason : String) (reading : Nat) : Supervision clearDisabled × List Effect :=
  let core := Core.start persisted clearDisabled reason reading
  (⟨core, .start persisted reason reading⟩, ({ core } : Stepped).effects)

/-- One step on an event, with its effects. -/
def Supervision.step {clearDisabled : Option String} (supervision : Supervision clearDisabled)
    (reading : Nat) (event : Event) : Supervision clearDisabled × List Effect :=
  let stepped := supervision.core.step clearDisabled reading event
  (⟨stepped.core, .step supervision.reached reading event⟩, stepped.effects)

/-- The outcome of the pending call, with its effects. -/
def Supervision.resume {clearDisabled : Option String} (supervision : Supervision clearDisabled)
    {pending : Pending} (waiting : supervision.core.pending = some pending) (reading : Nat)
    (result : (pending.call supervision.core.lifecycle).Result) :
    Supervision clearDisabled × List Effect :=
  let stepped := supervision.core.resume reading pending result
  (⟨stepped.core, .resume supervision.reached waiting reading result⟩, stepped.effects)

/-! ## What the step guarantees

The theorems below are about `Core.step` and `Core.resume`, the functions the actor runs, over
every state a run reaches (`Ran`). -/

namespace Core

@[simp] theorem report_pending (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).pending = core.pending := rfl
@[simp] theorem report_owner (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).owner = core.owner := rfl
@[simp] theorem report_closing (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).closing = core.closing := rfl
@[simp] theorem report_lifecycle (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).lifecycle = core.lifecycle := rfl
@[simp] theorem report_replacement (core : Core) (transition : ControlTransition)
    (reason : String) : (core.report transition reason).replacement = core.replacement := rfl
@[simp] theorem report_slot (core : Core) (transition : ControlTransition) (reason : String) :
    (core.report transition reason).slot = core.slot := rfl
@[simp] theorem report_persisted (core : Core) (transition : ControlTransition)
    (reason : String) : (core.report transition reason).persisted = core.persisted := rfl
@[simp] theorem report_transition (core : Core) (transition : ControlTransition)
    (reason : String) : (core.report transition reason).detail.transition = transition := rfl

@[simp] theorem moveTo_pending (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).pending =
      (windUpTarget core.slot core.lifecycle lifecycle).map .windUp := rfl
@[simp] theorem moveTo_owner (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).owner = core.owner := rfl
@[simp] theorem moveTo_closing (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).closing = core.closing := rfl
@[simp] theorem moveTo_lifecycle (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).lifecycle = lifecycle := rfl
@[simp] theorem moveTo_replacement (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).replacement = core.replacement := rfl
@[simp] theorem moveTo_slot (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).slot = core.slot := rfl
@[simp] theorem moveTo_persisted (core : Core) (lifecycle : Lifecycle) :
    (core.moveTo lifecycle).persisted = core.persisted := rfl

@[simp] theorem stop_eq (core : Core) : core.stop = core.moveTo (core.lifecycle.request .stop) :=
  rfl

end Core

/-- What every reached state holds. -/
structure Core.Invariant (clearDisabled : Option String) (core : Core) : Prop where
  /-- Nothing acts on a retired run directory. -/
  retired : ∀ pending, core.pending = some pending → pending.writes = true →
    core.owner = .current
  /-- With Clear disabled, no Clear is pending or under way. -/
  clearless : clearDisabled.isSome = true → core.lifecycle.Clearless ∧
    core.replacement = none ∧ ∀ pending, core.pending = some pending → pending.clears = false
  /-- A closing viewer starts nothing. -/
  closing : core.closing ≠ .open → ∀ pending, core.pending = some pending →
    pending.serves = false
  /-- An attempted launch is saved with the launch's own identity. -/
  launch : ∀ state plan, core.pending = some (.launch state plan) →
    state.processStarted = true ∧ state.identity = plan.identity
  /-- A spawn waits on a published state that records the attempted launch of its plan. -/
  spawn : ∀ generation plan, core.pending = some (.spawn generation plan) →
    core.persisted.processStarted = true ∧ core.persisted.identity = plan.identity

/-- An admitted launch names the identity of the state it was prepared from. -/
theorem PersistedState.launch_identity (state : PersistedState) (plan : CoreLaunch)
    (admitted : state.launch = .ok plan) : plan.identity = state.identity := by
  unfold PersistedState.launch at admitted
  by_cases safe : state.identity.browserSafe = true <;>
    by_cases exhausted : (state.processStarted && decide (state.identity.agentEpoch.toNat ≥ browserIntegerMax)) = true <;>
    simp_all [bind, Except.bind, pure, Except.pure]
  all_goals (subst admitted; rfl)

/-- **The instants of a supervision do not go back.** For every state and reading of the
clock, the instant of the step is not before the instant of the last step, and it is the
reading when the reading is not before it. -/
theorem Core.instant_later (core : Core) (reading : Nat) :
    core.last ≤ core.instant reading ∧ (core.last ≤ reading → core.instant reading = reading) :=
  ⟨Nat.le_max_left _ _, fun later => Nat.max_eq_right later⟩

/-- A step records its instant. -/
theorem Core.step_last (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) : (core.step clearDisabled reading event).core.last = core.instant reading :=
  rfl

/-- An outcome records its instant. -/
theorem Core.resume_last (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result) :
    (core.resume reading pending result).core.last = core.instant reading := rfl

/-- **Every result settles its own state first.** The effects of every result begin with the
installation of its lifecycle, with its observer changes, and the publication of its control
record from that lifecycle and its detail; everything after them is a notice, a reader start
or a terminal line. -/
theorem Stepped.effects_settle (stepped : Stepped) :
    stepped.effects = .settle stepped.core.lifecycle stepped.changes stepped.core.detail ::
      stepped.follows.map .follow := rfl


namespace Core

/-- The derived comparison of commands is equality. -/
@[simp] theorem command_beq (left right : Command) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

/-- The derived comparison of intents is equality. -/
@[simp] theorem desired_beq (left right : Desired) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

/-- The derived comparison of phases is equality. -/
@[simp] theorem phase_beq (left right : Phase) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> first
    | rfl
    | (rename_i first second; show (first == second) = _; rw [Bool.eq_iff_iff]; simp)

/-- A property of every value of an optional mapped value is one of every value it maps. -/
private theorem forall_map_some {α β : Type} (f : α → β) (value : Option α) (property : β → Prop) :
    (∀ mapped, value.map f = some mapped → property mapped) ↔
      ∀ inner, value = some inner → property (f inner) := by
  cases value <;> simp

/-- Discharges the invariant of a branch of a transition: each field follows from the
transition's own guards, the invariant of the state it starts from, and the lifecycle's
lemmas. -/
scoped macro "invariant_leaf" : tactic => `(tactic| (
  refine ⟨?_, fun _ => ?_, ?_, ?_, ?_⟩
  · simp_all [Pending.writes, forall_map_some, Core.mapWritable]
  · (try have := Lifecycle.reserve_clearless _ _ _ _ (by assumption))
    simp_all [Pending.clears, forall_map_some, Lifecycle.ite_clearless,
      Lifecycle.request_clearless, Lifecycle.reserve_clearless, Lifecycle.started_clearless,
      Lifecycle.failed_clearless, Lifecycle.retire_clearless, Lifecycle.archiveFailed_clearless,
      Lifecycle.replacementIntent_clearless, Lifecycle.adoptFinalIdentity_clearless,
      Lifecycle.clearless_archiveIntent, Lifecycle.clearless_beginArchive,
      Lifecycle.clearless_archived]
  · simp_all [Pending.serves, Pending.clears, forall_map_some]
  · (try have := PersistedState.launch_identity _ _ (by assumption))
    simp_all [forall_map_some]
  · simp_all [forall_map_some]))

theorem command_invariant (core : Core) (clearDisabled : Option String) (command : Command)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none)
    (serving : core.closing = .open) :
    (core.command clearDisabled command).core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold Core.command Core.intentFailed <;> cases command <;> repeat' split
  all_goals invariant_leaf

/-- The definitions a transition's proof unfolds, its helpers included. -/
scoped macro "unfold_transition" : tactic => `(tactic| simp only [Core.command, Core.intentFailed,
  Core.candidate, Core.adoptFailed, Core.exited, Core.refused, Core.closed, Core.closeOut,
  Core.exitReported, Core.finished, Core.launchCheck, Core.mapOrLaunch, Core.clear, Core.tick,
  Core.close])

theorem candidate_invariant (core : Core) (clearDisabled : Option String) (generation : UInt64)
    (actual : CoreIdentity) (invariant : core.Invariant clearDisabled)
    (ready : core.pending = none) :
    (core.candidate generation actual).core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

theorem exited_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (code : UInt32) (uptime : Nat) (invariant : core.Invariant clearDisabled)
    (ready : core.pending = none) :
    (core.exited now code uptime).core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

theorem refused_invariant (core : Core) (clearDisabled : Option String) (reason : String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.refused reason).core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

theorem closed_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    core.closed.core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

theorem exitReported_invariant (core : Core) (clearDisabled : Option String)
    (report : ExitReport) (invariant : core.Invariant clearDisabled)
    (ready : core.pending = none) (serving : core.closing = .open) :
    (core.exitReported report).core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

theorem closeOut_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    core.closeOut.core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

theorem finished_invariant (core : Core) (clearDisabled : Option String)
    (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.finished stdout stderr log).core.Invariant clearDisabled := by
  simp only [Core.finished]
  split
  · split
    · split
      · obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
          invariant_leaf
      · exact Core.exitReported_invariant _ clearDisabled _
          (by obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
                invariant <;> invariant_leaf)
          ready (by assumption)
    · obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
        invariant_leaf
    · obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
        invariant_leaf
  · exact invariant
  · exact invariant

theorem launchCheck_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.launchCheck now).core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

theorem tick_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    (core.tick now).core.Invariant clearDisabled := by
  unfold Core.tick
  split
  · obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
      unfold_transition <;> repeat' split
    all_goals invariant_leaf
  · split
    · exact core.closeOut_invariant clearDisabled invariant ready
    · exact invariant
  · exact invariant

theorem close_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) (ready : core.pending = none) :
    core.close.core.Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    unfold_transition <;> repeat' split
  all_goals invariant_leaf

/-- A state that waits for a call that only a serving viewer makes is serving. -/
theorem Invariant.serving {clearDisabled : Option String} {core : Core} {pending : Pending}
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some pending)
    (serves : pending.serves = true) : core.closing = .open := by
  cases closing : core.closing with
  | «open» => rfl
  | closing failed =>
    have refused := invariant.closing (by simp [closing]) pending waiting
    simp_all
  | closed failed =>
    have refused := invariant.closing (by simp [closing]) pending waiting
    simp_all

/-- The outcomes a proof of a call's outcome unfolds, its helpers included. -/
scoped macro "unfold_outcome" : tactic => `(tactic| simp only [Core.resolve, Core.intentFailed,
  Core.intentSaved, Core.adoptFailed, Core.adopted, Core.committed, Core.seeded, Core.replaced,
  Core.refused])

theorem resolve_intent_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (command : Command) (state : PersistedState)
    (result : ((Pending.intent command state).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.intent command state)) :
    ({ core with pending := none }.resolve now (.intent command state) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_launch_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (state : PersistedState) (plan : CoreLaunch)
    (result : ((Pending.launch state plan).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.launch state plan)) :
    ({ core with pending := none }.resolve now (.launch state plan) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_spawn_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (generation : UInt64) (plan : CoreLaunch)
    (result : ((Pending.spawn generation plan).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.spawn generation plan)) :
    ({ core with pending := none }.resolve now (.spawn generation plan) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_adopt_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
    (result : ((Pending.adopt generation actual state).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.adopt generation actual state)) :
    ({ core with pending := none }.resolve now (.adopt generation actual state) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_commit_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (generation : UInt64) (actual : CoreIdentity) (state : PersistedState) (detail : ControlDetail)
    (result : ((Pending.commit generation actual state detail).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.commit generation actual state detail)) :
    ({ core with pending := none }.resolve now (.commit generation actual state detail) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_exitIntent_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (state : PersistedState)
    (result : ((Pending.exitIntent state).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.exitIntent state)) :
    ({ core with pending := none }.resolve now (.exitIntent state) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_seed_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (intended : Desired)
    (result : ((Pending.seed intended).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.seed intended)) :
    ({ core with pending := none }.resolve now (.seed intended) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_archive_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (identity : Identity) (intended : Desired) (stamp : UInt64)
    (result : ((Pending.archive identity intended stamp).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.archive identity intended stamp)) :
    ({ core with pending := none }.resolve now (.archive identity intended stamp) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_reopen_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (identity : Identity) (intended : Desired) (archive : System.FilePath)
    (result : ((Pending.reopen identity intended archive).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.reopen identity intended archive)) :
    ({ core with pending := none }.resolve now (.reopen identity intended archive) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

theorem resolve_replacement_invariant (core : Core) (clearDisabled : Option String) (now : Nat)
    (state : PersistedState)
    (result : ((Pending.replacement state).call core.lifecycle).Result)
    (invariant : core.Invariant clearDisabled) (waiting : core.pending = some (.replacement state)) :
    ({ core with pending := none }.resolve now (.replacement state) result).core.Invariant clearDisabled := by
  cases result <;> obtain ⟨retired, clearless, closing, launch, spawn⟩ :=
    invariant <;> unfold_outcome <;> repeat' split
  all_goals invariant_leaf

/-- The state an outcome starts from keeps the invariant of the state that waited. -/
theorem cleared_invariant (core : Core) (clearDisabled : Option String)
    (invariant : core.Invariant clearDisabled) :
    ({ core with pending := none } : Core).Invariant clearDisabled := by
  obtain ⟨retired, clearless, closing, launch, spawn⟩ := invariant <;>
    invariant_leaf

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

/-- **Every outcome keeps the invariant.** -/
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
  | replacement => exact core.resolve_replacement_invariant _ _ _ _ invariant waiting

/-- **Every event keeps the invariant.** -/
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

/-- **Every state a run reaches keeps the invariant.** -/
theorem Ran.invariant {clearDisabled : Option String} {core : Core}
    (ran : Ran clearDisabled core) : core.Invariant clearDisabled := by
  induction ran with
  | start persisted reason reading => exact Core.start_invariant persisted _ reason reading
  | step _ reading event invariant => exact Core.step_invariant _ _ reading event invariant
  | resume _ waiting reading result invariant =>
    exact Core.resume_invariant _ _ reading _ result invariant waiting


/-! ## The guarantees, for every supervision -/

/-- **A retired run directory is never acted on again.** For every supervision whose run
directory moved with no replacement owned, the call it waits for, if any, neither writes
through the old capability, archives nor opens a replacement. -/
theorem Supervision.retired_untouched {clearDisabled : Option String}
    (supervision : Supervision clearDisabled) (pending : Pending)
    (waiting : supervision.core.pending = some pending)
    (retired : supervision.core.owner ≠ .current) : pending.writes = false := by
  cases writes : pending.writes
  · rfl
  · exact absurd (supervision.reached.invariant.retired pending waiting writes) retired

/-- **A disabled Clear never archives.** For every supervision of a configuration that cannot
preserve whole-run ownership: no Clear is pending, no archival is under way, no replacement
waits, and the call it waits for, if any, neither saves a Clear's intent nor belongs to a
Clear. -/
theorem Supervision.clear_disabled {reason : String} (supervision : Supervision (some reason)) :
    supervision.core.lifecycle.Clearless ∧ supervision.core.replacement = none ∧
      ∀ pending, supervision.core.pending = some pending → pending.clears = false :=
  supervision.reached.invariant.clearless rfl

/-- **A closing viewer starts nothing.** For every supervision that is closing or closed, the
call it waits for, if any, saves no intent, launches nothing, spawns nothing, writes no
periodic map and belongs to no Clear. -/
theorem Supervision.closing_starts_nothing {clearDisabled : Option String}
    (supervision : Supervision clearDisabled) (closing : supervision.core.closing ≠ .open)
    (pending : Pending) (waiting : supervision.core.pending = some pending) :
    pending.serves = false :=
  supervision.reached.invariant.closing closing pending waiting

/-- **A spawn waits on the state that records its launch.** For every supervision that waits
to spawn, the durable state it holds records an attempted launch with the identity of the
launch it spawns. -/
theorem Supervision.spawn_recorded {clearDisabled : Option String}
    (supervision : Supervision clearDisabled) (generation : UInt64) (plan : CoreLaunch)
    (waiting : supervision.core.pending = some (.spawn generation plan)) :
    supervision.core.persisted.processStarted = true ∧
      supervision.core.persisted.identity = plan.identity :=
  supervision.reached.invariant.spawn generation plan waiting

namespace Core

/-- **A spawn follows the launch write, and only its success.** For every state and every
outcome of the write of an attempted launch: when the outcome leaves the state waiting to
spawn, the write succeeded, the spawn is of that launch, the state holds the state written,
the generation is one more than the last one reserved, the allocator holds it, and the
lifecycle admitted a reservation at the instant of the outcome: it was idle, intended to run,
had no Clear pending and its restart budget admitted a launch. -/
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
    simp [resume, Stepped.at, resolve, Option.map_eq_some_iff] at spawning
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

/-- **A Stop winds a live process up, whether or not its intent is saved.** For every state
that serves, waits for nothing, has no replacement waiting and holds a live process that runs:
after the Stop command, either the stop line is the next call, or the intent is saved first and
the stop line is the next call after either outcome of that write. -/
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
    simp [windUpTarget, live, stopping, running, bne]
  cases owner : core.owner with
  | retired reason =>
    left
    simp [step, dispatch, Stepped.at, ready, serving, Core.command, noReplacement, owner,
      intentFailed, target]
  | current =>
    right
    refine ⟨{ core.persisted with desired := .stopped }, ?_, ?_⟩
    · simp [step, dispatch, Stepped.at, ready, serving, Core.command, noReplacement, owner,
        Command.desired]
    · intro later result
      cases result <;>
        simp [step, dispatch, Stepped.at, ready, serving, Core.command, noReplacement, owner,
          resume, resolve, intentFailed, intentSaved, target]

/-- **Clear installs a run other than the one it retires.** For every state and replacement
state: when publishing the replacement installs it, the lifecycle holds the replacement's
identity, whose run differs from the run of the lifecycle it replaced. -/
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
  · simp at cleared

/-- The readers' report closes nothing and begins no closing map write. -/
theorem finished_defers (core : Core) (stdout : OutputStatus) (stderr : PipeResult)
    (log : LogStatus) :
    (∀ failed, (core.finished stdout stderr log).core.closing = .closed failed →
        core.closing = .closed failed) ∧
      ∀ skip, (core.finished stdout stderr log).core.pending = some (.closeMap skip) →
        core.pending = some (.closeMap skip) := by
  simp only [Core.finished, Core.exitReported]
  repeat' split
  all_goals simp_all

/-- **A core's exit never closes the viewer.** For every state and every report of a reaped
child's readers, the step on that report yields a closed state only from a closed one, and waits
on the closing map write only when the state it starts from does. A closing viewer closes at a
later tick, which the actor hands after it attributes the identity the readers delivered. -/
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

/-- What a transition leaves alone: the generation allocator, and any wait to spawn. Every
event's step and every outcome other than a launch write's is calm. -/
structure Calm (before after : Core) : Prop where
  /-- The allocator holds the same last generation. -/
  generation : after.lifecycle.lastGenerationValue = before.lifecycle.lastGenerationValue
  /-- The state does not wait to spawn. -/
  quiet : ∀ generation plan, after.pending ≠ some (.spawn generation plan)

/-- Discharges calmness of a branch of a transition. -/
scoped macro "calm_leaf" : tactic => `(tactic| (
  (try have := Lifecycle.beginArchive_lastGeneration _ _ (by assumption)) <;>
  (try have := Lifecycle.archived_lastGeneration _ _ _ (by assumption)) <;>
  constructor <;>
  simp_all [Option.map_eq_some_iff, Lifecycle.request_lastGeneration,
    Lifecycle.started_lastGeneration, Lifecycle.failed_lastGeneration,
    Lifecycle.retire_lastGeneration, Lifecycle.archiveFailed_lastGeneration,
    Lifecycle.replacementIntent_lastGeneration, Lifecycle.adoptFinalIdentity_lastGeneration]))

theorem command_calm (core : Core) (clearDisabled : Option String) (command : Command)
    (ready : core.pending = none) :
    Calm core (core.command clearDisabled command).core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem candidate_calm (core : Core) (generation : UInt64) (actual : CoreIdentity)
    (ready : core.pending = none) :
    Calm core (core.candidate generation actual).core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem exited_calm (core : Core) (now : Nat) (code : UInt32) (uptime : Nat)
    (ready : core.pending = none) : Calm core (core.exited now code uptime).core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem refused_calm (core : Core) (reason : String) (ready : core.pending = none) :
    Calm core (core.refused reason).core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem closed_calm (core : Core) (ready : core.pending = none) : Calm core core.closed.core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem closeOut_calm (core : Core) (ready : core.pending = none) :
    Calm core core.closeOut.core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem exitReported_calm (core : Core) (report : ExitReport) (ready : core.pending = none) :
    Calm core (core.exitReported report).core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem launchCheck_calm (core : Core) (now : Nat) (ready : core.pending = none) :
    Calm core (core.launchCheck now).core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

theorem tick_calm (core : Core) (now : Nat) (ready : core.pending = none) :
    Calm core (core.tick now).core := by
  unfold Core.tick
  split
  · unfold_transition
    repeat' split
    all_goals calm_leaf
  · split
    · exact core.closeOut_calm ready
    · calm_leaf
  · calm_leaf

theorem close_calm (core : Core) (ready : core.pending = none) : Calm core core.close.core := by
  unfold_transition
  repeat' split
  all_goals calm_leaf

/-- Calmness composes through a state that differs in neither field. -/
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
      · calm_leaf
      · exact Calm.through (by calm_leaf) (Core.exitReported_calm _ _ (by simpa using ready))
    · calm_leaf
    · calm_leaf
  · calm_leaf
  · calm_leaf

/-- **No event reserves a generation or makes the state wait to spawn.** -/
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
        | calm_leaf
  exact ⟨calm.generation, calm.quiet⟩

/-- A state that waits takes no event: its step changes only the instant. -/
theorem step_waiting (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (pending : Pending) (waiting : core.pending = some pending) :
    (core.step clearDisabled reading event).core = { core with last := core.instant reading } := by
  simp [step, dispatch, Stepped.at, waiting]

end Core

namespace Core

theorem resolve_intent_calm (core : Core) (now : Nat) (command : Command) (state : PersistedState)
    (result : ((Pending.intent command state).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.intent command state) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_spawn_calm (core : Core) (now : Nat) (generation : UInt64) (plan : CoreLaunch)
    (result : ((Pending.spawn generation plan).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.spawn generation plan) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_adopt_calm (core : Core) (now : Nat) (generation : UInt64) (actual : CoreIdentity) (state : PersistedState)
    (result : ((Pending.adopt generation actual state).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.adopt generation actual state) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_commit_calm (core : Core) (now : Nat) (generation : UInt64) (actual : CoreIdentity) (state : PersistedState) (detail : ControlDetail)
    (result : ((Pending.commit generation actual state detail).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.commit generation actual state detail) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_exitIntent_calm (core : Core) (now : Nat) (state : PersistedState)
    (result : ((Pending.exitIntent state).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.exitIntent state) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_seed_calm (core : Core) (now : Nat) (intended : Desired)
    (result : ((Pending.seed intended).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.seed intended) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_archive_calm (core : Core) (now : Nat) (identity : Identity) (intended : Desired) (stamp : UInt64)
    (result : ((Pending.archive identity intended stamp).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.archive identity intended stamp) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_reopen_calm (core : Core) (now : Nat) (identity : Identity) (intended : Desired) (archive : System.FilePath)
    (result : ((Pending.reopen identity intended archive).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.reopen identity intended archive) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_replacement_calm (core : Core) (now : Nat) (state : PersistedState)
    (result : ((Pending.replacement state).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.replacement state) result).core := by
  cases result <;> unfold_outcome <;> repeat' split
  all_goals calm_leaf

theorem resolve_windUp_calm (core : Core) (now : Nat) (generation : UInt64)
    (result : ((Pending.windUp generation).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.windUp generation) result).core := by
  cases result
  · exact Calm.through (by calm_leaf) (Core.refused_calm _ _ rfl)
  · exact ⟨rfl, fun _ _ waiting => nomatch waiting⟩

theorem resolve_exitMap_calm (core : Core) (now : Nat) (report : ExitReport) (skip : Option Nat)
    (result : ((Pending.exitMap report skip).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.exitMap report skip) result).core := by
  cases result
  · exact Calm.through (by calm_leaf) (Core.exitReported_calm _ _ rfl)
  · exact Calm.through (by calm_leaf) (Core.exitReported_calm _ _ rfl)

theorem resolve_map_calm (core : Core) (now : Nat) (skip : Option Nat)
    (result : ((Pending.map skip).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.map skip) result).core := by
  cases result
  · exact Calm.through (by calm_leaf) (Core.launchCheck_calm _ _ rfl)
  · exact Calm.through (by calm_leaf) (Core.launchCheck_calm _ _ rfl)

theorem resolve_closeMap_calm (core : Core) (now : Nat) (skip : Option Nat)
    (result : ((Pending.closeMap skip).call core.lifecycle).Result) :
    Calm core ({ core with pending := none }.resolve now (.closeMap skip) result).core := by
  cases result
  · exact Calm.through (by calm_leaf) (Core.closed_calm _ rfl)
  · exact Calm.through (by calm_leaf) (Core.closed_calm _ rfl)

/-- **Only a launch write's outcome reserves a generation or makes the state wait to spawn.**
Every other outcome leaves the allocator unchanged and the state not waiting to spawn. -/
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
    | replacement => exact core.resolve_replacement_calm _ _ _
  exact ⟨calm.generation, calm.quiet⟩

end Core

end Acorn.Host.Viewer
