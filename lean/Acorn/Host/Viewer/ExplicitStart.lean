/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Supervision

/-!
# A spawn follows an explicit start

The viewer's supervisor starts its child, the core or the command `--cmd` names, in one place:
the actor's `Call.spawn`. The actor makes a call only as the call of the pending operation its
state waits on, after it has performed the effects of the step that produced that state; so it
makes `Call.spawn` only when the state waits on `Pending.spawn`, and it makes it then if it
reaches that call. This module proves, of the step the actor runs (`Core.start`, `Core.step`,
`Core.resume`), that a supervisor started from a durable state that intends to stay stopped
admits no reservation and waits neither on a spawn nor on a write of a running intent, in
every state reached by events that hold no operator's Start
(`Reached.stopped_spawns_nothing`). It also proves that the statement is not empty: from the
start on every durable state that admits a launch, there are events that hold a Start and a
state reached by them that waits to spawn (`Core.start_spawns`). That is a statement of
existence. Its witness is a Start and one tick with every call between them succeeding; a
Start whose intent cannot be written is another continuation, and it reaches no spawn.

**One supervisor's lifetime.** `Reached` relates an origin, the events handed to the step and a
state. Its constructors are one start, a step on an event and the outcome of a pending call: it
ends with that viewer, and nothing in it reads a state file or starts a second viewer. The
states reached from a start are exactly the states of `Ran` (`Reached.ran`, `Ran.reached`),
which every `Supervision` carries. What holds across viewers, a restart of the viewer after a
crash included, is argued from these theorems under assumptions that are named where the
argument is made, and is not proved.

**The child.** The theorems speak of the one process the supervisor starts. The viewer starts
two other processes outside the supervisor, and neither is a learner: under `--control-stdin`
a relay of its standard input (`/bin/cat`, `Acorn.Host.StopFlag.withCommands`), and under
`--open-browser` the system's opener for the page's address.

**The state built when no state file exists** is `PersistedState.unstarted`, which intends to
stay stopped, so the theorem holds of the supervisor started from it
(`Reached.unstarted_spawns_nothing`), and the control record of the start on that state says
the run is desired stopped and actually stopped (`Core.start_control`; the start on a restored
running state has another desired word).

**Every state file a viewer can meet.** With no state file the bootstrap builds
`PersistedState.unstarted`, and the run is stopped. A file is decoded only when it is a JSON
object that holds the six members of the state, each admitted, and beside them at most a
`schema_version` and a `child`: a seed and an agent epoch spelled as unsigned 64-bit
integers, a run identity of sixteen hexadecimal digits, an intent, an origin and the process
flag. For a file that is decoded, two things decide whether
the intent it records is kept.

The first is its version. A `schema_version` member that is absent, as in every file the
viewer wrote before the file carried one, or that is not a number spelled in decimal digits
alone, marks an earlier version's file. The rule is about spelling: a string, `null`, and a
number spelled with a sign, a fraction or an exponent, such as `3e0`, are all read as no
readable version. Every state the decoder returns for a file whose version does not read as
the current one intends to stay stopped (`PersistedState.decode_earlier`), so the theorem
holds of a supervisor started from a state decoded from such a file
(`Reached.earlier_spawns_nothing`). For a file whose member spells another natural number in
decimal digits the decoder returns an error (`PersistedState.decode_other`), and so it does
for digits that spell a number of `2 ^ 64` or more (`PersistedState.decode_wide`).

The second is its child. A viewer writes, with every state it saves, the record of the child its
supervisor would start (`childRecord`): the executable's path, its length in bytes, the 64-bit
FNV-1a digest of every byte of the file (`fileDigest`), and the argument vector at a reference
launch. A launch that has no such record, as under `--cmd`, writes none. The decoder returns a
running intent only for a file that names the current schema and the record of the launch that
reads it, which must have one (`PersistedState.decode_running`); every state it returns to a
launch with no record, or with another record than the file names, intends to stay stopped
(`PersistedState.decode_unbound`), and the theorem holds of a supervisor started from such a
state (`Reached.unbound_spawns_nothing`). So a running intent saved while the supervisor's
child was one process is not taken as a Start for another. Sameness is equality of the two
records, and no more. Before the ranked core is started, the first time and at every restart,
the actor reads the executable's file again, by the action the bootstrap read it with, and
compares its length and digest (`ProgramReading`) with what the viewer read when it started,
whether or not the state file can hold the record (`ChildProgram`). It does so once
(`Supervisor.call`), before the launch is recorded: a refusal there writes nothing and spawns
nothing, so the saved state is exactly as it was, not marked as having started a process and
with its agent epoch unspent, and the step, given the write's error, stops the run. No
process could have been created on that path. After a launch is recorded the actor spawns
with no further reading, so no refusal of this kind follows the record. The reason
(`childDiffers`, `childUnreadable`, `childUnread`) is reported in the page and printed on
standard error. A fixed command is
written and spawned with no reading: a Start under `--cmd` is an explicit act for that command
line as given, and it covers the restarts of the command by the viewer that received the
Start, whatever program the command designates when each restart is made, so a program
replaced under that command line between a Start and a restart is run by the restart. That is
an accepted limit of the guarantee, beside the three of the ranked core's record, of which
three things are assumed and not compared: the interval between that reading and the
operating system starting the program, in which the launch is recorded, so that a file
replaced in that interval is started;
that the environment the child inherits has not changed; and that two files of equal length
and equal digest are one. The digest suffices against accident, a rebuilt file that agrees in
length and in a 64-bit digest by chance; forging it needs no more power than writing the state
file by hand, which is not defended against either.

A file that names `stateSchema` and this launch's child is restored with the intent it
records. A running one resumes if its launch is admitted (`PersistedState.launch`: among its
conditions, a run that has started a process needs a next agent epoch within the browser's
integers) and the writes and the spawn that follow succeed. By the write clause of the
theorem, a supervisor waits on the write of a running intent only after a Start was handed to
its step, or from a start state that held one.

**What is read, not proved.** The actor hands `Event.command .start` only for a Start that
`Supervisor.submit` queued, and `Supervisor.submit` is called for the `--start` flag and for an
admitted control request. The bootstrap passes the state it built or read to
`Supervision.start`, and constructs no supervisor for a state file it refuses. Every state the
actor writes goes through `RunDirectory.writeState` with the record of its own configuration's
child. `RunDirectory.readState` refuses a state file that is unreadable or malformed, refuses
without opening it an entry that is not a regular file or a link to one, such as a link whose
target is gone, a directory, a pipe or a device, and reads only a run directory with no entry
under the state file's name as no file; on a refusal the viewer exits before it serves
anything and leaves the file as it is, because a file another version wrote is not guessed at
and reading it as stopped would publish over it. A state built with no file, or restored with
its intent, is published before the listener binds; a file whose running intent was set aside
(an earlier version's, or one given for another child) is left exactly as it is until the
listener is bound. The bootstrap then prints and flushes the line that says why the run is
shown stopped (`startAccount`), under `--start` as well, and only then publishes the stopped
state it started from, with this launch's record, before it prints the ready line, before
`--start` submits its Start and before any command is processed (`StartSource.kept`,
`Supervisor.new`, `NativeApp.runViewer`); if the line cannot be written or flushed, the viewer
exits before the publication and the file is still the original. For any other stopped start
state the line is printed after the ready line and not under `--start`. So a
start-up that fails before that publication leaves the next viewer the same file and the same
reason, and the file is read as an earlier version's, or as given for another child, once: in
the first launch that publishes the stopped state, whose first control record and log already
hold the reason. A start-up that fails after the
publication, when the ready line cannot be written for example, leaves a current-version
stopped file, and the reason the next launch gives is that the saved state says stopped. A
Start queued on the control endpoint between the bind and the publication is processed by a
later step if the start-up goes on, and is lost with the viewer if the start-up fails after
the publication: a viewer that fails once its listener is bound ends through its shutdown,
whose turns step the supervisor to close it and can write the map, and none of them takes a
command from the queue. That a running intent in a state file follows a
Start given, in some earlier viewer, while its child had the record the file names is argued
from the write clause and these readings by induction over the viewers that owned the run
directory, assuming that only viewers write the file, that the other fields of a state read
back as written, and that a running intent reads back as running exactly for a launch with
the same, present record: a running intent written under `--cmd`, which has no record, reads
back stopped, by design. No theorem covers these: the actor
(`Acorn.Host.Viewer.Supervisor`), the reader and the bootstrap (`NativeApp.Viewer`) are
effects.

**What the theorem does not cover.** It starts from a durable state that intends to stay
stopped. A Stop the viewer has acknowledged but not yet written to its state file when the
viewer crashes, or whose write failed, leaves a running intent on disk, set by the earlier
Start; the next viewer with the same child resumes it. Holding the acknowledgement of a Stop
until it is written would close that window and is a change to the control interface. Nor does
the theorem say who may submit a Start: the viewer serves its page on the loopback interface
to whoever loads it. And it says nothing of permission: that a Start was given is a property
of the program, separate from the owner's authorization for a run of a learner.
-/
namespace Acorn.Host.Viewer

/-- The intent of every command but Start is stopped: `Command.desired` computes it, and whether
it is saved is the step's (a disabled Clear changes nothing). -/
theorem Command.desired_stopped (command : Command) (other : command ≠ .start) :
    command.desired = .stopped := by
  cases command with
  | start => exact absurd rfl other
  | stop => rfl
  | clear => rfl

/-- A pending operation that carries no running intent and starts no process: neither a launch
nor a spawn, no Start's intent, and no state or Clear intent that says running. -/
def Pending.Unstarted : Pending → Prop
  | .intent command state => command ≠ .start ∧ state.desired = .stopped
  | .launch _ _ | .spawn _ _ => False
  | .adopt _ _ state | .commit _ _ state _ | .exitIntent state | .replacement state =>
    state.desired = .stopped
  | .seed intended | .archive _ intended _ | .reopen _ intended _ => intended = .stopped
  | .windUp _ | .exitMap _ _ | .map _ | .closeMap _ => True

/-- Every intent the supervisor holds is to stay stopped: the lifecycle's, the durable state's,
a waiting replacement's and the pending operation's. -/
structure Core.Unstarted (core : Core) : Prop where
  /-- The lifecycle intends to stop and no Clear restores a running intent. -/
  lifecycle : core.lifecycle.Unstarted
  /-- The durable state intends to stop. -/
  persisted : core.persisted.desired = .stopped
  /-- A replacement that waits to be published intends to stop. -/
  replacement : ∀ state, core.replacement = some state → state.desired = .stopped
  /-- The pending operation carries no running intent and starts no process. -/
  pending : ∀ pending, core.pending = some pending → pending.Unstarted

namespace Core

private theorem Unstarted.same {core next : Core} (unstarted : core.Unstarted)
    (lifecycle : next.lifecycle = core.lifecycle) (persisted : next.persisted = core.persisted)
    (replacement : next.replacement = core.replacement)
    (pending : next.pending = core.pending) : next.Unstarted :=
  ⟨lifecycle ▸ unstarted.lifecycle, persisted ▸ unstarted.persisted,
    replacement ▸ unstarted.replacement, pending ▸ unstarted.pending⟩

private theorem Unstarted.waiting {core next : Core} {operation : Pending}
    (unstarted : core.Unstarted) (lifecycle : next.lifecycle = core.lifecycle)
    (persisted : next.persisted = core.persisted)
    (replacement : next.replacement = core.replacement)
    (pending : next.pending = some operation) (admitted : operation.Unstarted) :
    next.Unstarted :=
  ⟨lifecycle ▸ unstarted.lifecycle, persisted ▸ unstarted.persisted,
    replacement ▸ unstarted.replacement, fun held waits => by
      rw [pending] at waits
      cases waits
      exact admitted⟩

private theorem Unstarted.moved {core : Core} {lifecycle : Lifecycle}
    (unstarted : core.Unstarted) (stays : lifecycle.Unstarted) :
    (core.moveTo lifecycle).Unstarted :=
  ⟨stays, unstarted.persisted, unstarted.replacement, fun held waits => by
    rw [moveTo_pending, Option.map_eq_some_iff] at waits
    obtain ⟨generation, -, rfl⟩ := waits
    exact True.intro⟩

private theorem Unstarted.stopped {core : Core} (unstarted : core.Unstarted) :
    core.stop.Unstarted :=
  unstarted.moved (core.lifecycle.request_unstarted .stop (by decide) unstarted.lifecycle)

private theorem Unstarted.reported {core : Core} (unstarted : core.Unstarted)
    (transition : ControlTransition) (reason : String) :
    (core.report transition reason).Unstarted :=
  unstarted.same rfl rfl rfl rfl

/-! ## Each transition keeps every intent stopped -/

theorem command_unstarted (core : Core) (clearDisabled : Option String) (command : Command)
    (other : command ≠ .start) (unstarted : core.Unstarted) :
    (core.command clearDisabled command).core.Unstarted := by
  have stopped := command.desired_stopped other
  unfold Core.command
  split
  · exact unstarted
  · split
    · split
      · exact unstarted.reported _ _
      · exact ⟨unstarted.lifecycle, unstarted.persisted,
          fun state held => by cases held; exact stopped, unstarted.pending⟩
    · split
      · exact unstarted.stopped.reported _ _
      · exact unstarted.waiting rfl rfl rfl rfl ⟨other, stopped⟩

theorem candidate_unstarted (core : Core) (generation : UInt64) (actual : CoreIdentity)
    (unstarted : core.Unstarted) : (core.candidate generation actual).core.Unstarted := by
  unfold Core.candidate
  split
  · exact unstarted
  · split
    · exact unstarted.stopped.reported _ _
    · split
      · exact unstarted.stopped.reported _ _
      · exact unstarted.waiting rfl rfl rfl rfl unstarted.persisted

theorem exited_unstarted (core : Core) (now : Nat) (code : UInt32) (uptime : Nat)
    (unstarted : core.Unstarted) : (core.exited now code uptime).core.Unstarted := by
  unfold Core.exited
  split
  · rename_i generation _
    refine ⟨Lifecycle.retire_unstarted _ generation ?_, unstarted.persisted,
      unstarted.replacement, unstarted.pending⟩
    split
    · exact unstarted.lifecycle
    · exact Lifecycle.failed_unstarted _ _ _ _ unstarted.lifecycle
  all_goals exact unstarted

theorem closed_unstarted (core : Core) (unstarted : core.Unstarted) :
    core.closed.core.Unstarted := by
  unfold Core.closed
  split
  · exact unstarted.same rfl rfl rfl rfl
  all_goals exact unstarted

theorem closeOut_unstarted (core : Core) (unstarted : core.Unstarted) :
    core.closeOut.core.Unstarted := by
  unfold Core.closeOut
  split
  · exact unstarted.waiting rfl rfl rfl rfl True.intro
  · exact core.closed_unstarted unstarted

theorem exitReported_unstarted (core : Core) (report : ExitReport)
    (unstarted : core.Unstarted) : (core.exitReported report).core.Unstarted := by
  have base : (({ core with detail := report.detail, failure := report.failure }).report
      report.transition report.reason).Unstarted := unstarted.same rfl rfl rfl rfl
  have stopped := core.lifecycle.unstarted_desired unstarted.lifecycle
  simp only [Core.exitReported]
  repeat' split
  all_goals first
    | exact base.reported _ _
    | exact base.waiting (operation := .exitIntent _) rfl rfl rfl rfl stopped

theorem finished_unstarted (core : Core) (stdout : OutputStatus) (stderr : PipeResult)
    (log : LogStatus) (unstarted : core.Unstarted) :
    (core.finished stdout stderr log).core.Unstarted := by
  have emptied : ({ core with slot := .empty } : Core).Unstarted := unstarted.same rfl rfl rfl rfl
  simp only [Core.finished]
  repeat' split
  all_goals first
    | exact unstarted
    | exact unstarted.same rfl rfl rfl rfl
    | exact emptied.waiting (operation := .exitMap _ _) rfl rfl rfl rfl True.intro
    | exact Core.exitReported_unstarted _ _ emptied

theorem refused_unstarted (core : Core) (reason : String) (unstarted : core.Unstarted) :
    (core.refused reason).core.Unstarted := by
  unfold Core.refused
  split
  all_goals first
    | exact unstarted
    | exact unstarted.same rfl rfl rfl rfl

/-- **An unstarted supervisor launches nothing.** For every state whose intents are all to
stay stopped and every instant, the launch check leaves the state as it is, with no change and
nothing to follow. -/
theorem launchCheck_unstarted (core : Core) (now : Nat) (unstarted : core.Unstarted) :
    core.launchCheck now = ⟨core, [], []⟩ := by
  simp [Core.launchCheck, core.lifecycle.unstarted_reserve unstarted.lifecycle]

theorem mapOrLaunch_unstarted (core : Core) (now : Nat) (unstarted : core.Unstarted) :
    (core.mapOrLaunch now).core.Unstarted := by
  unfold Core.mapOrLaunch
  split
  · exact unstarted.waiting (operation := .map _) rfl rfl rfl rfl True.intro
  · rw [core.launchCheck_unstarted now unstarted]
    exact unstarted

theorem clear_unstarted (core : Core) (intended : Desired) (stopped : intended = .stopped)
    (unstarted : core.Unstarted) : (core.clear intended).core.Unstarted := by
  unfold Core.clear
  repeat' split
  all_goals first
    | exact unstarted
    | exact unstarted.stopped.reported _ _
    | exact unstarted.waiting (operation := .seed _) rfl rfl rfl rfl stopped

theorem tick_unstarted (core : Core) (now : Nat) (unstarted : core.Unstarted) :
    (core.tick now).core.Unstarted := by
  unfold Core.tick
  repeat' split
  all_goals first
    | exact unstarted
    | exact core.mapOrLaunch_unstarted now unstarted
    | exact core.closeOut_unstarted unstarted
    | exact unstarted.waiting (operation := .replacement _) rfl rfl rfl rfl
        (unstarted.replacement _ (by assumption))
    | exact core.clear_unstarted _
        (core.lifecycle.unstarted_archiveIntent unstarted.lifecycle _ (by assumption)) unstarted

theorem close_unstarted (core : Core) (unstarted : core.Unstarted) :
    core.close.core.Unstarted := by
  have base : (({ core with closing := .closing core.failure.isSome } : Core).stop.report
      .stopRequested "viewer closing; finishing the current attempt and checkpoint").Unstarted :=
    (Unstarted.stopped (unstarted.same
      (next := { core with closing := .closing core.failure.isSome }) rfl rfl rfl rfl)).reported
      _ _
  simp only [Core.close]
  repeat' split
  all_goals first
    | exact unstarted
    | exact base
    | exact Core.closeOut_unstarted _ base

theorem seeded_unstarted (core : Core) (now : Nat) (intended : Desired) (seed : UInt64)
    (stopped : intended = .stopped) (unstarted : core.Unstarted) :
    (core.seeded now intended seed).core.Unstarted := by
  simp only [Core.seeded]
  repeat' split
  all_goals first
    | exact unstarted
    | exact unstarted.stopped.reported _ _
    | exact ⟨Lifecycle.beginArchive_unstarted _ _ (by assumption) unstarted.lifecycle,
        unstarted.persisted, unstarted.replacement, fun held waits => by cases waits; exact stopped⟩

theorem replaced_unstarted (core : Core) (state : PersistedState)
    (stopped : state.desired = .stopped) (unstarted : core.Unstarted) :
    (core.replaced state).core.Unstarted := by
  have queued : (core.lifecycle.replacementIntent state.desired).Unstarted := by
    rw [stopped]
    exact core.lifecycle.replacementIntent_unstarted unstarted.lifecycle
  simp only [Core.replaced]
  split
  · exact ⟨Lifecycle.archived_unstarted _ _ _ (by assumption) queued, stopped,
      fun _ held => (nomatch held), unstarted.pending⟩
  · exact ⟨queued, unstarted.persisted, unstarted.replacement, unstarted.pending⟩

theorem resolve_unstarted (core : Core) (now : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result) (unstarted : core.Unstarted)
    (admitted : pending.Unstarted) : (core.resolve now pending result).core.Unstarted := by
  cases pending with
  | launch state plan => exact admitted.elim
  | spawn generation plan => exact admitted.elim
  | intent command state =>
    have saved : ({ core with persisted := state } : Core).Unstarted :=
      ⟨unstarted.lifecycle, admitted.2, unstarted.replacement, unstarted.pending⟩
    have moved := (saved.moved
      (core.lifecycle.request_unstarted command admitted.1 unstarted.lifecycle))
    cases result with
    | error reason => exact unstarted.stopped.reported _ _
    | ok =>
      cases command with
      | start => exact absurd rfl admitted.1
      | stop => exact moved.reported _ _
      | clear => exact moved.reported _ _
  | windUp generation =>
    cases result with
    | error reason => exact core.refused_unstarted reason unstarted
    | ok => exact unstarted
  | adopt generation actual state =>
    cases result with
    | error reason => exact unstarted.stopped.reported _ _
    | ok => exact unstarted.waiting (operation := .commit _ _ _ _) rfl rfl rfl rfl admitted
  | commit generation actual state detail =>
    have saved : ({ core with persisted := state } : Core).Unstarted :=
      ⟨unstarted.lifecycle, admitted, unstarted.replacement, unstarted.pending⟩
    cases result with
    | error reason => exact saved.stopped.reported _ _
    | ok dropped =>
      have installed : ({ core with
          persisted := state, detail
          lifecycle := core.lifecycle.adoptFinalIdentity generation actual.identity } :
          Core).Unstarted :=
        ⟨Lifecycle.adoptFinalIdentity_unstarted _ _ _ unstarted.lifecycle, admitted,
          unstarted.replacement, unstarted.pending⟩
      simp only [Core.resolve, Core.committed]
      split
      · exact installed.reported _ _
      · exact installed
  | exitMap report skip =>
    cases result with
    | error reason => exact Core.exitReported_unstarted _ _ unstarted
    | ok revision =>
      exact Core.exitReported_unstarted _ _ (unstarted.same rfl rfl rfl rfl)
  | exitIntent state =>
    cases result with
    | error reason => exact unstarted.reported _ _
    | ok => exact ⟨unstarted.lifecycle, admitted, unstarted.replacement, unstarted.pending⟩
  | map skip =>
    cases result with
    | error reason =>
      show ((core.report _ _).launchCheck now).core.Unstarted
      rw [Core.launchCheck_unstarted _ now (unstarted.reported _ _)]
      exact unstarted.reported _ _
    | ok revision =>
      have kept : ({ core with mapRevision := revision.or core.mapRevision } : Core).Unstarted :=
        unstarted.same rfl rfl rfl rfl
      show (({ core with mapRevision := revision.or core.mapRevision } : Core).launchCheck
        now).core.Unstarted
      rw [Core.launchCheck_unstarted _ now kept]
      exact kept
  | closeMap skip =>
    cases result with
    | error reason => exact Core.closed_unstarted _ (unstarted.reported _ _)
    | ok revision => exact Core.closed_unstarted _ (unstarted.same rfl rfl rfl rfl)
  | seed intended =>
    cases result with
    | error reason => exact unstarted.stopped.reported _ _
    | ok seed => exact core.seeded_unstarted now intended seed admitted unstarted
  | archive identity intended stamp =>
    have failed : ({ core with lifecycle := core.lifecycle.archiveFailed } : Core).Unstarted :=
      ⟨Lifecycle.archiveFailed_unstarted _ unstarted.lifecycle, unstarted.persisted,
        unstarted.replacement, unstarted.pending⟩
    cases result with
    | unchanged reason => exact failed.reported _ _
    | moved archive reason => exact failed.same rfl rfl rfl rfl
    | ready archive =>
      exact unstarted.waiting (operation := .reopen _ _ _) rfl rfl rfl rfl admitted
  | reopen identity intended archive =>
    cases result with
    | error reason => exact unstarted.same rfl rfl rfl rfl
    | ok =>
      exact ⟨unstarted.lifecycle, unstarted.persisted,
        fun state held => by cases held; exact admitted,
        fun waiting held => by cases held; exact admitted⟩
  | replacement state =>
    cases result with
    | error reason => exact unstarted.reported _ _
    | ok => exact core.replaced_unstarted state admitted unstarted

theorem start_unstarted (persisted : PersistedState) (clearDisabled : Option String)
    (reason : String) (reading : Nat) (stopped : persisted.desired = .stopped) :
    (Core.start persisted clearDisabled reason reading).Unstarted := by
  refine ⟨?_, stopped, fun _ held => (nomatch held), fun _ held => (nomatch held)⟩
  show (Lifecycle.initial persisted.identity persisted.desired).Unstarted
  rw [stopped]
  exact Lifecycle.initial_unstarted _

theorem dispatch_unstarted (core : Core) (clearDisabled : Option String) (now : Nat)
    (event : Event) (other : event ≠ .command .start) (unstarted : core.Unstarted) :
    (core.dispatch clearDisabled now event).core.Unstarted := by
  unfold Core.dispatch
  split
  · exact unstarted
  · split <;> first
      | exact unstarted
      | exact core.command_unstarted clearDisabled _
          (fun same => other (congrArg Event.command same)) unstarted
      | exact core.candidate_unstarted _ _ unstarted
      | exact core.exited_unstarted now _ _ unstarted
      | exact core.finished_unstarted _ _ _ unstarted
      | exact core.refused_unstarted _ unstarted
      | exact core.tick_unstarted now unstarted
      | exact core.close_unstarted unstarted

/-- **A step on any event but an operator's Start keeps every intent stopped.** For every state
whose intents are all to stay stopped, every Clear configuration and every reading. -/
theorem step_unstarted (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (other : event ≠ .command .start) (unstarted : core.Unstarted) :
    (core.step clearDisabled reading event).core.Unstarted :=
  (core.dispatch_unstarted clearDisabled (core.instant reading) event other unstarted).same
    rfl rfl rfl rfl

/-- **Every outcome of the pending call keeps every intent stopped.** For every state whose
intents are all to stay stopped, the operation it waits for and every reading. -/
theorem resume_unstarted (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result) (unstarted : core.Unstarted)
    (waiting : core.pending = some pending) :
    (core.resume reading pending result).core.Unstarted :=
  (Core.resolve_unstarted { core with pending := none } (core.instant reading) pending result
    ⟨unstarted.lifecycle, unstarted.persisted, unstarted.replacement,
      fun _ held => (nomatch held)⟩ (unstarted.pending pending waiting)).same rfl rfl rfl rfl

/-- **An unstarted supervisor starts no process and writes no running intent.** For every
state whose intents are all to stay stopped: the lifecycle admits no reservation at any
instant and intends to stop, and the call the state waits for, if any, is no spawn and writes
no state that intends to run. -/
theorem Unstarted.spawns_nothing {core : Core} (unstarted : core.Unstarted) :
    (∀ now, core.lifecycle.reserve now = none) ∧ core.lifecycle.desiredValue = .stopped ∧
      ∀ pending, core.pending = some pending →
        (∀ generation plan, pending.call core.lifecycle ≠ .spawn generation plan) ∧
          ∀ state, pending.call core.lifecycle = .writeState state →
            state.desired = .stopped := by
  refine ⟨core.lifecycle.unstarted_reserve unstarted.lifecycle,
    core.lifecycle.unstarted_desired unstarted.lifecycle, fun pending waiting => ?_⟩
  have admitted := unstarted.pending pending waiting
  cases pending <;> simp_all [Pending.call, Pending.Unstarted]

end Core

/-! ## Runs -/

/-- A state reached from an origin by steps on events and by outcomes of pending calls, with
the events handed to the step, the most recent first. -/
inductive Reached (clearDisabled : Option String) (origin : Core) : List Event → Core → Prop where
  /-- The origin, before any event. -/
  | origin : Reached clearDisabled origin [] origin
  /-- A step on an event. -/
  | step {events : List Event} {core : Core} (reached : Reached clearDisabled origin events core)
      (reading : Nat) (event : Event) :
      Reached clearDisabled origin (event :: events) (core.step clearDisabled reading event).core
  /-- The outcome of the call the state waits for. -/
  | resume {events : List Event} {core : Core} {pending : Pending}
      (reached : Reached clearDisabled origin events core)
      (waiting : core.pending = some pending) (reading : Nat)
      (result : (pending.call core.lifecycle).Result) :
      Reached clearDisabled origin events (core.resume reading pending result).core

/-- **The states reached from a start are states of a run.** -/
theorem Reached.ran {clearDisabled : Option String} {persisted : PersistedState}
    {reason : String} {reading : Nat} {events : List Event} {core : Core}
    (reached : Reached clearDisabled (Core.start persisted clearDisabled reason reading)
      events core) : Ran clearDisabled core := by
  induction reached with
  | origin => exact .start persisted reason reading
  | step _ reading event hold => exact hold.step reading event
  | resume _ waiting reading result hold => exact hold.resume waiting reading result

/-- **Every state of a run is reached from a start by some events.** -/
theorem Ran.reached {clearDisabled : Option String} {core : Core}
    (ran : Ran clearDisabled core) :
    ∃ persisted reason reading events,
      Reached clearDisabled (Core.start persisted clearDisabled reason reading) events core := by
  induction ran with
  | start persisted reason reading => exact ⟨persisted, reason, reading, [], .origin⟩
  | step _ reading event hold =>
    obtain ⟨persisted, reason, first, events, reached⟩ := hold
    exact ⟨persisted, reason, first, event :: events, reached.step reading event⟩
  | resume _ waiting reading result hold =>
    obtain ⟨persisted, reason, first, events, reached⟩ := hold
    exact ⟨persisted, reason, first, events, reached.resume waiting reading result⟩

/-- **No Start, no running intent.** For every Clear configuration, every origin whose intents
are all to stay stopped, and every state reached from it by events that hold no operator's
Start: the state's intents are all to stay stopped. -/
theorem Reached.unstarted {clearDisabled : Option String} {origin core : Core}
    {events : List Event} (reached : Reached clearDisabled origin events core)
    (unstarted : origin.Unstarted) (startless : Event.command .start ∉ events) :
    core.Unstarted := by
  induction reached with
  | origin => exact unstarted
  | step _ reading event hold =>
    exact Core.step_unstarted _ _ reading event
      (fun same => startless (same ▸ List.mem_cons_self))
      (hold fun inside => startless (List.mem_cons_of_mem _ inside))
  | resume _ waiting reading result hold =>
    exact Core.resume_unstarted _ reading _ result (hold startless) waiting

/-- **A supervisor started from a stopped intent waits on no spawn while no Start is handed to
its step.** For
every Clear configuration, every durable state that intends to stay stopped, every reason and
reading the viewer starts with, every sequence of events that holds no operator's Start, and
every state reached by it from that start: the lifecycle admits no reservation at any instant
and intends to stop, and the call the state waits for, if any, is no spawn and writes no state
that intends to run. -/
theorem Reached.stopped_spawns_nothing {clearDisabled : Option String}
    {persisted : PersistedState} {reason : String} {reading : Nat} {events : List Event}
    {core : Core} (stopped : persisted.desired = .stopped)
    (reached : Reached clearDisabled (Core.start persisted clearDisabled reason reading)
      events core) (startless : Event.command .start ∉ events) :
    (∀ now, core.lifecycle.reserve now = none) ∧ core.lifecycle.desiredValue = .stopped ∧
      ∀ pending, core.pending = some pending →
        (∀ generation plan, pending.call core.lifecycle ≠ .spawn generation plan) ∧
          ∀ state, pending.call core.lifecycle = .writeState state →
            state.desired = .stopped :=
  (reached.unstarted (Core.start_unstarted persisted clearDisabled reason reading stopped)
    startless).spawns_nothing

/-- **A supervisor started from the state built with no state file waits on no spawn while no
Start is handed to its step.** The
statement of `Reached.stopped_spawns_nothing` for the state the bootstrap builds when the run
directory holds no state file, for every seed and whether or not a stray checkpoint was
adopted. -/
theorem Reached.unstarted_spawns_nothing {clearDisabled : Option String} {seed : UInt64}
    {migrated : Bool} {reason : String} {reading : Nat} {events : List Event} {core : Core}
    (reached : Reached clearDisabled
      (Core.start (PersistedState.unstarted seed migrated) clearDisabled reason reading)
      events core) (startless : Event.command .start ∉ events) :
    (∀ now, core.lifecycle.reserve now = none) ∧ core.lifecycle.desiredValue = .stopped ∧
      ∀ pending, core.pending = some pending →
        (∀ generation plan, pending.call core.lifecycle ≠ .spawn generation plan) ∧
          ∀ state, pending.call core.lifecycle = .writeState state →
            state.desired = .stopped :=
  Reached.stopped_spawns_nothing rfl reached startless

/-- **A supervisor started from an earlier version's state file waits on no spawn while no
Start is handed to its step.** The statement of `Reached.stopped_spawns_nothing` for every
state that `PersistedState.decode` returns for a JSON value whose `schema_version` member is
absent, is not a number spelled in decimal digits alone or spells a number other than
`stateSchema`. -/
theorem Reached.earlier_spawns_nothing {clearDisabled : Option String}
    {child : Option (List String)} {value : Json.Value}
    {persisted : PersistedState} {reason : String} {reading : Nat} {events : List Event}
    {core : Core} (earlier : stateVersion value ≠ some stateSchema)
    (decoded : PersistedState.decode child value = .ok persisted)
    (reached : Reached clearDisabled (Core.start persisted clearDisabled reason reading)
      events core) (startless : Event.command .start ∉ events) :
    (∀ now, core.lifecycle.reserve now = none) ∧ core.lifecycle.desiredValue = .stopped ∧
      ∀ pending, core.pending = some pending →
        (∀ generation plan, pending.call core.lifecycle ≠ .spawn generation plan) ∧
          ∀ state, pending.call core.lifecycle = .writeState state →
            state.desired = .stopped :=
  Reached.stopped_spawns_nothing
    (PersistedState.decode_earlier child value persisted earlier decoded) reached startless

/-- **A supervisor started from a state file that does not name its launch's child waits on no
spawn while no Start is handed to its step.** The statement of
`Reached.stopped_spawns_nothing` for every state that `PersistedState.decode` returns to a
launch that has no child record, or whose record differs from the one the JSON value's `child`
member names, or that reads a value with no such record. -/
theorem Reached.unbound_spawns_nothing {clearDisabled : Option String}
    {child : Option (List String)} {value : Json.Value}
    {persisted : PersistedState} {reason : String} {reading : Nat} {events : List Event}
    {core : Core} (unbound : child = none ∨ stateChild value ≠ child)
    (decoded : PersistedState.decode child value = .ok persisted)
    (reached : Reached clearDisabled (Core.start persisted clearDisabled reason reading)
      events core) (startless : Event.command .start ∉ events) :
    (∀ now, core.lifecycle.reserve now = none) ∧ core.lifecycle.desiredValue = .stopped ∧
      ∀ pending, core.pending = some pending →
        (∀ generation plan, pending.call core.lifecycle ≠ .spawn generation plan) ∧
          ∀ state, pending.call core.lifecycle = .writeState state →
            state.desired = .stopped :=
  Reached.stopped_spawns_nothing
    (PersistedState.decode_unbound child value persisted unbound decoded) reached startless

/-- **The control record of a start with no state file says the run is stopped.** For every
seed, whether or not a stray checkpoint was adopted, and every Clear configuration, reason,
reading and observation: in the control record of the start state, the desired word and the
actual word are both `stopped`. -/
theorem Core.start_control (seed : UInt64) (migrated : Bool) (clearDisabled : Option String)
    (reason : String) (reading : Nat) (observed : ControlObservation) :
    let core := Core.start (PersistedState.unstarted seed migrated) clearDisabled reason reading
    (controlTelemetry core.lifecycle observed core.detail)[1]? =
        some ⟨"desired", .text, "stopped"⟩ ∧
      (controlTelemetry core.lifecycle observed core.detail)[2]? =
        some ⟨"actual", .text, "stopped"⟩ :=
  ⟨rfl, rfl⟩

/-! ## After a Start, a spawn can be reached

The theorems above would hold of a supervisor that never spawned. This section shows that the
supervisor they are about can: from the same start state, there is a run that holds a Start
and reaches a state that waits to spawn. -/

namespace Core

/-- A serving state with no process, no replacement and its run directory, whose lifecycle has
no Clear to go on with and reserves its first generation at every instant, and whose durable
state admits the launch `plan`. -/
private structure Poised (core : Core) (plan : CoreLaunch) : Prop where
  closing : core.closing = .open
  replacement : core.replacement = none
  slot : core.slot = .empty
  owner : core.owner = .current
  clearless : core.lifecycle.archiveIntent = none
  reserves : ∀ now, ∃ next, core.lifecycle.reserve now = some (1, next)
  admitted : core.persisted.launch = .ok plan

private theorem Poised.launchCheck {core : Core} {plan : CoreLaunch} (poised : Poised core plan)
    (now : Nat) :
    core.launchCheck now = ⟨{ core with
      pending := some (.launch { core.persisted with processStarted := true } plan) }, [], []⟩ := by
  obtain ⟨next, reserved⟩ := poised.reserves (clockWord now)
  simp [Core.launchCheck, poised.replacement, poised.slot, poised.closing, poised.owner, reserved,
    poised.admitted]

private theorem Poised.tick {core : Core} {plan : CoreLaunch} (poised : Poised core plan)
    (ready : core.pending = none) (clearDisabled : Option String) (reading : Nat) :
    ((core.step clearDisabled reading .tick).core.pending =
        some (.launch { core.persisted with processStarted := true } plan) ∧
      (core.step clearDisabled reading .tick).core.lifecycle = core.lifecycle) ∨
    ∃ skip, (core.step clearDisabled reading .tick).core.pending = some (.map skip) ∧
      Poised (core.step clearDisabled reading .tick).core plan := by
  have stepped : (core.step clearDisabled reading .tick).core =
      ((core.mapOrLaunch (core.instant reading)).at (core.instant reading)).core := by
    simp [Core.step, Core.dispatch, Core.tick, ready, poised.closing, poised.replacement,
      poised.clearless]
  rw [stepped]
  unfold Core.mapOrLaunch
  split
  · exact .inr ⟨core.mapRevision, rfl, poised.closing, poised.replacement, poised.slot,
      poised.owner, poised.clearless, poised.reserves, poised.admitted⟩
  · rw [poised.launchCheck]
    exact .inl ⟨rfl, rfl⟩

private theorem Poised.mapped {core : Core} {plan : CoreLaunch} (poised : Poised core plan)
    (reading : Nat) (skip : Option Nat) :
    (core.resume reading (.map skip) (Except.ok none : Except String (Option Nat))).core.pending =
        some (.launch { core.persisted with processStarted := true } plan) ∧
      (core.resume reading (.map skip)
        (Except.ok none : Except String (Option Nat))).core.lifecycle = core.lifecycle := by
  have inner : Poised ({ core with
      pending := none, mapRevision := (none : Option Nat).or core.mapRevision } : Core) plan :=
    ⟨poised.closing, poised.replacement, poised.slot, poised.owner, poised.clearless,
      poised.reserves, poised.admitted⟩
  have checked := inner.launchCheck (core.instant reading)
  exact ⟨congrArg (fun stepped : Stepped => (stepped.at (core.instant reading)).core.pending)
      checked,
    congrArg (fun stepped : Stepped => (stepped.at (core.instant reading)).core.lifecycle)
      checked⟩

private theorem resume_spawns (core : Core) (reading : Nat) (state : PersistedState)
    (plan : CoreLaunch)
    (reserves : ∀ now, ∃ next, core.lifecycle.reserve now = some (1, next)) :
    (core.resume reading (.launch state plan) (Except.ok () : Except String Unit)).core.pending =
      some (.spawn 1 plan) := by
  obtain ⟨next, reserved⟩ := reserves (clockWord (core.instant reading))
  simp [Core.resume, Core.resolve, Stepped.at, reserved]

/-- **After a Start, some continuation waits to spawn.** For every Clear configuration, every
durable state that admits a launch, and every reason and reading the viewer starts with: there
are events that hold an operator's Start, and a state reached by them from that start state,
that waits to spawn the first generation with the launch the durable state admits. The proof's
witness is the Start and one tick, with every call between them succeeding. It is a statement
of existence: a Start whose intent cannot be written is another continuation and reaches no
spawn. -/
theorem start_spawns (persisted : PersistedState) (clearDisabled : Option String)
    (reason : String) (reading : Nat) (plan : CoreLaunch)
    (admitted : persisted.launch = .ok plan) :
    ∃ events core,
      Reached clearDisabled (Core.start persisted clearDisabled reason reading) events core ∧
        Event.command .start ∈ events ∧ core.pending = some (.spawn 1 plan) := by
  let origin := Core.start persisted clearDisabled reason reading
  let saved : PersistedState := { persisted with desired := .running }
  let asked := (origin.step clearDisabled reading (.command .start)).core
  have waiting : asked.pending = some (.intent .start saved) := rfl
  let started :=
    (asked.resume reading (.intent .start saved) (Except.ok () : Except String Unit)).core
  have first : Reached clearDisabled origin [.command .start] started :=
    (Reached.origin.step reading (.command .start)).resume waiting reading _
  have ready : started.pending = none := rfl
  have poised : Poised started plan :=
    ⟨rfl, rfl, rfl, rfl,
      Lifecycle.clearless_archiveIntent _
        (Lifecycle.request_clearless _ .start (by decide) (Lifecycle.initial_clearless _ _)),
      fun now => Lifecycle.start_reserves persisted.identity persisted.desired now, admitted⟩
  rcases poised.tick ready clearDisabled reading with ⟨launching, same⟩ | ⟨skip, mapping, again⟩
  · refine ⟨[.tick, .command .start], _,
      (first.step reading .tick).resume launching reading (Except.ok () : Except String Unit),
      by simp, ?_⟩
    exact resume_spawns _ reading _ plan (by rw [same]; exact poised.reserves)
  · have ⟨launching, same⟩ := again.mapped reading skip
    refine ⟨[.tick, .command .start], _,
      ((first.step reading .tick).resume mapping reading
        (Except.ok none : Except String (Option Nat))).resume launching reading
        (Except.ok () : Except String Unit),
      by simp, ?_⟩
    exact resume_spawns _ reading _ plan (by rw [same]; exact again.reserves)

/-- **The state built when no state file exists admits a launch.** For every seed within the
browser's integers and whether or not a stray checkpoint was adopted. The seeds the bootstrap
uses are within them: a drawn seed is below `2 ^ 48` (`viewerSeed_bound`) and the seed beside an
adopted checkpoint is 42. With `Core.start_spawns`: from the start on that state there are
events that hold a Start and reach a state that waits to spawn. -/
theorem unstarted_launch (seed : UInt64) (migrated : Bool)
    (safe : seed.toNat ≤ browserIntegerMax) :
    ∃ plan, (PersistedState.unstarted seed migrated).launch = .ok plan := by
  have zero : (0 : UInt64).toNat = 0 := rfl
  have within : seed.toNat ≤ 9007199254740991 := safe
  cases migrated <;>
    simp [PersistedState.launch, PersistedState.unstarted, Identity.browserSafe, within, zero,
      browserIntegerMax, pure, Except.pure]

end Core

end Acorn.Host.Viewer
