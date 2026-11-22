import Acorn.Host.Viewer.Supervision

namespace Acorn.Host.Viewer

theorem Command.desired_stopped (command : Command) (other : command ≠ .start) :
    command.desired = .stopped := by
  cases command with
  | start => exact absurd rfl other
  | stop => rfl
  | clear => rfl

def Pending.Unstarted : Pending → Prop
  | .intent command state => command ≠ .start ∧ state.desired = .stopped
  | .launch _ _ | .spawn _ _ => False
  | .adopt _ _ state | .commit _ _ state _ | .exitIntent state | .replacement state =>
    state.desired = .stopped
  | .seed intended | .archive _ intended _ | .reopen _ intended _ => intended = .stopped
  | .windUp _ | .exitMap _ _ | .map _ | .closeMap _ => True

structure Core.Unstarted (core : Core) : Prop where
  lifecycle : core.lifecycle.Unstarted
  persisted : core.persisted.desired = .stopped
  replacement : ∀ state, core.replacement = some state → state.desired = .stopped
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

theorem step_unstarted (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (other : event ≠ .command .start) (unstarted : core.Unstarted) :
    (core.step clearDisabled reading event).core.Unstarted :=
  (core.dispatch_unstarted clearDisabled (core.instant reading) event other unstarted).same
    rfl rfl rfl rfl

theorem resume_unstarted (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result) (unstarted : core.Unstarted)
    (waiting : core.pending = some pending) :
    (core.resume reading pending result).core.Unstarted :=
  (Core.resolve_unstarted { core with pending := none } (core.instant reading) pending result
    ⟨unstarted.lifecycle, unstarted.persisted, unstarted.replacement,
      fun _ held => (nomatch held)⟩ (unstarted.pending pending waiting)).same rfl rfl rfl rfl

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

inductive Reached (clearDisabled : Option String) (origin : Core) : List Event → Core → Prop where
  | origin : Reached clearDisabled origin [] origin
  | step {events : List Event} {core : Core} (reached : Reached clearDisabled origin events core)
      (reading : Nat) (event : Event) :
      Reached clearDisabled origin (event :: events) (core.step clearDisabled reading event).core
  | resume {events : List Event} {core : Core} {pending : Pending}
      (reached : Reached clearDisabled origin events core)
      (waiting : core.pending = some pending) (reading : Nat)
      (result : (pending.call core.lifecycle).Result) :
      Reached clearDisabled origin events (core.resume reading pending result).core

theorem Reached.ran {clearDisabled : Option String} {persisted : PersistedState}
    {reason : String} {reading : Nat} {events : List Event} {core : Core}
    (reached : Reached clearDisabled (Core.start persisted clearDisabled reason reading)
      events core) : Ran clearDisabled core := by
  induction reached with
  | origin => exact .start persisted reason reading
  | step _ reading event hold => exact hold.step reading event
  | resume _ waiting reading result hold => exact hold.resume waiting reading result

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

theorem Core.start_control (seed : UInt64) (migrated : Bool) (clearDisabled : Option String)
    (reason : String) (reading : Nat) (observed : ControlObservation) :
    let core := Core.start (PersistedState.unstarted seed migrated) clearDisabled reason reading
    (controlTelemetry core.lifecycle observed core.detail)[1]? =
        some ⟨"desired", .text, "stopped"⟩ ∧
      (controlTelemetry core.lifecycle observed core.detail)[2]? =
        some ⟨"actual", .text, "stopped"⟩ :=
  ⟨rfl, rfl⟩

namespace Core

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
