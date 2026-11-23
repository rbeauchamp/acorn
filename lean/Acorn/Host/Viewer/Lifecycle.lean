/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Control
import Acorn.Host.Viewer.Buffer
import Acorn.Host.Viewer.Retry

/-!
# Viewer process ownership

A process generation is distinct from durable run identity. Retirement revokes
its output capability before archive or replacement. The native shell must
serialize the pure transition and the associated observer write under one
mutex. OS process termination and filesystem rename are reported effects, not
conclusions of these pure definitions.
-/
namespace Acorn.Host.Viewer

/-- The only requests available to an observer's operator. -/
inductive Command where
  /-- Request a process for the current durable run. -/
  | start
  /-- Request wind-up at the next attempt boundary. -/
  | stop
  /-- Request retirement followed by whole-directory archival. -/
  | clear
  deriving DecidableEq, BEq

/-- Unknown control words cannot select a lifecycle action. -/
def Command.parse : String → Option Command
  | "start" => some .start
  | "stop" => some .stop
  | "clear" => some .clear
  | _ => none

/-- The specification of the spelling of a lifecycle command, written with no executed
function: a text spells a command when it is that command's one word. -/
def Command.Spelled (text : String) (command : Command) : Prop :=
  (text = "start" ∧ command = .start) ∨ (text = "stop" ∧ command = .stop) ∨
    (text = "clear" ∧ command = .clear)

/-- **The control-word parser accepts exactly the spelled commands.** For every text and
command, the parser returns the command exactly when the text spells it. -/
theorem Command.parse_spelled (text : String) (command : Command) :
    Command.parse text = some command ↔ Command.Spelled text command := by
  unfold Command.parse Command.Spelled
  split <;> cases command <;> simp_all

/-- Durable world and logical agent identity; process restarts have separate generations. -/
structure Identity where
  /-- Opaque durable run identifier. -/
  run : UInt64
  /-- World generation seed. -/
  seed : UInt64
  /-- Durable logical agent identity within a run. -/
  agentEpoch : UInt64
  deriving DecidableEq, BEq

/-- Operator intent persists across process failure. -/
inductive Desired where
  /-- Maintain a process subject to the failure limit. -/
  | running
  /-- Leave the process stopped. -/
  | stopped
  deriving DecidableEq, BEq

/-- A live generation exists only while a process can supply accepted output. -/
inductive Phase where
  /-- No process owns observation writes. -/
  | idle
  /-- A reserved generation is awaiting a spawn result. -/
  | starting (generation : UInt64)
  /-- The current process owns writes. -/
  | running (generation : UInt64)
  /-- The current process may finish its attempt and emit its final records. -/
  | stopping (generation : UInt64)
  /-- All process observation capabilities have been revoked. -/
  | archiving
  deriving DecidableEq, BEq

/-- Only an installed live process can admit output. -/
def Phase.accepts (phase : Phase) (generation : UInt64) : Bool :=
  match phase with
  | .running current | .stopping current => current == generation
  | .idle | .starting _ | .archiving => false

/-- The comparison with the idle phase is equality with it. -/
theorem Phase.beq_idle (phase : Phase) : (phase == .idle) = true ↔ phase = .idle := by
  cases phase with
  | idle => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | starting _ | running _ | stopping _ | archiving =>
    exact ⟨fun same => (nomatch same), fun same => (nomatch same)⟩

/-- The comparison with the archiving phase is equality with it. -/
theorem Phase.beq_archiving (phase : Phase) :
    (phase == .archiving) = true ↔ phase = .archiving := by
  cases phase with
  | archiving => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | idle | starting _ | running _ | stopping _ =>
    exact ⟨fun same => (nomatch same), fun same => (nomatch same)⟩

/-- Complete process intent, generation allocator and durable identity state. -/
structure Lifecycle where
  private mk ::
  /-- Durable identity changes only after successful archive/new-directory admission. -/
  private identity : Identity
  /-- Current native lifecycle boundary. -/
  private phase : Phase := .idle
  /-- Operator intent. -/
  private desired : Desired := .stopped
  /-- Last reserved generation; exhaustion refuses further spawns instead of wrapping. -/
  private lastGeneration : UInt64 := 0
  /-- Clear waits for retirement before any filesystem effect. -/
  private clearPending : Option Desired := none
  /-- Failure budget and elapsed backoff are enforced before each reservation. -/
  private retry : Retry := .initial
  /-- An exhausted restart budget leaves the operator's intent stopped, so no lifecycle
  value holds an exhausted budget while it intends to run. -/
  private exhaustedStopped : retry.exhausted = true → desired = .stopped

/-- Native startup has no live process or inherited generation capability. -/
def Lifecycle.initial (identity : Identity) (desired : Desired) : Lifecycle :=
  { identity, desired, exhaustedStopped := fun exhausted =>
      absurd exhausted (by simp [Retry.initial_not_exhausted]) }

/-- Read-only durable identity for publication and frame admission. -/
def Lifecycle.identityValue (state : Lifecycle) : Identity := state.identity

/-- Read-only process phase; callers cannot write allocator or phase fields. -/
def Lifecycle.phaseValue (state : Lifecycle) : Phase := state.phase

/-- Read-only current operator intent. -/
def Lifecycle.desiredValue (state : Lifecycle) : Desired := state.desired

/-- Read-only last reserved generation. -/
def Lifecycle.lastGenerationValue (state : Lifecycle) : UInt64 := state.lastGeneration

/-- Read-only intent that a pending Clear restores after archival. -/
def Lifecycle.clearPendingValue (state : Lifecycle) : Option Desired := state.clearPending

/-- Whether the restart budget is exhausted. -/
def Lifecycle.exhausted (state : Lifecycle) : Bool := state.retry.exhausted

/-- **An exhausted restart budget leaves the run stopped.** Every lifecycle value carries it,
so no transition can intend to run on a budget the failure limit has used up. -/
theorem Lifecycle.exhausted_stopped (state : Lifecycle) (exhausted : state.exhausted = true) :
    state.desiredValue = .stopped :=
  state.exhaustedStopped exhausted

/-- Read-only consecutive-failure count for control telemetry. -/
def Lifecycle.failureCount (state : Lifecycle) : Nat := state.retry.count

/-- Exhaustion is exactly a failure count of three, for every lifecycle value. -/
theorem Lifecycle.exhausted_iff (state : Lifecycle) :
    state.exhausted = true ↔ state.failureCount = 3 := by
  simp [exhausted, failureCount, Retry.exhausted, Retry.count, failureLimit]

/-- Clear's retained post-archive intent is visible only after process retirement. -/
def Lifecycle.archiveIntent (state : Lifecycle) : Option Desired :=
  if state.phase == .idle then state.clearPending else none

/-- A queued operator change during replacement publication changes only its
post-archive intent; it cannot leave the archival phase or admit a process. -/
def Lifecycle.replacementIntent (state : Lifecycle) (desired : Desired) : Lifecycle :=
  if state.phase == .archiving then { state with clearPending := some desired } else state

/-- Pure command handling never starts a second process or archives a live one. -/
def Lifecycle.request (state : Lifecycle) (command : Command) : Lifecycle :=
  match command with
  | .start =>
    { state with
      desired := .running, clearPending := none, retry := .initial
      exhaustedStopped := fun exhausted =>
        absurd exhausted (by simp [Retry.initial_not_exhausted]) }
  | .stop =>
    { state with
      desired := .stopped, clearPending := none, exhaustedStopped := fun _ => rfl
      phase := match state.phase with
        | .running generation => .stopping generation
        | phase => phase }
  | .clear =>
    { state with
      desired := .stopped, clearPending := state.clearPending.or (some state.desired)
      exhaustedStopped := fun _ => rfl
      phase := match state.phase with
        | .running generation => .stopping generation
        | phase => phase }

/-- A spawn is reserved only from idle state, without generation reuse or overlap. -/
def Lifecycle.reserve (state : Lifecycle) (now : UInt64) : Option (UInt64 × Lifecycle) :=
  if state.phase == .idle && state.desired == .running && state.clearPending.isNone &&
      state.lastGeneration != 18446744073709551615 && state.retry.ready now then
    let generation := state.lastGeneration + 1
    some (generation, { state with phase := .starting generation, lastGeneration := generation })
  else none

/-- A spawn result installs only its own still-reserved generation. -/
def Lifecycle.started (state : Lifecycle) (generation : UInt64) : Lifecycle :=
  if state.phase == .starting generation then
    { state with phase := if state.desired == .stopped || state.clearPending.isSome then
        .stopping generation else .running generation }
  else state

/-- Only a failed spawn or unexpectedly exited running process consumes the restart budget. -/
def Lifecycle.acceptsFailure (state : Lifecycle) (generation : UInt64) : Bool :=
  state.phase == .starting generation || state.phase == .running generation

/-- Failure retirement and the next reservation policy update are one transition. -/
def Lifecycle.failed (state : Lifecycle) (generation now : UInt64) (healthy : Bool) : Lifecycle :=
  if state.acceptsFailure generation then
    let retry := state.retry.failed now healthy
    { state with
      phase := .idle, retry
      desired := if retry.exhausted then .stopped else state.desired
      exhaustedStopped := fun exhausted => by simp [exhausted] }
  else state

/-- Reaping revokes observation rights before any later filesystem action. -/
def Lifecycle.retire (state : Lifecycle) (generation : UInt64) : Lifecycle :=
  if state.phase.accepts generation || state.phase == .starting generation then
    { state with phase := .idle }
  else state

/-- Only an idle owner with pending Clear may enter archival. -/
def Lifecycle.beginArchive (state : Lifecycle) : Option Lifecycle :=
  if state.phase == .idle && state.clearPending.isSome then
    some { state with phase := .archiving }
  else none

/-- Install fresh identity only after the IO owner reports completed archival and creation.
Distinct run identity is an admission condition, never inferred from a timestamp. -/
def Lifecycle.archived (state : Lifecycle) (identity : Identity) : Option Lifecycle :=
  if state.phase == .archiving && identity.run != state.identity.run then
    some { state with
      identity := identity
      phase := .idle
      desired := state.clearPending.getD state.desired
      clearPending := none
      retry := .initial
      exhaustedStopped := fun exhausted =>
        absurd exhausted (by simp [Retry.initial_not_exhausted]) }
  else none

/-- Failed archival leaves the old identity installed and disables automatic restart. -/
def Lifecycle.archiveFailed (state : Lifecycle) : Lifecycle :=
  if state.phase == .archiving then
    { state with
      phase := .idle, desired := .stopped, clearPending := none
      exhaustedStopped := fun _ => rfl }
  else state

/-- The last reserved generation retains identity attribution while its readers
drain in idle phase. This does not confer observation-forwarding rights. -/
def Lifecycle.ownsIdentity (state : Lifecycle) (generation : UInt64) : Bool :=
  state.phase.accepts generation || (state.phase == .idle && state.lastGeneration == generation)

/-- The generations that own identity attribution, stated on the stored phase and the
generation allocator: the generation of a live process, or the last reserved generation while
no process is live. -/
def Lifecycle.OwnsIdentity (state : Lifecycle) (generation : UInt64) : Prop :=
  state.phase = .running generation ∨ state.phase = .stopping generation ∨
    (state.phase = .idle ∧ state.lastGeneration = generation)

/-- The identity test accepts exactly the generations that own identity attribution. -/
theorem Lifecycle.ownsIdentity_iff (state : Lifecycle) (generation : UInt64) :
    state.ownsIdentity generation = true ↔ state.OwnsIdentity generation := by
  unfold ownsIdentity OwnsIdentity
  cases state.phase with
  | idle =>
    have idle : (Phase.idle == Phase.idle) = true := rfl
    simp [Phase.accepts, idle]
  | starting current =>
    have live : (Phase.starting current == Phase.idle) = false := rfl
    simp [Phase.accepts, live]
  | running current =>
    have live : (Phase.running current == Phase.idle) = false := rfl
    simp [Phase.accepts, live]
  | stopping current =>
    have live : (Phase.stopping current == Phase.idle) = false := rfl
    simp [Phase.accepts, live]
  | archiving =>
    have closed : (Phase.archiving == Phase.idle) = false := rfl
    simp [Phase.accepts, closed]

/-- Final pipe drain may complete identity attribution before any subsequent
reservation or archive. Frame forwarding remains governed by `Phase.accepts`. -/
def Lifecycle.adoptFinalIdentity (state : Lifecycle) (generation : UInt64) (identity : Identity) : Lifecycle :=
  if state.ownsIdentity generation then { state with identity } else state

/-- Final identity attribution cannot resurrect observation rights. -/
theorem Lifecycle.finalIdentity_phase (state : Lifecycle) (generation : UInt64) (identity : Identity) :
    (state.adoptFinalIdentity generation identity).phase = state.phase := by
  simp [adoptFinalIdentity]; split <;> rfl

/-- The retiring generation can no longer write, regardless of its prior phase. -/
theorem Lifecycle.retire_revokes (state : Lifecycle) (generation : UInt64) :
    (state.retire generation).phase.accepts generation = false := by
  simp only [retire]
  split
  · rfl
  · rename_i h
    cases phase : state.phase <;> simp_all [Phase.accepts]

/-- Operator commands preserve durable identity. -/
theorem Lifecycle.request_identity (state : Lifecycle) (command : Command) :
    (state.request command).identity = state.identity := by cases command <;> rfl

/-- Repeated Clear preserves the original post-archive intent and pending retirement. -/
theorem Lifecycle.clear_idempotent (state : Lifecycle) :
    (state.request .clear).request .clear = state.request .clear := by
  rcases state with ⟨identity, phase, desired, generation, pending, retry, sound⟩
  cases phase <;> cases pending <;> rfl

/-- A successfully started process retains the durable run identity. -/
theorem Lifecycle.started_identity (state : Lifecycle) (generation : UInt64) :
    (state.started generation).identity = state.identity := by
  simp [started]; split <;> rfl

/-- An archiving owner accepts no generation, including an old buffered tail. -/
theorem Phase.archiving_rejects (generation : UInt64) :
    Phase.archiving.accepts generation = false := rfl

/-- Whether the restart budget admits a launch at this instant. -/
def Lifecycle.retryReady (state : Lifecycle) (now : UInt64) : Bool := state.retry.ready now

/-! ## The generation allocator

Only a reservation moves the allocator, and it moves it up by one. -/

theorem Lifecycle.request_lastGeneration (state : Lifecycle) (command : Command) :
    (state.request command).lastGenerationValue = state.lastGenerationValue := by
  cases command <;> rfl

theorem Lifecycle.started_lastGeneration (state : Lifecycle) (generation : UInt64) :
    (state.started generation).lastGenerationValue = state.lastGenerationValue := by
  unfold started lastGenerationValue; split <;> rfl

theorem Lifecycle.failed_lastGeneration (state : Lifecycle) (generation now : UInt64)
    (healthy : Bool) :
    (state.failed generation now healthy).lastGenerationValue = state.lastGenerationValue := by
  unfold failed lastGenerationValue; split <;> rfl

theorem Lifecycle.retire_lastGeneration (state : Lifecycle) (generation : UInt64) :
    (state.retire generation).lastGenerationValue = state.lastGenerationValue := by
  unfold retire lastGenerationValue; split <;> rfl

theorem Lifecycle.archiveFailed_lastGeneration (state : Lifecycle) :
    state.archiveFailed.lastGenerationValue = state.lastGenerationValue := by
  unfold archiveFailed lastGenerationValue; split <;> rfl

theorem Lifecycle.replacementIntent_lastGeneration (state : Lifecycle) (desired : Desired) :
    (state.replacementIntent desired).lastGenerationValue = state.lastGenerationValue := by
  unfold replacementIntent lastGenerationValue; split <;> rfl

theorem Lifecycle.adoptFinalIdentity_lastGeneration (state : Lifecycle) (generation : UInt64)
    (identity : Identity) :
    (state.adoptFinalIdentity generation identity).lastGenerationValue =
      state.lastGenerationValue := by
  unfold adoptFinalIdentity lastGenerationValue; split <;> rfl

theorem Lifecycle.beginArchive_lastGeneration (state next : Lifecycle)
    (begun : state.beginArchive = some next) :
    next.lastGenerationValue = state.lastGenerationValue := by
  unfold beginArchive at begun
  split at begun
  · cases begun; rfl
  · cases begun

theorem Lifecycle.archived_lastGeneration (state next : Lifecycle) (identity : Identity)
    (installed : state.archived identity = some next) :
    next.lastGenerationValue = state.lastGenerationValue := by
  unfold archived at installed
  split at installed
  · cases installed; rfl
  · cases installed

/-- **A reservation takes the next generation of an idle lifecycle that intends to run, has no
Clear pending and whose restart budget admits a launch now.** The generation it returns is
one more than the last, as natural numbers, so no generation is reserved twice, and the
lifecycle it returns is starting that generation. -/
theorem Lifecycle.reserve_some (state next : Lifecycle) (now generation : UInt64)
    (reserved : state.reserve now = some (generation, next)) :
    state.phaseValue = .idle ∧ state.desiredValue = .running ∧ state.clearPendingValue = none ∧
      state.retryReady now = true ∧
      generation.toNat = state.lastGenerationValue.toNat + 1 ∧
      next.lastGenerationValue = generation ∧ next.phaseValue = .starting generation ∧
      next.desiredValue = state.desiredValue ∧ next.clearPendingValue = state.clearPendingValue := by
  unfold reserve at reserved
  split at reserved
  · rename_i admitted
    simp only [Option.some.injEq, Prod.mk.injEq] at reserved
    obtain ⟨rfl, rfl⟩ := reserved
    simp only [Bool.and_eq_true] at admitted
    obtain ⟨⟨⟨⟨idle, running⟩, pending⟩, notLast⟩, ready⟩ := admitted
    have idle : state.phase = .idle := (Phase.beq_idle _).mp idle
    have running : state.desired = .running := by
      revert running; cases state.desired <;> intro running <;> first | rfl | nomatch running
    have pending : state.clearPending = none := Option.isNone_iff_eq_none.mp pending
    have notLast : state.lastGeneration ≠ 18446744073709551615 := by simpa using notLast
    have below : state.lastGeneration.toNat < 18446744073709551615 := by
      have bound := state.lastGeneration.toNat_lt_size
      have differs : state.lastGeneration.toNat ≠ 18446744073709551615 := fun same =>
        notLast (UInt64.toNat_inj.mp (by simpa using same))
      change state.lastGeneration.toNat < 18446744073709551616 at bound
      omega
    refine ⟨idle, running, pending, ready, ?_, rfl, rfl, rfl, rfl⟩
    simp only [lastGenerationValue, UInt64.toNat_add, UInt64.toNat_one]
    change (state.lastGeneration.toNat + 1) % 18446744073709551616 = _
    omega
  · cases reserved

/-- A queued intent revision keeps the installed identity. -/
theorem Lifecycle.replacementIntent_identity (state : Lifecycle) (desired : Desired) :
    (state.replacementIntent desired).identityValue = state.identityValue := by
  unfold replacementIntent identityValue; split <;> rfl

/-- An installed replacement holds its identity, whose run differs from the run it replaced. -/
theorem Lifecycle.archived_identity (state next : Lifecycle) (identity : Identity)
    (installed : state.archived identity = some next) :
    next.identityValue = identity ∧ identity.run ≠ state.identityValue.run := by
  unfold archived at installed
  split at installed
  · rename_i admitted
    cases installed
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at admitted
    exact ⟨rfl, admitted.2⟩
  · cases installed

/-! ## Clear's absence

A lifecycle with no Clear pending and not archiving keeps both under every transition except a
Clear request, and offers no archival. -/

/-- No Clear is pending and no archival is under way. -/
def Lifecycle.Clearless (state : Lifecycle) : Prop :=
  state.clearPending = none ∧ state.phase ≠ .archiving

theorem Lifecycle.ite_clearless (condition : Prop) [Decidable condition] (left right : Lifecycle) :
    (if condition then left else right).Clearless ↔
      (condition → left.Clearless) ∧ (¬condition → right.Clearless) := by
  by_cases holds : condition <;> simp [holds]

theorem Lifecycle.initial_clearless (identity : Identity) (desired : Desired) :
    (Lifecycle.initial identity desired).Clearless :=
  ⟨rfl, nofun⟩

theorem Lifecycle.request_clearless (state : Lifecycle) (command : Command)
    (notClear : command ≠ .clear) (clearless : state.Clearless) :
    (state.request command).Clearless := by
  obtain ⟨none, notArchiving⟩ := clearless
  cases command with
  | clear => exact absurd rfl notClear
  | start => exact ⟨rfl, notArchiving⟩
  | stop =>
    refine ⟨rfl, ?_⟩
    show (match state.phase with
      | .running generation => Phase.stopping generation
      | phase => phase) ≠ .archiving
    split <;> simp_all

theorem Lifecycle.reserve_clearless (state next : Lifecycle) (now generation : UInt64)
    (reserved : state.reserve now = some (generation, next)) (clearless : state.Clearless) :
    next.Clearless := by
  unfold reserve at reserved
  split at reserved
  · simp only [Option.some.injEq, Prod.mk.injEq] at reserved
    obtain ⟨rfl, rfl⟩ := reserved
    exact ⟨clearless.1, nofun⟩
  · cases reserved

theorem Lifecycle.started_clearless (state : Lifecycle) (generation : UInt64)
    (clearless : state.Clearless) : (state.started generation).Clearless := by
  unfold started
  split
  · refine ⟨clearless.1, ?_⟩
    show (if state.desired == .stopped || state.clearPending.isSome then
      Phase.stopping generation else .running generation) ≠ .archiving
    split <;> nofun
  · exact clearless

theorem Lifecycle.failed_clearless (state : Lifecycle) (generation now : UInt64)
    (healthy : Bool) (clearless : state.Clearless) :
    (state.failed generation now healthy).Clearless := by
  unfold failed
  split
  · exact ⟨clearless.1, nofun⟩
  · exact clearless

theorem Lifecycle.retire_clearless (state : Lifecycle) (generation : UInt64)
    (clearless : state.Clearless) : (state.retire generation).Clearless := by
  unfold retire
  split
  · exact ⟨clearless.1, nofun⟩
  · exact clearless

theorem Lifecycle.archiveFailed_clearless (state : Lifecycle) (clearless : state.Clearless) :
    state.archiveFailed.Clearless := by
  unfold archiveFailed
  split
  · exact ⟨rfl, nofun⟩
  · exact clearless

theorem Lifecycle.replacementIntent_clearless (state : Lifecycle) (desired : Desired)
    (clearless : state.Clearless) : (state.replacementIntent desired).Clearless := by
  unfold replacementIntent
  split
  · rename_i archiving
    exact absurd ((Phase.beq_archiving _).mp archiving) clearless.2
  · exact clearless

theorem Lifecycle.adoptFinalIdentity_clearless (state : Lifecycle) (generation : UInt64)
    (identity : Identity) (clearless : state.Clearless) :
    (state.adoptFinalIdentity generation identity).Clearless := by
  unfold adoptFinalIdentity
  split
  · exact clearless
  · exact clearless

theorem Lifecycle.clearless_archiveIntent (state : Lifecycle) (clearless : state.Clearless) :
    state.archiveIntent = none := by
  unfold archiveIntent
  split
  · exact clearless.1
  · rfl

theorem Lifecycle.clearless_beginArchive (state : Lifecycle) (clearless : state.Clearless) :
    state.beginArchive = none := by
  unfold beginArchive
  simp [clearless.1]

theorem Lifecycle.clearless_archived (state : Lifecycle) (identity : Identity)
    (clearless : state.Clearless) : state.archived identity = none := by
  unfold archived
  have notArchiving : (state.phase == .archiving) = false :=
    Bool.eq_false_iff.mpr fun same => clearless.2 ((Phase.beq_archiving _).mp same)
  simp [notArchiving]

/-- A Stop or Clear request moves a running generation to stopping. -/
theorem Lifecycle.request_stopping (state : Lifecycle) (command : Command)
    (generation : UInt64) (stopping : command ≠ .start)
    (running : state.phaseValue = .running generation) :
    (state.request command).phaseValue = .stopping generation := by
  unfold phaseValue at running
  cases command with
  | start => exact absurd rfl stopping
  | stop =>
    show (match state.phase with
      | .running generation => Phase.stopping generation
      | phase => phase) = _
    rw [running]
  | clear =>
    show (match state.phase with
      | .running generation => Phase.stopping generation
      | phase => phase) = _
    rw [running]

def Lifecycle.Unstarted (state : Lifecycle) : Prop :=
  state.desired = .stopped ∧ state.clearPending ≠ some .running

theorem Lifecycle.initial_unstarted (identity : Identity) :
    (Lifecycle.initial identity .stopped).Unstarted :=
  ⟨rfl, nofun⟩

theorem Lifecycle.unstarted_desired (state : Lifecycle) (unstarted : state.Unstarted) :
    state.desiredValue = .stopped :=
  unstarted.1

theorem Lifecycle.unstarted_reserve (state : Lifecycle) (unstarted : state.Unstarted)
    (now : UInt64) : state.reserve now = none := by
  have stopped : (state.desired == .running) = false := by rw [unstarted.1]; rfl
  simp [reserve, stopped]

theorem Lifecycle.unstarted_archiveIntent (state : Lifecycle) (unstarted : state.Unstarted)
    (intended : Desired) (pending : state.archiveIntent = some intended) :
    intended = .stopped := by
  unfold archiveIntent at pending
  split at pending
  · cases intended with
    | stopped => rfl
    | running => exact absurd pending unstarted.2
  · cases pending

theorem Lifecycle.request_unstarted (state : Lifecycle) (command : Command)
    (other : command ≠ .start) (unstarted : state.Unstarted) :
    (state.request command).Unstarted := by
  cases command with
  | start => exact absurd rfl other
  | stop => exact ⟨rfl, nofun⟩
  | clear =>
    refine ⟨rfl, ?_⟩
    show state.clearPending.or (some state.desired) ≠ some .running
    rw [unstarted.1]
    cases held : state.clearPending with
    | none => exact nofun
    | some intent =>
      cases intent with
      | stopped => exact nofun
      | running => exact absurd held unstarted.2

theorem Lifecycle.failed_unstarted (state : Lifecycle) (generation now : UInt64)
    (healthy : Bool) (unstarted : state.Unstarted) :
    (state.failed generation now healthy).Unstarted := by
  unfold failed
  split
  · refine ⟨?_, unstarted.2⟩
    show (if (state.retry.failed now healthy).exhausted then Desired.stopped else state.desired) =
      .stopped
    split
    · rfl
    · exact unstarted.1
  · exact unstarted

theorem Lifecycle.retire_unstarted (state : Lifecycle) (generation : UInt64)
    (unstarted : state.Unstarted) : (state.retire generation).Unstarted := by
  unfold retire
  split
  · exact unstarted
  · exact unstarted

theorem Lifecycle.archiveFailed_unstarted (state : Lifecycle) (unstarted : state.Unstarted) :
    state.archiveFailed.Unstarted := by
  unfold archiveFailed
  split
  · exact ⟨rfl, nofun⟩
  · exact unstarted

theorem Lifecycle.adoptFinalIdentity_unstarted (state : Lifecycle) (generation : UInt64)
    (identity : Identity) (unstarted : state.Unstarted) :
    (state.adoptFinalIdentity generation identity).Unstarted := by
  unfold adoptFinalIdentity
  split
  · exact unstarted
  · exact unstarted

theorem Lifecycle.beginArchive_unstarted (state next : Lifecycle)
    (begun : state.beginArchive = some next) (unstarted : state.Unstarted) : next.Unstarted := by
  unfold beginArchive at begun
  split at begun
  · cases begun; exact unstarted
  · cases begun

theorem Lifecycle.replacementIntent_unstarted (state : Lifecycle) (unstarted : state.Unstarted) :
    (state.replacementIntent .stopped).Unstarted := by
  unfold replacementIntent
  split
  · exact ⟨unstarted.1, nofun⟩
  · exact unstarted

theorem Lifecycle.archived_unstarted (state next : Lifecycle) (identity : Identity)
    (installed : state.archived identity = some next) (unstarted : state.Unstarted) :
    next.Unstarted := by
  unfold archived at installed
  split at installed
  · cases installed
    refine ⟨?_, nofun⟩
    show state.clearPending.getD state.desired = .stopped
    cases held : state.clearPending with
    | none => exact unstarted.1
    | some intent =>
      cases intent with
      | stopped => rfl
      | running => exact absurd held unstarted.2
  · cases installed

theorem Lifecycle.start_reserves (identity : Identity) (desired : Desired) (now : UInt64) :
    ∃ next, ((Lifecycle.initial identity desired).request .start).reserve now =
      some (1, next) := by
  have ready : (Retry.initial.ready now) = true := Retry.initial_ready now
  exact ⟨_, by simp [reserve, request, initial, ready]; exact ⟨⟨rfl, rfl⟩, rfl⟩⟩

def Lifecycle.Archival (state : Lifecycle) : Prop :=
  (state.clearPending.isSome = true → state.desired = .stopped) ∧
    (state.phase = .archiving → state.desired = .stopped)

theorem Lifecycle.initial_archival (identity : Identity) (desired : Desired) :
    (Lifecycle.initial identity desired).Archival :=
  ⟨(fun h => by cases h), (fun h => by cases h)⟩

theorem Lifecycle.request_stop_unstarted (state : Lifecycle) :
    (state.request .stop).Unstarted :=
  ⟨rfl, nofun⟩

theorem Lifecycle.request_archival (state : Lifecycle) (command : Command)
    (hsafe : command = .start → state.phase ≠ .archiving) :
    state.Archival → (state.request command).Archival := by
  intro arch
  cases command with
  | start =>
    refine ⟨(fun h => by cases h), fun hphase => ?_⟩
    have harch : state.phase = .archiving := by
      cases hp : state.phase <;> simp_all [request]
    exact absurd harch (hsafe rfl)
  | stop => exact ⟨(fun h => by cases h), fun _ => rfl⟩
  | clear => exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem Lifecycle.reserve_archival (state : Lifecycle) (now : UInt64)
    (generation : UInt64) (next : Lifecycle)
    (hres : state.reserve now = some (generation, next)) (arch : state.Archival) :
    next.Archival := by
  unfold reserve at hres
  split at hres
  · cases hres
    exact ⟨arch.1, (fun h => by cases h)⟩
  · cases hres

theorem Lifecycle.started_archival (state : Lifecycle) (generation : UInt64)
    (arch : state.Archival) : (state.started generation).Archival := by
  unfold started
  split
  · refine ⟨arch.1, fun h => ?_⟩
    split at h <;> cases h
  · exact arch

theorem Lifecycle.failed_archival (state : Lifecycle) (generation now : UInt64)
    (healthy : Bool) (arch : state.Archival) :
    (state.failed generation now healthy).Archival := by
  unfold failed
  split
  · refine ⟨fun hc => ?_, (fun hp => by cases hp)⟩
    show (if (state.retry.failed now healthy).exhausted then Desired.stopped else state.desired) =
      .stopped
    split
    · rfl
    · exact arch.1 hc
  · exact arch

theorem Lifecycle.retire_archival (state : Lifecycle) (generation : UInt64)
    (arch : state.Archival) : (state.retire generation).Archival := by
  unfold retire
  split
  · exact ⟨arch.1, (fun hp => by cases hp)⟩
  · exact arch

theorem Lifecycle.beginArchive_archival (state next : Lifecycle)
    (hbeg : state.beginArchive = some next) (arch : state.Archival) : next.Archival := by
  unfold beginArchive at hbeg
  split at hbeg
  · rename_i hcond
    cases hbeg
    have hc : state.clearPending.isSome = true := by
      simp only [Bool.and_eq_true] at hcond
      exact hcond.2
    exact ⟨fun _ => arch.1 hc, fun _ => arch.1 hc⟩
  · cases hbeg

theorem Lifecycle.archived_archival (state next : Lifecycle) (identity : Identity)
    (hins : state.archived identity = some next) : next.Archival := by
  unfold archived at hins
  split at hins
  · cases hins
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  · cases hins

theorem Lifecycle.archiveFailed_archival (state : Lifecycle) (arch : state.Archival) :
    state.archiveFailed.Archival := by
  unfold archiveFailed
  split
  · exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  · exact arch

theorem Lifecycle.adoptFinalIdentity_archival (state : Lifecycle) (generation : UInt64)
    (identity : Identity) (arch : state.Archival) :
    (state.adoptFinalIdentity generation identity).Archival := by
  unfold adoptFinalIdentity
  split <;> exact arch

theorem Lifecycle.replacementIntent_archival (state : Lifecycle) (desired : Desired)
    (arch : state.Archival) : (state.replacementIntent desired).Archival := by
  unfold replacementIntent
  split
  · rename_i hph
    have harch : state.phase = .archiving := by
      simpa [Phase.beq_archiving] using hph
    exact ⟨fun _ => arch.2 harch, fun _ => arch.2 harch⟩
  · exact arch

theorem Lifecycle.replacementIntent_stopped_unstarted (state : Lifecycle) (identity : Identity)
    (arch : state.Archival) :
    (∀ next, (state.replacementIntent .stopped).archived identity = some next → next.Unstarted) ∧
      ((state.replacementIntent .stopped).archived identity = none →
        state.phase = .archiving → (state.replacementIntent .stopped).Unstarted) := by
  have helper : state.phase = .archiving → (state.replacementIntent .stopped).Unstarted := by
    intro hph
    unfold replacementIntent
    have hbeq : (state.phase == .archiving) = true := (Phase.beq_archiving state.phase).mpr hph
    rw [hbeq]
    exact ⟨arch.2 hph, nofun⟩
  refine ⟨?_, fun _ hph => helper hph⟩
  intro next hins
  have harch : state.phase = .archiving := by
    unfold archived replacementIntent at hins
    cases hp : (state.phase == .archiving) <;> simp_all [Phase.beq_archiving]
  exact Lifecycle.archived_unstarted (state.replacementIntent .stopped) next identity hins
    (helper harch)

theorem Lifecycle.retire_phase_eq (state : Lifecycle) (generation : UInt64)
    (harch : state.phase = .archiving) : (state.retire generation).phase = .archiving := by
  unfold retire
  split
  · rename_i hbad
    rw [harch] at hbad
    change (Phase.archiving.accepts generation || (Phase.archiving == Phase.starting generation)) = true at hbad
    have hfalse : (Phase.archiving.accepts generation || (Phase.archiving == Phase.starting generation)) = false := rfl
    rw [hfalse] at hbad
    cases hbad
  · exact harch

theorem Lifecycle.failed_phase_ne_archiving (state : Lifecycle) (generation now : UInt64)
    (healthy : Bool) : (state.failed generation now healthy).phase = .archiving ↔ state.phase = .archiving := by
  unfold failed acceptsFailure
  split
  · rename_i hacc
    cases hp : state.phase <;> simp [hp] at hacc ⊢
    have hfalse : ((Phase.archiving == Phase.starting generation) = true ∨ (Phase.archiving == Phase.running generation) = true) → False := by
      intro h; rcases h with h1 | h2
      · cases h1
      · cases h2
    exact False.elim (hfalse hacc)
  · rfl

theorem Lifecycle.request_phase_archiving (state : Lifecycle) (command : Command) :
    (state.request command).phase = .archiving ↔ state.phase = .archiving := by
  cases command <;> cases hp : state.phase <;> simp [request, hp]

theorem Lifecycle.adoptFinalIdentity_phaseValue (state : Lifecycle) (generation : UInt64)
    (identity : Identity) :
    (state.adoptFinalIdentity generation identity).phaseValue = state.phaseValue := by
  exact Lifecycle.finalIdentity_phase state generation identity

theorem Lifecycle.archiveIntent_phase_ne_archiving (state : Lifecycle) (intended : Desired)
    (hint : state.archiveIntent = some intended) : state.phaseValue ≠ .archiving := by
  unfold archiveIntent at hint
  split at hint
  · rename_i hidle
    intro harch
    rw [show state.phase = .archiving from harch] at hidle
    cases hidle
  · cases hint

theorem Lifecycle.replacementIntent_phaseValue (state : Lifecycle) (desired : Desired) :
    (state.replacementIntent desired).phaseValue = state.phaseValue := by
  unfold replacementIntent phaseValue
  split <;> rfl

theorem Lifecycle.reserve_guards (state : Lifecycle) (now generation : UInt64) (next : Lifecycle)
    (hres : state.reserve now = some (generation, next)) :
    state.phaseValue ≠ .archiving ∧ state.clearPendingValue = none ∧ next.phaseValue ≠ .archiving := by
  unfold reserve at hres
  split at hres
  · rename_i hcond
    cases hres
    simp only [Bool.and_eq_true] at hcond
    have hph : state.phase ≠ .archiving := by
      intro harch
      have : (state.phase == .idle) = false := by
        change (state.phase == Phase.idle) = false
        rw [harch]
        rfl
      rw [this] at hcond
      cases hcond.1.1.1.1
    have hcp : state.clearPending = none := by
      cases hnone : state.clearPending with
      | none => rfl
      | some _ =>
        have hfalse : (state.clearPending.isNone) = false := by simp [hnone]
        rw [hfalse] at hcond
        cases hcond.1.1.2
    exact ⟨hph, hcp, fun h => by cases h⟩
  · cases hres

theorem Lifecycle.started_phase_archiving (state : Lifecycle) (generation : UInt64) :
    (state.started generation).phaseValue = .archiving ↔ state.phaseValue = .archiving := by
  unfold started phaseValue
  split
  · rename_i hph
    constructor
    · intro h; split at h <;> cases h
    · intro h
      exfalso
      have : (Phase.archiving == Phase.starting generation) = false := rfl
      change (state.phase == Phase.starting generation) = true at hph
      rw [h, this] at hph
      cases hph
  · rfl

theorem Lifecycle.retire_phaseValue_archiving (state : Lifecycle) (generation : UInt64) :
    (state.retire generation).phaseValue = .archiving ↔ state.phaseValue = .archiving := by
  unfold retire phaseValue
  split
  · rename_i hacc
    constructor
    · intro h; cases h
    · intro h
      exfalso
      change (state.phase.accepts generation || (state.phase == Phase.starting generation)) = true at hacc
      have : (Phase.archiving.accepts generation || (Phase.archiving == Phase.starting generation)) = false := rfl
      rw [h, this] at hacc
      cases hacc
  · rfl

theorem Lifecycle.failed_phaseValue_archiving (state : Lifecycle) (generation now : UInt64)
    (healthy : Bool) :
    (state.failed generation now healthy).phaseValue = .archiving ↔ state.phaseValue = .archiving :=
  Lifecycle.failed_phase_ne_archiving state generation now healthy

theorem Lifecycle.request_phaseValue_archiving (state : Lifecycle) (command : Command) :
    (state.request command).phaseValue = .archiving ↔ state.phaseValue = .archiving :=
  Lifecycle.request_phase_archiving state command

theorem Lifecycle.archived_phase_ne_archiving (state next : Lifecycle) (identity : Identity)
    (hins : state.archived identity = some next) : next.phaseValue ≠ .archiving := by
  unfold archived at hins
  split at hins
  · cases hins; intro h; cases h
  · cases hins

theorem Lifecycle.archiveFailed_phase_ne_archiving (state : Lifecycle) :
    state.archiveFailed.phaseValue ≠ .archiving := by
  unfold archiveFailed phaseValue
  split
  · intro h; cases h
  · rename_i hph
    intro h
    change ¬(state.phase == Phase.archiving) = true at hph
    have : (Phase.archiving == Phase.archiving) = true := rfl
    rw [h, this] at hph
    exact hph rfl

theorem Lifecycle.beginArchive_phaseValue (state next : Lifecycle)
    (hbeg : state.beginArchive = some next) : next.phaseValue = .archiving := by
  unfold beginArchive at hbeg
  split at hbeg
  · cases hbeg; rfl
  · cases hbeg

theorem Lifecycle.request_clear_unstarted (state : Lifecycle) (unstarted : state.Unstarted) :
    (state.request .clear).Unstarted := by
  refine ⟨rfl, ?_⟩
  intro h
  unfold request at h
  dsimp at h
  cases hcp : state.clearPending with
  | none =>
    simp [hcp, Option.or] at h
    exact absurd h (by rw [unstarted.1]; intro hc; cases hc)
  | some prev =>
    simp [hcp, Option.or] at h
    subst h
    exact unstarted.2 hcp

theorem Lifecycle.Archival.desired_stopped (state : Lifecycle) (arch : state.Archival)
    (h : state.clearPendingValue.isSome = true ∨ state.phaseValue = .archiving) :
    state.desiredValue = .stopped :=
  h.elim arch.1 arch.2

theorem Lifecycle.Unstarted.desired_stopped (state : Lifecycle) (u : state.Unstarted) :
    state.desiredValue = .stopped :=
  u.1

theorem Lifecycle.request_start_clearPendingValue (state : Lifecycle) :
    (state.request .start).clearPendingValue = none := rfl

theorem Lifecycle.request_stop_clearPendingValue (state : Lifecycle) :
    (state.request .stop).clearPendingValue = none := rfl

theorem Lifecycle.reserve_clearPendingValue (state : Lifecycle) (now generation : UInt64)
    (next : Lifecycle) (hres : state.reserve now = some (generation, next)) :
    next.clearPendingValue = none := by
  have hcp := (Lifecycle.reserve_guards state now generation next hres).2.1
  unfold reserve at hres
  split at hres
  · cases hres; exact hcp
  · cases hres

theorem Lifecycle.started_clearPendingValue (state : Lifecycle) (generation : UInt64) :
    (state.started generation).clearPendingValue = state.clearPendingValue := by
  unfold started clearPendingValue; split <;> rfl

theorem Lifecycle.failed_clearPendingValue (state : Lifecycle) (generation now : UInt64)
    (healthy : Bool) :
    (state.failed generation now healthy).clearPendingValue = state.clearPendingValue := by
  unfold failed clearPendingValue; split <;> rfl

theorem Lifecycle.retire_clearPendingValue (state : Lifecycle) (generation : UInt64) :
    (state.retire generation).clearPendingValue = state.clearPendingValue := by
  unfold retire clearPendingValue; split <;> rfl

theorem Lifecycle.beginArchive_clearPendingValue (state next : Lifecycle)
    (hbeg : state.beginArchive = some next) :
    next.clearPendingValue = state.clearPendingValue := by
  unfold beginArchive at hbeg
  split at hbeg
  · cases hbeg; rfl
  · cases hbeg

theorem Lifecycle.beginArchive_clearPending_isSome (state next : Lifecycle)
    (hbeg : state.beginArchive = some next) :
    state.clearPendingValue.isSome = true := by
  unfold beginArchive at hbeg
  split at hbeg
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    exact hcond.2
  · cases hbeg

theorem Lifecycle.beginArchive_old_phaseValue (state next : Lifecycle)
    (hbeg : state.beginArchive = some next) :
    state.phaseValue ≠ .archiving := by
  unfold beginArchive at hbeg
  split at hbeg
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    have hidle : (state.phase == Phase.idle) = true := hcond.1
    intro h
    have : (Phase.archiving == Phase.idle) = false := rfl
    rw [show state.phase = .archiving from h, this] at hidle
    cases hidle
  · cases hbeg

theorem Lifecycle.archived_clearPendingValue (state next : Lifecycle) (identity : Identity)
    (hins : state.archived identity = some next) : next.clearPendingValue = none := by
  unfold archived at hins
  split at hins
  · cases hins; rfl
  · cases hins

theorem Lifecycle.archiveFailed_clearPendingValue (state : Lifecycle) :
    state.archiveFailed.clearPendingValue.isSome = true →
      state.clearPendingValue.isSome = true := by
  unfold archiveFailed clearPendingValue
  split <;> intro h <;> first | cases h | exact h

theorem Lifecycle.adoptFinalIdentity_clearPendingValue (state : Lifecycle)
    (generation : UInt64) (identity : Identity) :
    (state.adoptFinalIdentity generation identity).clearPendingValue = state.clearPendingValue := by
  unfold adoptFinalIdentity clearPendingValue; split <;> rfl

end Acorn.Host.Viewer
