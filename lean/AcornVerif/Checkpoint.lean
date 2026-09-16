/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.List.Basic

/-!
# Receiver-bound checkpoint contracts

These structural specifications model a receiver-indexed checkpoint capability
and admitted images. The receiver index represents exclusive ownership. Byte
decoding, checksums, length checks, assignment legality and numerical admission
are separate execution obligations; the current implementation linkage lives in
`AcornVerif.CurrentCheckpoint` and the proof-bearing `Acorn.Host.Checkpoint` modules.

Primary knowledge includes weights and log step sizes in canonical learner order.
Durable state includes steps, gain, lifetime and bank progress; transient state
includes models, traces, RNG and execution state. The commit definition copies
assignments and primary knowledge pointwise, without ranking or controller reset.
Refusal is a pure admission result. An implementation must preserve these
properties through parsing, installation and transient reset.

Identity is equality of every represented component. Natural-number tags abstract
injective encodings of supported criteria and policies; supported-policy and
format-version admission are separate obligations. Counts and schedules use
unbounded naturals here, so bounded machine representations need correspondence.

Filename results concern finite lists of name units. Separator-free suffixes,
sibling construction, filesystem name equivalence, exclusive creation,
synchronization and rename semantics remain platform obligations.
-/

namespace AcornVerif.Checkpoint

/-- Campaign admission uses the effective range, including an empty curriculum. -/
def campaignAccepted (maxGoals curriculumLen cycles : Nat) : Prop :=
  cycles ≠ 0 ∨ min maxGoals curriculumLen ≠ 0

/-- Campaign domain with positive finite counts or continuous execution. -/
structure AdmittedCampaign where
  /-- Goal count after clipping to the curriculum length. -/
  goals : Nat
  /-- Zero denotes an unbounded campaign. -/
  cycles : Nat
  /-- Only a finite campaign can have an empty goal range. -/
  admissible : cycles ≠ 0 ∨ goals ≠ 0

/-- Admission carries the clipped goal range into execution, not an unused token. -/
def admitCampaign (maxGoals curriculumLen cycles : Nat)
    (accepted : campaignAccepted maxGoals curriculumLen cycles) : AdmittedCampaign :=
  ⟨min maxGoals curriculumLen, cycles, accepted⟩

/-- Execution consumes precisely the admitted effective goal count. -/
theorem campaign_goals_exact (maxGoals curriculumLen cycles : Nat)
    (accepted : campaignAccepted maxGoals curriculumLen cycles) :
    (admitCampaign maxGoals curriculumLen cycles accepted).goals =
      min maxGoals curriculumLen := rfl

/-- An unbounded admitted campaign necessarily has a nonempty goal range. -/
theorem campaign_unbounded_nonempty (campaign : AdmittedCampaign)
    (unbounded : campaign.cycles = 0) : campaign.goals ≠ 0 := by
  exact campaign.admissible.resolve_left (fun nonzero => nonzero unbounded)

/-- Every positive finite cycle budget admits even an empty effective range. -/
theorem campaign_finite_accepted (maxGoals curriculumLen cycles : Nat)
    (finite : cycles ≠ 0) : campaignAccepted maxGoals curriculumLen cycles :=
  Or.inl finite

/-- An empty effective range is refused exactly when the cycle budget is unbounded. -/
theorem campaign_empty_accepted_iff (maxGoals curriculumLen cycles : Nat)
    (empty : min maxGoals curriculumLen = 0) :
    campaignAccepted maxGoals curriculumLen cycles ↔ cycles ≠ 0 := by
  simp [campaignAccepted, empty]

/-- Complete representation identity checked independently of payload admission. -/
structure Identity where
  /-- Agent seed. -/
  seed : Nat
  /-- Number of tilings. -/
  tilings : Nat
  /-- Initial imprint-bank size, before retirement. -/
  initialBank : Nat
  /-- Weights per learner. -/
  weights : Nat
  /-- Canonical learner count. -/
  learners : Nat
  /-- Control criterion tag. -/
  criterion : Nat
  /-- Supported policy encoding. -/
  policy : Nat
  deriving DecidableEq

/-- Every component is required; no component is summarized by a digest. -/
def identityAccepted (receiver image : Identity) : Prop :=
  image.seed = receiver.seed ∧ image.tilings = receiver.tilings ∧
  image.initialBank = receiver.initialBank ∧ image.weights = receiver.weights ∧
  image.learners = receiver.learners ∧ image.criterion = receiver.criterion ∧
  image.policy = receiver.policy

/-- Componentwise acceptance is exactly complete representation equality. -/
theorem identity_accepted_iff (receiver image : Identity) :
    identityAccepted receiver image ↔ image = receiver := by
  cases receiver
  cases image
  simp [identityAccepted, Identity.mk.injEq]

/-- Any representation mismatch prevents identity acceptance. -/
theorem identity_mismatch_refused (receiver image : Identity) (h : image ≠ receiver) :
    ¬ identityAccepted receiver image := by
  exact fun accepted => h ((identity_accepted_iff receiver image).mp accepted)

/-- Full mathematical state, with explicit durable and transient ownership. -/
structure State (Slot Learner Assignment Knowledge Durable Transient : Type*) where
  /-- Immutable representation. -/
  identity : Identity
  /-- Actual assignments by canonical option slot. -/
  assignments : Slot → Assignment
  /-- Primary knowledge by canonical learner index. -/
  primary : Learner → Knowledge
  /-- Other durable state. -/
  durable : Durable
  /-- State intentionally cold-started by restore. -/
  transient : Transient

/-- Image whose compatibility witness refers to this exact prior receiver. -/
structure Admitted {S L A K D T : Type*} (receiver : State S L A K D T) where
  /-- Image representation. -/
  identity : Identity
  /-- Evidence that every representation component matches. -/
  compatible : identityAccepted receiver.identity identity
  /-- Admitted assignments in their persisted order. -/
  assignments : S → A
  /-- Admitted, projected primary knowledge in its persisted order. -/
  primary : L → K
  /-- Admitted durable state. -/
  durable : D

/-- Infallible installation into the receiver that admitted the image. -/
def commit {S L A K D T : Type*} {receiver : State S L A K D T}
    (image : Admitted receiver) (cold : T) : State S L A K D T :=
  ⟨receiver.identity, image.assignments, image.primary, image.durable, cold⟩

/-- Every slot receives its own assignment, independently of any ranking. -/
theorem commit_assignment {S L A K D T : Type*} (receiver : State S L A K D T)
    (image : Admitted receiver) (cold : T) (slot : S) :
    (commit image cold).assignments slot = image.assignments slot := rfl

/-- Every learner receives its own admitted primary knowledge. -/
theorem commit_primary {S L A K D T : Type*} (receiver : State S L A K D T)
    (image : Admitted receiver) (cold : T) (learner : L) :
    (commit image cold).primary learner = image.primary learner := rfl

/-- Assignment and knowledge installation hold together for every pair of indices. -/
theorem commit_pair {S L A K D T : Type*} (receiver : State S L A K D T)
    (image : Admitted receiver) (cold : T) (slot : S) (learner : L) :
    ((commit image cold).assignments slot, (commit image cold).primary learner) =
      (image.assignments slot, image.primary learner) := rfl

/-- Commit preserves the receiver identity and therefore the admitted image identity. -/
theorem commit_identity {S L A K D T : Type*} (receiver : State S L A K D T)
    (image : Admitted receiver) (cold : T) :
    (commit image cold).identity = image.identity :=
  ((identity_accepted_iff receiver.identity image.identity).mp image.compatible).symm

/-- Admission either returns a receiver-bound image or refuses without a state update. -/
def restore {S L A K D T : Type*} (receiver : State S L A K D T)
    (admission : Option (Admitted receiver)) (cold : T) : State S L A K D T :=
  match admission with
  | none => receiver
  | some image => commit image cold

/-- Refusal preserves the whole arbitrary prior state, including transients. -/
theorem refusal_unchanged {S L A K D T : Type*} (receiver : State S L A K D T)
    (cold : T) : restore receiver none cold = receiver := rfl

/-- Successful admission installs precisely the receiver-bound image. -/
theorem restore_admitted {S L A K D T : Type*} (receiver : State S L A K D T)
    (image : Admitted receiver) (cold : T) :
    restore receiver (some image) cold = commit image cold := rfl

/-- Appending a nonempty suffix strictly increases any finite filename's length. -/
theorem appended_name_longer {α : Type*} (name suffix : List α) (h : suffix ≠ []) :
    name.length < (name ++ suffix).length := by
  rw [List.length_append]
  have positive : 0 < suffix.length := List.length_pos_iff.mpr h
  exact Nat.lt_add_of_pos_right positive

/-- A nonempty appended suffix cannot equal the original name, for any name units. -/
theorem appended_name_ne {α : Type*} (name suffix : List α) (h : suffix ≠ []) :
    name ++ suffix ≠ name := by
  intro same
  have longer := appended_name_longer name suffix h
  rw [same] at longer
  exact (Nat.lt_irrefl _) longer

/-- Complete load-result domain used by the runtime capability constructor. -/
inductive Admission where
  /-- An existing image was accepted. -/
  | loaded
  /-- No existing image was found. -/
  | missing
  /-- An existing image could not be accepted. -/
  | refused
  deriving DecidableEq

/-- Authority retains both the destination and a nonzero interval. -/
structure Writable (Path : Type*) where
  /-- Destination bound at admission. -/
  path : Path
  /-- Nonzero write interval. -/
  interval : {n : Nat // n ≠ 0}

/-- Capability admission follows the runtime's load-result and interval cases. -/
def authorize {Path : Type*} (path : Path) (interval : Nat) (admission : Admission) :
    Option (Writable Path) :=
  match admission with
  | .refused => none
  | .loaded | .missing =>
    if h : interval = 0 then none else some ⟨path, ⟨interval, h⟩⟩

/-- Stop or the periodic boundary makes an already authorized capability due. -/
def due {Path : Type*} (_capability : Writable Path) (periodic stop : Bool) : Prop :=
  stop = true ∨ periodic = true

/-- The capability's due method accepts all periodic and stop flags. -/
theorem due_iff {Path : Type*} (capability : Writable Path) (periodic stop : Bool) :
    due capability periodic stop ↔ (stop || periodic) = true := by
  simp [due]

/-- A write requires an admitted capability whose own schedule is due. -/
def writes {Path : Type*} (path : Path) (interval attempts : Nat)
    (admission : Admission) (present stop : Bool) : Prop :=
  present = true ∧ ∃ capability, authorize path interval admission = some capability ∧
    due capability (decide (attempts % capability.interval.val = 0)) stop

/-- Exact write permission over all paths, intervals, attempts, admissions and stop flags. -/
theorem writes_iff {Path : Type*} (path : Path) (interval attempts : Nat)
    (admission : Admission) (present stop : Bool) :
    writes path interval attempts admission present stop ↔
      present = true ∧ admission ≠ .refused ∧ interval ≠ 0 ∧
        (stop = true ∨ attempts % interval = 0) := by
  cases admission <;> by_cases h : interval = 0 <;> simp [writes, authorize, due, h]

/-- Graceful stop cannot authorize replacement of a refused image. -/
theorem refused_never_writes {Path : Type*} (path : Path) (interval attempts : Nat)
    (present stop : Bool) : ¬ writes path interval attempts .refused present stop := by
  simp [writes_iff]

/-- A zero interval is load-only, including during graceful stop. -/
theorem load_only_never_writes {Path : Type*} (path : Path) (attempts : Nat)
    (admission : Admission) (present stop : Bool) :
    ¬ writes path 0 attempts admission present stop := by
  simp [writes_iff]

/-- With stop requested, permission depends exactly on admission and a nonzero interval. -/
theorem stop_permission_iff {Path : Type*} (path : Path) (interval attempts : Nat)
    (admission : Admission) (present : Bool) :
    writes path interval attempts admission present true ↔
      present = true ∧ admission ≠ .refused ∧ interval ≠ 0 := by
  simp [writes_iff]

end AcornVerif.Checkpoint
