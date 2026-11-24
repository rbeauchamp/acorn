import Mathlib.Data.List.Basic

namespace AcornVerif.Checkpoint

def campaignAccepted (maxGoals curriculumLen cycles : Nat) : Prop :=
  cycles ≠ 0 ∨ min maxGoals curriculumLen ≠ 0

structure AdmittedCampaign where
  goals : Nat
  cycles : Nat
  admissible : cycles ≠ 0 ∨ goals ≠ 0

def admitCampaign (maxGoals curriculumLen cycles : Nat)
    (accepted : campaignAccepted maxGoals curriculumLen cycles) : AdmittedCampaign :=
  ⟨min maxGoals curriculumLen, cycles, accepted⟩

theorem campaign_goals_exact (maxGoals curriculumLen cycles : Nat)
    (accepted : campaignAccepted maxGoals curriculumLen cycles) :
    (admitCampaign maxGoals curriculumLen cycles accepted).goals =
      min maxGoals curriculumLen := rfl

theorem campaign_unbounded_nonempty (campaign : AdmittedCampaign)
    (unbounded : campaign.cycles = 0) : campaign.goals ≠ 0 := by
  exact campaign.admissible.resolve_left (fun nonzero => nonzero unbounded)

theorem campaign_finite_accepted (maxGoals curriculumLen cycles : Nat)
    (finite : cycles ≠ 0) : campaignAccepted maxGoals curriculumLen cycles :=
  Or.inl finite

theorem campaign_empty_accepted_iff (maxGoals curriculumLen cycles : Nat)
    (empty : min maxGoals curriculumLen = 0) :
    campaignAccepted maxGoals curriculumLen cycles ↔ cycles ≠ 0 := by
  simp [campaignAccepted, empty]

structure Identity where
  seed : Nat
  tilings : Nat
  initialBank : Nat
  weights : Nat
  learners : Nat
  criterion : Nat
  policy : Nat
  order : Nat
  deriving DecidableEq

def identityAccepted (receiver image : Identity) : Prop :=
  image.seed = receiver.seed ∧ image.tilings = receiver.tilings ∧
  image.initialBank = receiver.initialBank ∧ image.weights = receiver.weights ∧
  image.learners = receiver.learners ∧ image.criterion = receiver.criterion ∧
  image.policy = receiver.policy ∧ image.order = receiver.order

theorem identity_accepted_iff (receiver image : Identity) :
    identityAccepted receiver image ↔ image = receiver := by
  cases receiver
  cases image
  simp [identityAccepted, Identity.mk.injEq]

theorem identity_mismatch_refused (receiver image : Identity) (h : image ≠ receiver) :
    ¬ identityAccepted receiver image := by
  exact fun accepted => h ((identity_accepted_iff receiver image).mp accepted)

theorem appended_name_longer {α : Type*} (name suffix : List α) (h : suffix ≠ []) :
    name.length < (name ++ suffix).length := by
  rw [List.length_append]
  have positive : 0 < suffix.length := List.length_pos_iff.mpr h
  exact Nat.lt_add_of_pos_right positive

theorem appended_name_ne {α : Type*} (name suffix : List α) (h : suffix ≠ []) :
    name ++ suffix ≠ name := by
  intro same
  have longer := appended_name_longer name suffix h
  rw [same] at longer
  exact (Nat.lt_irrefl _) longer

inductive Admission where
  | loaded
  | missing
  | refused
  deriving DecidableEq

structure Writable (Path : Type*) where
  path : Path
  interval : {n : Nat // n ≠ 0}

def authorize {Path : Type*} (path : Path) (interval : Nat) (admission : Admission) :
    Option (Writable Path) :=
  match admission with
  | .refused => none
  | .loaded | .missing =>
    if h : interval = 0 then none else some ⟨path, ⟨interval, h⟩⟩

def due {Path : Type*} (_capability : Writable Path) (periodic stop : Bool) : Prop :=
  stop = true ∨ periodic = true

theorem due_iff {Path : Type*} (capability : Writable Path) (periodic stop : Bool) :
    due capability periodic stop ↔ (stop || periodic) = true := by
  simp [due]

def writes {Path : Type*} (path : Path) (interval attempts : Nat)
    (admission : Admission) (present stop : Bool) : Prop :=
  present = true ∧ ∃ capability, authorize path interval admission = some capability ∧
    due capability (decide (attempts % capability.interval.val = 0)) stop

theorem writes_iff {Path : Type*} (path : Path) (interval attempts : Nat)
    (admission : Admission) (present stop : Bool) :
    writes path interval attempts admission present stop ↔
      present = true ∧ admission ≠ .refused ∧ interval ≠ 0 ∧
        (stop = true ∨ attempts % interval = 0) := by
  cases admission <;> by_cases h : interval = 0 <;> simp [writes, authorize, due, h]

theorem refused_never_writes {Path : Type*} (path : Path) (interval attempts : Nat)
    (present stop : Bool) : ¬ writes path interval attempts .refused present stop := by
  simp [writes_iff]

theorem load_only_never_writes {Path : Type*} (path : Path) (attempts : Nat)
    (admission : Admission) (present stop : Bool) :
    ¬ writes path 0 attempts admission present stop := by
  simp [writes_iff]

theorem stop_permission_iff {Path : Type*} (path : Path) (interval attempts : Nat)
    (admission : Admission) (present : Bool) :
    writes path interval attempts admission present true ↔
      present = true ∧ admission ≠ .refused ∧ interval ≠ 0 := by
  simp [writes_iff]

end AcornVerif.Checkpoint
