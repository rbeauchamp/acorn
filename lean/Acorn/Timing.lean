namespace Acorn

inductive StepOrder where
  | learnThenAct
  | planAfterAct
  | actThenLearn
  deriving DecidableEq

def StepOrder.name : StepOrder → String
  | .learnThenAct => "learn-then-act"
  | .planAfterAct => "plan-after-act"
  | .actThenLearn => "act-then-learn"

def StepOrder.parse (text : String) : Option StepOrder :=
  if text = "learn-then-act" then some .learnThenAct
  else if text = "plan-after-act" then some .planAfterAct
  else if text = "act-then-learn" then some .actThenLearn
  else none

def StepOrder.tag : StepOrder → UInt32
  | .learnThenAct => 0
  | .planAfterAct => 1
  | .actThenLearn => 2

theorem StepOrder.tag_injective (first second : StepOrder) (same : first.tag = second.tag) :
    first = second := by
  cases first <;> cases second <;> first | rfl | cases same

theorem StepOrder.tag_small (order : StepOrder) : order.tag.toNat < 256 := by
  cases order <;> decide

def StepOrder.Stored (word : UInt32) (order : StepOrder) : Prop :=
  (word = 0 ∧ order = .learnThenAct) ∨ (word = 1 ∧ order = .planAfterAct) ∨
    (word = 2 ∧ order = .actThenLearn)

theorem StepOrder.tag_stored (order : StepOrder) (word : UInt32) :
    order.tag = word ↔ StepOrder.Stored word order := by
  cases order <;> simp [StepOrder.tag, StepOrder.Stored, eq_comm]

theorem StepOrder.stored_injective (word : UInt32) (first second : StepOrder)
    (one : StepOrder.Stored word first) (other : StepOrder.Stored word second) :
    first = second :=
  StepOrder.tag_injective first second
    (((StepOrder.tag_stored first word).mpr one).trans
      ((StepOrder.tag_stored second word).mpr other).symm)

def StepOrder.Spelled (text : String) (order : StepOrder) : Prop :=
  (text = "learn-then-act" ∧ order = .learnThenAct) ∨
    (text = "plan-after-act" ∧ order = .planAfterAct) ∨
    (text = "act-then-learn" ∧ order = .actThenLearn)

theorem StepOrder.parse_spelled (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ StepOrder.Spelled text order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "plan-after-act" <;>
    by_cases third : text = "act-then-learn" <;>
    simp_all [StepOrder.parse, StepOrder.Spelled]

theorem StepOrder.parse_refused (text : String) :
    StepOrder.parse text = none ↔ ∀ order, ¬ StepOrder.Spelled text order := by
  constructor
  · intro refused order spelled
    rw [(StepOrder.parse_spelled text order).mpr spelled] at refused
    cases refused
  · intro unspelled
    cases parsed : StepOrder.parse text with
    | none => rfl
    | some order => exact (unspelled order ((StepOrder.parse_spelled text order).mp parsed)).elim

theorem StepOrder.name_spelled (order other : StepOrder) :
    StepOrder.Spelled order.name other ↔ other = order := by
  cases order <;> cases other <;> simp [StepOrder.Spelled, StepOrder.name]

theorem StepOrder.parse_accepted (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ text = StepOrder.name order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "plan-after-act" <;>
    by_cases third : text = "act-then-learn" <;>
    simp_all [StepOrder.parse, StepOrder.name]

def StepOrder.Releases (order : StepOrder) : Prop := order ≠ .learnThenAct

structure Pace where
  cycle : Nat
  latency : Nat
  running : 0 < cycle
  causal : 0 < latency

inductive Timing where
  | synchronized
  | wallClock (pace : Pace)

structure Instant where
  nanoseconds : Nat

def Pace.boundary (pace : Pace) (origin : Instant) (index : Nat) : Instant :=
  ⟨origin.nanoseconds + index * pace.cycle⟩

def Pace.index (pace : Pace) (origin now : Instant) : Nat :=
  (now.nanoseconds - origin.nanoseconds) / pace.cycle

def Pace.deadline (pace : Pace) (origin : Instant) (index : Nat) : Instant :=
  pace.boundary origin (index + pace.latency)

def Pace.meets (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) : Bool :=
  decide (released.nanoseconds < (pace.deadline origin index).nanoseconds)

theorem Pace.boundary_nanoseconds (pace : Pace) (origin : Instant) (index : Nat) :
    (pace.boundary origin index).nanoseconds = origin.nanoseconds + index * pace.cycle := rfl

theorem Pace.boundary_lt (pace : Pace) (origin : Instant) {index other : Nat}
    (earlier : index < other) :
    (pace.boundary origin index).nanoseconds < (pace.boundary origin other).nanoseconds :=
  Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right earlier pace.running) origin.nanoseconds

theorem Pace.boundary_le (pace : Pace) (origin : Instant) (index : Nat) (now : Instant) :
    (pace.boundary origin index).nanoseconds ≤ now.nanoseconds ↔
      origin.nanoseconds ≤ now.nanoseconds ∧ index ≤ pace.index origin now := by
  rw [pace.boundary_nanoseconds origin index]
  unfold Pace.index
  rw [Nat.le_div_iff_mul_le pace.running]
  omega

theorem Pace.index_early (pace : Pace) (origin now : Instant)
    (before : now.nanoseconds < origin.nanoseconds) : pace.index origin now = 0 := by
  unfold Pace.index
  rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt before)]
  exact Nat.zero_div pace.cycle

theorem Pace.index_boundary (pace : Pace) (origin : Instant) (index : Nat) :
    pace.index origin (pace.boundary origin index) = index := by
  unfold Pace.index
  rw [pace.boundary_nanoseconds origin index, Nat.add_sub_cancel_left]
  exact Nat.mul_div_cancel index pace.running

theorem Pace.index_iff (pace : Pace) (origin now : Instant) (index : Nat)
    (started : origin.nanoseconds ≤ now.nanoseconds) :
    pace.index origin now = index ↔
      (pace.boundary origin index).nanoseconds ≤ now.nanoseconds ∧
        now.nanoseconds < (pace.boundary origin (index + 1)).nanoseconds := by
  have here := pace.boundary_le origin index now
  have next := pace.boundary_le origin (index + 1) now
  omega

theorem Pace.deadline_nanoseconds (pace : Pace) (origin : Instant) (index : Nat) :
    (pace.deadline origin index).nanoseconds =
      origin.nanoseconds + (index + pace.latency) * pace.cycle := rfl

theorem Pace.deadline_lt (pace : Pace) (origin : Instant) (index : Nat) :
    (pace.boundary origin index).nanoseconds < (pace.deadline origin index).nanoseconds :=
  pace.boundary_lt origin (Nat.lt_add_of_pos_right pace.causal)

theorem Pace.meets_iff (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) :
    pace.meets origin index released = true ↔
      released.nanoseconds < origin.nanoseconds + (index + pace.latency) * pace.cycle :=
  decide_eq_true_iff

theorem Pace.meets_index (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) :
    pace.meets origin index released = true ↔
      pace.index origin released < index + pace.latency := by
  have started := pace.boundary_le origin (index + pace.latency) released
  have early := pace.index_early origin released
  have positive := pace.causal
  rw [pace.boundary_nanoseconds origin (index + pace.latency)] at started
  rw [pace.meets_iff origin index released]
  omega

theorem Pace.meets_begun (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) :
    pace.meets origin index released = true ↔
      ∀ later, index + pace.latency ≤ later →
        released.nanoseconds < (pace.boundary origin later).nanoseconds := by
  rw [pace.meets_iff origin index released]
  constructor
  · intro met later due
    have grows : (index + pace.latency) * pace.cycle ≤ later * pace.cycle :=
      Nat.mul_le_mul_right pace.cycle due
    rw [pace.boundary_nanoseconds origin later]
    omega
  · intro none
    have first := none (index + pace.latency) (Nat.le_refl _)
    rw [pace.boundary_nanoseconds origin (index + pace.latency)] at first
    exact first

theorem Pace.met_gap (pace : Pace) (origin : Instant) (index span : Nat)
    (first second : Instant)
    (sensed : (pace.boundary origin index).nanoseconds ≤ first.nanoseconds)
    (met : pace.meets origin (index + span) second = true) :
    second.nanoseconds < first.nanoseconds + (span + pace.latency) * pace.cycle := by
  have verdict := (pace.meets_iff origin (index + span) second).mp met
  have split : (index + span + pace.latency) * pace.cycle =
      index * pace.cycle + (span + pace.latency) * pace.cycle := by
    rw [Nat.add_assoc, Nat.add_mul]
  rw [pace.boundary_nanoseconds origin index] at sensed
  omega

def Pace.first (pace : Pace) (origin now : Instant) : Nat :=
  (now.nanoseconds - origin.nanoseconds + pace.cycle - 1) / pace.cycle

theorem Pace.first_starts (pace : Pace) (origin now : Instant) :
    now.nanoseconds ≤ (pace.boundary origin (pace.first origin now)).nanoseconds := by
  have running := pace.running
  have lower := Nat.lt_div_mul_add
    (a := now.nanoseconds - origin.nanoseconds + pace.cycle - 1) running
  rw [pace.boundary_nanoseconds origin (pace.first origin now)]
  unfold Pace.first
  omega

theorem Pace.first_least (pace : Pace) (origin now : Instant) (index : Nat)
    (starts : now.nanoseconds ≤ (pace.boundary origin index).nanoseconds) :
    pace.first origin now ≤ index := by
  have running := pace.running
  rw [pace.boundary_nanoseconds origin index] at starts
  unfold Pace.first
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul running, Nat.succ_mul]
  omega

theorem Pace.first_within (pace : Pace) (origin now : Instant)
    (started : origin.nanoseconds ≤ now.nanoseconds) :
    (pace.boundary origin (pace.first origin now)).nanoseconds <
      now.nanoseconds + pace.cycle := by
  have running := pace.running
  have upper := Nat.div_mul_le_self
    (now.nanoseconds - origin.nanoseconds + pace.cycle - 1) pace.cycle
  rw [pace.boundary_nanoseconds origin (pace.first origin now)]
  unfold Pace.first
  omega

structure Force (α : Type) where
  action : Option α
  lapse : Option Instant

variable {α : Type}

def Force.named (force : Force α) (rest : Option α) (now : Instant) : Option α :=
  match force.lapse with
  | none => force.action
  | some lapse => if now.nanoseconds < lapse.nanoseconds then force.action else rest

inductive Standing (α : Type) where
  | idle (force : Force α)
  | awaiting (prior : Force α) (index : Nat)

def Standing.force : Standing α → Force α
  | .idle force => force
  | .awaiting prior _ => prior

structure Standing.Outcome (α : Type) where
  action : Option α
  fault : Bool

def Pace.outcome (pace : Pace) (origin : Instant) (rest : Option α) (standing : Standing α)
    (now : Instant) : Standing.Outcome α :=
  match standing with
  | .idle force => ⟨force.named rest now, false⟩
  | .awaiting prior index => ⟨prior.named rest now, !pace.meets origin index now⟩

def Standing.during (prior : Force α) (index : Nat) (released : Instant) (chosen : Force α)
    (now : Instant) : Standing α :=
  if now.nanoseconds ≤ released.nanoseconds then .awaiting prior index else .idle chosen

theorem Force.named_lasting (force : Force α) (rest : Option α) (now : Instant)
    (lasting : force.lapse = none) : force.named rest now = force.action := by
  unfold Force.named
  rw [lasting]

theorem Force.named_lapse (force : Force α) (rest : Option α) (now lapse : Instant)
    (lapses : force.lapse = some lapse) :
    force.named rest now =
      if now.nanoseconds < lapse.nanoseconds then force.action else rest := by
  unfold Force.named
  rw [lapses]

theorem Pace.outcome_action (pace : Pace) (origin : Instant) (rest : Option α)
    (standing : Standing α) (now : Instant) :
    (pace.outcome origin rest standing now).action = standing.force.named rest now := by
  cases standing <;> rfl

theorem Pace.outcome_fault (pace : Pace) (origin : Instant) (rest : Option α)
    (standing : Standing α) (now : Instant) :
    (pace.outcome origin rest standing now).fault = true ↔
      ∃ prior index, standing = .awaiting prior index ∧
        (pace.deadline origin index).nanoseconds ≤ now.nanoseconds := by
  cases standing with
  | idle force =>
    constructor
    · intro fault
      cases fault
    · intro ⟨_, _, same, _⟩
      cases same
  | awaiting prior index =>
    simp only [Pace.outcome, Pace.meets, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
    constructor
    · intro late
      exact ⟨prior, index, rfl, late⟩
    · intro ⟨_, _, same, late⟩
      cases same
      exact late

theorem Pace.step_fault (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now : Instant) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).fault =
        true ↔
      (pace.deadline origin index).nanoseconds ≤ now.nanoseconds ∧
        now.nanoseconds ≤ released.nanoseconds := by
  rw [pace.outcome_fault origin]
  unfold Standing.during
  split
  · rename_i awaited
    constructor
    · intro ⟨_, _, same, late⟩
      cases same
      exact ⟨late, awaited⟩
    · intro ⟨late, _⟩
      exact ⟨prior, index, rfl, late⟩
  · rename_i passed
    constructor
    · intro ⟨_, _, same, _⟩
      cases same
    · intro ⟨_, awaited⟩
      exact absurd awaited passed

theorem Pace.step_action (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now : Instant) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).action =
      if now.nanoseconds ≤ released.nanoseconds then prior.named rest now
      else chosen.named rest now := by
  rw [pace.outcome_action origin]
  unfold Standing.during
  split <;> rfl

theorem Pace.step_holds (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now : Instant)
    (fault : (pace.outcome origin rest (Standing.during prior index released chosen now)
      now).fault = true)
    (holding : ∀ lapse, prior.lapse = some lapse → now.nanoseconds < lapse.nanoseconds) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).action =
      prior.action := by
  rw [pace.step_action origin rest prior index released chosen now]
  split
  · cases lapses : prior.lapse with
    | none => exact prior.named_lasting rest now lapses
    | some lapse =>
      rw [prior.named_lapse rest now lapse lapses]
      split
      · rfl
      · rename_i lapsed
        exact absurd (holding lapse lapses) lapsed
  · rename_i passed
    exact absurd
      ((pace.step_fault origin rest prior index released chosen now).mp fault).2 passed

theorem Pace.step_lapsed (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now lapse : Instant)
    (fault : (pace.outcome origin rest (Standing.during prior index released chosen now)
      now).fault = true)
    (lapses : prior.lapse = some lapse) (lapsed : lapse.nanoseconds ≤ now.nanoseconds) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).action =
      rest := by
  rw [pace.step_action origin rest prior index released chosen now]
  split
  · rw [prior.named_lapse rest now lapse lapses]
    split
    · rename_i before
      exact absurd before (Nat.not_lt.mpr lapsed)
    · rfl
  · rename_i passed
    exact absurd
      ((pace.step_fault origin rest prior index released chosen now).mp fault).2 passed

theorem Pace.step_faultless (pace : Pace) (origin : Instant) (rest : Option α)
    (prior : Force α) (index : Nat) (released : Instant) (chosen : Force α) :
    pace.meets origin index released = true ↔
      ∀ now, (pace.outcome origin rest (Standing.during prior index released chosen now)
        now).fault = false := by
  have verdict := pace.meets_iff origin index released
  have due := pace.deadline_nanoseconds origin index
  constructor
  · intro met now
    have early := verdict.mp met
    have none := not_congr (pace.step_fault origin rest prior index released chosen now)
    rw [Bool.not_eq_true] at none
    refine none.mpr ?_
    omega
  · intro none
    have last := not_congr
      (pace.step_fault origin rest prior index released chosen released)
    rw [Bool.not_eq_true] at last
    have clear := last.mp (none released)
    refine verdict.mpr ?_
    omega

end Acorn
