import Acorn.FeatureLifecycle
import AcornVerif.CurrentArithmetic
import Acorn.Handcrafted.FeatureProfile
import Mathlib.Tactic.NormNum

namespace AcornVerif.Retirement
open Acorn.Features

variable {shape : PatchShape} {actions : Acorn.Word.Count} {config : Config} {criterion : Criterion}
  {dimension : Acorn.Dimension} {discounts : List Acorn.Discount}

structure Cycle (actions : Acorn.Word.Count) (config : Config) (criterion : Criterion)
    (dimension : Acorn.Dimension)
    (discounts : List Acorn.Discount) where
  learn : Ensemble actions config criterion dimension discounts →
    Ensemble actions config criterion dimension discounts
  free : Bool
  active : Vector Bool config.units.count

def Cycle.prepare (input : Cycle actions config criterion dimension discounts)
    (state : Lifecycle shape actions config criterion dimension discounts) :
    Lifecycle shape actions config criterion dimension discounts :=
  { state.advance with consumers := input.learn state.advance.consumers }

def run : List (Cycle actions config criterion dimension discounts) →
    Lifecycle shape actions config criterion dimension discounts →
      Lifecycle shape actions config criterion dimension discounts × List Nat × Nat
  | [], state => (state, [], 0)
  | input :: rest, state =>
    let prepared := input.prepare state
    let tested := prepared.test input.free input.active
    let later := run rest tested.1
    (later.1, prepared.eligibleCount input.free :: later.2.1, tested.2.length + later.2.2)

theorem run_length : ∀ (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts),
    (run inputs state).2.1.length = inputs.length
  | [], _ => rfl
  | _ :: rest, state => by simp [run, run_length rest]

theorem run_balance : ∀ (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts),
    config.tester.period * (run inputs state).2.2 + (run inputs state).1.progress.credit.val =
      state.progress.credit.val + (run inputs state).2.1.sum
  | [], _ => by simp [run]
  | input :: rest, state => by
    have step := (input.prepare state).test_balance input.free input.active
    have later := run_balance rest ((input.prepare state).test input.free input.active).1
    have credit : (input.prepare state).progress.credit = state.progress.credit := by
      simp only [Lifecycle.progress, Cycle.prepare, Lifecycle.advance, Representation.advance,
        (Progress.advance_fields _).2.1]
    simp only [run, List.sum_cons, Nat.mul_add]
    rw [credit] at step
    omega

theorem run_replaced (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts) :
    (run inputs state).2.2 =
      (state.progress.credit.val + (run inputs state).2.1.sum) / config.tester.period := by
  have balance := run_balance inputs state
  have below := (run inputs state).1.progress.credit.isLt
  rw [← balance, Nat.mul_add_div config.tester.positive, Nat.div_eq_of_lt below, Nat.add_zero]

theorem sum_lower (bound : Nat) :
    ∀ (values : List Nat), (∀ value ∈ values, bound ≤ value) →
      bound * values.length ≤ values.sum
  | [], _ => by simp
  | head :: rest, lower => by
    have tail := sum_lower bound rest
      (fun value member => lower value (List.mem_cons_of_mem _ member))
    have first := lower head (by simp)
    simp only [List.length_cons, List.sum_cons, Nat.mul_succ]
    omega

theorem sum_upper (bound : Nat) :
    ∀ (values : List Nat), (∀ value ∈ values, value ≤ bound) →
      values.sum ≤ bound * values.length
  | [], _ => by simp
  | head :: rest, upper => by
    have tail := sum_upper bound rest
      (fun value member => upper value (List.mem_cons_of_mem _ member))
    have first := upper head (by simp)
    simp only [List.length_cons, List.sum_cons, Nat.mul_succ]
    omega

theorem run_turnover (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts) (bound : Nat)
    (eligible : ∀ count ∈ (run inputs state).2.1, bound ≤ count)
    (long : config.tester.period ≤ bound * inputs.length) :
    1 ≤ (run inputs state).2.2 := by
  have total := sum_lower bound _ eligible
  rw [run_length] at total
  rw [run_replaced, Nat.le_div_iff_mul_le config.tester.positive]
  omega

def matureCount (state : Lifecycle shape actions config criterion dimension discounts) : Nat :=
  (List.finRange config.units.count).countP state.mature

def heldCount (state : Lifecycle shape actions config criterion dimension discounts) : Nat :=
  (List.finRange config.units.count).countP state.consumers.holds

theorem countP_le_add {α : Type} (p q r : α → Bool) :
    ∀ (items : List α), (∀ item ∈ items, p item = true → q item = true ∨ r item = true) →
      items.countP p ≤ items.countP q + items.countP r
  | [], _ => by simp
  | head :: rest, covered => by
    have tail := countP_le_add p q r rest
      (fun item member => covered item (List.mem_cons_of_mem _ member))
    have first := covered head List.mem_cons_self
    simp only [List.countP_cons]
    split <;> split <;> split <;> simp_all <;> omega

theorem holds_count_le (assignment : Acorn.Features.Assignment config) :
    (List.finRange config.units.count).countP (fun unit => assignment.holds unit) ≤ 1 := by
  cases assignment with
  | neutral => simp [Assignment.holds]
  | selected held bonus =>
    have once := List.nodup_iff_count.mp (List.nodup_finRange config.units.count) held
    refine Nat.le_trans (Nat.le_of_eq (List.countP_congr fun unit _ => ?_)) once
    change (held == unit) = true ↔ (unit == held) = true
    rw [beq_iff_eq, beq_iff_eq]
    exact eq_comm

theorem heldCount_le_slots :
    ∀ (skills : List (Skill actions config criterion dimension discounts)),
      (List.finRange config.units.count).countP
        (fun unit => skills.any (·.interest.held.holds unit)) ≤ skills.length
  | [] => by simp
  | skill :: rest => by
    have parts := countP_le_add (fun unit => (skill :: rest).any (·.interest.held.holds unit))
      (fun unit => skill.interest.held.holds unit)
      (fun unit => rest.any (·.interest.held.holds unit))
      (List.finRange config.units.count) (fun unit _ held => by simpa using held)
    have one := holds_count_le skill.interest.held
    have later := heldCount_le_slots rest
    simp only [List.length_cons]
    omega

theorem heldCount_le (state : Lifecycle shape actions config criterion dimension discounts) :
    heldCount state ≤ Acorn.FeatureConstants.skillCount := by
  have bound := heldCount_le_slots (criterion := criterion) state.consumers.skills.toList
  rw [Vector.length_toList] at bound
  exact bound

theorem mature_le (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) :
    matureCount state ≤ state.eligibleCount free + heldCount state :=
  countP_le_add _ _ _ _ fun unit _ mature => by
    cases held : state.consumers.holds unit
    · left
      simp [Lifecycle.eligible, mature, held]
    · exact Or.inr rfl

theorem eligibleCount_le (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) : state.eligibleCount free ≤ config.units.count := by
  have := List.countP_le_length (p := state.eligible free) (l := List.finRange config.units.count)
  simpa [Lifecycle.eligibleCount] using this

theorem run_counts_le : ∀ (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts),
    ∀ count ∈ (run inputs state).2.1, count ≤ config.units.count
  | [], _, _, member => by simp [run] at member
  | input :: rest, state, count, member => by
    simp only [run, List.mem_cons] at member
    rcases member with same | later
    · subst same
      exact eligibleCount_le _ _
    · exact run_counts_le rest _ count later

def MatureAtEach (bound : Nat) : List (Cycle actions config criterion dimension discounts) →
    Lifecycle shape actions config criterion dimension discounts → Prop
  | [], _ => True
  | input :: rest, state =>
    bound ≤ matureCount (input.prepare state) ∧
      MatureAtEach bound rest ((input.prepare state).test input.free input.active).1

theorem run_counts_mature (bound : Nat) :
    ∀ (inputs : List (Cycle actions config criterion dimension discounts))
      (state : Lifecycle shape actions config criterion dimension discounts),
      MatureAtEach bound inputs state →
        ∀ count ∈ (run inputs state).2.1, bound - Acorn.FeatureConstants.skillCount ≤ count
  | [], _, _, _, member => by simp [run] at member
  | input :: rest, state, mature, count, member => by
    simp only [run, List.mem_cons] at member
    rcases member with same | later
    · subst same
      have covered := mature_le (input.prepare state) input.free
      have held := heldCount_le (input.prepare state)
      have now := mature.1
      omega
    · exact run_counts_mature bound rest _ mature.2 count later

theorem run_mature_turnover (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts) (bound : Nat)
    (mature : MatureAtEach bound inputs state)
    (long : config.tester.period ≤ (bound - Acorn.FeatureConstants.skillCount) * inputs.length) :
    1 ≤ (run inputs state).2.2 :=
  run_turnover inputs state _ (run_counts_mature bound inputs state mature) long

theorem run_replaced_le (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts) :
    (run inputs state).2.2 ≤
      (config.tester.period - 1 + config.units.count * inputs.length) / config.tester.period := by
  have total := sum_upper config.units.count _ (run_counts_le inputs state)
  rw [run_length] at total
  have credit := state.progress.credit.isLt
  rw [run_replaced]
  apply Nat.div_le_div_right
  omega

def bornAfter (τ : Nat) (state : Lifecycle shape actions config criterion dimension discounts) : Nat
    :=
  (List.finRange config.units.count).countP fun unit =>
    decide (τ < state.progress.units[unit.val].birth.toNat)

theorem countP_le_succ {α : Type} (p q : α → Bool) (target : α) :
    ∀ (items : List α), items.Nodup →
      (∀ item ∈ items, item ≠ target → q item = p item) →
        items.countP q ≤ items.countP p + 1
  | [], _, _ => by simp
  | head :: rest, nodup, agree => by
    have ⟨absent, restNodup⟩ := List.nodup_cons.mp nodup
    by_cases same : head = target
    · subst same
      have restAgree : rest.countP q = rest.countP p := by
        apply List.countP_congr
        intro item itemMember
        have different : item ≠ head := fun equal => absent (equal ▸ itemMember)
        rw [agree item (List.mem_cons_of_mem _ itemMember) different]
      simp only [List.countP_cons, restAgree]
      split <;> split <;> omega
    · have headAgree := agree head List.mem_cons_self same
      have inner := countP_le_succ p q target rest restNodup
        (fun item itemMember => agree item (List.mem_cons_of_mem _ itemMember))
      simp only [List.countP_cons, headAgree]
      omega

theorem bornAfter_replace (τ : Nat)
    (state : Lifecycle shape actions config criterion dimension discounts)
    (unit : Fin config.units.count) :
    bornAfter τ (state.replace unit) ≤ bornAfter τ state + 1 :=
  countP_le_succ _ _ unit _ (List.nodup_finRange _) (fun other _ different => by
    have distinct : unit.val ≠ other.val := fun same => different (Fin.ext same.symm)
    have kept := Progress.replace_other state.representation.progress unit other distinct
    simp only [Lifecycle.progress, Lifecycle.replace, Representation.replace, kept])

theorem bornAfter_replaceDue (τ : Nat) (free : Bool) :
    ∀ (due : Nat) (state : Lifecycle shape actions config criterion dimension discounts),
      bornAfter τ (Lifecycle.replaceDue free due state).1 ≤
        bornAfter τ state + (Lifecycle.replaceDue free due state).2.length
  | 0, _ => by simp [Lifecycle.replaceDue]
  | due + 1, state => by
    cases selected : state.candidate free with
    | none => simp [Lifecycle.replaceDue, selected]
    | some unit =>
      have rest := bornAfter_replaceDue τ free due (state.replace unit)
      have one := bornAfter_replace τ state unit
      simp only [Lifecycle.replaceDue, selected, List.length_cons]
      omega

theorem bornAfter_test (τ : Nat)
    (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    bornAfter τ (state.test free active).1 ≤
      bornAfter τ state + (state.test free active).2.length := by
  let accrued := (state.score active).accrued free
  have kept : bornAfter τ ((state.score active).withCredit (config.tester.remainder accrued)) =
      bornAfter τ state := by
    simp only [bornAfter, Lifecycle.withCredit_units, Lifecycle.score_birth]
  have := bornAfter_replaceDue τ free (config.tester.due accrued)
    ((state.score active).withCredit (config.tester.remainder accrued))
  rw [kept] at this
  exact this

theorem run_bornAfter (τ : Nat) : ∀
    (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts),
    bornAfter τ (run inputs state).1 ≤ bornAfter τ state + (run inputs state).2.2
  | [], _ => by simp [run]
  | input :: rest, state => by
    have prepared : bornAfter τ (input.prepare state) = bornAfter τ state := by
      simp only [bornAfter, Lifecycle.progress, Cycle.prepare, Lifecycle.advance,
        Representation.advance, (Progress.advance_fields _).1]
    have step := bornAfter_test τ (input.prepare state) input.free input.active
    have later := run_bornAfter τ rest ((input.prepare state).test input.free input.active).1
    simp only [run]
    omega

theorem bornAfter_clock (state : Lifecycle shape actions config criterion dimension discounts) :
    bornAfter state.progress.clock.toNat state = 0 := by
  simp only [bornAfter, List.countP_eq_zero, decide_eq_true_eq, Nat.not_lt]
  intro unit _
  exact state.progress.born unit

theorem run_young (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts) :
    bornAfter state.progress.clock.toNat (run inputs state).1 ≤
      (config.tester.period - 1 + config.units.count * inputs.length) / config.tester.period := by
  have grown := run_bornAfter state.progress.clock.toNat inputs state
  rw [bornAfter_clock] at grown
  exact Nat.le_trans (by omega) (run_replaced_le inputs state)

theorem run_clock : ∀ (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts),
    state.progress.clock.toNat + inputs.length ≤ maxClock →
      (run inputs state).1.progress.clock.toNat = state.progress.clock.toNat + inputs.length
  | [], _, _ => by simp [run]
  | input :: rest, state, room => by
    have advanced :
        (input.prepare state).progress.clock.toNat = state.progress.clock.toNat + 1 := by
      simp only [Lifecycle.progress, Cycle.prepare, Lifecycle.advance, Representation.advance,
        (Progress.advance_fields _).2.2, advanceClock_exact]
      simp only [List.length_cons, Lifecycle.progress] at room
      rw [Nat.min_eq_left (by omega)]
    have tested := (input.prepare state).test_clock input.free input.active
    have later := run_clock rest ((input.prepare state).test input.free input.active).1 (by
      rw [tested, advanced]
      simp only [List.length_cons] at room
      omega)
    simp only [run, List.length_cons]
    rw [later, tested, advanced]
    omega

theorem run_immature (inputs : List (Cycle actions config criterion dimension discounts))
    (state : Lifecycle shape actions config criterion dimension discounts)
    (window : inputs.length = config.tester.maturity + 1)
    (room : state.progress.clock.toNat + inputs.length ≤ maxClock) :
    (List.finRange config.units.count).countP (fun unit => !(run inputs state).1.mature unit) ≤
      (config.tester.period - 1 + config.units.count * inputs.length) / config.tester.period := by
  have clock := run_clock inputs state room
  apply Nat.le_trans _ (run_young inputs state)
  apply List.countP_mono_left
  intro unit _ immature
  simp [Lifecycle.mature] at immature
  simp only [decide_eq_true_eq]
  omega

theorem declared_decay_value :
    AcornVerif.CurrentArithmetic.numerical32 Acorn.Handcrafted.declaredTester.decay =
      16609444 * 2 ^ (-24 : Int) := by
  change (1:ℚ)*16609444*2^(-24:Int) = _
  norm_num

set_option exponentiation.threshold 2048 in
theorem maturity_bias :
    (AcornVerif.CurrentArithmetic.numerical32 Acorn.Handcrafted.declaredTester.decay) ^
        (Acorn.Handcrafted.declaredTester.maturity + 1) < 1 / 20000 := by
  rw [declared_decay_value]
  change ((16609444 : ℚ) * 2 ^ (-24 : Int)) ^ (1000 + 1) < 1 / 20000
  norm_num

end AcornVerif.Retirement
