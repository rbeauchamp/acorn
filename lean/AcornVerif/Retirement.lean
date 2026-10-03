/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureLifecycle
import AcornVerif.CurrentArithmetic
import Acorn.Handcrafted.FeatureProfile
import Mathlib.Tactic.NormNum

/-!
# Turnover by construction

These theorems concern the executed `Lifecycle.advance` and `Lifecycle.test`,
composed as the agent composes them at the end of every frame: the clock advances,
the learners change in any way that leaves the representation, then the tester
runs. With replacement rate `ρ = 1/period` accrued per eligible unit, the number
of replacements over any run is exactly `⌊(c₀ + Σ nₜ)/period⌋`, where `c₀` is the stored
credit and `nₜ` the eligible count at each test. Consequently a replacement occurs within
`⌈period/k⌉` tests whenever at least `k` units are eligible at each of them
(`⌈1/(ρk)⌉` steps), and no more than `⌊(period − 1 + L·N)/period⌋` units of a bank
of `N` can be younger than `L` steps. Both are counting arguments over the
tester's own state, with no hypothesis on the stream or on learner values.

The same bound over *mature* units does not hold: away from a free boundary a
held unit is mature but not eligible, so it accrues no credit. Each of the
`h = skillCount` slots holds at most one unit, so `k` mature units leave at least
`k − h` eligible, and a replacement occurs within `⌈period/(k − h)⌉` tests whenever
at least `k > h` units are mature at each of them.

The agent's learners write only the consumer ensemble; `Lifecycle.advance` and
`Lifecycle.test` are the only writers of the representation. That structural
fact links `run` to `Agent.act`; it is read from the owning definitions, not
restated here as a theorem about the whole agent transition.
-/

namespace AcornVerif.Retirement
open Acorn.Features

variable {shape : PatchShape} {config : Config} {criterion : Criterion}
  {dimension : Acorn.Dimension} {discounts : List Acorn.Discount}

/-- One end-of-frame cycle: any learner update, the frame's free-boundary flag and
the frame's unit outputs. -/
structure Cycle (config : Config) (criterion : Criterion) (dimension : Acorn.Dimension)
    (discounts : List Acorn.Discount) where
  /-- Learning between tests; it writes only the consumers. -/
  learn : Ensemble config criterion dimension discounts →
    Ensemble config criterion dimension discounts
  /-- Whether the test runs at a free boundary. -/
  free : Bool
  /-- The frame's unit outputs. -/
  active : Vector Bool config.units.count

/-- The state a cycle tests: the advanced clock and the updated learners. -/
def Cycle.prepare (input : Cycle config criterion dimension discounts)
    (state : Lifecycle shape config criterion dimension discounts) :
    Lifecycle shape config criterion dimension discounts :=
  { state.advance with consumers := input.learn state.advance.consumers }

/-- Run cycles, recording each test's eligible count and the total replaced. -/
def run : List (Cycle config criterion dimension discounts) →
    Lifecycle shape config criterion dimension discounts →
      Lifecycle shape config criterion dimension discounts × List Nat × Nat
  | [], state => (state, [], 0)
  | input :: rest, state =>
    let prepared := input.prepare state
    let tested := prepared.test input.free input.active
    let later := run rest tested.1
    (later.1, prepared.eligibleCount input.free :: later.2.1, tested.2.length + later.2.2)

/-- One eligible count is recorded per cycle. -/
theorem run_length : ∀ (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts),
    (run inputs state).2.1.length = inputs.length
  | [], _ => rfl
  | _ :: rest, state => by simp [run, run_length rest]

/-- Credit balance over any run: `period · replaced + c_final = c₀ + Σ nₜ`. -/
theorem run_balance : ∀ (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts),
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

/-- **Turnover by construction.** The number replaced over any run is exactly
`⌊(c₀ + Σ nₜ)/period⌋`. -/
theorem run_replaced (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts) :
    (run inputs state).2.2 =
      (state.progress.credit.val + (run inputs state).2.1.sum) / config.tester.period := by
  have balance := run_balance inputs state
  have below := (run inputs state).1.progress.credit.isLt
  rw [← balance, Nat.mul_add_div config.tester.positive, Nat.div_eq_of_lt below, Nat.add_zero]

/-- Every term of a list bounded below by `k` makes its sum at least `k · length`. -/
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

/-- Every term of a list bounded above by `k` makes its sum at most `k · length`. -/
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

/-- A replacement occurs within `⌈period/k⌉` tests whenever at least `k` units are
eligible at each of them. -/
theorem run_turnover (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts) (bound : Nat)
    (eligible : ∀ count ∈ (run inputs state).2.1, bound ≤ count)
    (long : config.tester.period ≤ bound * inputs.length) :
    1 ≤ (run inputs state).2.2 := by
  have total := sum_lower bound _ eligible
  rw [run_length] at total
  rw [run_replaced, Nat.le_div_iff_mul_le config.tester.positive]
  omega

/-- Units mature now. -/
def matureCount (state : Lifecycle shape config criterion dimension discounts) : Nat :=
  (List.finRange config.units.count).countP state.mature

/-- Units some slot holds as its objective. -/
def heldCount (state : Lifecycle shape config criterion dimension discounts) : Nat :=
  (List.finRange config.units.count).countP state.consumers.holds

/-- A count of items satisfying `p` is at most the counts for `q` and `r` together
when every such item satisfies one of them. -/
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

/-- An objective holds at most one unit. -/
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

/-- The slots together hold at most one unit each. -/
theorem heldCount_le_slots :
    ∀ (skills : List (Skill config criterion dimension discounts)),
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

/-- **Bounded holding.** At most one unit per slot is held, whatever the learner values. -/
theorem heldCount_le (state : Lifecycle shape config criterion dimension discounts) :
    heldCount state ≤ Acorn.FeatureConstants.skillCount := by
  have bound := heldCount_le_slots (criterion := criterion) state.consumers.skills.toList
  rw [Vector.length_toList] at bound
  exact bound

/-- Every mature unit is eligible or held, so `k` mature units leave at least
`k − h` eligible when `h` are held. -/
theorem mature_le (state : Lifecycle shape config criterion dimension discounts) (free : Bool) :
    matureCount state ≤ state.eligibleCount free + heldCount state :=
  countP_le_add _ _ _ _ fun unit _ mature => by
    cases held : state.consumers.holds unit
    · left
      simp [Lifecycle.eligible, mature, held]
    · exact Or.inr rfl

/-- Eligible counts never exceed the bank. -/
theorem eligibleCount_le (state : Lifecycle shape config criterion dimension discounts)
    (free : Bool) : state.eligibleCount free ≤ config.units.count := by
  have := List.countP_le_length (p := state.eligible free) (l := List.finRange config.units.count)
  simpa [Lifecycle.eligibleCount] using this

/-- Every recorded count is an eligible count, so it is at most the bank size. -/
theorem run_counts_le : ∀ (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts),
    ∀ count ∈ (run inputs state).2.1, count ≤ config.units.count
  | [], _, _, member => by simp [run] at member
  | input :: rest, state, count, member => by
    simp only [run, List.mem_cons] at member
    rcases member with same | later
    · subst same
      exact eligibleCount_le _ _
    · exact run_counts_le rest _ count later

/-- At least `bound` units are mature at every test of a run. -/
def MatureAtEach (bound : Nat) : List (Cycle config criterion dimension discounts) →
    Lifecycle shape config criterion dimension discounts → Prop
  | [], _ => True
  | input :: rest, state =>
    bound ≤ matureCount (input.prepare state) ∧
      MatureAtEach bound rest ((input.prepare state).test input.free input.active).1

/-- With at least `k` mature units at each test, every recorded eligible count is
at least `k − skillCount`. -/
theorem run_counts_mature (bound : Nat) :
    ∀ (inputs : List (Cycle config criterion dimension discounts))
      (state : Lifecycle shape config criterion dimension discounts),
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

/-- **Mature-count turnover.** A replacement occurs within `⌈period/(k − h)⌉` tests
whenever at least `k` units are mature at each of them, where `h = skillCount`
bounds the held units; the hypothesis `period ≤ (k − h)·L` forces `k > h`. -/
theorem run_mature_turnover (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts) (bound : Nat)
    (mature : MatureAtEach bound inputs state)
    (long : config.tester.period ≤ (bound - Acorn.FeatureConstants.skillCount) * inputs.length) :
    1 ≤ (run inputs state).2.2 :=
  run_turnover inputs state _ (run_counts_mature bound inputs state mature) long

/-- At most `⌊(period − 1 + L·N)/period⌋` replacements occur in `L` cycles. -/
theorem run_replaced_le (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts) :
    (run inputs state).2.2 ≤
      (config.tester.period - 1 + config.units.count * inputs.length) / config.tester.period := by
  have total := sum_upper config.units.count _ (run_counts_le inputs state)
  rw [run_length] at total
  have credit := state.progress.credit.isLt
  rw [run_replaced]
  apply Nat.div_le_div_right
  omega

/-- Units born after clock `τ`. -/
def bornAfter (τ : Nat) (state : Lifecycle shape config criterion dimension discounts) : Nat :=
  (List.finRange config.units.count).countP fun unit =>
    decide (τ < state.progress.units[unit.val].birth.toNat)

/-- Changing one element's predicate raises a duplicate-free count by at most one. -/
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

/-- One replacement adds at most one unit born after `τ`. -/
theorem bornAfter_replace (τ : Nat) (state : Lifecycle shape config criterion dimension discounts)
    (unit : Fin config.units.count) :
    bornAfter τ (state.replace unit) ≤ bornAfter τ state + 1 :=
  countP_le_succ _ _ unit _ (List.nodup_finRange _) (fun other _ different => by
    have distinct : unit.val ≠ other.val := fun same => different (Fin.ext same.symm)
    have kept := Progress.replace_other state.representation.progress unit other distinct
    simp only [Lifecycle.progress, Lifecycle.replace, Representation.replace, kept])

/-- The units born after `τ` grow by at most the number replaced. -/
theorem bornAfter_replaceDue (τ : Nat) (free : Bool) :
    ∀ (due : Nat) (state : Lifecycle shape config criterion dimension discounts),
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

/-- Scoring, crediting, advancing and learning change no birth. -/
theorem bornAfter_test (τ : Nat) (state : Lifecycle shape config criterion dimension discounts)
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

/-- Units born after any clock `τ` grow by at most the number replaced over a run. -/
theorem run_bornAfter (τ : Nat) : ∀ (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts),
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

/-- No unit is born after the current clock. -/
theorem bornAfter_clock (state : Lifecycle shape config criterion dimension discounts) :
    bornAfter state.progress.clock.toNat state = 0 := by
  simp only [bornAfter, List.countP_eq_zero, decide_eq_true_eq, Nat.not_lt]
  intro unit _
  exact state.progress.born unit

/-- **Bounded youth.** In a bank of `N` units, at most `⌊(period − 1 + L·N)/period⌋`
units are born during any `L` cycles, whatever the stream and learner values. -/
theorem run_young (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts) :
    bornAfter state.progress.clock.toNat (run inputs state).1 ≤
      (config.tester.period - 1 + config.units.count * inputs.length) / config.tester.period := by
  have grown := run_bornAfter state.progress.clock.toNat inputs state
  rw [bornAfter_clock] at grown
  exact Nat.le_trans (by omega) (run_replaced_le inputs state)

/-- Before saturation each cycle advances the clock by exactly one step. -/
theorem run_clock : ∀ (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts),
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

/-- **Bounded immaturity.** After `m + 1` unsaturated cycles, every unit that is not
yet mature was born during them, so at most `⌊(period − 1 + (m+1)·N)/period⌋` of the
`N` units are immature. -/
theorem run_immature (inputs : List (Cycle config criterion dimension discounts))
    (state : Lifecycle shape config criterion dimension discounts)
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

/-- The declared decay word is `16609444 · 2⁻²⁴`, the binary32 word nearest 0.99. -/
theorem declared_decay_value :
    AcornVerif.CurrentArithmetic.numerical32 Acorn.Handcrafted.declaredTester.decay =
      16609444 * 2 ^ (-24 : Int) := by
  change (1:ℚ)*16609444*2^(-24:Int) = _
  norm_num

set_option exponentiation.threshold 2048 in
/-- The omitted Adam-style bias correction is bounded for eligible units. The
source divides its running utility by `1 − η^age` (arXiv:2306.13812v3, eq. (8),
p. 21) and the released implementation does so for every utility type. With the
declared decay and maturity, `η^(m+1) < 5·10⁻⁵`, so every eligible unit's trace is
within a factor `1 − η^(m+1) > 0.99995` of its corrected value; the omission can
change only which of two utilities within that relative distance is smaller. This
is a real-arithmetic statement about the running average, not a bound on rounded
machine words. -/
theorem maturity_bias :
    (AcornVerif.CurrentArithmetic.numerical32 Acorn.Handcrafted.declaredTester.decay) ^
        (Acorn.Handcrafted.declaredTester.maturity + 1) < 1 / 20000 := by
  rw [declared_decay_value]
  change ((16609444 : ℚ) * 2 ^ (-24 : Int)) ^ (1000 + 1) < 1 / 20000
  norm_num

end AcornVerif.Retirement
