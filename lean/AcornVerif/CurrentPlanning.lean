/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentBackupBounds
import AcornVerif.CurrentRetirement
import AcornVerif.FloatLibBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Expectation-model planning contracts

Sutton, Machado, Holland, Szepesvari, Timbers, Tanner and White,
*Reward-Respecting Subtasks for Model-Based Reinforcement Learning*, Artificial
Intelligence 324 (2023) 104001, arXiv:2202.03466v4, §5, equation (19), p. 16,
backs up `r̂(x, o) + v̂(n̂(x, o), w)` with the current weights `w`. Wan, Abbas,
White, White and Sutton, *Planning with Expectation Models*, IJCAI 2019,
arXiv:1904.01191, §4, equations (1)–(2), show that a value function linear in the
features loses nothing when the expected next feature vector replaces the
distribution over next feature vectors.

The first part is real arithmetic and concerns no executed definition.
`expectation_linear` is Wan et al.'s equality for one linear value.
Acorn's value function is the nominal value of several linear action values, so
that equality holds for each action value and not for their maximum:
`expectation_maximum_le` is the inequality that replaces it, and
`expectation_maximum_eq` its equality case. `backup_propagation` is the
dependence of a backed-up action value on the value weights, and
`deterministic_backup` shows that the ranked part plus the residual is the whole
discounted value of a deterministic outcome under unchanged weights.

The second part concerns the executed definitions of `Acorn.Models`.
`ranked_value_rounding` bounds the distance between each executed action value of
a predicted feature vector and the exact dot product of the stored words, and
`discounted_backup_rounding` bounds the distance between the executed discounted
backed-up value and the same expression in exact arithmetic. Each product and
each addition is the exact result rounded once to nearest-even
(`AcornVerif.FloatLibBridge`), and the two horizon projections are exact. The
rounding bound assumes at most 64 ranked positions, which `default_width` shows
for the 16 384-slot dimension; the finiteness and magnitude statements hold for
every dimension. `differential_target_bound` keeps the differential backed-up
value finite; the rounding of the nominal policy mean, which the executing code
evaluates in binary64, is not bounded here.

The last part states storage and work. Native primitive and compiler
correspondence remain the arithmetic layer's declared trust boundary.
-/

open Acorn Acorn.Features
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentPrediction
open AcornVerif.CurrentLearner AcornVerif.CurrentFeatureConsumers
open AcornVerif.CurrentBackupBounds AcornVerif.CurrentModelArithmetic AcornVerif.FloatLibBridge

namespace AcornVerif.CurrentPlanning

/-! ## Real arithmetic -/

section Identities
variable {outcomes features actions : Type} [Fintype outcomes] [Fintype features]
  [Fintype actions]

/-- Wan et al. (2019), §4, equations (1)–(2): for one linear value with weights
`weight`, the expected value of the next feature vector equals the value of the
expected next feature vector, for every finite distribution `mass` over outcomes. -/
theorem expectation_linear (mass : outcomes → ℚ) (outcome : outcomes → features → ℚ)
    (weight : features → ℚ) :
    ∑ i, mass i * ∑ j, weight j * outcome i j =
      ∑ j, weight j * ∑ i, mass i * outcome i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- With several linear action values, the maximum over actions of the value of the
expected feature vector is at most the expected maximum: an expectation model
under a maximum never overestimates the distribution-model backup. -/
theorem expectation_maximum_le [Nonempty actions] (mass : outcomes → ℚ)
    (nonnegative : ∀ i, 0 ≤ mass i) (outcome : outcomes → features → ℚ)
    (weight : actions → features → ℚ) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ j, weight a j * ∑ i, mass i * outcome i j) ≤
      ∑ i, mass i * Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ j, weight a j * outcome i j) := by
  apply Finset.sup'_le
  intro a _
  rw [← expectation_linear]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun a => ∑ j, weight a j * outcome i j) (Finset.mem_univ a))
    (nonnegative i)

/-- The two agree when one action is maximal at every outcome, which includes every
deterministic outcome: then the expectation model loses nothing under the maximum. -/
theorem expectation_maximum_eq [Nonempty actions] (mass : outcomes → ℚ)
    (nonnegative : ∀ i, 0 ≤ mass i) (outcome : outcomes → features → ℚ)
    (weight : actions → features → ℚ) (best : actions)
    (dominates : ∀ i a, ∑ j, weight a j * outcome i j ≤ ∑ j, weight best j * outcome i j) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ j, weight a j * ∑ i, mass i * outcome i j) =
      ∑ i, mass i * Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ j, weight a j * outcome i j) := by
  apply le_antisymm (expectation_maximum_le mass nonnegative outcome weight)
  have each : ∀ i, Finset.univ.sup' Finset.univ_nonempty
      (fun a => ∑ j, weight a j * outcome i j) = ∑ j, weight best j * outcome i j := by
    intro i
    exact le_antisymm (Finset.sup'_le _ _ fun a _ => dominates i a)
      (Finset.le_sup' (fun a => ∑ j, weight a j * outcome i j) (Finset.mem_univ best))
  calc
    ∑ i, mass i * Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ j, weight a j * outcome i j) =
        ∑ i, mass i * ∑ j, weight best j * outcome i j :=
      Finset.sum_congr rfl fun i _ => by rw [each i]
    _ = ∑ j, weight best j * ∑ i, mass i * outcome i j := expectation_linear mass outcome _
    _ ≤ _ := Finset.le_sup' (fun a => ∑ j, weight a j * ∑ i, mass i * outcome i j)
      (Finset.mem_univ best)

/-- A change of the value weights changes one backed-up action value of a fixed
predicted feature vector by exactly the weight change applied to that vector. A
scalar continuation has no such term: its value does not read the weights. -/
theorem backup_propagation (before after expected : features → ℚ) :
    ∑ j, after j * expected j - ∑ j, before j * expected j =
      ∑ j, (after j - before j) * expected j := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- For a deterministic outcome reached with discount `discount`, the maximum over
the ranked parts of the discounted action values plus the discounted residual is
the discounted maximum of the complete action values. -/
theorem deterministic_backup [Nonempty actions] (discount : ℚ) (nonnegative : 0 ≤ discount)
    (complete ranked : actions → ℚ) :
    Finset.univ.sup' Finset.univ_nonempty (fun a => discount * ranked a) +
        discount * (Finset.univ.sup' Finset.univ_nonempty complete -
          Finset.univ.sup' Finset.univ_nonempty ranked) =
      discount * Finset.univ.sup' Finset.univ_nonempty complete := by
  have scaled : Finset.univ.sup' Finset.univ_nonempty (fun a => discount * ranked a) =
      discount * Finset.univ.sup' Finset.univ_nonempty ranked := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun a _ => mul_le_mul_of_nonneg_left
        (Finset.le_sup' ranked (Finset.mem_univ a)) nonnegative
    · obtain ⟨a, _, attained⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty ranked
      rw [attained]
      exact Finset.le_sup' (fun a => discount * ranked a) (Finset.mem_univ a)
  rw [scaled]
  ring

end Identities

/-! ## Executed action values of a predicted feature vector -/

variable {criterion : Criterion} {dimension : Dimension}

/-- The numerical value of the zero word. -/
theorem zero_numeric : numerical32 Binary32.zero = 0 := by decide

/-- Rounding allowance of one term of an executed action value: one product rounded
at magnitude at most `2^7` and one partial sum rounded at magnitude at most `2^13`. -/
def termRadius : ℚ := 1 / 131072 + 1 / 2048

/-- Every expected feature value is a finite word between zero and one. -/
theorem expectation_numeric (value : Expectation) :
    value.value.Finite ∧ 0 ≤ numerical32 value.value ∧ numerical32 value.value ≤ 1 := by
  have bounds := CurrentModels.interval_numeric expectationRange value
  have lower : numerical32 expectationRange.lower = 0 := by decide
  have upper : numerical32 expectationRange.upper = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  rw [lower, upper] at bounds
  exact ⟨value.legal.1, bounds.1, bounds.2⟩

/-- One executed term of an action value: the product of a legal value weight and an
expected feature value is finite, within `2^(-17)` of the exact product, and no
larger than the weight bound. -/
theorem term_bound {rule : ValueRule} (weight : Weight rule) (expected : Expectation) :
    (weight.value.mul expected.value).Finite ∧
      |numerical32 (weight.value.mul expected.value) -
        numerical32 weight.value * numerical32 expected.value| ≤ 1 / 131072 ∧
      |numerical32 (weight.value.mul expected.value)| ≤ 101 := by
  have w := weight_numerical_bound rule weight
  have n := expectation_numeric expected
  have product : |numerical32 weight.value * numerical32 expected.value| ≤ 101 := by
    rw [abs_mul, abs_of_nonneg n.2.1]
    calc
      |numerical32 weight.value| * numerical32 expected.value ≤ 101 * 1 :=
        mul_le_mul w.2 n.2.2 n.2.1 (by norm_num)
      _ = 101 := by norm_num
  have rounded := binary32_rounded_mul weight.value expected.value w.1 n.1 (by linarith)
  have cap := binary32_rounded_exact (Binary32.mk 0x42ca0000) (by decide)
  have capValue : numerical32 (Binary32.mk 0x42ca0000) = 101 := by
    change (1 : ℚ) * 13238272 * (2 : ℚ) ^ (-17 : Int) = 101
    norm_num
  rw [capValue] at cap
  refine ⟨rounded.1, binary32_mul_unit_error _ _ w.1 n.1 rounded.1 (by linarith),
    abs_le.mpr ⟨?_, ?_⟩⟩
  · exact Rounded.mono cap.neg rounded.2 (by linarith [(abs_le.mp product).1])
  · exact Rounded.mono rounded.2 cap (by linarith [(abs_le.mp product).2])

/-- The executed left-to-right sum of term words stays finite, within the summed
rounding allowance of the exact sum of the terms' exact values, and within the
summed term bound, while its magnitude has room below `2^13`. -/
theorem sum_rounding (terms : List (Binary32 × ℚ)) (initial : Binary32)
    (finite : initial.Finite)
    (room : |numerical32 initial| + 102 * (terms.length : ℚ) ≤ 8192)
    (close : ∀ term ∈ terms, term.1.Finite ∧ |numerical32 term.1| ≤ 101 ∧
      |numerical32 term.1 - term.2| ≤ 1 / 131072) :
    (Binary32.sumFrom initial (terms.map Prod.fst)).Finite ∧
      |numerical32 (Binary32.sumFrom initial (terms.map Prod.fst)) -
        (numerical32 initial + (terms.map Prod.snd).sum)| ≤
          (terms.length : ℚ) * termRadius ∧
      |numerical32 (Binary32.sumFrom initial (terms.map Prod.fst))| ≤
        |numerical32 initial| + 102 * (terms.length : ℚ) := by
  induction terms generalizing initial with
  | nil => simp [Binary32.sumFrom, finite]
  | cons term rest ih =>
    obtain ⟨termFinite, termBound, termClose⟩ := close term (by simp)
    have count : (((term :: rest).length : Nat) : ℚ) = (rest.length : ℚ) + 1 := by simp
    rw [count] at room
    have nonnegative : (0 : ℚ) ≤ (rest.length : ℚ) := Nat.cast_nonneg _
    have inner := abs_add_le (numerical32 initial) (numerical32 term.1)
    have exactBound : |numerical32 initial + numerical32 term.1| ≤ 8192 := by linarith
    have sum := binary32_rounded_add initial term.1 finite termFinite (by linarith)
    have error := binary32_add_sum_error initial term.1 finite termFinite sum.1 exactBound
    have magnitude : |numerical32 (initial.add term.1)| ≤ |numerical32 initial| + 102 := by
      have triangle := abs_add_le
        (numerical32 (initial.add term.1) - (numerical32 initial + numerical32 term.1))
        (numerical32 initial + numerical32 term.1)
      rw [sub_add_cancel] at triangle
      linarith
    have tail := ih (initial.add term.1) sum.1 (by linarith)
      (fun other member => close other (List.mem_cons_of_mem term member))
    have same : Binary32.sumFrom initial ((term :: rest).map Prod.fst) =
        Binary32.sumFrom (initial.add term.1) (rest.map Prod.fst) := by
      simp [Binary32.sumFrom]
    have expand : ((rest.length : ℚ) + 1) * termRadius =
        (rest.length : ℚ) * termRadius + termRadius := by ring
    have step : (1 : ℚ) / 2048 + 1 / 131072 = termRadius := by
      unfold termRadius
      norm_num
    rw [same, count, expand]
    refine ⟨tail.1, ?_, by linarith [tail.2.2]⟩
    have split : numerical32 (Binary32.sumFrom (initial.add term.1) (rest.map Prod.fst)) -
        (numerical32 initial + ((term :: rest).map Prod.snd).sum) =
        (numerical32 (Binary32.sumFrom (initial.add term.1) (rest.map Prod.fst)) -
          (numerical32 (initial.add term.1) + (rest.map Prod.snd).sum)) +
        ((numerical32 (initial.add term.1) - (numerical32 initial + numerical32 term.1)) +
          (numerical32 term.1 - term.2)) := by
      simp only [List.map_cons, List.sum_cons]
      ring
    rw [split]
    have outer := abs_add_le
      (numerical32 (Binary32.sumFrom (initial.add term.1) (rest.map Prod.fst)) -
        (numerical32 (initial.add term.1) + (rest.map Prod.snd).sum))
      ((numerical32 (initial.add term.1) - (numerical32 initial + numerical32 term.1)) +
        (numerical32 term.1 - term.2))
    have pair := abs_add_le
      (numerical32 (initial.add term.1) - (numerical32 initial + numerical32 term.1))
      (numerical32 term.1 - term.2)
    linarith [tail.2.1]

/-- The executed product word and the exact product of one occupied position, for
one meta action's value weights. -/
def rankedTerm (value : ValueFunction criterion dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat) (entry : RankIdx dimension × FeatIdx dimension) :
    Binary32 × ℚ :=
  (((value.controller.learners.get action).state.weights.get entry.2).value.mul
      (expected.get entry.1).value,
    numerical32 ((value.controller.learners.get action).state.weights.get entry.2).value *
      numerical32 (expected.get entry.1).value)

/-- The exact action value of an expected feature vector at the ranked slots: the dot
product `Σ_j w_a[slot j] · n_j` of the stored words, in exact arithmetic. For a linear
value function this is `v̂(n̂(x, o), w)` of equation (19). -/
def exactRankedValue (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat) : ℚ :=
  ((ranked.occupied.map (rankedTerm value expected action)).map Prod.snd).sum

/-- Each executed action value is the ordered sum of its executed term words. -/
theorem rankedValues_get (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat) :
    (value.rankedValues ranked expected).get action =
      Binary32.sumFrom .zero ((ranked.occupied.map (rankedTerm value expected action)).map
        Prod.fst) := by
  simp [ValueFunction.rankedValues, Binary32.sumMap_eq, vector_get, rankedTerm,
    Function.comp_def]

/-- Every executed term is finite, bounded and within `2^(-17)` of its exact product. -/
theorem rankedTerm_close (value : ValueFunction criterion dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat) (entry : RankIdx dimension × FeatIdx dimension) :
    (rankedTerm value expected action entry).1.Finite ∧
      |numerical32 (rankedTerm value expected action entry).1| ≤ 101 ∧
      |numerical32 (rankedTerm value expected action entry).1 -
        (rankedTerm value expected action entry).2| ≤ 1 / 131072 := by
  have bound := term_bound
    ((value.controller.learners.get action).state.weights.get entry.2) (expected.get entry.1)
  exact ⟨bound.1, bound.2.2, bound.2.1⟩

/-- Backup identity with its rounding bound, per action value. For every value
function, ranking and predicted feature vector with at most 64 ranked positions, the
executed action value is finite and within one term allowance per occupied position
of the exact dot product of the stored words. -/
theorem ranked_value_rounding (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat)
    (narrow : (rankDimension dimension).capacity ≤ 64) :
    ((value.rankedValues ranked expected).get action).Finite ∧
      |numerical32 ((value.rankedValues ranked expected).get action) -
        exactRankedValue value ranked expected action| ≤
          (ranked.occupied.length : ℚ) * termRadius ∧
      |numerical32 ((value.rankedValues ranked expected).get action)| ≤
        102 * (ranked.occupied.length : ℚ) := by
  rw [rankedValues_get]
  have count : (ranked.occupied.map (rankedTerm value expected action)).length =
      ranked.occupied.length := List.length_map _
  have few : (ranked.occupied.length : ℚ) ≤ 64 := by
    exact_mod_cast le_trans ranked.occupied_length narrow
  have sum := sum_rounding (ranked.occupied.map (rankedTerm value expected action)) .zero
    (by decide) (by rw [zero_numeric, abs_zero, count]; linarith)
    (by
      intro term member
      obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
      exact rankedTerm_close value expected action entry)
  rw [count, zero_numeric, abs_zero, zero_add, zero_add] at sum
  exact sum

/-- For every dimension, every executed action value is finite and inside the
ordered-sum envelope of its occupied positions. -/
theorem ranked_value_bound (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat) :
    ((value.rankedValues ranked expected).get action).Finite ∧
      |numerical32 ((value.rankedValues ranked expected).get action)| ≤
        predictionRadius ranked.occupied.length := by
  rw [rankedValues_get]
  have sum := prediction_sumFrom_bound 0 .zero
    ((ranked.occupied.map (rankedTerm value expected action)).map Prod.fst) (by decide)
    (by change |(0 : ℚ)| ≤ (0 : ℚ) * 256; norm_num)
    (by
      intro word member
      obtain ⟨term, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
      have close := rankedTerm_close value expected action entry
      exact ⟨close.1, close.2.1⟩)
  simpa only [List.length_map, Nat.zero_add] using sum

/-- An action value reads the value weights at the occupied slots only: two value
functions that agree there give the same word. -/
theorem ranked_values_congr (first second : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat)
    (same : ∀ entry ∈ ranked.occupied,
      (first.controller.learners.get action).state.weights.get entry.2 =
        (second.controller.learners.get action).state.weights.get entry.2) :
    (first.rankedValues ranked expected).get action =
      (second.rankedValues ranked expected).get action := by
  rw [rankedValues_get, rankedValues_get]
  congr 2
  exact List.map_congr_left fun entry member => by simp only [rankedTerm, same entry member]

/-- Dependence on the value weights, over the stored words: between two value
functions the exact action value of a fixed predicted vector differs by the weight
change at each occupied slot times that slot's predicted activity. This is the
look-ahead term of one action, before the maximum or mean over actions, the range
projections and rounding. -/
theorem ranked_value_propagation (before after : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat) :
    exactRankedValue after ranked expected action -
        exactRankedValue before ranked expected action =
      (ranked.occupied.map fun entry =>
        (numerical32 ((after.controller.learners.get action).state.weights.get entry.2).value -
          numerical32 ((before.controller.learners.get action).state.weights.get entry.2).value) *
          numerical32 (expected.get entry.1).value).sum := by
  unfold exactRankedValue
  induction ranked.occupied with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    simp only [rankedTerm]
    ring

/-- With no occupied position an action value is the zero word: the look-ahead then
reads no value weight. -/
theorem ranked_values_vacant (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (action : Action metaCount.word.toNat) (vacant : ranked.occupied = []) :
    (value.rankedValues ranked expected).get action = Binary32.zero := by
  rw [rankedValues_get, vacant]
  rfl

/-! ## The ordered maximum and the nominal mean -/

/-- A fold that keeps one of its two arguments at every step returns its start or a
list element. -/
theorem fold_choice_member {α : Type} (choose : α → α → α)
    (either : ∀ kept item, choose kept item = kept ∨ choose kept item = item)
    (items : List α) (first : α) : items.foldl choose first ∈ first :: items := by
  induction items generalizing first with
  | nil => simp
  | cons head tail ih =>
    have inner := ih (choose first head)
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp inner with same | later
    · rcases either first head with kept | taken
      · rw [same, kept]
        simp
      · rw [same, taken]
        simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ later)

/-- The ordered maximum fold dominates its start and every finite list element. -/
theorem fold_best_dominates (words : List Binary32) (first : Binary32)
    (finite : ∀ word ∈ first :: words, word.Finite) :
    ∀ word ∈ first :: words, numerical32 word ≤ numerical32
      (words.foldl (fun best value => if best.less value then value else best) first) := by
  induction words generalizing first with
  | nil =>
    intro word member
    have same : word = first := by simpa using member
    subst same
    exact le_refl _
  | cons head tail ih =>
    intro word member
    have firstFinite := finite first (by simp)
    have headFinite := finite head (by simp)
    have compare := numerical32_less first head firstFinite headFinite
    have chosenFinite : (if first.less head then head else first).Finite := by
      split <;> assumption
    have rest : ∀ other ∈ (if first.less head then head else first) :: tail,
        other.Finite := by
      intro other inside
      rcases List.mem_cons.mp inside with same | later
      · rw [same]
        exact chosenFinite
      · exact finite other (by simp [later])
    have tailBound := ih (if first.less head then head else first) rest
    have chosenBound := tailBound (if first.less head then head else first) (by simp)
    have firstLe : numerical32 first ≤
        numerical32 (if first.less head then head else first) := by
      split
      · rename_i less
        rw [compare] at less
        exact le_of_lt (of_decide_eq_true less)
      · exact le_refl _
    have headLe : numerical32 head ≤
        numerical32 (if first.less head then head else first) := by
      split
      · exact le_refl _
      · rename_i notLess
        rw [compare] at notLess
        exact not_lt.mp (by simpa using notLess)
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | later
    · rw [same]
      exact le_trans firstLe chosenBound
    · rcases List.mem_cons.mp later with same | inTail
      · rw [same]
        exact le_trans headLe chosenBound
      · exact tailBound word (List.mem_cons_of_mem _ inTail)

variable {count : Word.Count}

/-- A snapshot's words are its first word followed by the rest. -/
theorem snapshot_words (snapshot : PolicySnapshot count) :
    snapshot.values.toList =
      snapshot.values.get (firstAction count) :: snapshot.values.toList.drop 1 := by
  have positive : 0 < snapshot.values.toList.length := by
    rw [Vector.length_toList]
    exact count.positive
  have head := List.drop_eq_getElem_cons positive
  rw [List.drop_zero] at head
  rw [head]
  simp [firstAction, vector_get]

/-- A word is one of a snapshot's words exactly when some action has it. -/
theorem snapshot_member (snapshot : PolicySnapshot count) (word : Binary32) :
    word ∈ snapshot.values.toList ↔ ∃ action, word = snapshot.values.get action := by
  constructor
  · intro inside
    obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp inside
    have small : index < count.word.toNat := by simpa using bound
    exact ⟨⟨index, small⟩, by simp [vector_get, ← same]⟩
  · rintro ⟨action, rfl⟩
    exact List.mem_iff_getElem.mpr ⟨action.val, by simp, by simp [vector_get]⟩

/-- The ordered maximum of finite action values is one of them and dominates each. -/
theorem best_spec (snapshot : PolicySnapshot count)
    (finite : ∀ action, (snapshot.values.get action).Finite) :
    (∃ action, snapshot.best = snapshot.values.get action) ∧
      ∀ action, numerical32 (snapshot.values.get action) ≤ numerical32 snapshot.best := by
  have words := snapshot_words snapshot
  have allFinite : ∀ word ∈ snapshot.values.get (firstAction count) ::
      snapshot.values.toList.drop 1, word.Finite := by
    intro word inside
    rw [← words] at inside
    obtain ⟨action, rfl⟩ := (snapshot_member snapshot word).mp inside
    exact finite action
  have member := fold_choice_member
    (fun best value : Binary32 => if best.less value then value else best)
    (fun kept item => by by_cases less : kept.less item <;> simp [less])
    (snapshot.values.toList.drop 1) (snapshot.values.get (firstAction count))
  rw [← words] at member
  refine ⟨(snapshot_member snapshot _).mp member, fun action => ?_⟩
  exact fold_best_dominates (snapshot.values.toList.drop 1)
    (snapshot.values.get (firstAction count)) allFinite (snapshot.values.get action)
    (by rw [← words]; exact (snapshot_member snapshot _).mpr ⟨action, rfl⟩)

/-- Saturation between two finite words is finite and no larger than the larger of
them, for every input word including NaNs and infinities. -/
theorem saturate_hull (value lower upper : Binary32) (lowerFinite : lower.Finite)
    (upperFinite : upper.Finite) :
    (value.saturate lower upper).Finite ∧
      |numerical32 (value.saturate lower upper)| ≤
        max |numerical32 lower| |numerical32 upper| := by
  unfold Binary32.saturate
  split
  · exact ⟨lowerFinite, le_max_left _ _⟩
  · split
    · exact ⟨upperFinite, le_max_right _ _⟩
    · rename_i notLow notHigh
      have notNaN : value.isNaN = false := by
        cases nan : value.isNaN
        · rfl
        · simp [nan] at notLow
      have keys : lower.key ≤ value.key ∧ value.key ≤ upper.key := by
        simp only [Binary32.less_eq_key, notNaN, Binary32.finite_not_nan lower lowerFinite,
          Binary32.finite_not_nan upper upperFinite, Bool.not_false, Bool.true_and,
          Bool.false_or, decide_eq_true_eq] at notLow notHigh
        omega
      have finite : value.Finite := by
        have low : lower.magnitude < 0x7f800000 := lowerFinite
        have high : upper.magnitude < 0x7f800000 := upperFinite
        have lowKey : -(lower.magnitude : Int) ≤ lower.key := by
          unfold Binary32.key
          split <;> omega
        have highKey : upper.key ≤ (upper.magnitude : Int) := by
          unfold Binary32.key
          split <;> omega
        have valueKey : value.key = (value.magnitude : Int) ∨
            value.key = -(value.magnitude : Int) := by
          unfold Binary32.key
          split
          · exact Or.inr rfl
          · exact Or.inl rfl
        change value.magnitude < 0x7f800000
        omega
      have low := (numerical32_order lower value lowerFinite finite).mpr keys.1
      have high := (numerical32_order value upper finite upperFinite).mpr keys.2
      refine ⟨finite, abs_le.mpr ⟨?_, ?_⟩⟩
      · have := neg_abs_le (numerical32 lower)
        have := le_max_left |numerical32 lower| |numerical32 upper|
        linarith
      · have := le_abs_self (numerical32 upper)
        have := le_max_right |numerical32 lower| |numerical32 upper|
        linarith

/-- The nominal policy mean of finite, bounded action values is finite and within the
same bound: the executed mean is saturated between two of the action values. -/
theorem expected_bound (snapshot : PolicySnapshot count) (radius : ℚ)
    (bounded : ∀ action, (snapshot.values.get action).Finite ∧
      |numerical32 (snapshot.values.get action)| ≤ radius) :
    snapshot.expected.Finite ∧ |numerical32 snapshot.expected| ≤ radius := by
  have lowerMember := fold_choice_member
    (fun lo v : Binary32 => if v.less lo then v else lo)
    (fun kept item => by by_cases less : item.less kept <;> simp [less])
    snapshot.values.toList (snapshot.values.get (firstAction count))
  have lowerWord : ∃ action,
      snapshot.values.toList.foldl (fun lo v : Binary32 => if v.less lo then v else lo)
        (snapshot.values.get (firstAction count)) = snapshot.values.get action := by
    rcases List.mem_cons.mp lowerMember with same | inside
    · exact ⟨firstAction count, same⟩
    · exact (snapshot_member snapshot _).mp inside
  obtain ⟨low, lowerSame⟩ := lowerWord
  obtain ⟨high, upperSame⟩ := (best_spec snapshot fun action => (bounded action).1).1
  have hull : ∀ word : Binary32,
      (word.saturate (snapshot.values.get low) (snapshot.values.get high)).Finite ∧
        |numerical32 (word.saturate (snapshot.values.get low) (snapshot.values.get high))| ≤
          radius := by
    intro word
    have inside := saturate_hull word _ _ (bounded low).1 (bounded high).1
    exact ⟨inside.1, le_trans inside.2 (max_le (bounded low).2 (bounded high).2)⟩
  unfold PolicySnapshot.expected
  simp only [lowerSame, upperSame]
  exact hull _

/-- For every criterion and dimension, the executed nominal value of a predicted
feature vector is finite and inside the ordered-sum envelope of the occupied positions. -/
theorem ranked_nominal_bound (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    (value.rankedNominal ranked expected).Finite ∧
      |numerical32 (value.rankedNominal ranked expected)| ≤
        predictionRadius ranked.occupied.length := by
  have each := fun action => ranked_value_bound value ranked expected action
  cases criterion with
  | discounted =>
    obtain ⟨chosen, same⟩ := (best_spec
      (⟨value.rankedValues ranked expected, value.epsilon⟩ : PolicySnapshot metaCount)
      fun action => (each action).1).1
    change (PolicySnapshot.best (⟨value.rankedValues ranked expected, value.epsilon⟩ :
      PolicySnapshot metaCount)).Finite ∧ |numerical32 (PolicySnapshot.best
        (⟨value.rankedValues ranked expected, value.epsilon⟩ : PolicySnapshot metaCount))| ≤ _
    rw [same]
    exact each chosen
  | differential =>
    exact expected_bound
      (⟨value.rankedValues ranked expected, value.epsilon⟩ : PolicySnapshot metaCount) _ each

/-! ## The discounted backed-up value -/

/-- The meta-controller has an action, so a maximum over its actions exists. -/
instance : Nonempty (Action metaCount.word.toNat) := ⟨firstAction metaCount⟩

/-- The exact discounted nominal value of an expected feature vector at the ranked
slots: the maximum over meta actions of the exact dot products. -/
def exactRankedBest (value : ValueFunction .discounted dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (exactRankedValue value ranked expected)

/-- The executed discounted look-ahead is within one term allowance per occupied
position of the exact maximum over meta actions: the ordered maximum selects a word
and adds no rounding. -/
theorem ranked_best_rounding (value : ValueFunction .discounted dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity)
    (narrow : (rankDimension dimension).capacity ≤ 64) :
    (value.rankedNominal ranked expected).Finite ∧
      |numerical32 (value.rankedNominal ranked expected) -
        exactRankedBest value ranked expected| ≤ (ranked.occupied.length : ℚ) * termRadius ∧
      |numerical32 (value.rankedNominal ranked expected)| ≤
        102 * (ranked.occupied.length : ℚ) := by
  have each := fun action => ranked_value_rounding value ranked expected action narrow
  have spec := best_spec
    (⟨value.rankedValues ranked expected, value.epsilon⟩ : PolicySnapshot metaCount)
    fun action => (each action).1
  obtain ⟨chosen, same⟩ := spec.1
  have nominal : value.rankedNominal ranked expected =
      (value.rankedValues ranked expected).get chosen := same
  rw [nominal]
  refine ⟨(each chosen).1, abs_le.mpr ⟨?_, ?_⟩, (each chosen).2.2⟩
  · obtain ⟨best, _, attained⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (exactRankedValue value ranked expected)
    have dominated : numerical32 ((value.rankedValues ranked expected).get best) ≤
        numerical32 ((value.rankedValues ranked expected).get chosen) := by
      have largest := spec.2 best
      rw [same] at largest
      exact largest
    have close := (abs_le.mp (each best).2.1).1
    unfold exactRankedBest
    rw [attained]
    linarith
  · have upper : exactRankedValue value ranked expected chosen ≤
        Finset.univ.sup' Finset.univ_nonempty (exactRankedValue value ranked expected) :=
      Finset.le_sup' (exactRankedValue value ranked expected) (Finset.mem_univ chosen)
    have close := (abs_le.mp (each chosen).2.1).2
    unfold exactRankedBest
    linarith

/-- The discounted horizon as a rational. -/
def horizon : ℚ := numerical32 Discount.g99.horizon

/-- Projection onto the discounted prediction range, in exact arithmetic. -/
def clamp (x : ℚ) : ℚ := max (min x horizon) 0

/-- The horizon is nonnegative and at most the weight bound. -/
theorem horizon_bounds : 0 ≤ horizon ∧ horizon ≤ 101 := by
  have finite : Discount.g99.horizon.Finite := Discount.g99.predictionRange.upperFinite
  have lower := (numerical32_order .zero Discount.g99.horizon (by decide) finite).mpr
    Discount.g99.predictionRange.ordered
  have upper := (numerical32_order Discount.g99.horizon (Binary32.mk 0x42ca0000) finite
    (by decide)).mpr (by decide)
  have capValue : numerical32 (Binary32.mk 0x42ca0000) = 101 := by
    change (1 : ℚ) * 13238272 * (2 : ℚ) ^ (-17 : Int) = 101
    norm_num
  rw [zero_numeric] at lower
  rw [capValue] at upper
  exact ⟨lower, upper⟩

/-- The exact projection stays inside the prediction range. -/
theorem clamp_range (x : ℚ) : 0 ≤ clamp x ∧ clamp x ≤ horizon :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) horizon_bounds.1⟩

/-- The exact projection is nonexpansive. -/
theorem clamp_lipschitz (x y : ℚ) : |clamp x - clamp y| ≤ |x - y| := by
  unfold clamp
  exact le_trans (abs_max_sub_max_le_abs _ _ _)
    (le_trans (abs_min_sub_min_le_max _ _ _ _) (by simp))

/-- The executing prediction projection of a finite word is the exact projection of
its value: it selects a stored word and rounds nothing. -/
theorem project_numeric (raw : Binary32) (finite : raw.Finite) :
    numerical32 (Prediction.project .g99 raw).value = clamp (numerical32 raw) := by
  have top : Discount.g99.horizon.Finite := Discount.g99.predictionRange.upperFinite
  have low := numerical32_less raw .zero finite (by decide)
  have high := numerical32_less Discount.g99.horizon raw top finite
  have bounds := horizon_bounds
  change numerical32 (raw.saturate .zero Discount.g99.horizon) = _
  unfold Binary32.saturate clamp horizon
  rw [Binary32.finite_not_nan raw finite, low, high, zero_numeric]
  simp only [Bool.false_or, decide_eq_true_eq]
  split
  · rename_i negative
    rw [zero_numeric]
    exact (max_eq_right (le_trans (min_le_left _ _) (le_of_lt negative))).symm
  · split
    · rename_i above
      rw [min_eq_right (le_of_lt above)]
      exact (max_eq_left bounds.1).symm
    · rename_i notBelow notAbove
      rw [min_eq_left (not_lt.mp notAbove)]
      exact (max_eq_left (not_lt.mp notBelow)).symm

/-- An executed addition followed by the prediction projection is within `2^(-17)` of
the exact sum followed by the exact projection: outside the range both project to the
same endpoint, because rounding is monotone and the endpoints are words, and inside it
the sum is rounded at magnitude below `2^7`. -/
theorem clamped_add (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (bound : |numerical32 left + numerical32 right| ≤ 8589934592) :
    (left.add right).Finite ∧
      |clamp (numerical32 (left.add right)) - clamp (numerical32 left + numerical32 right)| ≤
        1 / 131072 := by
  have sum := binary32_rounded_add left right leftFinite rightFinite bound
  have top := binary32_rounded_exact Discount.g99.horizon
    Discount.g99.predictionRange.upperFinite
  have bounds := horizon_bounds
  refine ⟨sum.1, ?_⟩
  by_cases above : horizon ≤ numerical32 left + numerical32 right
  · have rounded : horizon ≤ numerical32 (left.add right) := Rounded.mono top sum.2 above
    have exactSide : clamp (numerical32 left + numerical32 right) = horizon := by
      unfold clamp
      rw [min_eq_right above, max_eq_left bounds.1]
    have wordSide : clamp (numerical32 (left.add right)) = horizon := by
      unfold clamp
      rw [min_eq_right rounded, max_eq_left bounds.1]
    rw [exactSide, wordSide, sub_self, abs_zero]
    norm_num
  · by_cases below : numerical32 left + numerical32 right ≤ 0
    · have rounded : numerical32 (left.add right) ≤ 0 := Rounded.mono sum.2 rounded_zero below
      have exactSide : clamp (numerical32 left + numerical32 right) = 0 := by
        unfold clamp
        exact max_eq_right (le_trans (min_le_left _ _) below)
      have wordSide : clamp (numerical32 (left.add right)) = 0 := by
        unfold clamp
        exact max_eq_right (le_trans (min_le_left _ _) rounded)
      rw [exactSide, wordSide, sub_self, abs_zero]
      norm_num
    · have small : |numerical32 left + numerical32 right| ≤ 128 :=
        abs_le.mpr ⟨by linarith [not_le.mp below], by linarith [not_le.mp above, bounds.2]⟩
      exact le_trans (clamp_lipschitz _ _)
        (binary32_add_unit_error left right leftFinite rightFinite sum.1 small)

/-- Backup identity with its rounding bound, for the executed discounted backed-up
value. Let `V` be the exact maximum over meta actions of the dot products of the stored
value weights with the stored predicted features, `ρ` the stored residual prediction
and `r` the stored reward prediction. For every model, value function, frame and gain,
with at most 64 ranked positions, the executed target is within one term allowance per
occupied position plus `2^(-16)` of `clamp (r + clamp (V + ρ))`, where `clamp` is the
exact projection onto the prediction range. -/
theorem discounted_backup_rounding
    (reward continuation : Managed (Criterion.config .discounted .demon) dimension)
    (transition : Transition dimension .discounted)
    (value : ValueFunction .discounted dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (narrow : (rankDimension dimension).capacity ≤ 64) :
    let prediction := (Model.discounted reward continuation transition).predict value features age
    |numerical32 (prediction.target gain) -
      clamp (numerical32 prediction.reward.value +
        clamp (exactRankedBest value transition.ranked (transition.expected features) +
          numerical32 (continuation.state.linearPrediction
            (modelInput .discounted features age))))| ≤
      (transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 := by
  intro prediction
  have look := ranked_best_rounding value transition.ranked (transition.expected features) narrow
  have residual := prediction_bound continuation.state (modelInput .discounted features age)
  change (continuation.state.linearPrediction (modelInput .discounted features age)).Finite ∧
    |numerical32 (continuation.state.linearPrediction (modelInput .discounted features age))| ≤
      predictionRadius (modelInput .discounted features age).indices.length at residual
  have radiusCap : predictionRadius (modelInput .discounted features age).indices.length ≤
      4294967296 := by
    unfold predictionRadius
    have := Nat.min_le_right (modelInput .discounted features age).indices.length (2 ^ 24)
    exact_mod_cast Nat.mul_le_mul_right 256 this
  have few : (transition.ranked.occupied.length : ℚ) ≤ 64 := by
    exact_mod_cast le_trans transition.ranked.occupied_length narrow
  have innerBound : |numerical32 (value.rankedNominal transition.ranked
      (transition.expected features)) + numerical32 (continuation.state.linearPrediction
        (modelInput .discounted features age))| ≤ 8589934592 :=
    le_trans (abs_add_le _ _) (by linarith [look.2.2, residual.2])
  have inner := clamped_add _ _ look.1 residual.1 innerBound
  have continuationValue := project_numeric _ inner.1
  have continuationRange := clamp_range (numerical32 ((value.rankedNominal transition.ranked
    (transition.expected features)).add (continuation.state.linearPrediction
      (modelInput .discounted features age))))
  have continuationFinite := (Prediction.project .g99 ((value.rankedNominal transition.ranked
    (transition.expected features)).add (continuation.state.linearPrediction
      (modelInput .discounted features age)))).legal.1
  have rewardBounds := CurrentModels.interval_numeric _ prediction.reward
  have lowerValue : numerical32 (Criterion.discounted.modelRewardRange).lower = 0 := by decide
  rw [lowerValue] at rewardBounds
  have rewardTop : numerical32 (Criterion.discounted.modelRewardRange).upper = horizon := rfl
  rw [rewardTop] at rewardBounds
  have top := horizon_bounds
  rw [← continuationValue] at continuationRange
  have outerBound : |numerical32 prediction.reward.value + numerical32 (Prediction.project .g99
      ((value.rankedNominal transition.ranked (transition.expected features)).add
        (continuation.state.linearPrediction (modelInput .discounted features age)))).value| ≤
      8589934592 :=
    abs_le.mpr ⟨by linarith [rewardBounds.1, continuationRange.1],
      by linarith [rewardBounds.2, continuationRange.2]⟩
  have outer := clamped_add _ _ prediction.reward.legal.1 continuationFinite outerBound
  have target : numerical32 (prediction.target gain) = clamp (numerical32
      (prediction.reward.value.add (Prediction.project .g99
        ((value.rankedNominal transition.ranked (transition.expected features)).add
          (continuation.state.linearPrediction (modelInput .discounted features age)))).value)) :=
    project_numeric _ outer.1
  rw [target]
  have first := clamp_lipschitz
    (numerical32 prediction.reward.value + numerical32 (Prediction.project .g99
      ((value.rankedNominal transition.ranked (transition.expected features)).add
        (continuation.state.linearPrediction (modelInput .discounted features age)))).value)
    (numerical32 prediction.reward.value +
      clamp (exactRankedBest value transition.ranked (transition.expected features) +
        numerical32 (continuation.state.linearPrediction
          (modelInput .discounted features age))))
  have second := clamp_lipschitz
    (numerical32 (value.rankedNominal transition.ranked (transition.expected features)) +
      numerical32 (continuation.state.linearPrediction (modelInput .discounted features age)))
    (exactRankedBest value transition.ranked (transition.expected features) +
      numerical32 (continuation.state.linearPrediction (modelInput .discounted features age)))
  rw [add_sub_add_left_eq_sub] at first
  rw [add_sub_add_right_eq_sub] at second
  rw [continuationValue] at first outer
  have chain := abs_sub_le
    (clamp (numerical32 (prediction.reward.value.add (Prediction.project .g99
      ((value.rankedNominal transition.ranked (transition.expected features)).add
        (continuation.state.linearPrediction (modelInput .discounted features age)))).value)))
    (clamp (numerical32 prediction.reward.value + clamp (numerical32
      ((value.rankedNominal transition.ranked (transition.expected features)).add
        (continuation.state.linearPrediction (modelInput .discounted features age))))))
    (clamp (numerical32 prediction.reward.value +
      clamp (exactRankedBest value transition.ranked (transition.expected features) +
        numerical32 (continuation.state.linearPrediction
          (modelInput .discounted features age)))))
  have middle := abs_sub_le
    (clamp (numerical32 ((value.rankedNominal transition.ranked
      (transition.expected features)).add (continuation.state.linearPrediction
        (modelInput .discounted features age)))))
    (clamp (numerical32 (value.rankedNominal transition.ranked (transition.expected features)) +
      numerical32 (continuation.state.linearPrediction (modelInput .discounted features age))))
    (clamp (exactRankedBest value transition.ranked (transition.expected features) +
      numerical32 (continuation.state.linearPrediction (modelInput .discounted features age))))
  linarith [outer.2, inner.2, look.2.1]

/-! ## The differential backed-up value stays finite -/

/-- A ranked width is at most `2^15`. -/
theorem rank_capacity (dimension : Dimension) : (rankDimension dimension).capacity ≤ 32768 := by
  have bound := rankExponentFrom_le dimension.capacity 15 0
  change rankWidth dimension ≤ 2 ^ 15
  rw [rankWidth_eq]
  exact Nat.pow_le_pow_right (by decide) (by unfold rankExponent; omega)

/-- The ordered-sum envelope of the occupied positions is at most `2^23`. -/
theorem ranked_radius (ranked : RankedFeatures dimension) :
    predictionRadius ranked.occupied.length ≤ 8388608 := by
  have width := le_trans ranked.occupied_length (rank_capacity dimension)
  unfold predictionRadius
  have small := Nat.min_le_left ranked.occupied.length (2 ^ 24)
  have scaled : min ranked.occupied.length (2 ^ 24) * 256 ≤ 32768 * 256 :=
    Nat.mul_le_mul_right 256 (le_trans small width)
  exact_mod_cast scaled

/-- The differential value of the predicted outcome is finite and inside the summed
envelopes of the residual and the look-ahead, for every model state, value function
and frame. The rational envelope includes machine-rounding slack; it is not a clip. -/
theorem differential_continuation_bound
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    let prediction := (Model.differential r c d transition).predict value features age
    prediction.continuation.Finite ∧ |numerical32 prediction.continuation| ≤
      predictionRadius (modelInput .differential features age).indices.length +
        predictionRadius transition.ranked.occupied.length + 256 := by
  intro prediction
  have look := ranked_nominal_bound value transition.ranked (transition.expected features)
  have residual := prediction_bound c.state (modelInput .differential features age)
  change (c.state.linearPrediction (modelInput .differential features age)).Finite ∧
    |numerical32 (c.state.linearPrediction (modelInput .differential features age))| ≤
      predictionRadius (modelInput .differential features age).indices.length at residual
  have radiusCap : predictionRadius (modelInput .differential features age).indices.length ≤
      4294967296 := by
    unfold predictionRadius
    have := Nat.min_le_right (modelInput .differential features age).indices.length (2 ^ 24)
    exact_mod_cast Nat.mul_le_mul_right 256 this
  have rankedCap := ranked_radius transition.ranked
  have triangle := abs_add_le
    (numerical32 (value.rankedNominal transition.ranked (transition.expected features)))
    (numerical32 (c.state.linearPrediction (modelInput .differential features age)))
  have sum := binary32_add_finite_strict_error
    (value.rankedNominal transition.ranked (transition.expected features))
    (c.state.linearPrediction (modelInput .differential features age)) look.1 residual.1 33
    (by decide) (by norm_num; linarith [look.2, residual.2])
  have slack : |numerical32 prediction.continuation -
      (numerical32 (value.rankedNominal transition.ranked (transition.expected features)) +
        numerical32 (c.state.linearPrediction (modelInput .differential features age)))| ≤
      256 := by
    have radius : (2 : ℚ) ^ (max ((33 : Int) - 24) (-149)) / 2 = 256 := by norm_num
    have bound := sum.2
    rw [radius] at bound
    exact bound
  refine ⟨sum.1, ?_⟩
  have outer := abs_add_le
    (numerical32 prediction.continuation -
      (numerical32 (value.rankedNominal transition.ranked (transition.expected features)) +
        numerical32 (c.state.linearPrediction (modelInput .differential features age))))
    (numerical32 (value.rankedNominal transition.ranked (transition.expected features)) +
      numerical32 (c.state.linearPrediction (modelInput .differential features age)))
  rw [sub_add_cancel] at outer
  linarith [look.2, residual.2]

/-- The executed differential backed-up value is finite under the actual producer
ranges, for every model state, value function, frame and gain. -/
theorem differential_target_bound
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) :
    let prediction := (Model.differential r c d transition).predict value features age
    (prediction.target gain).Finite ∧ |numerical32 (prediction.target gain)| ≤
      predictionRadius (modelInput .differential features age).indices.length +
        predictionRadius transition.ranked.occupied.length + 640 := by
  intro prediction
  have rb := CurrentModels.interval_numeric _ prediction.reward
  have db := CurrentModels.interval_numeric _ prediction.duration
  have gb := CurrentModels.interval_numeric _ gain
  have one : numerical32 Binary32.one = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  have cap : numerical32
      (Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64) = 128 := by
    rw [show Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64 =
      Binary32.mk 0x43000000 by decide]
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-16 : Int) = 128
    norm_num
  simp only [Criterion.modelRewardRange, zero_numeric, cap] at rb
  simp only [modelDurationRange, one, cap] at db
  change numerical32 (Binary32.mk 0x3f800000) = 1 at one
  simp only [rewardRange, zero_numeric, one] at gb
  have centered := centered_reward_bound prediction.reward.value gain.value
    prediction.duration.value prediction.reward.legal.1 gain.legal.1 prediction.duration.legal.1
    rb gb db
  have continuation := differential_continuation_bound r c d transition value features age
  change prediction.continuation.Finite ∧ |numerical32 prediction.continuation| ≤
    predictionRadius (modelInput .differential features age).indices.length +
      predictionRadius transition.ranked.occupied.length + 256 at continuation
  have radiusCap : predictionRadius (modelInput .differential features age).indices.length ≤
      4294967296 := by
    unfold predictionRadius
    have := Nat.min_le_right (modelInput .differential features age).indices.length (2 ^ 24)
    exact_mod_cast Nat.mul_le_mul_right 256 this
  have rankedCap := ranked_radius transition.ranked
  have triangle := abs_add_le
    (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)))
    (numerical32 prediction.continuation)
  have sum := binary32_add_finite_strict_error
    (prediction.reward.value.sub (gain.value.mul prediction.duration.value))
    prediction.continuation centered.1 continuation.1 33 (by decide)
    (by norm_num; linarith [centered.2, continuation.2])
  have slack : |numerical32 (prediction.target gain) -
      (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)) +
        numerical32 prediction.continuation)| ≤ 256 := by
    have radius : (2 : ℚ) ^ (max ((33 : Int) - 24) (-149)) / 2 = 256 := by norm_num
    simpa only [ModelPrediction.target, radius] using sum.2
  refine ⟨sum.1, ?_⟩
  have outer := abs_add_le
    (numerical32 (prediction.target gain) -
      (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)) +
        numerical32 prediction.continuation))
    (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)) +
      numerical32 prediction.continuation)
  rw [sub_add_cancel] at outer
  linarith [centered.2, continuation.2]

/-! ## Storage and work -/

/-- Retained logical slots of one transition part, summed over its row learners. -/
def transitionSlots (transition : Transition dimension criterion) : Nat :=
  (transition.rows.toList.map fun row => retainedSlots row.state).sum

/-- A transition part holds exactly the square of the ranked width in weights: one
row per position, each over the ranked positions. -/
theorem transition_weights (transition : Transition dimension criterion) :
    transition.rows.toList.length * (rankDimension dimension).capacity =
      rankWidth dimension * rankWidth dimension := by
  simp

/-- The logical retained storage of a transition part's rows is quadratic in the
ranked width, independently of stream length: each row is a learner over the ranked
positions. The part also holds the slot vector and the lookup table of
`transition_table`. Native object headers and allocator reuse are separate. -/
theorem transition_storage (transition : Transition dimension criterion) :
    transitionSlots transition ≤ rankWidth dimension * (13 * rankWidth dimension + 2) := by
  have bound (rows : List (Managed (criterion.config .demon) (rankDimension dimension))) :
      (rows.map fun row => retainedSlots row.state).sum ≤
        rows.length * (13 * rankWidth dimension + 2) := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      have h : retainedSlots row.state ≤ 13 * rankWidth dimension + 2 :=
        retained_slots_unique row.state (managed_schedule row).2.1
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  simpa [transitionSlots] using bound transition.rows.toList

/-- Beside its rows a transition part holds one lookup word per feature slot and one
slot word per position: linear in the dimension, and outside the weight budget. -/
theorem transition_table (transition : Transition dimension criterion) :
    transition.ranked.table.toList.length = dimension.capacity ∧
      transition.ranked.slots.toList.length = (rankDimension dimension).capacity := by
  simp

/-- The width follows from the memory budget: the transition parts of all options
together hold at most one weight vector's worth of weights. -/
theorem transition_budget (dimension : Dimension)
    (room : Acorn.FeatureConstants.skillCount ≤ dimension.capacity) :
    Acorn.FeatureConstants.skillCount *
        ((rankDimension dimension).capacity * (rankDimension dimension).capacity) ≤
      dimension.capacity :=
  rankWidth_budget dimension room

/-- A dimension of 16 384 feature slots has 64 ranked positions: 63 slots and the
bias. -/
theorem default_width (dimension : Dimension) (standard : dimension.capacity = 16384) :
    (rankDimension dimension).capacity = 64 := by
  change rankWidth dimension = 64
  rw [rankWidth_eq]
  change 2 ^ rankExponentFrom dimension.capacity 15 0 = 64
  rw [standard]
  decide

/-- A row's input has at most the ranked width of positions, and at most one more than
the frame has active features, so one row's prediction reads at most that many weights. -/
theorem ranked_input_work (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.input features).indices.length ≤ (rankDimension dimension).capacity ∧
      (ranked.input features).indices.length ≤ features.indices.length + 1 :=
  ⟨active_cardinality _, ranked.input_length features⟩

/-- Every row keeps an eligibility list within the ranked width, after every update. -/
theorem row_work (transition : Transition dimension criterion) (position : RankIdx dimension) :
    (transition.rows.get position).state.eligibleCount ≤ (rankDimension dimension).capacity :=
  managed_capacity _

/-- A planning boundary performs a fixed number of look-aheads: every option at the
current and at one stored feature vector. -/
theorem boundary_work :
    planningFrames * planningSlots.length = 2 * Acorn.FeatureConstants.skillCount := by
  simp [planningFrames, planning_work]

/-- A look-ahead at a stored position that no frame has filled changes no learner
state: the empty feature vector names no slot to write. -/
theorem plan_empty {cfg : Acorn.Config} {actions : Nat}
    (controller : Controller cfg dimension actions) (action row : Action actions)
    (target : Binary32) :
    ((controller.plan action (SwiftTd.ActiveSet.empty dimension) target).1.learners.get
      row).state = (controller.learners.get row).state := by
  by_cases same : row = action
  · subst same
    change ((controller.learners.set row.val _ row.isLt)[row.val]).state = _
    rw [Vector.getElem_set_self]
    change ((controller.learners.get row).state.planStep cfg
      (SwiftTd.ActiveSet.empty dimension) target).1 = _
    unfold NumericState.planStep
    dsimp only
    split <;> rfl
  · rw [CurrentModels.plan_other controller action row same]

/-! ## A change of subset -/

/-- Filling vacant positions keeps every held slot at its position. -/
theorem fillVacant_held {α : Type} (slots : List (Option α)) (entrants : List α) (index : Nat)
    (held : α) (stored : slots[index]? = some (some held)) :
    (fillVacant slots entrants)[index]? = some (some held) := by
  induction slots generalizing entrants index with
  | nil => simp at stored
  | cons slot rest ih =>
    cases index with
    | zero =>
      have first : slot = some held := by simpa using stored
      subst first
      simp [fillVacant]
    | succ index =>
      have later : rest[index]? = some (some held) := by simpa using stored
      cases slot with
      | some other => simpa [fillVacant] using ih entrants index later
      | none =>
        cases entrants with
        | nil => simpa [fillVacant] using ih [] index later
        | cons entrant more => simpa [fillVacant] using ih more index later

/-- Every filled position holds a slot that was held or an entrant. -/
theorem fillVacant_source {α : Type} (slots : List (Option α)) (entrants : List α) (slot : α)
    (member : some slot ∈ fillVacant slots entrants) : some slot ∈ slots ∨ slot ∈ entrants := by
  induction slots generalizing entrants with
  | nil => simp [fillVacant] at member
  | cons head rest ih =>
    cases head with
    | some held =>
      have split : slot = held ∨ some slot ∈ fillVacant rest entrants := by
        simpa [fillVacant] using member
      rcases split with same | later
      · exact Or.inl (by simp [same])
      · exact (ih entrants later).elim (fun inside => Or.inl (List.mem_cons_of_mem _ inside))
          Or.inr
    | none =>
      cases entrants with
      | nil =>
        have later : some slot ∈ fillVacant rest [] := by simpa [fillVacant] using member
        exact (ih [] later).elim (fun inside => Or.inl (List.mem_cons_of_mem _ inside)) Or.inr
      | cons entrant more =>
        have split : slot = entrant ∨ some slot ∈ fillVacant rest more := by
          simpa [fillVacant] using member
        rcases split with same | later
        · exact Or.inr (by simp [same])
        · exact (ih more later).elim (fun inside => Or.inl (List.mem_cons_of_mem _ inside))
            (fun inside => Or.inr (List.mem_cons_of_mem _ inside))

/-- A change of subset keeps a held slot at its position whenever the slot is still
ranked, for every held vector and every ranking. -/
theorem mergeSlots_retained {α : Type} [BEq α] [LawfulBEq α] (held : List (Option α))
    (order : List α) (index : Nat) (slot : α) (stored : held[index]? = some (some slot))
    (ranked : slot ∈ order) : (mergeSlots held order)[index]? = some (some slot) := by
  apply fillVacant_held
  simp [stored, Option.filter, ranked]

/-- After a change of subset every modeled slot is ranked. -/
theorem mergeSlots_ranked {α : Type} [BEq α] [LawfulBEq α] (held : List (Option α))
    (order : List α) (slot : α) (member : some slot ∈ mergeSlots held order) : slot ∈ order := by
  rcases fillVacant_source _ _ slot member with kept | entrant
  · obtain ⟨before, _, same⟩ := List.mem_map.mp kept
    cases before with
    | none => simp [Option.filter] at same
    | some other =>
      have both : other ∈ order ∧ other = slot := by simpa [Option.filter] using same
      rw [← both.2]
      exact both.1
  · exact (List.mem_filter.mp entrant).1

/-- A position that holds a slot is not the bias position, which holds none. -/
theorem held_inside (ranked : RankedFeatures dimension) (position : RankIdx dimension)
    (feature : FeatIdx dimension) (held : ranked.slots[position.val] = some feature) :
    position.val + 1 < (rankDimension dimension).capacity := by
  have vacant := ranked.reserved
  have bound := position.isLt
  by_cases last : position.val = (rankDimension dimension).capacity - 1
  · simp only [last] at held
    rw [vacant] at held
    contradiction
  · omega

/-- Installing a ranking keeps every held slot that is still ranked at its position. -/
theorem rerank_retained (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension))
    (position : RankIdx dimension) (feature : FeatIdx dimension)
    (held : ranked.slots[position.val] = some feature) (still : feature ∈ order) :
    (ranked.rerank order).slots[position.val] = some feature := by
  have reserved := held_inside ranked position feature held
  have inside : position.val < ranked.slots.toList.length - 1 := by
    rw [Vector.length_toList]
    omega
  have stored : ranked.slots.toList.dropLast[position.val]? = some (some feature) := by
    rw [List.getElem?_dropLast]
    simpa [held] using reserved
  have merged := mergeSlots_retained ranked.slots.toList.dropLast order position.val feature
    stored still
  have bound : position.val < (mergeSlots ranked.slots.toList.dropLast order).length := by
    rw [mergeSlots_length, List.length_dropLast]
    exact inside
  have appended : (mergeSlots ranked.slots.toList.dropLast order ++ [none])[position.val]? =
      some (some feature) := by
    rw [List.getElem?_append_left bound]
    exact merged
  obtain ⟨_, same⟩ := List.getElem?_eq_some_iff.mp appended
  simpa [RankedFeatures.rerank_slots, RankedFeatures.merged] using same

/-- After installing a ranking every modeled slot is ranked. -/
theorem rerank_ranked (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension))
    (position : RankIdx dimension) (feature : FeatIdx dimension)
    (modeled : (ranked.rerank order).slots[position.val] = some feature) : feature ∈ order := by
  have inside : (ranked.rerank order).slots[position.val] ∈
      mergeSlots ranked.slots.toList.dropLast order ++ [none] := by
    simp [RankedFeatures.rerank_slots, RankedFeatures.merged]
  rw [modeled] at inside
  rcases List.mem_append.mp inside with kept | last
  · exact mergeSlots_ranked ranked.slots.toList.dropLast order feature kept
  · simp at last

/-- Retiring a slot leaves no position holding it, whether one position held it or
several. -/
theorem retire_vacated (transition : Transition dimension criterion)
    (feature : FeatIdx dimension) (position : RankIdx dimension) :
    (transition.retire feature).ranked.slots[position.val] ≠ some feature := by
  unfold Transition.retire
  split
  · rename_i unheld
    intro held
    have member : position ∈ transition.ranked.holding feature :=
      List.mem_filter.mpr ⟨List.mem_finRange position, by simp [held]⟩
    rw [unheld] at member
    simp at member
  · rename_i first more holding
    rw [← holding]
    exact transition.ranked.vacate_holding feature position

/-- Forgetting positions leaves every other row's weight from every other position
bit-identical: only the forgotten rows and input columns lose what was learned. -/
theorem forget_other
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) (row column : RankIdx dimension)
    (keptRow : row ∉ positions) (keptColumn : column ∉ positions) :
    ((Transition.forget rows positions).get row).state.weights.get column =
      (rows.get row).state.weights.get column := by
  have fold : ∀ (retired : List (RankIdx dimension)) (learner : Managed
      (criterion.config .demon) (rankDimension dimension)), column ∉ retired →
      (retired.foldl (fun current position => current.retire position) learner).state.weights.get
        column = learner.state.weights.get column := by
    intro retired
    induction retired with
    | nil => intro learner _; rfl
    | cons head tail ih =>
      intro learner absent
      have different : column ≠ head := fun same => absent (by simp [same])
      have rest : column ∉ tail := fun inside => absent (List.mem_cons_of_mem _ inside)
      rw [List.foldl_cons, ih (learner.retire head) rest]
      exact CurrentRetirement.retireIndex_weight_other learner.state head column different
  have skipped : (positions.contains row) = false := by
    simpa [List.contains_iff_mem] using keptRow
  simp only [Transition.forget, vector_get, Vector.getElem_mapFinIdx, Fin.eta, skipped,
    Bool.false_eq_true, ↓reduceIte]
  exact fold positions _ keptColumn

/-- Forgetting a position zeroes every other row's weight from it: no row keeps what
it learned about the slot that was there. -/
theorem forget_column
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) (row column : RankIdx dimension)
    (keptRow : row ∉ positions) (forgotten : column ∈ positions) :
    (((Transition.forget rows positions).get row).state.weights.get column).value =
      Binary32.zero := by
  have fold : ∀ (retired : List (RankIdx dimension)) (learner : Managed
      (criterion.config .demon) (rankDimension dimension)),
      (column ∈ retired ∨ (learner.state.weights.get column).value = Binary32.zero) →
      ((retired.foldl (fun current position => current.retire position)
        learner).state.weights.get column).value = Binary32.zero := by
    intro retired
    induction retired with
    | nil =>
      intro learner source
      rcases source with member | zero
      · simp at member
      · exact zero
    | cons head tail ih =>
      intro learner source
      rw [List.foldl_cons]
      apply ih (learner.retire head)
      by_cases same : column = head
      · rw [same]
        exact Or.inr (retire_registers learner.state head).2.1
      · rcases source with member | zero
        · exact Or.inl ((List.mem_cons.mp member).resolve_left same)
        · refine Or.inr ?_
          have kept := CurrentRetirement.retireIndex_weight_other learner.state head column same
          exact (congrArg Weight.value kept).trans zero
  have skipped : (positions.contains row) = false := by
    simpa [List.contains_iff_mem] using keptRow
  simp only [Transition.forget, vector_get, Vector.getElem_mapFinIdx, Fin.eta, skipped,
    Bool.false_eq_true, ↓reduceIte]
  exact fold positions _ (Or.inl forgotten)

/-- Forgetting a position replaces its row by a fresh learner. -/
theorem forget_row
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) (row : RankIdx dimension) (forgotten : row ∈ positions) :
    (Transition.forget rows positions).get row = Managed.initial _ _ := by
  simp [Transition.forget, vector_get, forgotten]

/-- A position whose slot stays ranked is not among the changed positions. -/
theorem retained_unchanged (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension))
    (position : RankIdx dimension) (feature : FeatIdx dimension)
    (held : ranked.slots[position.val] = some feature) (still : feature ∈ order) :
    position ∉ ranked.changed (ranked.rerank order) := by
  intro inside
  have differs := (List.mem_filter.mp inside).2
  rw [rerank_retained ranked order position feature held still, held] at differs
  simp at differs

/-- The bias position is never among the changed positions: it holds no slot before
or after any ranking. -/
theorem bias_unchanged (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension)) :
    RankedFeatures.bias dimension ∉ ranked.changed (ranked.rerank order) := by
  intro inside
  have differs := (List.mem_filter.mp inside).2
  rw [(ranked.rerank order).bias_vacant, ranked.bias_vacant] at differs
  simp at differs

/-- A change of subset keeps what was learned between retained slots: the weight a
retained slot's row holds for another retained slot is bit-identical after the new
ranking is installed. Weights from a changed position are zeroed (`forget_column`). -/
theorem rerank_weights (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (row column : RankIdx dimension)
    (rowFeature columnFeature : FeatIdx dimension)
    (rowHeld : transition.ranked.slots[row.val] = some rowFeature)
    (rowStill : rowFeature ∈ order)
    (columnHeld : transition.ranked.slots[column.val] = some columnFeature)
    (columnStill : columnFeature ∈ order) :
    ((transition.rerank order).rows.get row).state.weights.get column =
      (transition.rows.get row).state.weights.get column :=
  forget_other transition.rows _ row column
    (retained_unchanged transition.ranked order row rowFeature rowHeld rowStill)
    (retained_unchanged transition.ranked order column columnFeature columnHeld columnStill)

/-- A change of subset keeps a retained slot's bias weight bit-identical. -/
theorem rerank_bias (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (row : RankIdx dimension) (rowFeature : FeatIdx dimension)
    (rowHeld : transition.ranked.slots[row.val] = some rowFeature)
    (rowStill : rowFeature ∈ order) :
    ((transition.rerank order).rows.get row).state.weights.get (RankedFeatures.bias dimension) =
      (transition.rows.get row).state.weights.get (RankedFeatures.bias dimension) :=
  forget_other transition.rows _ row (RankedFeatures.bias dimension)
    (retained_unchanged transition.ranked order row rowFeature rowHeld rowStill)
    (bias_unchanged transition.ranked order)

/-- The bias position is never a predicted outcome: no occupied entry names it, so no
action value reads it and no row at it is updated. -/
theorem bias_unoccupied (ranked : RankedFeatures dimension)
    (entry : RankIdx dimension × FeatIdx dimension) (member : entry ∈ ranked.occupied) :
    entry.1 ≠ RankedFeatures.bias dimension := by
  obtain ⟨position, _, found⟩ := List.mem_filterMap.mp member
  cases held : ranked.slots[position.val] with
  | none => simp [held] at found
  | some feature =>
    simp only [held, Option.map_some, Option.some.injEq] at found
    subst found
    intro same
    have inside := held_inside ranked position feature held
    have last : position.val = (rankDimension dimension).capacity - 1 := congrArg Fin.val same
    omega

/-! ## Search control -/

/-- The position search control reads after `count` boundaries: each boundary moves it
one step against the write order. -/
theorem sweep_position (count : Nat)
    (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    (Nat.iterate RecentFeatures.before count position).val =
      (position.val + 127 * count) % 128 := by
  induction count generalizing position with
  | zero =>
    have bound : position.val < 128 := position.isLt
    simp only [Nat.iterate]
    omega
  | succ count ih =>
    have step : (RecentFeatures.before position).val = (position.val + 127) % 128 := rfl
    simp only [Nat.iterate]
    rw [ih (RecentFeatures.before position), step]
    omega

/-- The sweep reaches every stored position within one pass: from any position, any
target is read after fewer than the store's size of boundaries. -/
theorem sweep_reaches (position target : Fin Acorn.FeatureConstants.optionMaxDuration) :
    Nat.iterate RecentFeatures.before ((position.val + 128 - target.val) % 128) position =
      target := by
  have first : position.val < 128 := position.isLt
  have second : target.val < 128 := target.isLt
  apply Fin.ext
  rw [sweep_position]
  omega

end AcornVerif.CurrentPlanning
