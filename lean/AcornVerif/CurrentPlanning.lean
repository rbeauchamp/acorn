/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentPolicyMean
import AcornVerif.CurrentRetirement
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
`expectation_maximum_eq` its equality case. The differential nominal value is a
tie-window mean, which is not convex; `expectation_sandwiched` gives the same
inequality up to the slack of `AcornVerif.CurrentPolicyMean.expected_sandwich`.
`backup_propagation` is the dependence of a backed-up action value on the value
weights.

The second part concerns the executed definitions of `Acorn.Models`. The value of the
predicted outcome is formed per meta action: the value weights at the predicted ranked
features, plus the shared residual prediction, plus that action's deviation prediction.
`ranked_value_rounding` and `outcome_value_rounding` bound the distance between each
executed per-action value and the exact sum of the stored words;
`outcome_value_propagation` is the dependence of the exact value on the value weights,
and `outcome_decomposition` and `deterministic_outcome` show that the shared residual
and the deviations lose nothing of an action's unranked share. `discounted_backup_rounding`
and `differential_backup_rounding` bound the distance between the executed backed-up
value and the same expression in exact arithmetic, for every model state.

The per-action sums are formed before any projection, so their rounding follows the
magnitude of the stored predictions. That magnitude is bounded by the prediction
envelope of the active inputs, for every learner state, because every stored weight is
inside its rule's domain. The contracts therefore carry a scale `2^k`, `k` up to 20:
they hold whenever the envelopes of the active inputs fit below `8000 · 2^k`, a
condition on input counts and not on the stored state, with allowances proportional to
`2^k`. `discounted_backup_total` and `differential_backup_total` take `k = 20`, which
every input satisfies. `discounted_backup_small` and `differential_backup_small` are
the tight case, conditional on stored predictions of summed magnitude at most 1024.
Each binary32 product, sum and difference is the exact result rounded once to
nearest-even; the horizon projections are exact. The rounding bounds assume at most 64
ranked positions, which `default_width` shows for the 16 384-slot dimension.

The last part states storage and work, what a change of subset keeps, the terminal
target of a row and the reach of search control. Native primitive and compiler
correspondence remain the arithmetic layer's declared trust boundary.
-/

open Acorn Acorn.Features
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentPrediction
open AcornVerif.CurrentLearner AcornVerif.CurrentFeatureConsumers
open AcornVerif.CurrentBackupBounds AcornVerif.CurrentModelArithmetic AcornVerif.FloatLibBridge
open AcornVerif.CurrentPolicyMean

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

/-- The nominal value differential control uses is a mean over a tie set that depends
on the values, so it is not convex and no Jensen inequality holds for it. What holds:
if the nominal value of the expected action values is at most the convex combination
`(1 − rate) · max + rate · mean` plus `upper`, and the nominal value at each outcome is
at least that combination less `lower`, then the value of the expected action values is
at most the expected value plus both allowances, for every finite distribution.
`expected_expectation` instantiates it with the executed mean. -/
theorem expectation_sandwiched [Nonempty actions] (mass : outcomes → ℚ)
    (nonnegative : ∀ i, 0 ≤ mass i) (total : ∑ i, mass i = 1) (rate lower upper : ℚ)
    (rateHigh : rate ≤ 1) (value : outcomes → actions → ℚ) (mixed : ℚ)
    (nominal : outcomes → ℚ)
    (above : mixed ≤ (1 - rate) *
        Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ i, mass i * value i a) +
      rate * ((∑ a, ∑ i, mass i * value i a) / (Fintype.card actions : ℚ)) + upper)
    (below : ∀ i, (1 - rate) * Finset.univ.sup' Finset.univ_nonempty (value i) +
      rate * ((∑ a, value i a) / (Fintype.card actions : ℚ)) - lower ≤ nominal i) :
    mixed ≤ ∑ i, mass i * nominal i + lower + upper := by
  have greatest : Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ i, mass i * value i a) ≤
      ∑ i, mass i * Finset.univ.sup' Finset.univ_nonempty (value i) := by
    apply Finset.sup'_le
    intro a _
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (value i) (Finset.mem_univ a))
      (nonnegative i)
  have mean : (∑ a, ∑ i, mass i * value i a) / (Fintype.card actions : ℚ) =
      ∑ i, mass i * ((∑ a, value i a) / (Fintype.card actions : ℚ)) := by
    rw [Finset.sum_comm, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, mul_div_assoc]
  have complement : 0 ≤ 1 - rate := by linarith
  have each : ∀ i, mass i * ((1 - rate) * Finset.univ.sup' Finset.univ_nonempty (value i) +
      rate * ((∑ a, value i a) / (Fintype.card actions : ℚ))) ≤
      mass i * (nominal i + lower) := fun i =>
    mul_le_mul_of_nonneg_left (by linarith [below i]) (nonnegative i)
  have summed := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => each i
  have expand : ∑ i, mass i * (nominal i + lower) =
      ∑ i, mass i * nominal i + lower := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, total, one_mul]
  have convex : ∑ i, mass i * ((1 - rate) * Finset.univ.sup' Finset.univ_nonempty (value i) +
      rate * ((∑ a, value i a) / (Fintype.card actions : ℚ))) =
      (1 - rate) * ∑ i, mass i * Finset.univ.sup' Finset.univ_nonempty (value i) +
        rate * ∑ i, mass i * ((∑ a, value i a) / (Fintype.card actions : ℚ)) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  rw [mean] at above
  have scaled := mul_le_mul_of_nonneg_left greatest complement
  rw [expand, convex] at summed
  linarith

/-- A change of the value weights changes one backed-up action value of a fixed
predicted feature vector by exactly the weight change applied to that vector. A
scalar continuation has no such term: its value does not read the weights. -/
theorem backup_propagation (before after expected : features → ℚ) :
    ∑ j, after j * expected j - ∑ j, before j * expected j =
      ∑ j, (after j - before j) * expected j := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

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

/-! ## The nominal value of the ranked action values -/

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

/-! ## The value of the predicted outcome, per action -/

variable {count : Word.Count}

/-- A machine action space has an action, so a maximum over its actions exists. -/
instance : Nonempty (Action count.word.toNat) := ⟨firstAction count⟩

/-- The ordered maximum of action values, each finite and within `radius` of an exact
value, is finite and within `radius` of the exact maximum: it selects a word and adds
no rounding. -/
theorem best_rounding (snapshot : PolicySnapshot count) (exact : Action count.word.toNat → ℚ)
    (radius : ℚ)
    (close : ∀ action, (snapshot.values.get action).Finite ∧
      |numerical32 (snapshot.values.get action) - exact action| ≤ radius) :
    snapshot.best.Finite ∧
      |numerical32 snapshot.best - Finset.univ.sup' Finset.univ_nonempty exact| ≤ radius := by
  have spec := best_spec snapshot fun action => (close action).1
  obtain ⟨chosen, same⟩ := spec.1
  rw [same]
  refine ⟨(close chosen).1, abs_le.mpr ⟨?_, ?_⟩⟩
  · obtain ⟨best, _, attained⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty exact
    have dominated := spec.2 best
    rw [same] at dominated
    have near := (abs_le.mp (close best).2).1
    rw [attained]
    linarith
  · have upper : exact chosen ≤ Finset.univ.sup' Finset.univ_nonempty exact :=
      Finset.le_sup' exact (Finset.mem_univ chosen)
    have near := (abs_le.mp (close chosen).2).2
    linarith

/-- One deviation learner's prediction at a frame: its ordered weight sum over the
active ranked positions and the bias. -/
def deviationWord (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) (action : Action metaCount.word.toNat) : Binary32 :=
  (transition.deviations.get action).state.linearPrediction (transition.ranked.input features)

/-- A deviation prediction is finite and inside the ordered-sum envelope of its input. -/
theorem deviation_bound (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) (action : Action metaCount.word.toNat) :
    (deviationWord transition features action).Finite ∧
      |numerical32 (deviationWord transition features action)| ≤
        predictionRadius (transition.ranked.input features).indices.length :=
  prediction_bound (transition.deviations.get action).state (transition.ranked.input features)

/-- The exact value of the predicted outcome for one meta action: the dot product of
the stored value weights with the stored predicted features, plus the stored shared
residual prediction, plus the stored deviation prediction of that action. -/
def exactOutcomeValue (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) (action : Action metaCount.word.toNat) : ℚ :=
  exactRankedValue value transition.ranked (transition.expected features) action +
    numerical32 shared + numerical32 (deviationWord transition features action)

/-- Each executed outcome value is the ranked action value plus the shared residual
plus the action's deviation, added in that order. -/
theorem outcomeValues_get (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) (action : Action metaCount.word.toNat) :
    (transition.outcomeValues value features shared).get action =
      (((value.rankedValues transition.ranked (transition.expected features)).get action).add
        shared).add (deviationWord transition features action) := by
  simp [Transition.outcomeValues, Transition.expected, deviationWord, vector_get]

/-- Two successive additions whose partial sums stay below `2^13 · 2^k`: the result is
finite, within `2^(-11) · 2^k` more of the exact sum than its first operand was of its
exact value, and at most `8000 · 2^k` in magnitude. -/
theorem add_twice (ranked shared deviation : Binary32) (exact radius : ℚ) (k : Nat)
    (small : k ≤ 20) (rankedFinite : ranked.Finite) (sharedFinite : shared.Finite)
    (deviationFinite : deviation.Finite)
    (close : |numerical32 ranked - exact| ≤ radius) (size : |numerical32 ranked| ≤ 6528)
    (room : 6528 + |numerical32 shared| + |numerical32 deviation| + 1 / 2048 * (2 : ℚ) ^ k ≤
      8000 * (2 : ℚ) ^ k) :
    ((ranked.add shared).add deviation).Finite ∧
      |numerical32 ((ranked.add shared).add deviation) -
        (exact + numerical32 shared + numerical32 deviation)| ≤
          radius + 1 / 2048 * (2 : ℚ) ^ k ∧
      |numerical32 ((ranked.add shared).add deviation)| ≤ 8000 * (2 : ℚ) ^ k := by
  have scale : (0 : ℚ) < (2 : ℚ) ^ k := pow_pos (by norm_num) k
  have sharedSize := abs_nonneg (numerical32 shared)
  have deviationSize := abs_nonneg (numerical32 deviation)
  have firstTriangle := abs_add_le (numerical32 ranked) (numerical32 shared)
  have first := binary32_add_scaled ranked shared k small rankedFinite sharedFinite
    (by linarith)
  have firstSize : |numerical32 (ranked.add shared)| ≤
      |numerical32 ranked| + |numerical32 shared| + 1 / 4096 * (2 : ℚ) ^ k := by
    have triangle := abs_add_le
      (numerical32 (ranked.add shared) - (numerical32 ranked + numerical32 shared))
      (numerical32 ranked + numerical32 shared)
    rw [sub_add_cancel] at triangle
    linarith [first.2]
  have secondTriangle := abs_add_le (numerical32 (ranked.add shared)) (numerical32 deviation)
  have second := binary32_add_scaled (ranked.add shared) deviation k small first.1
    deviationFinite (by linarith)
  refine ⟨second.1, ?_, ?_⟩
  · have split : numerical32 ((ranked.add shared).add deviation) -
        (exact + numerical32 shared + numerical32 deviation) =
        (numerical32 ((ranked.add shared).add deviation) -
          (numerical32 (ranked.add shared) + numerical32 deviation)) +
        ((numerical32 (ranked.add shared) - (numerical32 ranked + numerical32 shared)) +
          (numerical32 ranked - exact)) := by ring
    rw [split]
    have outer := abs_add_le
      (numerical32 ((ranked.add shared).add deviation) -
        (numerical32 (ranked.add shared) + numerical32 deviation))
      ((numerical32 (ranked.add shared) - (numerical32 ranked + numerical32 shared)) +
        (numerical32 ranked - exact))
    have inner := abs_add_le
      (numerical32 (ranked.add shared) - (numerical32 ranked + numerical32 shared))
      (numerical32 ranked - exact)
    linarith [first.2, second.2]
  · have triangle := abs_add_le
      (numerical32 ((ranked.add shared).add deviation) -
        (numerical32 (ranked.add shared) + numerical32 deviation))
      (numerical32 (ranked.add shared) + numerical32 deviation)
    rw [sub_add_cancel] at triangle
    linarith [second.2]

/-- Backup identity with its rounding bound, per action, at the magnitude of the stored
words. For every transition part, value function and frame with at most 64 ranked
positions, and any `k` up to 20 with
`6528 + |shared| + |deviation| + 2^k / 2048 ≤ 8000 · 2^k`, the executed value of the
predicted outcome for one action is finite, within one term allowance per occupied
position plus `2^(-11) · 2^k` of the exact sum of the stored words, and at most
`8000 · 2^k` in magnitude. `2^(-11) · 2^k` is the binary32 spacing below `2^13 · 2^k`:
the two additions are formed before any projection, so their rounding follows the
magnitude of the stored predictions. -/
theorem outcome_value_rounding (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) (action : Action metaCount.word.toNat) (k : Nat) (small : k ≤ 20)
    (narrow : (rankDimension dimension).capacity ≤ 64) (finite : shared.Finite)
    (room : 6528 + |numerical32 shared| +
      |numerical32 (deviationWord transition features action)| + 1 / 2048 * (2 : ℚ) ^ k ≤
        8000 * (2 : ℚ) ^ k) :
    ((transition.outcomeValues value features shared).get action).Finite ∧
      |numerical32 ((transition.outcomeValues value features shared).get action) -
        exactOutcomeValue transition value features shared action| ≤
          (transition.ranked.occupied.length : ℚ) * termRadius + 1 / 2048 * (2 : ℚ) ^ k ∧
      |numerical32 ((transition.outcomeValues value features shared).get action)| ≤
        8000 * (2 : ℚ) ^ k := by
  rw [outcomeValues_get]
  have ranked := ranked_value_rounding value transition.ranked (transition.expected features)
    action narrow
  have few : (transition.ranked.occupied.length : ℚ) ≤ 64 := by
    exact_mod_cast le_trans transition.ranked.occupied_length narrow
  exact add_twice _ shared _ _ _ k small ranked.1 finite
    (deviation_bound transition features action).1 ranked.2.1 (by linarith [ranked.2.2]) room

/-- The room of `outcome_value_rounding` from the prediction envelopes alone. A shared
prediction read from `inputs` active features and a deviation prediction read from the
row input are each inside their ordered-sum envelope, for every learner state, because
every stored weight is inside its rule's domain. So the room holds whenever the
envelopes fit, which is a condition on the counts of active inputs and not on the
stored state. -/
theorem envelope_room (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) (shared : Binary32) (inputs k : Nat)
    (action : Action metaCount.word.toNat)
    (bound : |numerical32 shared| ≤ predictionRadius inputs)
    (fits : 6528 + predictionRadius inputs +
      predictionRadius (transition.ranked.input features).indices.length +
        1 / 2048 * (2 : ℚ) ^ k ≤ 8000 * (2 : ℚ) ^ k) :
    6528 + |numerical32 shared| + |numerical32 (deviationWord transition features action)| +
      1 / 2048 * (2 : ℚ) ^ k ≤ 8000 * (2 : ℚ) ^ k := by
  have deviation := (deviation_bound transition features action).2
  linarith

/-- Dependence on the value weights, over the executed definitions and for the complete
per-action value: between two value functions, with the transition part and the shared
prediction held fixed, the exact value of the predicted outcome for an action differs
by the weight change at each occupied slot times that slot's predicted activity. The
maximum or mean over actions is taken after, so no change at a ranked slot is hidden by
another action's value. This is an identity between exact values, before rounding; the
executed word is within the allowance of `outcome_value_rounding` of each. -/
theorem outcome_value_propagation (transition : Transition dimension criterion)
    (before after : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) (action : Action metaCount.word.toNat) :
    exactOutcomeValue transition after features shared action -
        exactOutcomeValue transition before features shared action =
      (transition.ranked.occupied.map fun entry =>
        (numerical32 ((after.controller.learners.get action).state.weights.get entry.2).value -
          numerical32 ((before.controller.learners.get action).state.weights.get entry.2).value) *
          numerical32 ((transition.expected features).get entry.1).value).sum := by
  rw [← ranked_value_propagation before after transition.ranked (transition.expected features)
    action]
  unfold exactOutcomeValue
  ring

/-- The shared residual and an action's deviation add up to that action's unranked
share, in exact arithmetic: whatever the shared part is, nothing of the share is lost.
`complete` is the action's value at the terminal frame, `ranked` its value at the
frame's ranked slots, `residual` the shared residual and `discount` the terminal
discount of `Transition.outcome`. -/
theorem outcome_decomposition (discount complete ranked residual : ℚ) :
    discount * residual + discount * ((complete - ranked) - residual) =
      discount * (complete - ranked) := by
  ring

/-- For a deterministic outcome reached with discount `discount`, the maximum over
actions of the discounted ranked part plus the discounted shared residual plus the
discounted deviation is the discounted maximum of the complete action values, whatever
the shared residual is. With the ranked parts read from the current weights, a change
at a ranked slot for any action therefore changes the exact backed-up value. -/
theorem deterministic_outcome {actions : Type} [Fintype actions] [Nonempty actions]
    (discount : ℚ) (nonnegative : 0 ≤ discount) (complete ranked share : actions → ℚ)
    (residual : ℚ) (split : ∀ action, complete action = ranked action + share action) :
    Finset.univ.sup' Finset.univ_nonempty (fun action =>
        discount * ranked action + discount * residual +
          discount * (share action - residual)) =
      discount * Finset.univ.sup' Finset.univ_nonempty complete := by
  have each : (fun action => discount * ranked action + discount * residual +
      discount * (share action - residual)) = fun action => discount * complete action := by
    funext action
    rw [split action]
    ring
  rw [each]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun action _ => mul_le_mul_of_nonneg_left
      (Finset.le_sup' complete (Finset.mem_univ action)) nonnegative
  · obtain ⟨best, _, attained⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty complete
    rw [attained]
    exact Finset.le_sup' (fun action => discount * complete action) (Finset.mem_univ best)

/-- Two successive additions of finite words inside their envelopes stay finite and
inside the summed envelopes, with machine-rounding slack. -/
theorem add_twice_bound (ranked shared deviation : Binary32) (first second third : ℚ)
    (rankedFinite : ranked.Finite) (sharedFinite : shared.Finite)
    (deviationFinite : deviation.Finite) (rankedBound : |numerical32 ranked| ≤ first)
    (sharedBound : |numerical32 shared| ≤ second)
    (deviationBound : |numerical32 deviation| ≤ third) (firstCap : first ≤ 8388608)
    (secondCap : second ≤ 4294967296) (thirdCap : third ≤ 8388608) :
    ((ranked.add shared).add deviation).Finite ∧
      |numerical32 ((ranked.add shared).add deviation)| ≤ first + second + third + 512 := by
  have radius : (2 : ℚ) ^ (max ((33 : Int) - 24) (-149)) / 2 = 256 := by norm_num
  have firstTriangle := abs_add_le (numerical32 ranked) (numerical32 shared)
  have inner := binary32_add_finite_strict_error ranked shared rankedFinite sharedFinite 33
    (by decide) (by norm_num; linarith)
  have innerSlack := inner.2
  rw [radius] at innerSlack
  have innerSize : |numerical32 (ranked.add shared)| ≤ first + second + 256 := by
    have triangle := abs_add_le
      (numerical32 (ranked.add shared) - (numerical32 ranked + numerical32 shared))
      (numerical32 ranked + numerical32 shared)
    rw [sub_add_cancel] at triangle
    linarith
  have secondTriangle := abs_add_le (numerical32 (ranked.add shared)) (numerical32 deviation)
  have outer := binary32_add_finite_strict_error (ranked.add shared) deviation inner.1
    deviationFinite 33 (by decide) (by norm_num; linarith)
  have outerSlack := outer.2
  rw [radius] at outerSlack
  refine ⟨outer.1, ?_⟩
  have triangle := abs_add_le
    (numerical32 ((ranked.add shared).add deviation) -
      (numerical32 (ranked.add shared) + numerical32 deviation))
    (numerical32 (ranked.add shared) + numerical32 deviation)
  rw [sub_add_cancel] at triangle
  linarith

/-- Envelope of one outcome value: the ordered-sum envelopes of the occupied positions,
of the shared prediction's input and of the row input, plus machine-rounding slack. -/
def outcomeRadius (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) (inputs : Nat) : ℚ :=
  predictionRadius transition.ranked.occupied.length + predictionRadius inputs +
    predictionRadius (transition.ranked.input features).indices.length + 512

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

/-- An ordered-sum envelope is at most `2^32`. -/
theorem radius_cap (inputs : Nat) : predictionRadius inputs ≤ 4294967296 := by
  unfold predictionRadius
  have := Nat.min_le_right inputs (2 ^ 24)
  exact_mod_cast Nat.mul_le_mul_right 256 this

/-- The envelope of a row input is at most `2^23`. -/
theorem input_radius (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    predictionRadius (ranked.input features).indices.length ≤ 8388608 := by
  have width := le_trans (active_cardinality (ranked.input features)) (rank_capacity dimension)
  unfold predictionRadius
  have small := Nat.min_le_left (ranked.input features).indices.length (2 ^ 24)
  have scaled : min (ranked.input features).indices.length (2 ^ 24) * 256 ≤ 32768 * 256 :=
    Nat.mul_le_mul_right 256 (le_trans small width)
  exact_mod_cast scaled

/-- For every criterion, dimension, state and frame, every executed outcome value is
finite and inside its envelope, given a finite shared prediction inside its own. -/
theorem outcome_value_bound (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) (inputs : Nat) (action : Action metaCount.word.toNat)
    (finite : shared.Finite) (bound : |numerical32 shared| ≤ predictionRadius inputs) :
    ((transition.outcomeValues value features shared).get action).Finite ∧
      |numerical32 ((transition.outcomeValues value features shared).get action)| ≤
        outcomeRadius transition features inputs := by
  rw [outcomeValues_get]
  have ranked := ranked_value_bound value transition.ranked (transition.expected features) action
  have deviation := deviation_bound transition features action
  exact add_twice_bound _ shared _ _ _ _ ranked.1 finite deviation.1 ranked.2 bound deviation.2
    (ranked_radius transition.ranked) (radius_cap inputs) (input_radius transition.ranked features)

/-! ## The discounted backed-up value -/

/-- The exact discounted value of the predicted outcome: the maximum over meta actions
of the exact per-action values. -/
def exactOutcomeBest (transition : Transition dimension .discounted)
    (value : ValueFunction .discounted dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (exactOutcomeValue transition value features shared)

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

/-- The discounted backed-up value from per-action values that are each finite and
within `radius` of their exact values: the ordered maximum selects a word, both
projections are exact, and the one remaining addition is rounded inside the prediction
range, so the executed target is within `radius + 2^(-17)` of `clamp (r + clamp V)`. -/
theorem discounted_backup_close
    (reward continuation : Managed (Criterion.config .discounted .demon) dimension)
    (transition : Transition dimension .discounted)
    (value : ValueFunction .discounted dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (radius : ℚ)
    (each : ∀ action, ((transition.outcomeValues value features
        (continuation.state.linearPrediction (modelInput .discounted features age))).get
          action).Finite ∧
      |numerical32 ((transition.outcomeValues value features
        (continuation.state.linearPrediction (modelInput .discounted features age))).get
          action) -
        exactOutcomeValue transition value features
          (continuation.state.linearPrediction (modelInput .discounted features age))
          action| ≤ radius) :
    let prediction := (Model.discounted reward continuation transition).predict value features age
    |numerical32 (prediction.target gain) -
      clamp (numerical32 prediction.reward.value +
        clamp (exactOutcomeBest transition value features
          (continuation.state.linearPrediction (modelInput .discounted features age))))| ≤
      radius + 1 / 131072 := by
  intro prediction
  have best := best_rounding
    (⟨transition.outcomeValues value features
      (continuation.state.linearPrediction (modelInput .discounted features age)),
      value.epsilon⟩ : PolicySnapshot metaCount)
    (exactOutcomeValue transition value features
      (continuation.state.linearPrediction (modelInput .discounted features age)))
    radius each
  have continuationValue := project_numeric _ best.1
  have continuationFinite := (Prediction.project .g99 (PolicySnapshot.best
    (⟨transition.outcomeValues value features
      (continuation.state.linearPrediction (modelInput .discounted features age)),
      value.epsilon⟩ : PolicySnapshot metaCount))).legal.1
  have continuationRange := clamp_range (numerical32 (PolicySnapshot.best
    (⟨transition.outcomeValues value features
      (continuation.state.linearPrediction (modelInput .discounted features age)),
      value.epsilon⟩ : PolicySnapshot metaCount)))
  rw [← continuationValue] at continuationRange
  have rewardBounds := CurrentModels.interval_numeric _ prediction.reward
  have lowerValue : numerical32 (Criterion.discounted.modelRewardRange).lower = 0 := by decide
  rw [lowerValue] at rewardBounds
  have rewardTop : numerical32 (Criterion.discounted.modelRewardRange).upper = horizon := rfl
  rw [rewardTop] at rewardBounds
  have top := horizon_bounds
  have outer := clamped_add prediction.reward.value _ prediction.reward.legal.1
    continuationFinite
    (abs_le.mpr ⟨by linarith [rewardBounds.1, continuationRange.1],
      by linarith [rewardBounds.2, continuationRange.2]⟩)
  have target : numerical32 (prediction.target gain) = clamp (numerical32
      (prediction.reward.value.add (Prediction.project .g99 (PolicySnapshot.best
        (⟨transition.outcomeValues value features
          (continuation.state.linearPrediction (modelInput .discounted features age)),
          value.epsilon⟩ : PolicySnapshot metaCount))).value)) :=
    project_numeric _ outer.1
  rw [target]
  rw [continuationValue] at outer
  have inner := clamp_lipschitz
    (numerical32 (PolicySnapshot.best
      (⟨transition.outcomeValues value features
        (continuation.state.linearPrediction (modelInput .discounted features age)),
        value.epsilon⟩ : PolicySnapshot metaCount)))
    (exactOutcomeBest transition value features
      (continuation.state.linearPrediction (modelInput .discounted features age)))
  have lifted := clamp_lipschitz
    (numerical32 prediction.reward.value + clamp (numerical32 (PolicySnapshot.best
      (⟨transition.outcomeValues value features
        (continuation.state.linearPrediction (modelInput .discounted features age)),
        value.epsilon⟩ : PolicySnapshot metaCount))))
    (numerical32 prediction.reward.value + clamp (exactOutcomeBest transition value features
      (continuation.state.linearPrediction (modelInput .discounted features age))))
  rw [add_sub_add_left_eq_sub] at lifted
  have chain := abs_sub_le
    (clamp (numerical32 (prediction.reward.value.add (Prediction.project .g99
      (PolicySnapshot.best (⟨transition.outcomeValues value features
        (continuation.state.linearPrediction (modelInput .discounted features age)),
        value.epsilon⟩ : PolicySnapshot metaCount))).value)))
    (clamp (numerical32 prediction.reward.value + clamp (numerical32 (PolicySnapshot.best
      (⟨transition.outcomeValues value features
        (continuation.state.linearPrediction (modelInput .discounted features age)),
        value.epsilon⟩ : PolicySnapshot metaCount)))))
    (clamp (numerical32 prediction.reward.value + clamp (exactOutcomeBest transition value
      features (continuation.state.linearPrediction (modelInput .discounted features age)))))
  have bestClose : |numerical32 (PolicySnapshot.best
      (⟨transition.outcomeValues value features
        (continuation.state.linearPrediction (modelInput .discounted features age)),
        value.epsilon⟩ : PolicySnapshot metaCount)) -
      exactOutcomeBest transition value features
        (continuation.state.linearPrediction (modelInput .discounted features age))| ≤
      radius := best.2
  linarith [outer.2]

/-- The largest envelope: with `k = 20` the room of `outcome_value_rounding` holds for
every count of active inputs. -/
theorem envelope_total (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) (inputs : Nat) :
    6528 + predictionRadius inputs +
      predictionRadius (transition.ranked.input features).indices.length +
        1 / 2048 * (2 : ℚ) ^ 20 ≤ 8000 * (2 : ℚ) ^ 20 := by
  have first := radius_cap inputs
  have second := input_radius transition.ranked features
  norm_num
  linarith

/-- Backup identity with its rounding bound, for the executed discounted backed-up
value, for every model state. Let `V` be the exact maximum over meta actions of: the
dot product of the stored value weights with the stored predicted features, plus the
stored shared residual prediction, plus the stored deviation prediction of that
action; and `r` the stored reward prediction. For every model, value function, frame
and gain with at most 64 ranked positions, and any `k` up to 20 for which the
prediction envelopes of the active inputs fit below `8000 · 2^k`, the executed target
is within one term allowance per occupied position plus `2^(-11) · 2^k + 2^(-17)` of
`clamp (r + clamp V)`, where `clamp` is the exact projection onto the prediction range.
The hypothesis is on the counts of active inputs; no hypothesis is made on the stored
state. `discounted_backup_total` takes `k = 20`, which every input satisfies, and
`discounted_backup_small` is the tight case. -/
theorem discounted_backup_rounding
    (reward continuation : Managed (Criterion.config .discounted .demon) dimension)
    (transition : Transition dimension .discounted)
    (value : ValueFunction .discounted dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (k : Nat) (small : k ≤ 20)
    (narrow : (rankDimension dimension).capacity ≤ 64)
    (fits : 6528 + predictionRadius (modelInput .discounted features age).indices.length +
      predictionRadius (transition.ranked.input features).indices.length +
        1 / 2048 * (2 : ℚ) ^ k ≤ 8000 * (2 : ℚ) ^ k) :
    let prediction := (Model.discounted reward continuation transition).predict value features age
    |numerical32 (prediction.target gain) -
      clamp (numerical32 prediction.reward.value +
        clamp (exactOutcomeBest transition value features
          (continuation.state.linearPrediction (modelInput .discounted features age))))| ≤
      (transition.ranked.occupied.length : ℚ) * termRadius + 1 / 2048 * (2 : ℚ) ^ k +
        1 / 131072 := by
  have sharedBound := prediction_bound continuation.state (modelInput .discounted features age)
  change (continuation.state.linearPrediction (modelInput .discounted features age)).Finite ∧
    |numerical32 (continuation.state.linearPrediction (modelInput .discounted features age))| ≤
      predictionRadius (modelInput .discounted features age).indices.length at sharedBound
  exact discounted_backup_close reward continuation transition value features age gain _
    fun action =>
      have result := outcome_value_rounding transition value features
        (continuation.state.linearPrediction (modelInput .discounted features age)) action k
        small narrow sharedBound.1
        (envelope_room transition features _ _ k action sharedBound.2 fits)
      ⟨result.1, result.2.1⟩

/-- The discounted backup identity with no hypothesis beyond the ranked width: for
every model state, value function, frame and gain, the executed target is within one
term allowance per occupied position plus `2^9 + 2^(-17)` of `clamp (r + clamp V)`.
`2^9` is the binary32 spacing at the largest magnitude a prediction envelope allows; the
bound is as loose as that magnitude is large. -/
theorem discounted_backup_total
    (reward continuation : Managed (Criterion.config .discounted .demon) dimension)
    (transition : Transition dimension .discounted)
    (value : ValueFunction .discounted dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (narrow : (rankDimension dimension).capacity ≤ 64) :
    let prediction := (Model.discounted reward continuation transition).predict value features age
    |numerical32 (prediction.target gain) -
      clamp (numerical32 prediction.reward.value +
        clamp (exactOutcomeBest transition value features
          (continuation.state.linearPrediction (modelInput .discounted features age))))| ≤
      (transition.ranked.occupied.length : ℚ) * termRadius + 512 + 1 / 131072 := by
  have result := discounted_backup_rounding reward continuation transition value features age
    gain 20 (by decide) narrow (envelope_total transition features _)
  have scale : (1 : ℚ) / 2048 * (2 : ℚ) ^ 20 = 512 := by norm_num
  rw [scale] at result
  exact result

/-- The tight case of the discounted backup identity, conditional on the stored state:
when the stored shared and deviation predictions have summed magnitude at most 1024,
the executed target is within one term allowance per occupied position plus
`2^(-11) + 2^(-17)` of `clamp (r + clamp V)`. Nothing enforces the condition;
`discounted_backup_rounding` is the statement without it. -/
theorem discounted_backup_small
    (reward continuation : Managed (Criterion.config .discounted .demon) dimension)
    (transition : Transition dimension .discounted)
    (value : ValueFunction .discounted dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (narrow : (rankDimension dimension).capacity ≤ 64)
    (room : ∀ action, |numerical32 (continuation.state.linearPrediction
        (modelInput .discounted features age))| +
      |numerical32 (deviationWord transition features action)| ≤ 1024) :
    let prediction := (Model.discounted reward continuation transition).predict value features age
    |numerical32 (prediction.target gain) -
      clamp (numerical32 prediction.reward.value +
        clamp (exactOutcomeBest transition value features
          (continuation.state.linearPrediction (modelInput .discounted features age))))| ≤
      (transition.ranked.occupied.length : ℚ) * termRadius + 1 / 2048 + 1 / 131072 := by
  have sharedBound := prediction_bound continuation.state (modelInput .discounted features age)
  change (continuation.state.linearPrediction (modelInput .discounted features age)).Finite ∧ _
    at sharedBound
  have result := discounted_backup_close reward continuation transition value features age
    gain ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 2048 * (2 : ℚ) ^ 0)
    fun action =>
      have each := outcome_value_rounding transition value features
        (continuation.state.linearPrediction (modelInput .discounted features age)) action 0
        (by decide) narrow sharedBound.1 (by norm_num; linarith [room action])
      ⟨each.1, each.2.1⟩
  simpa using result

/-! ## The differential backed-up value -/

/-- The words of a vector summed in list order are the sum over its indices. -/
theorem words_sum {size : Nat} (words : Vector Binary32 size) :
    (words.toList.map numerical32).sum = ∑ action : Fin size, numerical32 (words.get action) := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro index first second
    simp [vector_get]

/-- The convex combination of action values within `radius` of exact values is within
`radius` of the same combination of the exact values. -/
theorem greedy_mean_close (snapshot : PolicySnapshot count)
    (exact : Action count.word.toNat → ℚ) (radius : ℚ)
    (close : ∀ action, (snapshot.values.get action).Finite ∧
      |numerical32 (snapshot.values.get action) - exact action| ≤ radius) :
    |greedyMean snapshot -
      ((1 - numerical32 snapshot.epsilon.value) * Finset.univ.sup' Finset.univ_nonempty exact +
        numerical32 snapshot.epsilon.value *
          ((∑ action, exact action) / (count.word.toNat : ℚ)))| ≤ radius := by
  have rateBounds := CurrentModels.interval_numeric SwiftTd.exploreRange snapshot.epsilon
  have rateLower : numerical32 SwiftTd.exploreRange.lower = 0 := by decide
  have rateUpper : numerical32 SwiftTd.exploreRange.upper = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  rw [rateLower, rateUpper] at rateBounds
  have best := (best_rounding snapshot exact radius close).2
  have positive : (0 : ℚ) < (count.word.toNat : ℚ) := by exact_mod_cast count.positive
  have nonnegative : 0 ≤ radius := le_trans (abs_nonneg _) (close (firstAction count)).2
  have sums : |(snapshot.values.toList.map numerical32).sum - ∑ action, exact action| ≤
      (count.word.toNat : ℚ) * radius := by
    rw [words_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have each := Finset.sum_le_sum fun action (_ : action ∈ Finset.univ) => (close action).2
    simpa using each
  have mean : |(snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ) -
      (∑ action, exact action) / (count.word.toNat : ℚ)| ≤ radius := by
    rw [← sub_div, abs_div, abs_of_pos positive, div_le_iff₀ positive]
    linarith
  have complement : 0 ≤ 1 - numerical32 snapshot.epsilon.value := by linarith [rateBounds.2]
  unfold greedyMean
  have split : (1 - numerical32 snapshot.epsilon.value) * numerical32 snapshot.best +
      numerical32 snapshot.epsilon.value *
        ((snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ)) -
      ((1 - numerical32 snapshot.epsilon.value) *
        Finset.univ.sup' Finset.univ_nonempty exact +
        numerical32 snapshot.epsilon.value *
          ((∑ action, exact action) / (count.word.toNat : ℚ))) =
      (1 - numerical32 snapshot.epsilon.value) *
        (numerical32 snapshot.best - Finset.univ.sup' Finset.univ_nonempty exact) +
      numerical32 snapshot.epsilon.value *
        ((snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ) -
          (∑ action, exact action) / (count.word.toNat : ℚ)) := by ring
  rw [split]
  have triangle := abs_add_le
    ((1 - numerical32 snapshot.epsilon.value) *
      (numerical32 snapshot.best - Finset.univ.sup' Finset.univ_nonempty exact))
    (numerical32 snapshot.epsilon.value *
      ((snapshot.values.toList.map numerical32).sum / (count.word.toNat : ℚ) -
        (∑ action, exact action) / (count.word.toNat : ℚ)))
  rw [abs_mul, abs_mul, abs_of_nonneg complement, abs_of_nonneg rateBounds.1] at triangle
  have first := mul_le_mul_of_nonneg_left best complement
  have second := mul_le_mul_of_nonneg_left mean rateBounds.1
  nlinarith

/-- `greedyMean` of finite words, written over the action index: the greatest word is
the maximum over actions and the list sum is the sum over actions. -/
theorem greedyMean_eq (snapshot : PolicySnapshot count)
    (finite : ∀ action, (snapshot.values.get action).Finite) :
    greedyMean snapshot =
      (1 - numerical32 snapshot.epsilon.value) *
          Finset.univ.sup' Finset.univ_nonempty
            (fun action => numerical32 (snapshot.values.get action)) +
        numerical32 snapshot.epsilon.value *
          ((∑ action, numerical32 (snapshot.values.get action)) /
            (Fintype.card (Action count.word.toNat) : ℚ)) := by
  have best := (best_rounding snapshot (fun action => numerical32 (snapshot.values.get action))
    0 fun action => ⟨finite action, by simp⟩).2
  have same : numerical32 snapshot.best = Finset.univ.sup' Finset.univ_nonempty
      (fun action => numerical32 (snapshot.values.get action)) :=
    sub_eq_zero.mp (abs_nonpos_iff.mp best)
  unfold greedyMean
  rw [same, words_sum, Fintype.card_fin]

/-- The expectation inequality for the executed nominal mean. Take finitely many
outcomes with masses summing to one, each with at most eight finite action values of
magnitude at most `8000 · 2^k`, and a vector of words whose values are the expected
action values, all under one rate. Then the executed mean of the expected values is at
most the expected executed mean plus `(meanSlack + meanRadius) · 2^k`: the tie window
on the outcomes' side and the rounding on both. -/
theorem expected_expectation {outcomes : Type} [Fintype outcomes] (mass : outcomes → ℚ)
    (nonnegative : ∀ i, 0 ≤ mass i) (total : ∑ i, mass i = 1) (rate : SwiftTd.ExploreRate)
    (values : outcomes → Vector Binary32 count.word.toNat)
    (mixed : Vector Binary32 count.word.toNat) (k : Nat) (small : k ≤ 20)
    (few : count.word.toNat ≤ 8)
    (bounded : ∀ i action, ((values i).get action).Finite ∧
      |numerical32 ((values i).get action)| ≤ 8000 * (2 : ℚ) ^ k)
    (mixedBounded : ∀ action, (mixed.get action).Finite ∧
      |numerical32 (mixed.get action)| ≤ 8000 * (2 : ℚ) ^ k)
    (mixture : ∀ action, numerical32 (mixed.get action) =
      ∑ i, mass i * numerical32 ((values i).get action)) :
    numerical32 (PolicySnapshot.expected (⟨mixed, rate⟩ : PolicySnapshot count)) ≤
      ∑ i, mass i *
          numerical32 (PolicySnapshot.expected (⟨values i, rate⟩ : PolicySnapshot count)) +
        meanSlack * (2 : ℚ) ^ k + meanRadius * (2 : ℚ) ^ k := by
  have rateBounds := CurrentModels.interval_numeric SwiftTd.exploreRange rate
  have rateUpper : numerical32 SwiftTd.exploreRange.upper = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  rw [rateUpper] at rateBounds
  have above := (expected_sandwich (⟨mixed, rate⟩ : PolicySnapshot count) k small few
    mixedBounded).2.2
  rw [greedyMean_eq (⟨mixed, rate⟩ : PolicySnapshot count) fun action =>
    (mixedBounded action).1] at above
  have below : ∀ i, (1 - numerical32 rate.value) *
        Finset.univ.sup' Finset.univ_nonempty
          (fun action => numerical32 ((values i).get action)) +
      numerical32 rate.value * ((∑ action, numerical32 ((values i).get action)) /
        (Fintype.card (Action count.word.toNat) : ℚ)) - meanSlack * (2 : ℚ) ^ k ≤
      numerical32 (PolicySnapshot.expected (⟨values i, rate⟩ : PolicySnapshot count)) := by
    intro i
    have lower := (expected_sandwich (⟨values i, rate⟩ : PolicySnapshot count) k small few
      (bounded i)).2.1
    rw [greedyMean_eq (⟨values i, rate⟩ : PolicySnapshot count) fun action =>
      (bounded i action).1] at lower
    exact lower
  change numerical32 (PolicySnapshot.expected (⟨mixed, rate⟩ : PolicySnapshot count)) ≤
    (1 - numerical32 rate.value) * Finset.univ.sup' Finset.univ_nonempty
        (fun action => numerical32 (mixed.get action)) +
      numerical32 rate.value * ((∑ action, numerical32 (mixed.get action)) /
        (Fintype.card (Action count.word.toNat) : ℚ)) + meanRadius * (2 : ℚ) ^ k at above
  simp only [mixture] at above
  exact expectation_sandwiched mass nonnegative total (numerical32 rate.value)
    (meanSlack * (2 : ℚ) ^ k) (meanRadius * (2 : ℚ) ^ k) rateBounds.2
    (fun i action => numerical32 ((values i).get action)) _ _ above below

/-- The exact differential value of the predicted outcome with one greedy action:
`(1 − ε)` times the maximum over meta actions of the exact per-action values plus `ε`
times their mean. The executed value averages the actions within the tie window of
the maximum, so it can lie below this by the window. -/
def exactOutcomeMean (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : ℚ :=
  (1 - numerical32 value.epsilon.value) *
      Finset.univ.sup' Finset.univ_nonempty (exactOutcomeValue transition value features shared) +
    numerical32 value.epsilon.value *
      ((∑ action, exactOutcomeValue transition value features shared action) /
        (metaCount.word.toNat : ℚ))

/-- The executed differential value of the predicted outcome against the exact
expression, at the magnitude of the stored words. For every transition part, value
function and frame with at most 64 ranked positions, and any `k` up to 20 with the room
of `outcome_value_rounding` for every action, the executed word is finite, at most
`exactOutcomeMean` plus one term allowance per occupied position plus
`(2^(-11) + meanRadius) · 2^k`, at least `exactOutcomeMean` less the same with
`meanSlack` in place of `meanRadius`, and at most `8000 · 2^k` in magnitude. -/
theorem outcome_mean_rounding (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) (k : Nat) (small : k ≤ 20)
    (narrow : (rankDimension dimension).capacity ≤ 64) (finite : shared.Finite)
    (room : ∀ action, 6528 + |numerical32 shared| +
      |numerical32 (deviationWord transition features action)| + 1 / 2048 * (2 : ℚ) ^ k ≤
        8000 * (2 : ℚ) ^ k) :
    (transition.lookahead value features shared).Finite ∧
      exactOutcomeMean transition value features shared -
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 2048 * (2 : ℚ) ^ k +
            meanSlack * (2 : ℚ) ^ k) ≤
        numerical32 (transition.lookahead value features shared) ∧
      numerical32 (transition.lookahead value features shared) ≤
        exactOutcomeMean transition value features shared +
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 2048 * (2 : ℚ) ^ k +
            meanRadius * (2 : ℚ) ^ k) ∧
      |numerical32 (transition.lookahead value features shared)| ≤ 8000 * (2 : ℚ) ^ k := by
  have each := fun action => outcome_value_rounding transition value features shared action k
    small narrow finite (room action)
  have sandwich := expected_sandwich
    (⟨transition.outcomeValues value features shared, value.epsilon⟩ : PolicySnapshot metaCount)
    k small (by decide) fun action => ⟨(each action).1, (each action).2.2⟩
  have close := greedy_mean_close
    (⟨transition.outcomeValues value features shared, value.epsilon⟩ : PolicySnapshot metaCount)
    (exactOutcomeValue transition value features shared)
    ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 2048 * (2 : ℚ) ^ k)
    fun action => ⟨(each action).1, (each action).2.1⟩
  have size := expected_bound
    (⟨transition.outcomeValues value features shared, value.epsilon⟩ : PolicySnapshot metaCount)
    (8000 * (2 : ℚ) ^ k) fun action => ⟨(each action).1, (each action).2.2⟩
  have bounds := abs_le.mp close
  change (PolicySnapshot.expected (⟨transition.outcomeValues value features shared,
    value.epsilon⟩ : PolicySnapshot metaCount)).Finite ∧ _
  unfold exactOutcomeMean
  refine ⟨sandwich.1, ?_, ?_, size.2⟩
  · have lower := sandwich.2.1
    change _ ≤ numerical32 (PolicySnapshot.expected (⟨transition.outcomeValues value features
      shared, value.epsilon⟩ : PolicySnapshot metaCount))
    linarith [bounds.1]
  · have upper := sandwich.2.2
    change numerical32 (PolicySnapshot.expected (⟨transition.outcomeValues value features
      shared, value.epsilon⟩ : PolicySnapshot metaCount)) ≤ _
    linarith [bounds.2]

/-- The differential backed-up value from a room for every action: the centering
`r − g · d` is rounded twice at magnitude at most `2^7`, and the last addition once below
`2^13 · 2^k`. -/
theorem differential_backup_close
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (k : Nat) (small : k ≤ 20)
    (narrow : (rankDimension dimension).capacity ≤ 64)
    (room : ∀ action, 6528 + |numerical32 (c.state.linearPrediction
        (modelInput .differential features age))| +
      |numerical32 (deviationWord transition features action)| + 1 / 2048 * (2 : ℚ) ^ k ≤
        8000 * (2 : ℚ) ^ k) :
    let prediction := (Model.differential r c d transition).predict value features age
    (prediction.target gain).Finite ∧
      numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) -
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanSlack) * (2 : ℚ) ^ k) ≤ numerical32 (prediction.target gain) ∧
      numerical32 (prediction.target gain) ≤
        numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) +
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanRadius) * (2 : ℚ) ^ k) := by
  intro prediction
  have scale : (1 : ℚ) ≤ (2 : ℚ) ^ k := one_le_pow₀ (by norm_num)
  have sharedBound := prediction_bound c.state (modelInput .differential features age)
  change (c.state.linearPrediction (modelInput .differential features age)).Finite ∧ _
    at sharedBound
  have outcome := outcome_mean_rounding transition value features
    (c.state.linearPrediction (modelInput .differential features age)) k small narrow
    sharedBound.1 room
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
  have productBound : |numerical32 gain.value * numerical32 prediction.duration.value| ≤ 128 := by
    rw [abs_of_nonneg (mul_nonneg gb.1 (by linarith [db.1]))]
    nlinarith [gb.2, db.2]
  have product := binary32_rounded_mul gain.value prediction.duration.value gain.legal.1
    prediction.duration.legal.1 (by linarith)
  have productError := binary32_mul_unit_error gain.value prediction.duration.value
    gain.legal.1 prediction.duration.legal.1 product.1 productBound
  have capWord := binary32_rounded_exact (Binary32.mk 0x43000000) (by decide)
  have capValue : numerical32 (Binary32.mk 0x43000000) = 128 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-16 : Int) = 128
    norm_num
  rw [capValue] at capWord
  have productHigh : numerical32 (gain.value.mul prediction.duration.value) ≤ 128 :=
    Rounded.mono product.2 capWord (le_trans (le_abs_self _) productBound)
  have productLow : 0 ≤ numerical32 (gain.value.mul prediction.duration.value) :=
    Rounded.mono rounded_zero product.2 (mul_nonneg gb.1 (by linarith [db.1]))
  have differenceBound : |numerical32 prediction.reward.value -
      numerical32 (gain.value.mul prediction.duration.value)| ≤ 128 :=
    abs_le.mpr ⟨by linarith [rb.1], by linarith [rb.2]⟩
  have centered := centered_reward_bound prediction.reward.value gain.value
    prediction.duration.value prediction.reward.legal.1 gain.legal.1 prediction.duration.legal.1
    rb gb db
  have centeredError := binary32_sub_unit_error prediction.reward.value
    (gain.value.mul prediction.duration.value) prediction.reward.legal.1 product.1 centered.1
    differenceBound
  have continuationSame : prediction.continuation = transition.lookahead value features
      (c.state.linearPrediction (modelInput .differential features age)) := rfl
  have sumBound : |numerical32 (prediction.reward.value.sub
      (gain.value.mul prediction.duration.value)) + numerical32 prediction.continuation| <
      8192 * (2 : ℚ) ^ k := by
    rw [continuationSame]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith [centered.2, outcome.2.2.2])
  have sum := binary32_add_scaled
    (prediction.reward.value.sub (gain.value.mul prediction.duration.value))
    prediction.continuation k small centered.1 (continuationSame ▸ outcome.1) sumBound
  have target : prediction.target gain = (prediction.reward.value.sub
      (gain.value.mul prediction.duration.value)).add prediction.continuation := rfl
  rw [target]
  have sumBounds := abs_le.mp sum.2
  have centeredBounds := abs_le.mp centeredError
  have productBounds := abs_le.mp productError
  rw [continuationSame] at sumBounds ⊢
  refine ⟨continuationSame ▸ sum.1, ?_, ?_⟩
  · linarith [outcome.2.1]
  · linarith [outcome.2.2.1]

/-- Backup identity with its rounding bound, for the executed differential backed-up
value, for every model state. Let `M` be `exactOutcomeMean` of the stored words, `r`, `d`
the stored reward and duration predictions and `g` the gain. For every model, value
function, frame and gain with at most 64 ranked positions, and any `k` up to 20 for
which the prediction envelopes of the active inputs fit below `8000 · 2^k`, the executed
target is finite and lies between `r − g · d + M` less one term allowance per occupied
position, `2^(-16)` and `(3 · 2^(-12) + meanSlack) · 2^k`, and `r − g · d + M` plus the
same with `meanRadius` in place of `meanSlack`. The lower side is wider by the tie window
of the nominal mean. The hypothesis is on the counts of active inputs; no hypothesis is
made on the stored state. `differential_backup_total` takes `k = 20`, which every input
satisfies, and `differential_backup_small` is the tight case. -/
theorem differential_backup_rounding
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (k : Nat) (small : k ≤ 20)
    (narrow : (rankDimension dimension).capacity ≤ 64)
    (fits : 6528 + predictionRadius (modelInput .differential features age).indices.length +
      predictionRadius (transition.ranked.input features).indices.length +
        1 / 2048 * (2 : ℚ) ^ k ≤ 8000 * (2 : ℚ) ^ k) :
    let prediction := (Model.differential r c d transition).predict value features age
    (prediction.target gain).Finite ∧
      numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) -
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanSlack) * (2 : ℚ) ^ k) ≤ numerical32 (prediction.target gain) ∧
      numerical32 (prediction.target gain) ≤
        numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) +
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanRadius) * (2 : ℚ) ^ k) := by
  have sharedBound := prediction_bound c.state (modelInput .differential features age)
  change (c.state.linearPrediction (modelInput .differential features age)).Finite ∧
    |numerical32 (c.state.linearPrediction (modelInput .differential features age))| ≤
      predictionRadius (modelInput .differential features age).indices.length at sharedBound
  exact differential_backup_close r c d transition value features age gain k small narrow
    fun action => envelope_room transition features _ _ k action sharedBound.2 fits

/-- The differential backup identity with no hypothesis beyond the ranked width: for
every model state, value function, frame and gain, the executed target is finite and
within the allowance of `differential_backup_rounding` at `k = 20` of `r − g · d + M`.
The bound is as loose as the largest prediction envelope is large. -/
theorem differential_backup_total
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (narrow : (rankDimension dimension).capacity ≤ 64) :
    let prediction := (Model.differential r c d transition).predict value features age
    (prediction.target gain).Finite ∧
      numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) -
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanSlack) * (2 : ℚ) ^ 20) ≤ numerical32 (prediction.target gain) ∧
      numerical32 (prediction.target gain) ≤
        numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) +
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanRadius) * (2 : ℚ) ^ 20) :=
  differential_backup_rounding r c d transition value features age gain 20 (by decide) narrow
    (envelope_total transition features _)

/-- The tight case of the differential backup identity, conditional on the stored
state: when the stored shared and deviation predictions have summed magnitude at most
1024, the allowance is that of `differential_backup_rounding` at `k = 0`. Nothing
enforces the condition; `differential_backup_rounding` is the statement without it. -/
theorem differential_backup_small
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) (narrow : (rankDimension dimension).capacity ≤ 64)
    (room : ∀ action, |numerical32 (c.state.linearPrediction
        (modelInput .differential features age))| +
      |numerical32 (deviationWord transition features action)| ≤ 1024) :
    let prediction := (Model.differential r c d transition).predict value features age
    (prediction.target gain).Finite ∧
      numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) -
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanSlack)) ≤ numerical32 (prediction.target gain) ∧
      numerical32 (prediction.target gain) ≤
        numerical32 prediction.reward.value -
          numerical32 gain.value * numerical32 prediction.duration.value +
          exactOutcomeMean transition value features
            (c.state.linearPrediction (modelInput .differential features age)) +
          ((transition.ranked.occupied.length : ℚ) * termRadius + 1 / 65536 +
            (3 / 4096 + meanRadius)) := by
  have result := differential_backup_close r c d transition value features age gain 0
    (by decide) narrow fun action => by norm_num; linarith [room action]
  simpa using result

/-! ## The differential backed-up value stays finite -/

/-- The differential value of the predicted outcome is finite and inside the outcome
envelope, for every model state, value function and frame. The rational envelope
includes machine-rounding slack; it is not a clip. -/
theorem differential_continuation_bound
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    let prediction := (Model.differential r c d transition).predict value features age
    prediction.continuation.Finite ∧ |numerical32 prediction.continuation| ≤
      outcomeRadius transition features (modelInput .differential features age).indices.length := by
  intro prediction
  have shared := prediction_bound c.state (modelInput .differential features age)
  change (c.state.linearPrediction (modelInput .differential features age)).Finite ∧
    |numerical32 (c.state.linearPrediction (modelInput .differential features age))| ≤
      predictionRadius (modelInput .differential features age).indices.length at shared
  exact expected_bound
    (⟨transition.outcomeValues value features
      (c.state.linearPrediction (modelInput .differential features age)), value.epsilon⟩ :
      PolicySnapshot metaCount) _
    fun action => outcome_value_bound transition value features _ _ action shared.1 shared.2

/-- The executed differential backed-up value is finite under the actual producer
ranges, for every model state, value function, frame and gain. -/
theorem differential_target_bound
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (transition : Transition dimension .differential)
    (value : ValueFunction .differential dimension) (features : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (gain : RewardRate) :
    let prediction := (Model.differential r c d transition).predict value features age
    (prediction.target gain).Finite ∧ |numerical32 (prediction.target gain)| ≤
      outcomeRadius transition features (modelInput .differential features age).indices.length +
        384 := by
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
    outcomeRadius transition features (modelInput .differential features age).indices.length
    at continuation
  have sharedCap := radius_cap (modelInput .differential features age).indices.length
  have rankedCap := ranked_radius transition.ranked
  have inputCap := input_radius transition.ranked features
  unfold outcomeRadius at continuation ⊢
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

/-- Retained logical slots of one transition part, summed over its row learners and
its deviation learners. -/
def transitionSlots (transition : Transition dimension criterion) : Nat :=
  (transition.rows.toList.map fun row => retainedSlots row.state).sum +
    (transition.deviations.toList.map fun learner => retainedSlots learner.state).sum

/-- A transition part holds the ranked width times the ranked width plus the meta
action count in weights: one row per position and one deviation learner per meta
action, each over the ranked positions. -/
theorem transition_weights (transition : Transition dimension criterion) :
    (transition.rows.toList.length + transition.deviations.toList.length) *
        (rankDimension dimension).capacity =
      (rankWidth dimension + Acorn.FeatureConstants.metaActionCount) * rankWidth dimension := by
  simp

/-- The logical retained storage of a transition part's learners is quadratic in the
ranked width, independently of stream length: each row and each deviation learner is a
learner over the ranked positions. The part also holds the slot vector and the lookup
table of `transition_table`. Native object headers and allocator reuse are separate. -/
theorem transition_storage (transition : Transition dimension criterion) :
    transitionSlots transition ≤
      (rankWidth dimension + Acorn.FeatureConstants.metaActionCount) *
        (13 * rankWidth dimension + 2) := by
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
  have rows := bound transition.rows.toList
  have deviations := bound transition.deviations.toList
  simp only [Vector.length_toList] at rows deviations
  unfold transitionSlots
  rw [Nat.add_mul]
  exact Nat.add_le_add rows deviations

/-- Beside its rows a transition part holds one lookup word per feature slot and one
slot word per position: linear in the dimension, and outside the weight budget. -/
theorem transition_table (transition : Transition dimension criterion) :
    transition.ranked.table.toList.length = dimension.capacity ∧
      transition.ranked.slots.toList.length = (rankDimension dimension).capacity := by
  simp

/-- The width follows from a memory budget on the rows: the rows of all options'
transition parts together hold at most one weight vector's worth of weights. The
deviation learners are outside this statement; `complete_budget` and `default_budget`
count them. -/
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

/-- The complete transition parts, rows and deviation learners, of all options hold
`skillCount · k · (k + 4)` weights. That is within one weight vector whenever the
dimension has at least 1024 slots; at 256 slots the width is 8 and the three parts hold
288 weights, more than one weight vector, although their rows fit. -/
theorem complete_budget (dimension : Dimension) (large : 1024 ≤ dimension.capacity) :
    Acorn.FeatureConstants.skillCount *
        (((rankDimension dimension).capacity + Acorn.FeatureConstants.metaActionCount) *
          (rankDimension dimension).capacity) ≤ dimension.capacity := by
  obtain ⟨exponent, power⟩ := dimension.powerOfTwo
  have enough : Acorn.FeatureConstants.skillCount ≤ dimension.capacity :=
    le_trans (by decide) large
  have rows := rankWidth_budget dimension enough
  have least := rankWidth_maximal dimension
  have width := rankWidth_eq dimension
  change Acorn.FeatureConstants.skillCount *
    ((rankWidth dimension + Acorn.FeatureConstants.metaActionCount) * rankWidth dimension) ≤
      dimension.capacity
  rw [width] at rows ⊢
  rw [power] at rows least large ⊢
  have skills : Acorn.FeatureConstants.skillCount = 3 := rfl
  have actions : Acorn.FeatureConstants.metaActionCount = 4 := rfl
  rw [skills] at rows least ⊢
  rw [actions]
  have wide : 4 ≤ rankExponent dimension := by
    by_contra narrow
    have small : rankExponent dimension + 1 ≤ 4 := by omega
    have bound : 2 ^ (rankExponent dimension + 1) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by decide) small
    have product := Nat.mul_le_mul bound bound
    omega
  have square : 2 ^ rankExponent dimension * 2 ^ rankExponent dimension =
      2 ^ (2 * rankExponent dimension) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have room : 2 * rankExponent dimension + 2 ≤ exponent := by
    by_contra tight
    have small : exponent ≤ 2 * rankExponent dimension + 1 := by omega
    have bound : 2 ^ exponent ≤ 2 ^ (2 * rankExponent dimension + 1) :=
      Nat.pow_le_pow_right (by decide) small
    rw [Nat.pow_succ] at bound
    rw [square] at rows
    omega
  have capacity : 2 ^ (2 * rankExponent dimension + 2) ≤ 2 ^ exponent :=
    Nat.pow_le_pow_right (by decide) room
  have sixteen : 2 ^ 4 ≤ 2 ^ rankExponent dimension := Nat.pow_le_pow_right (by decide) wide
  have grows := Nat.mul_le_mul_right (2 ^ rankExponent dimension) sixteen
  rw [Nat.pow_add, ← square] at capacity
  nlinarith

/-- For 16 384 feature slots the transition parts of all options, deviation learners
included, hold 13 056 weights: within one weight vector. -/
theorem default_budget (dimension : Dimension) (standard : dimension.capacity = 16384) :
    Acorn.FeatureConstants.skillCount *
        (((rankDimension dimension).capacity + Acorn.FeatureConstants.metaActionCount) *
          (rankDimension dimension).capacity) ≤ dimension.capacity := by
  rw [default_width dimension standard, standard]
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

/-- Every deviation learner keeps an eligibility list within the ranked width, after
every update. -/
theorem deviation_work (transition : Transition dimension criterion)
    (action : Action metaCount.word.toNat) :
    (transition.deviations.get action).state.eligibleCount ≤ (rankDimension dimension).capacity :=
  managed_capacity _

/-- A change of ranking changes at most the ranked width of positions. Each retained
row and each deviation learner then retires each changed position once, and one
retirement searches that learner's eligibility list, at most the ranked width
(`row_work`, `deviation_work`): the work of forgetting is at most the number of
learners times the changed positions times the ranked width. -/
theorem changed_work (before after : RankedFeatures dimension) :
    (before.changed after).length ≤ (rankDimension dimension).capacity := by
  have bound := List.length_filter_le
    (fun position : RankIdx dimension => after.slots[position.val] != before.slots[position.val])
    (List.finRange (rankDimension dimension).capacity)
  simpa [RankedFeatures.changed] using bound

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
    (fresh : order.Nodup)
    (held : ranked.slots[position.val] = some feature) (still : feature ∈ order) :
    (ranked.rerank order fresh).slots[position.val] = some feature := by
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
    (fresh : order.Nodup) (position : RankIdx dimension) (feature : FeatIdx dimension)
    (modeled : (ranked.rerank order fresh).slots[position.val] = some feature) :
    feature ∈ order := by
  have inside : (ranked.rerank order fresh).slots[position.val] ∈
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

/-- Retiring positions keeps a learner's weight from every other position. -/
theorem retire_fold_other (retired : List (RankIdx dimension)) (column : RankIdx dimension) :
    ∀ learner : Managed (criterion.config .demon) (rankDimension dimension), column ∉ retired →
      (retired.foldl (fun current position => current.retire position)
        learner).state.weights.get column = learner.state.weights.get column := by
  induction retired with
  | nil => intro learner _; rfl
  | cons head tail ih =>
    intro learner absent
    have different : column ≠ head := fun same => absent (by simp [same])
    have rest : column ∉ tail := fun inside => absent (List.mem_cons_of_mem _ inside)
    rw [List.foldl_cons, ih (learner.retire head) rest]
    exact CurrentRetirement.retireIndex_weight_other learner.state head column different

/-- Retiring positions zeroes a learner's weight from each of them. -/
theorem retire_fold_column (retired : List (RankIdx dimension)) (column : RankIdx dimension) :
    ∀ learner : Managed (criterion.config .demon) (rankDimension dimension),
      (column ∈ retired ∨ (learner.state.weights.get column).value = Binary32.zero) →
      ((retired.foldl (fun current position => current.retire position)
        learner).state.weights.get column).value = Binary32.zero := by
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

/-- Forgetting positions leaves every other row's weight from every other position
bit-identical: only the forgotten rows and input columns lose what was learned. -/
theorem forget_other
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) (row column : RankIdx dimension)
    (keptRow : row ∉ positions) (keptColumn : column ∉ positions) :
    ((Transition.forget rows positions).get row).state.weights.get column =
      (rows.get row).state.weights.get column := by
  have skipped : (positions.contains row) = false := by
    simpa [List.contains_iff_mem] using keptRow
  simp only [Transition.forget, vector_get, Vector.getElem_mapFinIdx, Fin.eta, skipped,
    Bool.false_eq_true, ↓reduceIte]
  exact retire_fold_other positions column _ keptColumn

/-- Forgetting a position zeroes every other row's weight from it: no row keeps what
it learned about the slot that was there. -/
theorem forget_column
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) (row column : RankIdx dimension)
    (keptRow : row ∉ positions) (forgotten : column ∈ positions) :
    (((Transition.forget rows positions).get row).state.weights.get column).value =
      Binary32.zero := by
  have skipped : (positions.contains row) = false := by
    simpa [List.contains_iff_mem] using keptRow
  simp only [Transition.forget, vector_get, Vector.getElem_mapFinIdx, Fin.eta, skipped,
    Bool.false_eq_true, ↓reduceIte]
  exact retire_fold_column positions column _ (Or.inl forgotten)

/-- Forgetting a position replaces its row by a fresh learner. -/
theorem forget_row
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity)
    (positions : List (RankIdx dimension)) (row : RankIdx dimension) (forgotten : row ∈ positions) :
    (Transition.forget rows positions).get row = Managed.initial _ _ := by
  simp [Transition.forget, vector_get, forgotten]

/-- A deviation learner keeps its weight from every position that is not forgotten. -/
theorem forgetColumns_other {size : Nat}
    (learners : Vector (Managed (criterion.config .demon) (rankDimension dimension)) size)
    (positions : List (RankIdx dimension)) (index : Fin size) (column : RankIdx dimension)
    (kept : column ∉ positions) :
    ((Transition.forgetColumns learners positions).get index).state.weights.get column =
      (learners.get index).state.weights.get column := by
  simp only [Transition.forgetColumns, vector_get, Vector.getElem_map]
  exact retire_fold_other positions column _ kept

/-- A deviation learner's weight from a forgotten position is zero. -/
theorem forgetColumns_column {size : Nat}
    (learners : Vector (Managed (criterion.config .demon) (rankDimension dimension)) size)
    (positions : List (RankIdx dimension)) (index : Fin size) (column : RankIdx dimension)
    (forgotten : column ∈ positions) :
    (((Transition.forgetColumns learners positions).get index).state.weights.get column).value =
      Binary32.zero := by
  simp only [Transition.forgetColumns, vector_get, Vector.getElem_map]
  exact retire_fold_column positions column _ (Or.inl forgotten)

/-- A position whose slot stays ranked is not among the changed positions. -/
theorem retained_unchanged (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension))
    (fresh : order.Nodup) (position : RankIdx dimension) (feature : FeatIdx dimension)
    (held : ranked.slots[position.val] = some feature) (still : feature ∈ order) :
    position ∉ ranked.changed (ranked.rerank order fresh) := by
  intro inside
  have differs := (List.mem_filter.mp inside).2
  rw [rerank_retained ranked order position feature fresh held still, held] at differs
  simp at differs

/-- The bias position is never among the changed positions: it holds no slot before
or after any ranking. -/
theorem bias_unchanged (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension))
    (fresh : order.Nodup) :
    RankedFeatures.bias dimension ∉ ranked.changed (ranked.rerank order fresh) := by
  intro inside
  have differs := (List.mem_filter.mp inside).2
  rw [(ranked.rerank order fresh).bias_vacant, ranked.bias_vacant] at differs
  simp at differs

/-- A change of subset keeps what was learned between retained slots: the weight a
retained slot's row holds for another retained slot is bit-identical after the new
ranking is installed. Weights from a changed position are zeroed (`forget_column`). -/
theorem rerank_weights (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) (row column : RankIdx dimension)
    (rowFeature columnFeature : FeatIdx dimension)
    (rowHeld : transition.ranked.slots[row.val] = some rowFeature)
    (rowStill : rowFeature ∈ order)
    (columnHeld : transition.ranked.slots[column.val] = some columnFeature)
    (columnStill : columnFeature ∈ order) :
    ((transition.rerank order fresh).rows.get row).state.weights.get column =
      (transition.rows.get row).state.weights.get column :=
  forget_other transition.rows _ row column
    (retained_unchanged transition.ranked order fresh row rowFeature rowHeld rowStill)
    (retained_unchanged transition.ranked order fresh column columnFeature columnHeld columnStill)

/-- A change of subset keeps a retained slot's bias weight bit-identical. -/
theorem rerank_bias (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) (row : RankIdx dimension)
    (rowFeature : FeatIdx dimension)
    (rowHeld : transition.ranked.slots[row.val] = some rowFeature)
    (rowStill : rowFeature ∈ order) :
    ((transition.rerank order fresh).rows.get row).state.weights.get
        (RankedFeatures.bias dimension) =
      (transition.rows.get row).state.weights.get (RankedFeatures.bias dimension) :=
  forget_other transition.rows _ row (RankedFeatures.bias dimension)
    (retained_unchanged transition.ranked order fresh row rowFeature rowHeld rowStill)
    (bias_unchanged transition.ranked order fresh)

/-- A change of subset keeps every deviation learner's weight from each retained slot
and from the bias bit-identical. -/
theorem rerank_deviations (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup)
    (action : Action metaCount.word.toNat) (column : RankIdx dimension)
    (kept : (∃ feature, transition.ranked.slots[column.val] = some feature ∧ feature ∈ order) ∨
      column = RankedFeatures.bias dimension) :
    ((transition.rerank order fresh).deviations.get action).state.weights.get column =
      (transition.deviations.get action).state.weights.get column := by
  refine forgetColumns_other transition.deviations _ action column ?_
  rcases kept with ⟨feature, held, still⟩ | bias
  · exact retained_unchanged transition.ranked order fresh column feature held still
  · rw [bias]
    exact bias_unchanged transition.ranked order fresh

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

/-! ## The terminal target of a row -/

/-- Setting the entries at a list of positions leaves every other entry as it was. -/
theorem fold_present (positions : List (RankIdx dimension)) :
    ∀ (seen : Vector Expectation (rankDimension dimension).capacity)
      (position : RankIdx dimension),
      (positions.foldl (fun current active =>
        current.set active.val Expectation.present active.isLt) seen).get position =
        if position ∈ positions then Expectation.present else seen.get position := by
  induction positions with
  | nil => intro seen position; simp
  | cons head rest ih =>
    intro seen position
    rw [List.foldl_cons, ih (seen.set head.val Expectation.present head.isLt) position]
    by_cases later : position ∈ rest
    · simp [later]
    · by_cases same : position = head
      · subst same
        simp [later, vector_get]
      · have different : head.val ≠ position.val := fun equal => same (Fin.ext equal.symm)
        simp [later, same, vector_get, Vector.getElem_set_ne _ _ different]

/-- A slot is looked up at exactly the position that holds it. -/
theorem position_exact (ranked : RankedFeatures dimension) (position : RankIdx dimension)
    (feature : FeatIdx dimension) (held : ranked.slots[position.val] = some feature) :
    ranked.position feature = some position := by
  obtain ⟨found, located⟩ := ranked.position_complete position feature held
  rw [located, ranked.slot_unique found position feature
    (ranked.position_slot feature found located) held]

/-- The indicator of a frame is one at an occupied position exactly when that position's
slot is active in the frame, and zero otherwise. With `Transition.terminal` this is the
terminal target of every row: `γ` times its own slot's activity at the terminal frame. -/
theorem indicator_exact (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) (position : RankIdx dimension)
    (feature : FeatIdx dimension) (held : ranked.slots[position.val] = some feature) :
    (ranked.indicator features).get position =
      if feature ∈ features.indices then Expectation.present else Expectation.absent := by
  have fold := fold_present (ranked.active features).indices
    (Vector.replicate _ Expectation.absent) position
  have member : position ∈ (ranked.active features).indices ↔ feature ∈ features.indices := by
    constructor
    · intro inside
      obtain ⟨other, active, modeled⟩ := ranked.active_sound features position inside
      rw [held] at modeled
      rw [Option.some.inj modeled]
      exact active
    · intro active
      obtain ⟨found, inside, modeled⟩ := ranked.active_complete features position feature held
        active
      rw [← ranked.slot_unique found position feature modeled held]
      exact inside
  unfold RankedFeatures.indicator
  rw [fold]
  by_cases active : feature ∈ features.indices
  · simp [active, member.mpr active]
  · have absent : position ∉ (ranked.active features).indices := fun inside =>
      active (member.mp inside)
    simp [active, absent, vector_get]

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
