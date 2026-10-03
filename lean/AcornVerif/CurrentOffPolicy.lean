/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Extragradient
import AcornVerif.CurrentPolicyMean
import AcornVerif.CurrentLearner
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Off-policy question contracts

Every statement concerns the executed definitions of `Acorn.OffPolicy`.

**Energy.** `step_energy` is `AcornVerif.Extragradient.extragradient_energy` carried to
the executed GTD2-MP step, for every learner state, every classified transition, every
finite signal word in `[−1, 1]` and every reference `w*` inside the weight range, for
feature spaces of at most `2^16` slots. With `N = |u|² + |w − w*|²`: if `N ≤ t²` before the
step, `h·τ ≤ s²`, `|w*|² ≤ m²` and `(2|x| + |x'|)·2^(−48) ≤ R²`, then after it
`N ≤ ((1 + 2^(−21))·t + (1 + 2^(−22))·|ε|·s + 2^(−21)·m + R)²`. Here `h` is the executed
step-size word, `τ = h|x|`, and `ε = c − ⟨x − γx', w*⟩` is the TD error the reference leaves.
Against `w* = 0` the length of `(u, w)` grows per step by at most the factor `1 + 2^(−21)`,
plus the signal's push and `R`.

The proof has three parts. `exact_energy` applies the exact inequality to the exact step
from the stored words with the executed step size, whose guard `step_guard` proves.
`second_slot` and `main_slot` bound, slot by slot, how far each written word is from that
exact step before the weight projection: each binary32 write and each narrowed increment is
one nearest-even rounding, within `2^(−24)` of its exact value relative to its magnitude
plus `2^(−150)` (`binary32_add_relative`, `narrow_relative`), and the binary64 scalars are
within `2^(−26)` of their exact values after the step-size scaling (`scalars_approx`,
`increments_close`). The projection never moves a word away from a point inside the range
(`clampSym_toward`, `project_value`).

**Guard.** `step_guard` shows that the executed step size makes `τ(τ + 2κ) ≤ 1` and
`κ ≤ 2 − τ` hold for every transition: `h·(|x| + |x'|) ≤ 1/9`.

**Classes and writes.** `step_second` and `step_main` give every written word: the second
weights change exactly at `x`, the main weights exactly at `x ∪ x'`, and each slot is
written once, with the increment of its class.

**Questions.** The executed step of a question is `Question.step`: a question that has
learned from no signal word other than zero takes no step at a zero signal word, and every
other step is the learner's (`question_step`). `question_energy` gives the executed step
the bound of `step_energy` in both cases, and `silent_fixed` shows that where no step is
taken, Algorithm 2 in exact arithmetic adds zero to every weight.

Arithmetic statements are about Lean's float model through `AcornVerif.FloatLibBridge`
and the binary64 lemmas of `AcornVerif.CurrentPolicyMean`; the native primitive
correspondence is the declared trust boundary.
-/

open Acorn Acorn.Features
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder
open AcornVerif.CurrentOperations AcornVerif.CurrentPrediction AcornVerif.CurrentBackupBounds
open AcornVerif.CurrentPolicyMean AcornVerif.FloatLibBridge AcornVerif.CurrentLearner

namespace AcornVerif.CurrentOffPolicy

/-! ## Binary64 subtraction at a scale -/

/-- Actual binary64 subtraction at magnitude at most `2^16 · 2^k`: finite and within
`2^(-37) · 2^k` of the exact difference. -/
theorem binary64_sub_scaled (left right : Binary64) (k : Nat) (small : k ≤ 20)
    (leftFinite : left.Finite) (rightFinite : right.Finite)
    (bound : |numerical64 left - numerical64 right| ≤ 65536 * (2 : ℚ) ^ k) :
    (left.sub right).Finite ∧
      |numerical64 (left.sub right) - (numerical64 left - numerical64 right)| ≤
        1 / 137438953472 * (2 : ℚ) ^ k := by
  have positive : (0 : ℚ) < (2 : ℚ) ^ k := pow_pos (by norm_num) k
  have leftNormal := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rightNormal := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have localProof := model_sub_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    leftNormal rightNormal ((16 : Int) + (k : Int))
    (by rw [wide_limit]; simpa only [numerical64] using bound)
  have error : |unpackedValue (UnpackedFloat.sub Format.binary64 (decoded64 left)
      (decoded64 right)) - (numerical64 left - numerical64 right)| ≤
      1 / 137438953472 * (2 : ℚ) ^ k := by
    have result := localProof.2
    rw [wide_radius] at result
    simpa only [numerical64] using result
  have fits := wide_fits _ _ k small localProof.1 bound (by linarith)
  have exactDecoded := model_sub64_decoded left right leftFinite rightFinite localProof.1 fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [exactDecoded]
    exact model_normalized_finite _ _ localProof.1
  · simpa only [numerical64, exactDecoded] using error

/-! ## Approximation with an error and a magnitude -/

/-- A finite binary64 word within `error` of an exact value of magnitude at most
`magnitude`. -/
def Approx (word : Binary64) (value error magnitude : ℚ) : Prop :=
  word.Finite ∧ |numerical64 word - value| ≤ error ∧ |value| ≤ magnitude

theorem Approx.word_bound {word : Binary64} {value error magnitude : ℚ}
    (near : Approx word value error magnitude) :
    |numerical64 word| ≤ magnitude + error := by
  have triangle := abs_add_le (numerical64 word - value) value
  rw [sub_add_cancel] at triangle
  linarith [near.2.1, near.2.2]

theorem Approx.exact {word : Binary64} (finite : word.Finite) {magnitude : ℚ}
    (bound : |numerical64 word| ≤ magnitude) : Approx word (numerical64 word) 0 magnitude :=
  ⟨finite, by simp, bound⟩

theorem Approx.widen {value : Binary32} (finite : value.Finite) {magnitude : ℚ}
    (bound : |numerical32 value| ≤ magnitude) :
    Approx (Conversion.widen value) (numerical32 value) 0 magnitude :=
  ⟨Conversion.widen_finite value finite, by rw [numerical_widen_exact value finite]; simp, bound⟩

theorem Approx.add {left right : Binary64} {lv le lm rv re rm : ℚ} (k : Nat) (small : k ≤ 20)
    (l : Approx left lv le lm) (r : Approx right rv re rm)
    (room : lm + le + (rm + re) ≤ 65536 * (2 : ℚ) ^ k) :
    Approx (left.add right) (lv + rv) (le + re + 1 / 137438953472 * (2 : ℚ) ^ k) (lm + rm) := by
  have lb := l.word_bound
  have rb := r.word_bound
  have sum := binary64_add_scaled left right k small l.1 r.1
    (le_trans (abs_add_le _ _) (by linarith))
  refine ⟨sum.1, ?_, le_trans (abs_add_le _ _) (by linarith [l.2.2, r.2.2])⟩
  have split : numerical64 (left.add right) - (lv + rv) =
      (numerical64 (left.add right) - (numerical64 left + numerical64 right)) +
        ((numerical64 left - lv) + (numerical64 right - rv)) := by ring
  rw [split]
  have outer := abs_add_le (numerical64 (left.add right) - (numerical64 left + numerical64 right))
    ((numerical64 left - lv) + (numerical64 right - rv))
  have inner := abs_add_le (numerical64 left - lv) (numerical64 right - rv)
  linarith [sum.2, l.2.1, r.2.1]

theorem Approx.sub {left right : Binary64} {lv le lm rv re rm : ℚ} (k : Nat) (small : k ≤ 20)
    (l : Approx left lv le lm) (r : Approx right rv re rm)
    (room : lm + le + (rm + re) ≤ 65536 * (2 : ℚ) ^ k) :
    Approx (left.sub right) (lv - rv) (le + re + 1 / 137438953472 * (2 : ℚ) ^ k) (lm + rm) := by
  have lb := l.word_bound
  have rb := r.word_bound
  have difference := binary64_sub_scaled left right k small l.1 r.1
    (le_trans (abs_sub _ _) (by linarith))
  refine ⟨difference.1, ?_, le_trans (abs_sub _ _) (by linarith [l.2.2, r.2.2])⟩
  have split : numerical64 (left.sub right) - (lv - rv) =
      (numerical64 (left.sub right) - (numerical64 left - numerical64 right)) +
        ((numerical64 left - lv) - (numerical64 right - rv)) := by ring
  rw [split]
  have outer := abs_add_le (numerical64 (left.sub right) - (numerical64 left - numerical64 right))
    ((numerical64 left - lv) - (numerical64 right - rv))
  have inner := abs_sub (numerical64 left - lv) (numerical64 right - rv)
  linarith [difference.2, l.2.1, r.2.1]

theorem Approx.mul {left right : Binary64} {lv le lm rv re rm : ℚ} (k : Nat) (small : k ≤ 20)
    (l : Approx left lv le lm) (r : Approx right rv re rm)
    (room : (lm + le) * (rm + re) ≤ 65536 * (2 : ℚ) ^ k) :
    Approx (left.mul right) (lv * rv)
      (le * (rm + re) + lm * re + 1 / 137438953472 * (2 : ℚ) ^ k) (lm * rm) := by
  have lb := l.word_bound
  have rb := r.word_bound
  have leNonneg : 0 ≤ le := le_trans (abs_nonneg _) l.2.1
  have reNonneg : 0 ≤ re := le_trans (abs_nonneg _) r.2.1
  have lmNonneg : 0 ≤ lm := le_trans (abs_nonneg _) l.2.2
  have product : |numerical64 left * numerical64 right| ≤ 65536 * (2 : ℚ) ^ k := by
    rw [abs_mul]
    exact le_trans (mul_le_mul lb rb (abs_nonneg _) (by linarith)) room
  have rounded := binary64_mul_scaled left right k small l.1 r.1 product
  refine ⟨rounded.1, ?_, ?_⟩
  · have split : numerical64 (left.mul right) - lv * rv =
        (numerical64 (left.mul right) - numerical64 left * numerical64 right) +
          ((numerical64 left - lv) * numerical64 right + lv * (numerical64 right - rv)) := by
      ring
    rw [split]
    have outer := abs_add_le (numerical64 (left.mul right) - numerical64 left * numerical64 right)
      ((numerical64 left - lv) * numerical64 right + lv * (numerical64 right - rv))
    have inner := abs_add_le ((numerical64 left - lv) * numerical64 right)
      (lv * (numerical64 right - rv))
    have first : |(numerical64 left - lv) * numerical64 right| ≤ le * (rm + re) := by
      rw [abs_mul]
      exact mul_le_mul l.2.1 rb (abs_nonneg _) leNonneg
    have second : |lv * (numerical64 right - rv)| ≤ lm * re := by
      rw [abs_mul]
      exact mul_le_mul l.2.2 r.2.1 (abs_nonneg _) lmNonneg
    linarith [rounded.2]
  · rw [abs_mul]
    exact mul_le_mul l.2.2 r.2.2 (abs_nonneg _) lmNonneg

/-- Replace the magnitude by any bound on the value. -/
theorem Approx.within {word : Binary64} {value error magnitude magnitude' : ℚ}
    (near : Approx word value error magnitude) (bound : |value| ≤ magnitude') :
    Approx word value error magnitude' :=
  ⟨near.1, near.2.1, bound⟩

theorem Approx.mono {word : Binary64} {value error magnitude error' magnitude' : ℚ}
    (near : Approx word value error magnitude) (errorLe : error ≤ error')
    (magnitudeLe : magnitude ≤ magnitude') : Approx word value error' magnitude' :=
  ⟨near.1, le_trans near.2.1 errorLe, le_trans near.2.2 magnitudeLe⟩

/-! ## Counts, constants and the discount -/

/-- A count below `2^53` is exact in binary64. -/
theorem wideCount_exact (count : Nat) (small : count < 2 ^ 53) :
    Approx (wideCount count) count 0 count := by
  have word : count.toUInt64.toNat = count := by
    change count % 2 ^ 64 = count
    exact Nat.mod_eq_of_lt (by omega)
  have value := numerical64_ofUInt64 count.toUInt64 (by rw [word]; exact small)
  rw [word] at value
  have finite : (wideCount count).Finite := by
    have bound := ofUInt64_word_bound count.toUInt64 (by rw [word]; exact small)
    change (Binary64.ofUInt64 count.toUInt64).bits.toNat &&& (2 ^ 63 - 1) < _
    exact Nat.lt_of_le_of_lt Nat.and_le_left bound
  refine ⟨finite, ?_, ?_⟩
  · change |numerical64 (Binary64.ofUInt64 count.toUInt64) - count| ≤ 0
    rw [value]
    simp
  · have : (0 : ℚ) ≤ count := Nat.cast_nonneg _
    rw [abs_of_nonneg this]

/-- The binary64 one. -/
theorem one_exact : Approx (Binary64.ofUInt64 1) 1 0 1 := by
  have exact := wideCount_exact 1 (by norm_num)
  simp only [Nat.cast_one] at exact
  exact exact

/-- Every discount word is a finite probability. -/
theorem gamma_bounds (discount : Discount) :
    discount.gamma.Finite ∧ 0 ≤ numerical32 discount.gamma ∧ numerical32 discount.gamma ≤ 1 := by
  have finite : discount.gamma.Finite := by cases discount <;> decide
  have zeroFinite : Binary32.zero.Finite := by decide
  have oneFinite : Binary32.one.Finite := by decide
  have zeroValue : numerical32 Binary32.zero = 0 := by decide
  have oneValue : numerical32 Binary32.one = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  have lower := (numerical32_order Binary32.zero discount.gamma zeroFinite finite).mpr
    (by cases discount <;> decide)
  have upper := (numerical32_order discount.gamma Binary32.one finite oneFinite).mpr
    (by cases discount <;> decide)
  rw [zeroValue] at lower
  rw [oneValue] at upper
  exact ⟨finite, lower, upper⟩

/-- The widened discount. -/
theorem gamma_approx (discount : Discount) :
    Approx (Conversion.widen discount.gamma) (numerical32 discount.gamma) 0 1 := by
  have bounds := gamma_bounds discount
  exact Approx.widen bounds.1 (by rw [abs_of_nonneg bounds.2.1]; exact bounds.2.2)

/-! ## Membership indicators -/

/-- The indicator of membership in a list of slots. -/
def indicator {size : Nat} (indices : List (Fin size)) (query : Fin size) : ℚ :=
  if query ∈ indices then 1 else 0

theorem indicator_sq {size : Nat} (indices : List (Fin size)) (query : Fin size) :
    indicator indices query ^ 2 = indicator indices query := by
  unfold indicator
  split <;> norm_num

/-- A sum weighted by the indicator of a list without repeats is the list's sum. -/
theorem sum_indicator {size : Nat} (indices : List (Fin size)) (nodup : indices.Nodup)
    (f : Fin size → ℚ) : ∑ j, f j * indicator indices j = (indices.map f).sum := by
  have pointwise : ∀ j, f j * indicator indices j = if j ∈ indices.toFinset then f j else 0 := by
    intro j
    unfold indicator
    by_cases inside : j ∈ indices <;> simp [inside]
  simp only [pointwise]
  rw [Finset.sum_ite_mem, Finset.univ_inter, List.sum_toFinset f nodup]

/-- The number of slots of a list without repeats. -/
theorem sum_indicator_one {size : Nat} (indices : List (Fin size)) (nodup : indices.Nodup) :
    ∑ j, indicator indices j = indices.length := by
  have := sum_indicator indices nodup (fun _ => 1)
  simpa using this

/-- Every list of distinct slots fits the space. -/
theorem nodup_length {size : Nat} (indices : List (Fin size)) (nodup : indices.Nodup) :
    indices.length ≤ size := by
  simpa using nodup.length_le_card

/-! ## Folds that write -/

/-- An add fold over distinct slots writes each listed slot once, from its old word. -/
theorem addAll_get {rule : ValueRule} {dimension : Dimension}
    (weights : WeightArray rule dimension) (indices : List (FeatIdx dimension)) (delta : Binary32)
    (nodup : indices.Nodup) (query : FeatIdx dimension) :
    (addAll weights indices delta)[query.val] =
      if query ∈ indices then Weight.project rule (weights[query.val].value.add delta)
      else weights[query.val] := by
  induction indices generalizing weights with
  | nil => simp [addAll]
  | cons head tail ih =>
    have fresh := (List.nodup_cons.mp nodup).1
    have step : addAll weights (head :: tail) delta =
        addAll (weights.set head.val
          (Weight.project rule ((weights.get head).value.add delta)) head.isLt) tail delta := rfl
    rw [step, ih _ (List.nodup_cons.mp nodup).2]
    by_cases inTail : query ∈ tail
    · have different : head.val ≠ query.val := fun equal => fresh (by
        rw [show head = query from Fin.ext equal]
        exact inTail)
      simp [inTail, Vector.getElem_set_ne head.isLt query.isLt different]
    · by_cases same : query = head
      · subst same
        simp [inTail, vector_get]
      · have different : head.val ≠ query.val := fun equal => same (Fin.ext equal).symm
        simp [inTail, same, Vector.getElem_set_ne head.isLt query.isLt different]

/-- A subtract fold over distinct slots writes each listed slot once, from its old word. -/
theorem subAll_get {rule : ValueRule} {dimension : Dimension}
    (weights : WeightArray rule dimension) (indices : List (FeatIdx dimension)) (delta : Binary32)
    (nodup : indices.Nodup) (query : FeatIdx dimension) :
    (subAll weights indices delta)[query.val] =
      if query ∈ indices then Weight.project rule (weights[query.val].value.sub delta)
      else weights[query.val] := by
  induction indices generalizing weights with
  | nil => simp [subAll]
  | cons head tail ih =>
    have fresh := (List.nodup_cons.mp nodup).1
    have step : subAll weights (head :: tail) delta =
        subAll (weights.set head.val
          (Weight.project rule ((weights.get head).value.sub delta)) head.isLt) tail delta := rfl
    rw [step, ih _ (List.nodup_cons.mp nodup).2]
    by_cases inTail : query ∈ tail
    · have different : head.val ≠ query.val := fun equal => fresh (by
        rw [show head = query from Fin.ext equal]
        exact inTail)
      simp [inTail, Vector.getElem_set_ne head.isLt query.isLt different]
    · by_cases same : query = head
      · subst same
        simp [inTail, vector_get]
      · have different : head.val ≠ query.val := fun equal => same (Fin.ext equal).symm
        simp [inTail, same, Vector.getElem_set_ne head.isLt query.isLt different]

/-! ## The classes of a transition -/

variable {dimension : Dimension}

theorem onlySource_mem (passage : Passage dimension) (query : FeatIdx dimension) :
    query ∈ passage.onlySource ↔
      query ∈ passage.source.indices ∧ query ∉ passage.target.indices := by
  rw [passage.onlySource_eq]
  simp

theorem both_mem (passage : Passage dimension) (query : FeatIdx dimension) :
    query ∈ passage.both ↔ query ∈ passage.source.indices ∧ query ∈ passage.target.indices := by
  rw [passage.both_eq]
  simp [and_comm]

theorem onlyTarget_mem (passage : Passage dimension) (query : FeatIdx dimension) :
    query ∈ passage.onlyTarget ↔
      query ∈ passage.target.indices ∧ query ∉ passage.source.indices := by
  rw [passage.onlyTarget_eq]
  simp

theorem onlySource_nodup (passage : Passage dimension) : passage.onlySource.Nodup := by
  rw [passage.onlySource_eq]
  exact passage.source.nodup.sublist List.filter_sublist

theorem both_nodup (passage : Passage dimension) : passage.both.Nodup := by
  rw [passage.both_eq]
  exact passage.target.nodup.sublist List.filter_sublist

theorem onlyTarget_nodup (passage : Passage dimension) : passage.onlyTarget.Nodup := by
  rw [passage.onlyTarget_eq]
  exact passage.target.nodup.sublist List.filter_sublist

/-- The three classes partition `x ∪ x'`: every slot of either set is in exactly one class. -/
theorem classes_partition (passage : Passage dimension) (query : FeatIdx dimension) :
    (query ∈ passage.source.indices ∨ query ∈ passage.target.indices) ↔
      (query ∈ passage.onlySource ∨ query ∈ passage.both ∨ query ∈ passage.onlyTarget) := by
  rw [onlySource_mem, both_mem, onlyTarget_mem]
  tauto

theorem classes_disjoint (passage : Passage dimension) (query : FeatIdx dimension) :
    ¬ (query ∈ passage.onlySource ∧ query ∈ passage.both) ∧
      ¬ (query ∈ passage.onlySource ∧ query ∈ passage.onlyTarget) ∧
      ¬ (query ∈ passage.both ∧ query ∈ passage.onlyTarget) := by
  rw [onlySource_mem, both_mem, onlyTarget_mem]
  tauto

/-- The class counts: `|x| = |x \ x'| + |x ∩ x'|` and `|x'| = |x' \ x| + |x ∩ x'|`. -/
theorem class_counts (passage : Passage dimension) :
    passage.source.indices.length = passage.onlySource.length + passage.both.length ∧
      passage.target.indices.length = passage.onlyTarget.length + passage.both.length := by
  have bothSum : ∀ j, indicator passage.both j = indicator
      (passage.source.indices.filter fun index => decide (index ∈ passage.target.indices)) j := by
    intro j
    have same : j ∈ passage.both ↔ j ∈ passage.source.indices.filter
        (fun index => decide (index ∈ passage.target.indices)) := by
      rw [both_mem]
      simp
    unfold indicator
    by_cases inside : j ∈ passage.both
    · have other := same.mp inside
      simp only [inside, other, ↓reduceIte]
    · have other : j ∉ passage.source.indices.filter
          (fun index => decide (index ∈ passage.target.indices)) :=
        fun found => inside (same.mpr found)
      simp only [inside, other, ↓reduceIte]
  have bothLength : passage.both.length =
      (passage.source.indices.filter fun index =>
        decide (index ∈ passage.target.indices)).length := by
    have first := sum_indicator_one passage.both (both_nodup passage)
    have second := sum_indicator_one
      (passage.source.indices.filter fun index => decide (index ∈ passage.target.indices))
      (passage.source.nodup.sublist List.filter_sublist)
    simp only [bothSum] at first
    exact_mod_cast first.symm.trans second
  constructor
  · rw [bothLength, passage.onlySource_eq, List.length_eq_length_filter_add
      (fun index => decide (index ∈ passage.target.indices))]
    simp [add_comm]
  · rw [passage.onlyTarget_eq, passage.both_eq, List.length_eq_length_filter_add
      (fun index => decide (index ∈ passage.source.indices))]
    simp [add_comm]

/-! ## The step size -/

/-- The demons' rate budget as a rational: about 0.1. -/
theorem eta_value : numerical32 gradientEta = 13421773 / 134217728 := by
  change (1 : ℚ) * 13421773 * (2 : ℚ) ^ (-27 : Int) = 13421773 / 134217728
  norm_num

/-- The demons' initial step size as a rational: about `5·10⁻⁵`. -/
theorem alpha_bounds : gradientAlpha.Finite ∧ 0 < numerical32 gradientAlpha ∧
    numerical32 gradientAlpha ≤ 1 / 16384 := by
  have finite : gradientAlpha.Finite := by decide
  have zeroFinite : Binary32.zero.Finite := by decide
  have zeroValue : numerical32 Binary32.zero = 0 := by decide
  have capFinite : (Binary32.mk 0x38800000).Finite := by decide
  have capValue : numerical32 (Binary32.mk 0x38800000) = 1 / 16384 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-37 : Int) = 1 / 16384
    norm_num
  have lower := (numerical32_strict_order Binary32.zero gradientAlpha zeroFinite finite).mpr
    (by decide)
  have upper := (numerical32_order gradientAlpha (Binary32.mk 0x38800000) finite capFinite).mpr
    (by decide)
  rw [zeroValue] at lower
  rw [capValue] at upper
  exact ⟨finite, lower, upper⟩

/-- For a transition with `total` active slots in all, between one and `2^17`, the
executed step size is finite and positive, and `h·total ≤ 1/9`. -/
theorem gradientStep_bounds (total : Nat) (positive : 1 ≤ total) (small : total ≤ 131072) :
    (gradientStep total).Finite ∧ 0 < numerical64 (gradientStep total) ∧
      numerical64 (gradientStep total) * total ≤ 1 / 9 := by
  have etaFinite : gradientEta.Finite := by decide
  have count := wideCount_exact total (by omega)
  have totalPositive : (1 : ℚ) ≤ total := by exact_mod_cast positive
  have totalSmall : (total : ℚ) ≤ 131072 := by exact_mod_cast small
  have etaWide := numerical_widen_exact gradientEta etaFinite
  have countValue : numerical64 (wideCount total) = total := by
    have := count.2.1
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  have nonzero : numerical64 (wideCount total) ≠ 0 := by
    rw [countValue]
    positivity
  have quotient : |numerical64 (Conversion.widen gradientEta) / numerical64 (wideCount total)| ≤
      65536 * (2 : ℚ) ^ 0 := by
    rw [etaWide, countValue, eta_value]
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have budget := binary64_div_scaled (Conversion.widen gradientEta) (wideCount total) 0
    (by norm_num) (Conversion.widen_finite _ etaFinite) count.1 nonzero quotient
  rw [etaWide, countValue, eta_value] at budget
  have budgetValue := budget.2
  norm_num at budgetValue
  have budgetLower : 13421773 / 134217728 / (total : ℚ) - 1 / 34359738368 ≤
      numerical64 ((Conversion.widen gradientEta).div (wideCount total)) := by
    linarith [(abs_le.mp budgetValue).1]
  have budgetUpper : numerical64 ((Conversion.widen gradientEta).div (wideCount total)) ≤
      13421773 / 134217728 / (total : ℚ) + 1 / 34359738368 := by
    linarith [(abs_le.mp budgetValue).2]
  have budgetPositive : 0 < numerical64 ((Conversion.widen gradientEta).div (wideCount total)) := by
    have least : (13421773 / 134217728 : ℚ) / 131072 ≤ 13421773 / 134217728 / (total : ℚ) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) totalSmall
    norm_num at least
    linarith
  have budgetScaled : numerical64 ((Conversion.widen gradientEta).div (wideCount total)) * total ≤
      1 / 9 := by
    have expand : (13421773 / 134217728 / (total : ℚ) + 1 / 34359738368) * total =
        13421773 / 134217728 + total / 34359738368 := by
      field_simp
    have := mul_le_mul_of_nonneg_right budgetUpper (by linarith : (0 : ℚ) ≤ total)
    rw [expand] at this
    linarith
  have alpha := alpha_bounds
  have capWide := numerical_widen_exact gradientAlpha alpha.1
  unfold gradientStep
  dsimp only
  rw [numerical64_less _ _ budget.1 (Conversion.widen_finite _ alpha.1)]
  split
  · exact ⟨budget.1, budgetPositive, budgetScaled⟩
  · rename_i notBelow
    simp only [decide_eq_true_eq, not_lt] at notBelow
    refine ⟨Conversion.widen_finite _ alpha.1, by rw [capWide]; exact alpha.2.1, ?_⟩
    have := mul_le_mul_of_nonneg_right notBelow (by linarith : (0 : ℚ) ≤ total)
    linarith

/-! ## The projection -/

/-- The symmetric clamp onto `[−bound, bound]`. -/
def clampSym (bound value : ℚ) : ℚ := max (min value bound) (-bound)

/-- The clamp never moves a value away from a point inside the range. -/
theorem clampSym_toward (bound value reference : ℚ) (inside : |reference| ≤ bound) :
    (clampSym bound value - reference) ^ 2 ≤ (value - reference) ^ 2 := by
  have lower := (abs_le.mp inside).1
  have upper := (abs_le.mp inside).2
  unfold clampSym
  by_cases above : bound ≤ value
  · rw [min_eq_right above, max_eq_left (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr above)
      (by linarith : (0 : ℚ) ≤ value + bound - 2 * reference)]
  · by_cases below : value ≤ -bound
    · rw [min_eq_left (by linarith), max_eq_right below]
      nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ -bound - value)
        (by linarith : (0 : ℚ) ≤ 2 * reference + bound - value)]
    · rw [min_eq_left (by linarith), max_eq_left (by linarith)]

/-- The signed scale is odd. -/
theorem signedFieldUnits_neg (precision : Nat) (key : Int) :
    signedFieldUnits precision (-key) = -signedFieldUnits precision key := by
  unfold signedFieldUnits
  rcases lt_trichotomy key 0 with negative | zero | positive
  · have notNegative : ¬ (-key < 0) := by omega
    have magnitude : (-key).toNat = key.natAbs := by omega
    simp only [notNegative, negative, ↓reduceIte, neg_neg, magnitude]
  · subst zero
    simp [fieldUnits_zero]
  · have negated : -key < 0 := by omega
    have notNegative : ¬ (key < 0) := by omega
    have magnitude : (-key).natAbs = key.toNat := by omega
    simp only [negated, notNegative, ↓reduceIte, magnitude]

/-- Each weight range is `[−H, H]` with `H` a finite nonnegative word. -/
theorem horizon_facts (discount : Discount) :
    discount.horizon.Finite ∧ discount.horizon.negate.Finite ∧
      discount.horizon.negate.key = -discount.horizon.key ∧
      numerical32 discount.horizon.negate = -numerical32 discount.horizon ∧
      0 ≤ numerical32 discount.horizon ∧ numerical32 discount.horizon ≤ 101 := by
  have finite : discount.horizon.Finite := by cases discount <;> decide
  have negFinite : discount.horizon.negate.Finite := by cases discount <;> decide
  have keys : discount.horizon.negate.key = -discount.horizon.key := by cases discount <;> decide
  have negValue : numerical32 discount.horizon.negate = -numerical32 discount.horizon := by
    rw [numerical32_key_units _ negFinite, numerical32_key_units _ finite, keys,
      signedFieldUnits_neg]
    push_cast
    ring
  have zeroFinite : Binary32.zero.Finite := by decide
  have zeroValue : numerical32 Binary32.zero = 0 := by decide
  have capFinite : (Binary32.mk 0x42ca0000).Finite := by decide
  have capValue : numerical32 (Binary32.mk 0x42ca0000) = 101 := by
    change (1 : ℚ) * 13238272 * (2 : ℚ) ^ (-17 : Int) = 101
    norm_num
  have lower := (numerical32_order Binary32.zero discount.horizon zeroFinite finite).mpr
    (by cases discount <;> decide)
  have upper := (numerical32_order discount.horizon (Binary32.mk 0x42ca0000) finite
    capFinite).mpr (by cases discount <;> decide)
  rw [zeroValue] at lower
  rw [capValue] at upper
  exact ⟨finite, negFinite, keys, negValue, lower, upper⟩

/-- The weight projection of a finite word is the exact clamp of its value onto the
discount's range: it selects a word and rounds nothing. -/
theorem project_value (discount : Discount) (raw : Binary32) (finite : raw.Finite) :
    numerical32 (Weight.project (.discounted discount) raw).value =
      clampSym (numerical32 discount.horizon) (numerical32 raw) := by
  obtain ⟨hFinite, nFinite, _, negValue, nonneg, _⟩ := horizon_facts discount
  rw [Weight.project_eq]
  change numerical32 (raw.project discount.horizon) = _
  unfold Binary32.project
  rw [Binary32.finite_not_nan raw finite]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [numerical32_less _ _ hFinite finite, numerical32_less _ _ finite nFinite, negValue]
  unfold clampSym
  by_cases above : numerical32 discount.horizon < numerical32 raw
  · simp only [above, decide_true, ↓reduceIte]
    rw [min_eq_right (le_of_lt above), max_eq_left (by linarith)]
  · by_cases below : numerical32 raw < -numerical32 discount.horizon
    · simp only [above, below, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      exact negValue
    · simp only [above, below, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [min_eq_left (by linarith), max_eq_left (by linarith)]

/-! ## Sums -/

/-- The exact sum of the stored words at the listed slots. -/
def exactSum {rule : ValueRule} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) : ℚ :=
  (indices.map fun index => numerical32 (weights.get index).value).sum

/-- The binary64 sum of stored words continued from a partial total: with `count` words
already summed and at most `2^16` in all, the result is within `2^(-30)` per word of the
exact sum. -/
theorem fold_approx {rule : ValueRule} (weights : WeightArray rule dimension) :
    ∀ (indices : List (FeatIdx dimension)) (total : Binary64) (value : ℚ) (count : Nat),
      Approx total value (count / 1073741824) (count * 101) → count + indices.length ≤ 65536 →
      Approx (indices.foldl (fun total index =>
          total.add (Conversion.widen (weights.get index).value)) total)
        (value + exactSum weights indices) ((count + indices.length : Nat) / 1073741824)
        ((count + indices.length : Nat) * 101)
  | [], total, value, count, start, _ => by
    simpa [exactSum] using start
  | head :: tail, total, value, count, start, room => by
    have weight := weight_numerical_bound rule (weights.get head)
    have term := Approx.widen weight.1 weight.2
    have counted : (count : ℚ) ≤ 65535 := by
      simp only [List.length_cons] at room
      exact_mod_cast (by omega : count ≤ 65535)
    have next := Approx.add 7 (by norm_num) start term (by
      have nonneg : (0 : ℚ) ≤ count := Nat.cast_nonneg _
      norm_num
      nlinarith)
    have next' : Approx (total.add (Conversion.widen (weights.get head).value))
        (value + numerical32 (weights.get head).value) ((count + 1 : Nat) / 1073741824)
        ((count + 1 : Nat) * 101) :=
      next.mono (by push_cast; ring_nf; norm_num) (by push_cast; ring_nf; norm_num)
    have rest := fold_approx weights tail _ _ (count + 1) next'
      (by simp only [List.length_cons] at room; omega)
    have sums : value + numerical32 (weights.get head).value + exactSum weights tail =
        value + exactSum weights (head :: tail) := by
      simp [exactSum, add_assoc]
    have counts : count + 1 + tail.length = count + (head :: tail).length := by
      simp only [List.length_cons]
      omega
    simp only [List.foldl_cons]
    rw [← sums, ← counts]
    exact rest

/-- The binary64 sum of at most `2^16` stored words is finite and within `2^(-30)` per
word of their exact sum. -/
theorem wideSum_approx {rule : ValueRule} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (short : indices.length ≤ 65536) :
    Approx (wideSum weights indices) (exactSum weights indices)
      (indices.length / 1073741824) (indices.length * 101) := by
  have zeroValue : numerical64 (Binary64.mk 0) = 0 := by decide
  have zeroFinite : (Binary64.mk 0).Finite := by decide
  have start : Approx (Binary64.mk 0) 0 ((0 : Nat) / 1073741824) ((0 : Nat) * 101) :=
    ⟨zeroFinite, by rw [zeroValue]; simp, by simp⟩
  have folded := fold_approx weights indices _ 0 0 start (by omega)
  simpa [wideSum] using folded

/-- The exact sum over an active set is the sum over its two classes. -/
theorem exactSum_classes {rule : ValueRule} (weights : WeightArray rule dimension)
    (passage : Passage dimension) :
    exactSum weights passage.both + exactSum weights passage.onlySource =
        exactSum weights passage.source.indices ∧
      exactSum weights passage.both + exactSum weights passage.onlyTarget =
        exactSum weights passage.target.indices := by
  have listed (indices : List (FeatIdx dimension)) (nodup : indices.Nodup) :
      exactSum weights indices =
        ∑ j, numerical32 (weights.get j).value * indicator indices j :=
    (sum_indicator indices nodup _).symm
  have inOnlySource := onlySource_mem passage
  have inBoth := both_mem passage
  have inOnlyTarget := onlyTarget_mem passage
  rw [listed _ (both_nodup passage), listed _ (onlySource_nodup passage),
    listed _ passage.source.nodup, listed _ (onlyTarget_nodup passage),
    listed _ passage.target.nodup, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  constructor <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> unfold indicator <;>
    by_cases inSource : j ∈ passage.source.indices <;>
    by_cases inTarget : j ∈ passage.target.indices <;>
    simp [inOnlySource, inBoth, inOnlyTarget, inSource, inTarget]

/-- The sum of the main weights over `x ∩ x'`, continued over one of the two remaining
classes, is within `2^(-30)` per word of the exact sum over that active set. -/
theorem classSums_approx {rule : ValueRule} (weights : WeightArray rule dimension)
    (passage : Passage dimension) (small : dimension.capacity ≤ 65536) :
    Approx (wideSum weights passage.onlySource (wideSum weights passage.both))
        (exactSum weights passage.source.indices)
        (passage.source.indices.length / 1073741824) (passage.source.indices.length * 101) ∧
      Approx (wideSum weights passage.onlyTarget (wideSum weights passage.both))
        (exactSum weights passage.target.indices)
        (passage.target.indices.length / 1073741824) (passage.target.indices.length * 101) := by
  have counts := class_counts passage
  have classes := exactSum_classes weights passage
  have source := le_trans (nodup_length _ passage.source.nodup) small
  have target := le_trans (nodup_length _ passage.target.nodup) small
  have shared := wideSum_approx weights passage.both (by omega)
  have earlier := fold_approx weights passage.onlySource _ _ _ shared (by omega)
  have later := fold_approx weights passage.onlyTarget _ _ _ shared (by omega)
  rw [classes.1, show passage.both.length + passage.onlySource.length =
    passage.source.indices.length by omega] at earlier
  rw [classes.2, show passage.both.length + passage.onlyTarget.length =
    passage.target.indices.length by omega] at later
  exact ⟨earlier, later⟩

/-! ## Exact counterparts of the executed scalars -/

section Exact
variable {discount : Discount}

/-- The exact TD error minus the second weights' sum, `δ − p`, from the stored words. -/
def exactGap (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : ℚ :=
  numerical32 cumulant + numerical32 discount.gamma * exactSum learner.main passage.target.indices -
    exactSum learner.main passage.source.indices - exactSum learner.second passage.source.indices

/-- `τ = h|x|` with the executed step size. -/
def exactTau (passage : Passage dimension) : ℚ :=
  numerical64 passage.step * (passage.source.indices.length : ℚ)

/-- `κ = h|a|²` with the executed step size, from the class counts. -/
def exactCurvature (discount : Discount) (passage : Passage dimension) : ℚ :=
  numerical64 passage.step * (passage.onlySource.length +
    numerical32 discount.gamma * numerical32 discount.gamma * passage.onlyTarget.length +
      (1 - numerical32 discount.gamma) * (1 - numerical32 discount.gamma) * passage.both.length)

/-- The midpoint's `p_m = p + τ(δ − p)`. -/
def exactMidpoint (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : ℚ :=
  exactSum learner.second passage.source.indices +
    exactTau passage * exactGap learner passage cumulant

/-- The correction `(1 − τ)(δ − p) − κp`. -/
def exactCorrection (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) : ℚ :=
  (1 - exactTau passage) * exactGap learner passage cumulant -
    exactCurvature discount passage * exactSum learner.second passage.source.indices

end Exact

/-! ## The sizes of a transition -/

/-- Sizes of a transition in a space of at most `2^16` slots, and the step-size facts. -/
theorem passage_sizes (passage : Passage dimension) (small : dimension.capacity ≤ 65536) :
    1 ≤ passage.source.indices.length ∧ passage.source.indices.length ≤ 65536 ∧
      passage.target.indices.length ≤ 65536 ∧
      (passage.step).Finite ∧ 0 < numerical64 passage.step ∧
      numerical64 passage.step *
        ((passage.source.indices.length : ℚ) + passage.target.indices.length) ≤ 1 / 9 := by
  have source := le_trans (nodup_length _ passage.source.nodup) small
  have target := le_trans (nodup_length _ passage.target.nodup) small
  have nonempty : 1 ≤ passage.source.indices.length :=
    List.length_pos_iff.mpr passage.nonempty
  have facts := gradientStep_bounds (passage.source.indices.length + passage.target.indices.length)
    (by omega) (by omega)
  rw [← passage.step_eq] at facts
  push_cast at facts
  exact ⟨nonempty, source, target, facts.1, facts.2.1, facts.2.2⟩

/-! ## The scalars -/

/-- The scalar chain of one step over abstract words: from sums within `2^(-30)` per word,
an exact discount, signal and step size, and exact class counts, the midpoint and the
correction are within `N·2^(-24)` and `N·2^(-23)` of their exact values, `N = n + m`. Every
side condition is linear in `n`, `m`, `h·n` and `h·m`. -/
theorem chain_approx (earlier later expected signal gamma step tau onlySource both onlyTarget :
      Binary64) (E L P C G h n m n₁ n₁₂ n₂ : ℚ)
    (hE : Approx earlier E (n / 1073741824) (n * 101))
    (hL : Approx later L (m / 1073741824) (m * 101))
    (hP : Approx expected P (n / 1073741824) (n * 101))
    (hC : Approx signal C 0 1) (hG : Approx gamma G 0 1) (hStep : Approx step h 0 h)
    (hTau : Approx tau (h * n) (1 / 137438953472) (1 / 9))
    (hOne : Approx onlySource n₁ 0 n₁) (hBoth : Approx both n₁₂ 0 n₁₂)
    (hTwo : Approx onlyTarget n₂ 0 n₂)
    (gLower : 0 ≤ G) (gUpper : G ≤ 1) (hPos : 0 ≤ h) (scaled : h * (n + m) ≤ 1 / 9)
    (nOne : 1 ≤ n) (nLe : n ≤ 65536) (mNonneg : 0 ≤ m) (mLe : m ≤ 65536)
    (nSplit : n = n₁ + n₁₂) (mSplit : m = n₂ + n₁₂)
    (oneNonneg : 0 ≤ n₁) (bothNonneg : 0 ≤ n₁₂) (twoNonneg : 0 ≤ n₂) :
    let one := Binary64.ofUInt64 1
    let gap := ((signal.add (gamma.mul later)).sub earlier).sub expected
    let curvature := step.mul ((onlySource.add ((gamma.mul gamma).mul onlyTarget)).add
      ((((one.sub gamma)).mul (one.sub gamma)).mul both))
    Approx (expected.add (tau.mul gap)) (P + h * n * (C + G * L - E - P))
        ((n + m) / 16777216) (200 * (n + m)) ∧
      Approx (((one.sub tau).mul gap).sub (curvature.mul expected))
        ((1 - h * n) * (C + G * L - E - P) -
          h * (n₁ + G * G * n₂ + (1 - G) * (1 - G) * n₁₂) * P)
        ((n + m) / 8388608) (500 * (n + m)) := by
  intro one gap curvature
  have hn : h * n ≤ 1 / 9 := by nlinarith [mul_nonneg hPos mNonneg]
  have hm : h * m ≤ 1 / 9 := by nlinarith [mul_nonneg hPos (by linarith : (0 : ℚ) ≤ n)]
  have hnNonneg : 0 ≤ h * n := mul_nonneg hPos (by linarith)
  have hmNonneg : 0 ≤ h * m := mul_nonneg hPos mNonneg
  -- the TD error and the gap
  have product : Approx (gamma.mul later) (G * L) ((m + 1) / 1073741824) (m * 101) :=
    (Approx.mul 7 (by norm_num) hG hL (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have error₁ : Approx (signal.add (gamma.mul later)) (C + G * L) ((m + 3) / 1073741824)
      (1 + m * 101) :=
    (Approx.add 8 (by norm_num) hC product (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have error₂ : Approx ((signal.add (gamma.mul later)).sub earlier) (C + G * L - E)
      ((m + n + 7) / 1073741824) (1 + m * 101 + n * 101) :=
    (Approx.sub 9 (by norm_num) error₁ hE (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have gapApprox : Approx gap (C + G * L - E - P) ((n + m) / 33554432) (400 * (n + m)) :=
    (Approx.sub 10 (by norm_num) error₂ hP (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  -- `1 − τ` and the midpoint
  have oneMinus : Approx (one.sub tau) (1 - h * n) (1 / 68719476736) (10 / 9) :=
    (Approx.sub 0 (by norm_num) one_exact hTau (by norm_num)).mono (by norm_num) (by norm_num)
  have scaledGap : Approx (tau.mul gap) (h * n * (C + G * L - E - P)) ((n + m) / 67108864)
      (45 * (n + m)) :=
    (Approx.mul 10 (by norm_num) hTau gapApprox (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have midpoint := (Approx.add 10 (by norm_num) hP scaledGap (by norm_num; linarith)).mono
    (error' := (n + m) / 16777216) (magnitude' := 200 * (n + m))
    (by norm_num; linarith) (by linarith)
  -- the curvature
  have squared : Approx (gamma.mul gamma) (G * G) (1 / 137438953472) 1 :=
    (Approx.mul 0 (by norm_num) hG hG (by norm_num)).mono (by norm_num) (by norm_num)
  have complement : Approx (one.sub gamma) (1 - G) (1 / 137438953472) 1 :=
    ((Approx.sub 0 (by norm_num) one_exact hG (by norm_num)).within
      (by rw [abs_of_nonneg (by linarith)]; linarith)).mono (by norm_num) le_rfl
  have complementSquared : Approx ((one.sub gamma).mul (one.sub gamma)) ((1 - G) * (1 - G))
      (1 / 34359738368) 1 :=
    (Approx.mul 0 (by norm_num) complement complement (by norm_num)).mono
      (by norm_num) (by norm_num)
  have targetTerm : Approx ((gamma.mul gamma).mul onlyTarget) (G * G * n₂)
      ((n₂ + 2) / 137438953472) n₂ :=
    (Approx.mul 1 (by norm_num) squared hTwo (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have firstTerms : Approx (onlySource.add ((gamma.mul gamma).mul onlyTarget)) (n₁ + G * G * n₂)
      ((n₂ + 6) / 137438953472) (n₁ + n₂) :=
    (Approx.add 2 (by norm_num) hOne targetTerm (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have bothTerm : Approx (((one.sub gamma).mul (one.sub gamma)).mul both)
      ((1 - G) * (1 - G) * n₁₂) ((4 * n₁₂ + 2) / 137438953472) n₁₂ :=
    (Approx.mul 1 (by norm_num) complementSquared hBoth (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have weighted : Approx ((onlySource.add ((gamma.mul gamma).mul onlyTarget)).add
      (((one.sub gamma).mul (one.sub gamma)).mul both))
      (n₁ + G * G * n₂ + (1 - G) * (1 - G) * n₁₂) ((n + m) / 4294967296) (n + m) :=
    (Approx.add 3 (by norm_num) firstTerms bothTerm (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have curvatureApprox : Approx curvature (h * (n₁ + G * G * n₂ + (1 - G) * (1 - G) * n₁₂))
      (1 / 17179869184) (1 / 9) :=
    (Approx.mul 0 (by norm_num) hStep weighted (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  -- the correction
  have scaledGap₂ : Approx ((one.sub tau).mul gap) ((1 - h * n) * (C + G * L - E - P))
      ((n + m) / 16777216) (445 * (n + m)) :=
    (Approx.mul 10 (by norm_num) oneMinus gapApprox (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have curvatureTerm : Approx (curvature.mul expected)
      (h * (n₁ + G * G * n₂ + (1 - G) * (1 - G) * n₁₂) * P) ((n + m) / 67108864)
      (12 * (n + m)) :=
    (Approx.mul 10 (by norm_num) curvatureApprox hP (by norm_num; linarith)).mono
      (by norm_num; linarith) (by linarith)
  have correction := (Approx.sub 10 (by norm_num) scaledGap₂ curvatureTerm
    (by norm_num; linarith)).mono (error' := (n + m) / 8388608) (magnitude' := 500 * (n + m))
    (by norm_num; linarith) (by linarith)
  exact ⟨midpoint, correction⟩

/-- The executed midpoint and correction are within `N·2^(-24)` and `N·2^(-23)` of their
exact counterparts, with `N = |x| + |x'|`, for every learner state, every transition in a
space of at most `2^16` slots and every finite signal word in `[−1, 1]`. -/
theorem scalars_approx {discount : Discount} (learner : GradientLearner discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (small : dimension.capacity ≤ 65536)
    (finite : cumulant.Finite) (bounded : |numerical32 cumulant| ≤ 1) :
    Approx (learner.scalars passage cumulant).1 (exactMidpoint learner passage cumulant)
        (((passage.source.indices.length : ℚ) + passage.target.indices.length) / 16777216)
        (200 * ((passage.source.indices.length : ℚ) + passage.target.indices.length)) ∧
      Approx (learner.scalars passage cumulant).2 (exactCorrection learner passage cumulant)
        (((passage.source.indices.length : ℚ) + passage.target.indices.length) / 8388608)
        (500 * ((passage.source.indices.length : ℚ) + passage.target.indices.length)) := by
  obtain ⟨nPos, nSmall, mSmall, stepFinite, hPos, hScaled⟩ := passage_sizes passage small
  obtain ⟨gFinite, gLower, gUpper⟩ := gamma_bounds discount
  have counts := class_counts passage
  have hNonneg : 0 ≤ numerical64 passage.step := le_of_lt hPos
  have stepApprox : Approx passage.step (numerical64 passage.step) 0 (numerical64 passage.step) :=
    ⟨stepFinite, by simp, le_of_eq (abs_of_nonneg hNonneg)⟩
  have nOne : (1 : ℚ) ≤ passage.source.indices.length := by exact_mod_cast nPos
  have nLe : (passage.source.indices.length : ℚ) ≤ 65536 := by exact_mod_cast nSmall
  have mLe : (passage.target.indices.length : ℚ) ≤ 65536 := by exact_mod_cast mSmall
  have mNonneg : (0 : ℚ) ≤ passage.target.indices.length := Nat.cast_nonneg _
  have countSource := wideCount_exact passage.source.indices.length (by omega)
  have tau : Approx passage.tau
      (numerical64 passage.step * (passage.source.indices.length : ℚ)) (1 / 137438953472)
      (1 / 9) := by
    rw [passage.tau_eq]
    exact (Approx.mul 0 (by norm_num) stepApprox countSource (by norm_num; nlinarith)).mono
      (by norm_num) (by nlinarith)
  have onlySourceCount := wideCount_exact passage.onlySource.length (by omega)
  have bothCount := wideCount_exact passage.both.length (by omega)
  have onlyTargetCount := wideCount_exact passage.onlyTarget.length (by omega)
  rw [← passage.onlySourceCount_eq] at onlySourceCount
  rw [← passage.bothCount_eq] at bothCount
  rw [← passage.onlyTargetCount_eq] at onlyTargetCount
  exact chain_approx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (classSums_approx learner.main passage small).1
    (classSums_approx learner.main passage small).2
    (wideSum_approx learner.second passage.source.indices nSmall)
    (Approx.widen finite bounded) (gamma_approx discount) stepApprox tau onlySourceCount bothCount
    onlyTargetCount gLower gUpper hNonneg hScaled nOne nLe mNonneg mLe
    (by exact_mod_cast counts.1) (by exact_mod_cast counts.2) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ## The increments -/

set_option exponentiation.threshold 1200 in
/-- The rounding unit of a narrowing is at most `2^(-23)` of the source's magnitude units,
or the binary32 subnormal unit. -/
theorem narrowUnit_bound (value : Binary64) :
    Conversion.narrowUnit value * 16777216 ≤
      2 * Conversion.magnitudeUnits64 value + 2 ^ 925 * 16777216 := by
  have fields := Conversion.fields64_decomposition value
  set E := (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat with EDef
  set F := (((value.bits &&& 0xfffffffffffff) : UInt64)).toNat with FDef
  have fraction : F < 2 ^ 52 := by
    have : F ≤ 0xfffffffffffff := by
      rw [FDef, UInt64.toNat_and]
      exact Nat.le_trans Nat.and_le_right (by decide)
    omega
  have quotient : value.magnitude / 2 ^ 52 = E := by
    rw [fields, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt fraction, Nat.zero_add]
  have remainder : value.magnitude % 2 ^ 52 = F := by
    rw [fields, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt fraction]
  unfold Conversion.narrowUnit Conversion.magnitudeUnits64
  simp only [quotient, remainder, ← EDef]
  by_cases small : E + 28 ≤ 925
  · rw [Nat.max_eq_left small]
    exact Nat.le_add_left _ _
  · have large : 925 ≤ E + 28 := by omega
    rw [Nat.max_eq_right large]
    have nonzero : E ≠ 0 := by omega
    simp only [nonzero, ↓reduceIte]
    have split : 2 ^ (E + 28) * 16777216 = 2 * (2 ^ 52 * 2 ^ (E - 1)) := by
      have exponent : E + 28 = (E - 1) + 29 := by omega
      rw [exponent, pow_add]
      ring
    rw [split]
    have : 2 ^ 52 * 2 ^ (E - 1) ≤ (2 ^ 52 + F) * 2 ^ (E - 1) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega

set_option exponentiation.threshold 1200 in
/-- Narrowing follows FloatLib's standard model: a finite result is within `2^(-24)` of the
source relative to its magnitude, plus `2^(-150)`. -/
theorem narrow_relative (value : Binary64) (finite : value.Finite)
    (resultFinite : (Conversion.narrow value).Finite) :
    |numerical32 (Conversion.narrow value) - numerical64 value| ≤
      |numerical64 value| / 16777216 + 1 / 2 ^ 150 := by
  have distance := Conversion.narrow_finite_distance value finite resultFinite
  have unit := narrowUnit_bound value
  have signs : unpackSign (spec := Format.binary32) (Conversion.narrow value).bits.toBitVec =
      unpackSign (spec := Format.binary64) value.bits.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    change ((Conversion.narrow value).bits.toNat >>> 31) % 2 = (value.bits.toNat >>> 63) % 2
    simp only [Nat.shiftRight_eq_div_pow]
    rw [Conversion.narrow_sign value finite]
  rw [numerical64_units value finite, numerical32_units _ resultFinite, signs]
  set sign := signCoefficient (Sign.ofBitVec (unpackSign (spec := Format.binary64)
    value.bits.toBitVec)) with signDef
  have unitSign : |sign| = 1 := by
    rw [signDef]
    cases Sign.ofBitVec (unpackSign (spec := Format.binary64) value.bits.toBitVec) <;>
      simp [signCoefficient]
  set wide : ℚ := ((Conversion.magnitudeUnits64 value : ℕ) : ℚ) with wideDef
  set narrowed : ℚ := ((Conversion.magnitudeUnits32 (Conversion.narrow value) : ℕ) : ℚ)
    with narrowedDef
  have wideNonneg : 0 ≤ wide := Nat.cast_nonneg _
  have positive : (0 : ℚ) < (2 : ℚ) ^ (-1074 : Int) := zpow_pos (by norm_num) _
  have lower : 2 * wide ≤ 2 * narrowed + (Conversion.narrowUnit value : ℚ) := by
    rw [wideDef, narrowedDef]
    exact_mod_cast distance.1
  have upper : 2 * narrowed ≤ 2 * wide + (Conversion.narrowUnit value : ℚ) := by
    rw [wideDef, narrowedDef]
    exact_mod_cast distance.2
  have unitCast : (Conversion.narrowUnit value : ℚ) * 16777216 ≤
      2 * wide + (2 : ℚ) ^ 925 * 16777216 := by
    rw [wideDef]
    exact_mod_cast unit
  have close : |narrowed - wide| ≤ wide / 16777216 + (2 : ℚ) ^ 924 := by
    rw [abs_le]
    constructor <;> nlinarith
  have scale : (2 : ℚ) ^ 924 * (2 : ℚ) ^ (-1074 : Int) = 1 / 2 ^ 150 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    norm_num
  calc |sign * narrowed * (2 : ℚ) ^ (-1074 : Int) - sign * wide * (2 : ℚ) ^ (-1074 : Int)|
      = |narrowed - wide| * (2 : ℚ) ^ (-1074 : Int) := by
        rw [show sign * narrowed * (2 : ℚ) ^ (-1074 : Int) - sign * wide * (2 : ℚ) ^ (-1074 : Int) =
          sign * ((narrowed - wide) * (2 : ℚ) ^ (-1074 : Int)) by ring, abs_mul, unitSign, one_mul,
          abs_mul, abs_of_pos positive]
    _ ≤ (wide / 16777216 + (2 : ℚ) ^ 924) * (2 : ℚ) ^ (-1074 : Int) :=
        mul_le_mul_of_nonneg_right close positive.le
    _ = |sign * wide * (2 : ℚ) ^ (-1074 : Int)| / 16777216 + 1 / 2 ^ 150 := by
        rw [abs_mul, abs_mul, unitSign, one_mul, abs_of_nonneg wideNonneg,
          abs_of_pos positive, add_mul, scale]
        ring

/-- Narrowing a binary64 word within `2^(-26)` of a value of magnitude at most 63. -/
theorem narrow_close {word : Binary64} {value : ℚ} (near : Approx word value (1 / 67108864) 63) :
    (Conversion.narrow word).Finite ∧
      |numerical32 (Conversion.narrow word) - value| ≤ |value| / 8388608 + 1 / 33554432 ∧
      |numerical32 (Conversion.narrow word)| ≤ 64 := by
  have bound := near.word_bound
  have narrowed := narrow_scaled word 0 (by norm_num) near.1 (by norm_num; linarith)
  have relative := narrow_relative word near.1 narrowed.1
  have wordClose : |numerical64 word| ≤ |value| + 1 / 67108864 := by
    have triangle := abs_add_le (numerical64 word - value) value
    rw [sub_add_cancel] at triangle
    linarith [near.2.1]
  have valueNonneg : 0 ≤ |value| := abs_nonneg _
  have close : |numerical32 (Conversion.narrow word) - value| ≤
      |value| / 8388608 + 1 / 33554432 := by
    have split : numerical32 (Conversion.narrow word) - value =
        (numerical32 (Conversion.narrow word) - numerical64 word) + (numerical64 word - value) := by
      ring
    rw [split]
    have triangle := abs_add_le (numerical32 (Conversion.narrow word) - numerical64 word)
      (numerical64 word - value)
    have pow150 : (1 : ℚ) / 2 ^ 150 ≤ 1 / 2 ^ 60 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    linarith [near.2.1]
  refine ⟨narrowed.1, close, ?_⟩
  have triangle := abs_add_le (numerical32 (Conversion.narrow word) - value) value
  rw [sub_add_cancel] at triangle
  linarith [near.2.2]

/-- The four increments of the executed step are finite, at most 64 in magnitude, and within
`2^(-23)` relative plus `2^(-25)` of `h·(δ_m − p_m)`, `h·p_m`, `(1 − γ)·h·p_m` and
`γ·h·p_m`. -/
theorem increments_close {discount : Discount} (learner : GradientLearner discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (small : dimension.capacity ≤ 65536)
    (finite : cumulant.Finite) (bounded : |numerical32 cumulant| ≤ 1) :
    let h := numerical64 passage.step
    let G := numerical32 discount.gamma
    let deltas := learner.increments passage cumulant
    let correction := h * exactCorrection learner passage cumulant
    let midpoint := h * exactMidpoint learner passage cumulant
    (deltas.1.Finite ∧ |numerical32 deltas.1 - correction| ≤
        |correction| / 8388608 + 1 / 33554432 ∧ |numerical32 deltas.1| ≤ 64) ∧
      (deltas.2.1.Finite ∧ |numerical32 deltas.2.1 - midpoint| ≤
        |midpoint| / 8388608 + 1 / 33554432 ∧ |numerical32 deltas.2.1| ≤ 64) ∧
      (deltas.2.2.1.Finite ∧ |numerical32 deltas.2.2.1 - (1 - G) * midpoint| ≤
        |(1 - G) * midpoint| / 8388608 + 1 / 33554432 ∧ |numerical32 deltas.2.2.1| ≤ 64) ∧
      (deltas.2.2.2.Finite ∧ |numerical32 deltas.2.2.2 - G * midpoint| ≤
        |G * midpoint| / 8388608 + 1 / 33554432 ∧ |numerical32 deltas.2.2.2| ≤ 64) := by
  intro h G deltas correctionValue midpointValue
  obtain ⟨nPos, nSmall, mSmall, stepFinite, hPos, hScaled⟩ := passage_sizes passage small
  have scalars := scalars_approx learner passage cumulant small finite bounded
  set N : ℚ := (passage.source.indices.length : ℚ) + passage.target.indices.length with NDef
  have NOne : (1 : ℚ) ≤ N := by
    have : (1 : ℚ) ≤ passage.source.indices.length := by exact_mod_cast nPos
    have : (0 : ℚ) ≤ passage.target.indices.length := Nat.cast_nonneg _
    linarith
  have hN : h * N ≤ 1 / 9 := hScaled
  have hNonneg : 0 ≤ h := le_of_lt hPos
  have stepApprox : Approx passage.step h 0 h :=
    ⟨stepFinite, by simp only [h, sub_self, abs_zero, le_refl], le_of_eq (abs_of_nonneg hNonneg)⟩
  obtain ⟨gFinite, gLower, gUpper⟩ := gamma_bounds discount
  have gamma := gamma_approx discount
  have complement := Approx.sub 0 (by norm_num) one_exact gamma (by norm_num)
  have complement' : Approx _ (1 - G) (1 / 137438953472) 1 :=
    (complement.within (by rw [abs_of_nonneg (by linarith)]; linarith)).mono (by norm_num) le_rfl
  have correction := Approx.mul 0 (by norm_num) stepApprox scalars.2 (by norm_num; nlinarith)
  have mainStep := Approx.mul 0 (by norm_num) stepApprox scalars.1 (by norm_num; nlinarith)
  have correction' : Approx _ correctionValue (1 / 67108864) 63 :=
    correction.mono (by norm_num; nlinarith) (by nlinarith)
  have mainStep' : Approx _ midpointValue (1 / 134217728) 23 :=
    mainStep.mono (by norm_num; nlinarith) (by nlinarith)
  have shared := Approx.mul 0 (by norm_num) complement' mainStep' (by norm_num)
  have target := Approx.mul 0 (by norm_num) gamma mainStep' (by norm_num)
  exact ⟨narrow_close correction',
    narrow_close (mainStep'.mono (by norm_num) (by norm_num)),
    narrow_close (shared.mono (by norm_num) (by norm_num)),
    narrow_close (target.mono (by norm_num) (by norm_num))⟩

/-! ## The written words -/

/-- The second weights change exactly at `x`, once each. -/
theorem step_second {discount : Discount} (learner : GradientLearner discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (query : FeatIdx dimension) :
    (learner.step passage cumulant).second[query.val] =
      if query ∈ passage.source.indices then
        Weight.project _ (learner.second[query.val].value.add
          (learner.increments passage cumulant).1)
      else learner.second[query.val] := by
  simp only [GradientLearner.step]
  exact addAll_get _ _ _ passage.source.nodup query

/-- The main weights change exactly at `x ∪ x'`, once each, with the increment of the slot's
class. -/
theorem step_main {discount : Discount} (learner : GradientLearner discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (query : FeatIdx dimension) :
    (learner.step passage cumulant).main[query.val] =
      if query ∈ passage.onlySource then
        Weight.project _ (learner.main[query.val].value.add
          (learner.increments passage cumulant).2.1)
      else if query ∈ passage.both then
        Weight.project _ (learner.main[query.val].value.add
          (learner.increments passage cumulant).2.2.1)
      else if query ∈ passage.onlyTarget then
        Weight.project _ (learner.main[query.val].value.sub
          (learner.increments passage cumulant).2.2.2)
      else learner.main[query.val] := by
  have disjoint := classes_disjoint passage query
  simp only [GradientLearner.step, subAll_get _ _ _ (onlyTarget_nodup passage),
    addAll_get _ _ _ (both_nodup passage), addAll_get _ _ _ (onlySource_nodup passage)]
  by_cases inSource : query ∈ passage.onlySource <;>
    by_cases inBoth : query ∈ passage.both <;>
    by_cases inTarget : query ∈ passage.onlyTarget <;>
    simp_all

/-! ## Energy over the executed step -/

section Energy
variable {discount : Discount}

/-- The real value of a stored weight. -/
def weightValue {rule : ValueRule} (weight : Weight rule) : ℚ := numerical32 weight.value

/-- `a = x − γx'` as a rational vector. -/
def direction (discount : Discount) (passage : Passage dimension) (query : FeatIdx dimension) : ℚ :=
  indicator passage.source.indices query -
    numerical32 discount.gamma * indicator passage.target.indices query

/-- The residual `ε = c − ⟨a, w*⟩` the reference leaves on the transition. -/
def residual (discount : Discount) (passage : Passage dimension) (cumulant : Binary32)
    (reference : FeatIdx dimension → ℚ) : ℚ :=
  numerical32 cumulant - ∑ j, direction discount passage j * reference j

/-- `N = |u|² + |w − w*|²` of a learner against a reference. -/
def distance (learner : GradientLearner discount dimension) (reference : FeatIdx dimension → ℚ) :
    ℚ :=
  ∑ j : FeatIdx dimension, weightValue learner.second[j.val] ^ 2 +
    ∑ j : FeatIdx dimension, (weightValue learner.main[j.val] - reference j) ^ 2

theorem sum_exactSum {rule : ValueRule} (weights : WeightArray rule dimension)
    (indices : List (FeatIdx dimension)) (nodup : indices.Nodup) :
    ∑ j : FeatIdx dimension, weightValue weights[j.val] * indicator indices j =
      exactSum weights indices := by
  rw [sum_indicator indices nodup]
  simp [exactSum, weightValue, vector_get]

/-- The exact extragradient step and the executed scalars agree: the step's `τ`, `κ`, `p`
and `δ − p` read from the vectors are the exact counterparts of the executed scalars. -/
theorem exact_counterparts (learner : GradientLearner discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (reference : FeatIdx dimension → ℚ) :
    let h := numerical64 passage.step
    let φ := indicator passage.source.indices
    let a := direction discount passage
    let u := fun j : FeatIdx dimension => weightValue learner.second[j.val]
    let v := fun j : FeatIdx dimension => weightValue learner.main[j.val] - reference j
    h * ∑ j, φ j ^ 2 = exactTau passage ∧
      h * ∑ j, a j ^ 2 = exactCurvature discount passage ∧
      ∑ j, u j * φ j = exactSum learner.second passage.source.indices ∧
      residual discount passage cumulant reference - ∑ j, v j * a j -
          ∑ j, u j * φ j = exactGap learner passage cumulant ∧
      ∑ j, a j ^ 2 ≤ passage.source.indices.length + passage.target.indices.length := by
  intro h φ a u v
  obtain ⟨gFinite, gLower, gUpper⟩ := gamma_bounds discount
  set G := numerical32 discount.gamma
  have counts := class_counts passage
  have sourceCount : ∑ j, φ j ^ 2 = passage.source.indices.length := by
    simp only [φ, indicator_sq]
    exact sum_indicator_one _ passage.source.nodup
  have targetCount : ∑ j, indicator passage.target.indices j = passage.target.indices.length :=
    sum_indicator_one _ passage.target.nodup
  have overlap : ∑ j, φ j * indicator passage.target.indices j = passage.both.length := by
    have pointwise : ∀ j, φ j * indicator passage.target.indices j = indicator passage.both j := by
      intro j
      simp only [φ, indicator, both_mem]
      by_cases inSource : j ∈ passage.source.indices <;>
        by_cases inTarget : j ∈ passage.target.indices <;> simp [inSource, inTarget]
    simp only [pointwise]
    exact sum_indicator_one _ (both_nodup passage)
  have squares : ∀ j, a j ^ 2 = φ j - 2 * G * (φ j * indicator passage.target.indices j) +
      G * G * indicator passage.target.indices j := by
    intro j
    have φsq := indicator_sq passage.source.indices j
    have ψsq := indicator_sq passage.target.indices j
    simp only [a, direction]
    simp only [φ] at φsq ⊢
    nlinarith [φsq, ψsq]
  have squareSum : ∑ j, a j ^ 2 = passage.source.indices.length - 2 * G * passage.both.length +
      G * G * passage.target.indices.length := by
    simp only [squares, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [overlap, targetCount]
    have : ∑ j, φ j = passage.source.indices.length := sum_indicator_one _ passage.source.nodup
    rw [this]
  have nSplit : (passage.source.indices.length : ℚ) =
      passage.onlySource.length + passage.both.length := by exact_mod_cast counts.1
  have mSplit : (passage.target.indices.length : ℚ) =
      passage.onlyTarget.length + passage.both.length := by exact_mod_cast counts.2
  have bothNonneg : (0 : ℚ) ≤ passage.both.length := Nat.cast_nonneg _
  have targetNonneg : (0 : ℚ) ≤ passage.target.indices.length := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceCount]
    rfl
  · rw [squareSum]
    simp only [exactCurvature]
    rw [nSplit, mSplit]
    ring
  · exact sum_exactSum _ _ passage.source.nodup
  · have mainSource := sum_exactSum learner.main passage.source.indices passage.source.nodup
    have mainTarget := sum_exactSum learner.main passage.target.indices passage.target.nodup
    have secondSource := sum_exactSum learner.second passage.source.indices passage.source.nodup
    have term : ∀ j, v j * a j = weightValue learner.main[j.val] * φ j -
        G * (weightValue learner.main[j.val] * indicator passage.target.indices j) -
          direction discount passage j * reference j := by
      intro j
      simp only [v, a, direction, φ]
      ring
    have expand : ∑ j, v j * a j =
        ∑ j : FeatIdx dimension, weightValue learner.main[j.val] * φ j -
        G * ∑ j : FeatIdx dimension,
          weightValue learner.main[j.val] * indicator passage.target.indices j -
          ∑ j, direction discount passage j * reference j := by
      simp only [term, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have secondSum : ∑ j, u j * φ j = exactSum learner.second passage.source.indices :=
      secondSource
    have mainSum : ∑ j : FeatIdx dimension, weightValue learner.main[j.val] * φ j =
        exactSum learner.main passage.source.indices := mainSource
    simp only [residual, exactGap]
    rw [expand, secondSum, mainSum, mainTarget]
    ring
  · rw [squareSum]
    have gg : G * G ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) gLower) bothNonneg,
      mul_le_mul_of_nonneg_right gg targetNonneg]

end Energy

/-! ## Per-slot deviations of the executed writes -/

section Writes
variable {discount : Discount}

/-- The relative-error algebra of one write: if the executed word `y` is within `2^(-24)`
relative of `old ± D`, the increment `D` within `2^(-23)` relative plus `2^(-25)` of `T`,
and `E = old ± T`, then `|y − E| ≤ 2^(-22)(|E| + |old|) + 2^(-24)`. -/
theorem write_deviation (y old D T E : ℚ) (sign : ℚ) (unit : sign = 1 ∨ sign = -1)
    (exact : E = old + sign * T)
    (rounded : |y - (old + sign * D)| ≤ |old + sign * D| / 16777216 + 1 / 2 ^ 150)
    (increment : |D - T| ≤ |T| / 8388608 + 1 / 33554432) :
    |y - E| ≤ (|E| + |old|) / 4194304 + 1 / 16777216 := by
  have signAbs : |sign| = 1 := by rcases unit with rfl | rfl <;> norm_num
  have shift : |sign * D - sign * T| = |D - T| := by
    rw [← mul_sub, abs_mul, signAbs, one_mul]
  have target : |T| ≤ |E| + |old| := by
    have : sign * T = E - old := by rw [exact]; ring
    have absT : |T| = |E - old| := by rw [← this, abs_mul, signAbs, one_mul]
    rw [absT]
    exact abs_sub _ _
  have sum : |old + sign * D| ≤ |E| + |D - T| := by
    have : old + sign * D = E + (sign * D - sign * T) := by rw [exact]; ring
    rw [this, ← shift]
    exact abs_add_le _ _
  have split : y - E = (y - (old + sign * D)) + (sign * D - sign * T) := by rw [exact]; ring
  have total := abs_add_le (y - (old + sign * D)) (sign * D - sign * T)
  rw [← split, shift] at total
  have pow150 : (1 : ℚ) / 2 ^ 150 ≤ 1 / 2 ^ 60 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have nonneg := abs_nonneg (D - T)
  have targetNonneg := abs_nonneg T
  have newNonneg := abs_nonneg E
  have oldNonneg := abs_nonneg old
  norm_num at rounded increment pow150 ⊢
  linarith

/-- The deviation of the executed second weight at one slot from the exact step, before the
projection. -/
def secondDeviation (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (query : FeatIdx dimension) : ℚ :=
  if query ∈ passage.source.indices then
    numerical32 (learner.second[query.val].value.add (learner.increments passage cumulant).1) -
      (weightValue learner.second[query.val] +
        numerical64 passage.step * exactCorrection learner passage cumulant)
  else 0

/-- The deviation of the executed main weight at one slot from the exact step, before the
projection. -/
def mainDeviation (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (query : FeatIdx dimension) : ℚ :=
  let increment := numerical64 passage.step * exactMidpoint learner passage cumulant
  let G := numerical32 discount.gamma
  if query ∈ passage.onlySource then
    numerical32 (learner.main[query.val].value.add (learner.increments passage cumulant).2.1) -
      (weightValue learner.main[query.val] + increment)
  else if query ∈ passage.both then
    numerical32 (learner.main[query.val].value.add (learner.increments passage cumulant).2.2.1) -
      (weightValue learner.main[query.val] + (1 - G) * increment)
  else if query ∈ passage.onlyTarget then
    numerical32 (learner.main[query.val].value.sub (learner.increments passage cumulant).2.2.2) -
      (weightValue learner.main[query.val] - G * increment)
  else 0

/-- A finite word plus or minus a finite increment of magnitude at most 64, from a stored
weight: the result is finite and rounded relative to its magnitude. -/
theorem write_rounded (old delta : Binary32) (oldFinite : old.Finite) (deltaFinite : delta.Finite)
    (oldBound : |numerical32 old| ≤ 101) (deltaBound : |numerical32 delta| ≤ 64) :
    (old.add delta).Finite ∧
      |numerical32 (old.add delta) - (numerical32 old + 1 * numerical32 delta)| ≤
        |numerical32 old + 1 * numerical32 delta| / 16777216 + 1 / 2 ^ 150 ∧
      (old.sub delta).Finite ∧
      |numerical32 (old.sub delta) - (numerical32 old + -1 * numerical32 delta)| ≤
        |numerical32 old + -1 * numerical32 delta| / 16777216 + 1 / 2 ^ 150 := by
  have added := binary32_rounded_add old delta oldFinite deltaFinite
    (le_trans (abs_add_le _ _) (by linarith))
  have subtracted := binary32_rounded_sub old delta oldFinite deltaFinite
    (le_trans (abs_sub _ _) (by linarith))
  have addError := binary32_add_relative old delta oldFinite deltaFinite added.1
  have subError := binary32_sub_relative old delta oldFinite deltaFinite subtracted.1
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
  exact ⟨added.1, addError, subtracted.1, subError⟩

/-- At every slot the executed second weight is no farther from zero than the exact step plus
its deviation, and the deviation is at most `2^(-22)` of the old and new exact magnitudes plus
`2^(-24)` on `x`, and zero elsewhere. -/
theorem second_slot (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (small : dimension.capacity ≤ 65536) (finite : cumulant.Finite)
    (bounded : |numerical32 cumulant| ≤ 1) (query : FeatIdx dimension) :
    let exact := weightValue learner.second[query.val] +
      numerical64 passage.step * exactCorrection learner passage cumulant *
        indicator passage.source.indices query
    weightValue (learner.step passage cumulant).second[query.val] ^ 2 ≤
        (exact + secondDeviation learner passage cumulant query) ^ 2 ∧
      |secondDeviation learner passage cumulant query| ≤
        (|exact| + |weightValue learner.second[query.val]|) / 4194304 +
          indicator passage.source.indices query / 16777216 := by
  intro exact
  obtain ⟨_, _, _, _, nonneg, _⟩ := horizon_facts discount
  have increments := (increments_close learner passage cumulant small finite bounded).1
  have old := weight_numerical_bound _ learner.second[query.val]
  have write := write_rounded learner.second[query.val].value
    (learner.increments passage cumulant).1 old.1 increments.1 old.2 increments.2.2
  simp only [exact]
  rw [step_second]
  unfold secondDeviation indicator
  by_cases inside : query ∈ passage.source.indices
  · simp only [inside, ↓reduceIte, mul_one]
    constructor
    · have same : weightValue learner.second[query.val] +
          numerical64 passage.step * exactCorrection learner passage cumulant +
          (numerical32 (learner.second[query.val].value.add
            (learner.increments passage cumulant).1) -
            (weightValue learner.second[query.val] +
              numerical64 passage.step * exactCorrection learner passage cumulant)) =
          numerical32 (learner.second[query.val].value.add
            (learner.increments passage cumulant).1) :=
        by ring
      rw [same]
      have toward := clampSym_toward (numerical32 discount.horizon)
        (numerical32 (learner.second[query.val].value.add (learner.increments passage cumulant).1))
        0 (by simpa using nonneg)
      rw [← project_value discount _ write.1] at toward
      simpa [weightValue] using toward
    · have deviation := write_deviation
        (numerical32 (learner.second[query.val].value.add (learner.increments passage cumulant).1))
        (weightValue learner.second[query.val])
        (numerical32 (learner.increments passage cumulant).1)
        (numerical64 passage.step * exactCorrection learner passage cumulant)
        (weightValue learner.second[query.val] +
          numerical64 passage.step * exactCorrection learner passage cumulant) 1 (Or.inl rfl)
        (by ring) write.2.1 increments.2.1
      linarith
  · simp only [inside, ↓reduceIte, mul_zero, add_zero]
    constructor
    · exact le_refl _
    · simp only [abs_zero]
      positivity

/-- At every slot the executed main weight is no farther from the reference than the exact
step plus its deviation, and the deviation is at most `2^(-22)` of the old and new exact
magnitudes plus `2^(-24)` on `x ∪ x'`, and zero elsewhere. -/
theorem main_slot (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (small : dimension.capacity ≤ 65536) (finite : cumulant.Finite)
    (bounded : |numerical32 cumulant| ≤ 1) (reference : FeatIdx dimension → ℚ)
    (inside : ∀ j, |reference j| ≤ numerical32 discount.horizon) (query : FeatIdx dimension) :
    let exact := weightValue learner.main[query.val] +
      numerical64 passage.step * exactMidpoint learner passage cumulant *
        direction discount passage query
    (weightValue (learner.step passage cumulant).main[query.val] - reference query) ^ 2 ≤
        (exact - reference query + mainDeviation learner passage cumulant query) ^ 2 ∧
      |mainDeviation learner passage cumulant query| ≤
        (|exact| + |weightValue learner.main[query.val]|) / 4194304 +
          max (indicator passage.source.indices query) (indicator passage.target.indices query) /
            16777216 := by
  intro exact
  obtain ⟨_, sourceDelta, sharedDelta, targetDelta⟩ :=
    increments_close learner passage cumulant small finite bounded
  have old := weight_numerical_bound _ learner.main[query.val]
  have partition := classes_partition passage query
  have disjoint := classes_disjoint passage query
  set increment := numerical64 passage.step * exactMidpoint learner passage cumulant
    with incrementDef
  set G := numerical32 discount.gamma with GDef
  have toward (raw : Binary32) (rawFinite : raw.Finite) :
      (numerical32 (Weight.project (.discounted discount) raw).value - reference query) ^ 2 ≤
        (numerical32 raw - reference query) ^ 2 := by
    rw [project_value discount raw rawFinite]
    exact clampSym_toward _ _ _ (inside query)
  simp only [exact]
  rw [step_main]
  unfold mainDeviation direction indicator
  rw [onlySource_mem, both_mem, onlyTarget_mem] at disjoint partition
  simp only [onlySource_mem, both_mem, onlyTarget_mem]
  by_cases inSource : query ∈ passage.source.indices <;>
    by_cases inTarget : query ∈ passage.target.indices
  · -- both
    simp only [inSource, inTarget, not_true_eq_false, and_false, and_self, ↓reduceIte, mul_one]
    have write := write_rounded learner.main[query.val].value
      (learner.increments passage cumulant).2.2.1 old.1 sharedDelta.1 old.2 sharedDelta.2.2
    constructor
    · have same : weightValue learner.main[query.val] + increment * (1 - G) - reference query +
          (numerical32 (learner.main[query.val].value.add
            (learner.increments passage cumulant).2.2.1) -
            (weightValue learner.main[query.val] + (1 - G) * increment)) =
          numerical32 (learner.main[query.val].value.add
            (learner.increments passage cumulant).2.2.1) -
            reference query := by ring
      rw [same]
      exact toward _ write.1
    · have deviation := write_deviation
        (numerical32 (learner.main[query.val].value.add
          (learner.increments passage cumulant).2.2.1))
        (weightValue learner.main[query.val])
        (numerical32 (learner.increments passage cumulant).2.2.1)
        ((1 - G) * increment) (weightValue learner.main[query.val] + (1 - G) * increment) 1
        (Or.inl rfl) (by ring) write.2.1 sharedDelta.2.1
      have same : weightValue learner.main[query.val] + increment * (1 - G) =
          weightValue learner.main[query.val] + (1 - G) * increment := by ring
      rw [same]
      norm_num at deviation ⊢
      linarith
  · -- source only
    simp only [inSource, inTarget, not_false_eq_true, and_true, ↓reduceIte, mul_one, mul_zero,
      sub_zero]
    have write := write_rounded learner.main[query.val].value
      (learner.increments passage cumulant).2.1 old.1 sourceDelta.1 old.2 sourceDelta.2.2
    constructor
    · have same : weightValue learner.main[query.val] + increment - reference query +
          (numerical32 (learner.main[query.val].value.add
            (learner.increments passage cumulant).2.1) -
            (weightValue learner.main[query.val] + increment)) =
          numerical32 (learner.main[query.val].value.add
            (learner.increments passage cumulant).2.1) -
            reference query := by ring
      rw [same]
      exact toward _ write.1
    · have deviation := write_deviation
        (numerical32 (learner.main[query.val].value.add (learner.increments passage cumulant).2.1))
        (weightValue learner.main[query.val])
        (numerical32 (learner.increments passage cumulant).2.1)
        increment (weightValue learner.main[query.val] + increment) 1 (Or.inl rfl) (by ring)
        write.2.1 sourceDelta.2.1
      norm_num at deviation ⊢
      linarith
  · -- target only
    simp only [inSource, inTarget, not_false_eq_true, and_true, false_and, ↓reduceIte, mul_one,
      zero_sub, mul_neg]
    have write := write_rounded learner.main[query.val].value
      (learner.increments passage cumulant).2.2.2 old.1 targetDelta.1 old.2 targetDelta.2.2
    constructor
    · have same : weightValue learner.main[query.val] + -(increment * G) - reference query +
          (numerical32 (learner.main[query.val].value.sub
            (learner.increments passage cumulant).2.2.2) -
            (weightValue learner.main[query.val] - G * increment)) =
          numerical32 (learner.main[query.val].value.sub
            (learner.increments passage cumulant).2.2.2) -
            reference query := by ring
      rw [same]
      exact toward _ write.2.2.1
    · have deviation := write_deviation
        (numerical32 (learner.main[query.val].value.sub
          (learner.increments passage cumulant).2.2.2))
        (weightValue learner.main[query.val])
        (numerical32 (learner.increments passage cumulant).2.2.2)
        (G * increment) (weightValue learner.main[query.val] - G * increment) (-1) (Or.inr rfl)
        (by ring) write.2.2.2 targetDelta.2.1
      have same : weightValue learner.main[query.val] + -(increment * G) =
          weightValue learner.main[query.val] - G * increment := by ring
      rw [same]
      norm_num at deviation ⊢
      linarith
  · -- neither
    simp only [inSource, inTarget, false_and, and_false, ↓reduceIte, mul_zero, sub_zero,
      add_zero]
    constructor
    · exact le_refl _
    · simp only [abs_zero]
      positivity

end Writes

/-! ## The energy theorem -/

/-- Pointwise bounds by four nonnegative pairs of vectors bound the squared length by the
square of the sum of their lengths. -/
theorem pair_four {ι : Type} [Fintype ι] (f₁ f₂ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ι → ℚ)
    {α β γ δ : ℚ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (first : ∀ i, |f₁ i| ≤ a₁ i + b₁ i + c₁ i + d₁ i)
    (second : ∀ i, |f₂ i| ≤ a₂ i + b₂ i + c₂ i + d₂ i)
    (la : ∑ i, a₁ i ^ 2 + ∑ i, a₂ i ^ 2 ≤ α ^ 2) (lb : ∑ i, b₁ i ^ 2 + ∑ i, b₂ i ^ 2 ≤ β ^ 2)
    (lc : ∑ i, c₁ i ^ 2 + ∑ i, c₂ i ^ 2 ≤ γ ^ 2) (ld : ∑ i, d₁ i ^ 2 + ∑ i, d₂ i ^ 2 ≤ δ ^ 2) :
    ∑ i, f₁ i ^ 2 + ∑ i, f₂ i ^ 2 ≤ (α + β + γ + δ) ^ 2 := by
  have ab := AcornVerif.Extragradient.pair_add a₁ a₂ b₁ b₂ hα hβ la lb
  have abc := AcornVerif.Extragradient.pair_add (fun i => a₁ i + b₁ i) (fun i => a₂ i + b₂ i)
    c₁ c₂ (add_nonneg hα hβ) hγ ab lc
  have abcd := AcornVerif.Extragradient.pair_add (fun i => a₁ i + b₁ i + c₁ i)
    (fun i => a₂ i + b₂ i + c₂ i) d₁ d₂ (add_nonneg (add_nonneg hα hβ) hγ) hδ abc ld
  have pointwise₁ : ∀ i, f₁ i ^ 2 ≤ (a₁ i + b₁ i + c₁ i + d₁ i) ^ 2 := fun i =>
    sq_le_sq' (by linarith [neg_abs_le (f₁ i), first i]) (le_trans (le_abs_self _) (first i))
  have pointwise₂ : ∀ i, f₂ i ^ 2 ≤ (a₂ i + b₂ i + c₂ i + d₂ i) ^ 2 := fun i =>
    sq_le_sq' (by linarith [neg_abs_le (f₂ i), second i]) (le_trans (le_abs_self _) (second i))
  calc ∑ i, f₁ i ^ 2 + ∑ i, f₂ i ^ 2
      ≤ ∑ i, (a₁ i + b₁ i + c₁ i + d₁ i) ^ 2 + ∑ i, (a₂ i + b₂ i + c₂ i + d₂ i) ^ 2 :=
        add_le_add (Finset.sum_le_sum fun i _ => pointwise₁ i)
          (Finset.sum_le_sum fun i _ => pointwise₂ i)
    _ ≤ (α + β + γ + δ) ^ 2 := abcd

section EnergyTheorem
variable {discount : Discount}

theorem indicator_nonneg {size : Nat} (indices : List (Fin size)) (query : Fin size) :
    0 ≤ indicator indices query := by
  unfold indicator
  split <;> norm_num

/-- The exact step's second weight at one slot, from the stored words. -/
def exactSecond (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (query : FeatIdx dimension) : ℚ :=
  weightValue learner.second[query.val] +
    numerical64 passage.step * exactCorrection learner passage cumulant *
      indicator passage.source.indices query

/-- The exact step's main weight at one slot, from the stored words. -/
def exactMain (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (query : FeatIdx dimension) : ℚ :=
  weightValue learner.main[query.val] +
    numerical64 passage.step * exactMidpoint learner passage cumulant *
      direction discount passage query

/-- The exact extragradient step from the stored words, with the executed step size, satisfies
the energy inequality: its guard holds for every transition in a space of at most `2^16`
slots. -/
theorem exact_energy (learner : GradientLearner discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (small : dimension.capacity ≤ 65536)
    (reference : FeatIdx dimension → ℚ) {t s : ℚ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (start : distance learner reference ≤ t ^ 2)
    (push : numerical64 passage.step * exactTau passage ≤ s ^ 2) :
    ∑ j, exactSecond learner passage cumulant j ^ 2 +
        ∑ j, (exactMain learner passage cumulant j - reference j) ^ 2 ≤
      (t + |residual discount passage cumulant reference| * s) ^ 2 := by
  obtain ⟨nPos, nSmall, mSmall, stepFinite, hPos, hScaled⟩ := passage_sizes passage small
  obtain ⟨tauEq, curvatureEq, pEq, gapEq, squareBound⟩ :=
    exact_counterparts learner passage cumulant reference
  simp only at tauEq curvatureEq pEq gapEq squareBound
  have hNonneg : 0 ≤ numerical64 passage.step := le_of_lt hPos
  have nNonneg : (0 : ℚ) ≤ passage.source.indices.length := Nat.cast_nonneg _
  have mNonneg : (0 : ℚ) ≤ passage.target.indices.length := Nat.cast_nonneg _
  have tauBound : numerical64 passage.step * ∑ j, indicator passage.source.indices j ^ 2 ≤
      1 / 9 := by
    rw [tauEq]
    simp only [exactTau]
    nlinarith
  have curvatureBound : numerical64 passage.step * ∑ j, direction discount passage j ^ 2 ≤
      1 / 9 := by
    have := mul_le_mul_of_nonneg_left squareBound hNonneg
    linarith
  have tauNonneg : 0 ≤ numerical64 passage.step * ∑ j, indicator passage.source.indices j ^ 2 :=
    mul_nonneg hNonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have curvatureNonneg : 0 ≤ numerical64 passage.step * ∑ j, direction discount passage j ^ 2 :=
    mul_nonneg hNonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have guard : numerical64 passage.step * (∑ j, indicator passage.source.indices j ^ 2) *
      (numerical64 passage.step * (∑ j, indicator passage.source.indices j ^ 2) +
        2 * (numerical64 passage.step * ∑ j, direction discount passage j ^ 2)) ≤ 1 := by
    nlinarith
  have curvature : numerical64 passage.step * (∑ j, direction discount passage j ^ 2) ≤
      2 - numerical64 passage.step * (∑ j, indicator passage.source.indices j ^ 2) := by
    linarith
  have pushed : numerical64 passage.step *
      (numerical64 passage.step * ∑ j, indicator passage.source.indices j ^ 2) ≤ s ^ 2 := by
    rw [tauEq]
    exact push
  have exact := AcornVerif.Extragradient.extragradient_energy
    (fun j : FeatIdx dimension => weightValue learner.second[j.val])
    (fun j : FeatIdx dimension => weightValue learner.main[j.val] - reference j)
    (indicator passage.source.indices) (direction discount passage) (numerical64 passage.step)
    (residual discount passage cumulant reference) t s hNonneg guard curvature ht hs start pushed
  simp only at exact
  rw [gapEq, pEq, tauEq, curvatureEq] at exact
  refine le_trans (le_of_eq ?_) exact
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
  unfold exactMain exactMidpoint
  ring

/-- The deviations of the executed writes from the exact step are at most `2^(-22)` of the
exact step's distance and of the starting distance, plus `2^(-21)` of the reference's length
and the absolute term `R`. -/
theorem deviation_energy (learner : GradientLearner discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (small : dimension.capacity ≤ 65536)
    (finite : cumulant.Finite) (bounded : |numerical32 cumulant| ≤ 1)
    (reference : FeatIdx dimension → ℚ) (inside : ∀ j, |reference j| ≤ numerical32 discount.horizon)
    {t s m R : ℚ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hm : 0 ≤ m) (hR : 0 ≤ R)
    (start : distance learner reference ≤ t ^ 2)
    (push : numerical64 passage.step * exactTau passage ≤ s ^ 2)
    (size : ∑ j, reference j ^ 2 ≤ m ^ 2)
    (rounding : (2 * (passage.source.indices.length : ℚ) + passage.target.indices.length) /
      281474976710656 ≤ R ^ 2) :
    ∑ j, secondDeviation learner passage cumulant j ^ 2 +
        ∑ j, mainDeviation learner passage cumulant j ^ 2 ≤
      ((t + |residual discount passage cumulant reference| * s) / 4194304 + t / 4194304 +
        m / 2097152 + R) ^ 2 := by
  have exact := exact_energy learner passage cumulant small reference ht hs start push
  have exactNonneg : 0 ≤ t + |residual discount passage cumulant reference| * s :=
    add_nonneg ht (mul_nonneg (abs_nonneg _) hs)
  apply pair_four (secondDeviation learner passage cumulant)
    (mainDeviation learner passage cumulant)
    (fun j => |exactSecond learner passage cumulant j| / 4194304)
    (fun j => |exactMain learner passage cumulant j - reference j| / 4194304)
    (fun j => |weightValue learner.second[j.val]| / 4194304)
    (fun j => |weightValue learner.main[j.val] - reference j| / 4194304)
    (fun _ => 0) (fun j => |reference j| / 2097152)
    (fun j => indicator passage.source.indices j / 16777216)
    (fun j => max (indicator passage.source.indices j) (indicator passage.target.indices j) /
      16777216)
    (div_nonneg exactNonneg (by norm_num)) (div_nonneg ht (by norm_num))
    (div_nonneg hm (by norm_num)) hR
  · intro j
    have slot := (second_slot learner passage cumulant small finite bounded j).2
    simp only at slot
    simp only [exactSecond]
    linarith
  · intro j
    have slot := (main_slot learner passage cumulant small finite bounded reference inside j).2
    simp only at slot
    have newBound := abs_add_le (exactMain learner passage cumulant j - reference j) (reference j)
    have oldBound := abs_add_le (weightValue learner.main[j.val] - reference j) (reference j)
    rw [sub_add_cancel] at newBound oldBound
    simp only [exactMain] at newBound ⊢
    linarith
  · have scaled : ∑ j, (|exactSecond learner passage cumulant j| / 4194304) ^ 2 +
        ∑ j, (|exactMain learner passage cumulant j - reference j| / 4194304) ^ 2 =
        (∑ j, exactSecond learner passage cumulant j ^ 2 +
          ∑ j, (exactMain learner passage cumulant j - reference j) ^ 2) / 4194304 ^ 2 := by
      simp only [div_pow, sq_abs, ← Finset.sum_div]
      ring
    rw [scaled, div_pow]
    exact div_le_div_of_nonneg_right exact (by positivity)
  · have scaled : ∑ j : FeatIdx dimension, (|weightValue learner.second[j.val]| / 4194304) ^ 2 +
        ∑ j, (|weightValue learner.main[j.val] - reference j| / 4194304) ^ 2 =
        distance learner reference / 4194304 ^ 2 := by
      simp only [distance, div_pow, sq_abs, ← Finset.sum_div]
      ring
    rw [scaled, div_pow]
    exact div_le_div_of_nonneg_right start (by positivity)
  · have scaled : ∑ _j : FeatIdx dimension, (0 : ℚ) ^ 2 +
        ∑ j, (|reference j| / 2097152) ^ 2 = (∑ j, reference j ^ 2) / 2097152 ^ 2 := by
      simp only [div_pow, sq_abs, ← Finset.sum_div]
      norm_num
    rw [scaled, div_pow]
    exact div_le_div_of_nonneg_right size (by positivity)
  · have squares : ∀ j, (indicator passage.source.indices j / 16777216) ^ 2 ≤
        indicator passage.source.indices j / 281474976710656 := by
      intro j
      unfold indicator
      split <;> norm_num
    have pairSquares : ∀ j, (max (indicator passage.source.indices j)
        (indicator passage.target.indices j) / 16777216) ^ 2 ≤
        (indicator passage.source.indices j + indicator passage.target.indices j) /
          281474976710656 := by
      intro j
      unfold indicator
      split <;> split <;> norm_num
    have first := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => squares j
    have second := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => pairSquares j
    rw [← Finset.sum_div] at first second
    rw [Finset.sum_add_distrib] at second
    rw [sum_indicator_one _ passage.source.nodup] at first second
    rw [sum_indicator_one _ passage.target.nodup] at second
    linarith

/-- **Energy over the executed step.** For every learner state, every classified transition in
a space of at most `2^16` slots, every finite signal word in `[−1, 1]` and every reference `w*`
inside the weight range: if `N ≤ t²` before the step, `h·τ ≤ s²`, `|w*|² ≤ m²` and
`(2|x| + |x'|)·2^(−48) ≤ R²`, then after the step
`N ≤ ((1 + 2^(−21))·t + (1 + 2^(−22))·|ε|·s + 2^(−21)·m + R)²`. With `w* = 0`, `√N` grows per
step by at most the factor `1 + 2^(−21)`, plus `(1 + 2^(−22))·|c|·s + R`. -/
theorem step_energy (learner : GradientLearner discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (small : dimension.capacity ≤ 65536)
    (finite : cumulant.Finite) (bounded : |numerical32 cumulant| ≤ 1)
    (reference : FeatIdx dimension → ℚ) (inside : ∀ j, |reference j| ≤ numerical32 discount.horizon)
    {t s m R : ℚ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hm : 0 ≤ m) (hR : 0 ≤ R)
    (start : distance learner reference ≤ t ^ 2)
    (push : numerical64 passage.step * exactTau passage ≤ s ^ 2)
    (size : ∑ j, reference j ^ 2 ≤ m ^ 2)
    (rounding : (2 * (passage.source.indices.length : ℚ) + passage.target.indices.length) /
      281474976710656 ≤ R ^ 2) :
    distance (learner.step passage cumulant) reference ≤
      ((1 + 1 / 2097152) * t +
        (1 + 1 / 4194304) * |residual discount passage cumulant reference| * s +
        m / 2097152 + R) ^ 2 := by
  have exact := exact_energy learner passage cumulant small reference ht hs start push
  have deviations := deviation_energy learner passage cumulant small finite bounded reference
    inside ht hs hm hR start push size rounding
  have exactNonneg : 0 ≤ t + |residual discount passage cumulant reference| * s :=
    add_nonneg ht (mul_nonneg (abs_nonneg _) hs)
  have deviationNonneg : 0 ≤ (t + |residual discount passage cumulant reference| * s) / 4194304 +
      t / 4194304 + m / 2097152 + R := by
    have : 0 ≤ (t + |residual discount passage cumulant reference| * s) / 4194304 :=
      div_nonneg exactNonneg (by norm_num)
    linarith
  have total := AcornVerif.Extragradient.pair_add (exactSecond learner passage cumulant)
    (fun j => exactMain learner passage cumulant j - reference j)
    (secondDeviation learner passage cumulant) (mainDeviation learner passage cumulant)
    exactNonneg deviationNonneg exact deviations
  unfold distance
  calc ∑ j : FeatIdx dimension, weightValue (learner.step passage cumulant).second[j.val] ^ 2 +
        ∑ j : FeatIdx dimension,
          (weightValue (learner.step passage cumulant).main[j.val] - reference j) ^ 2
      ≤ ∑ j, (exactSecond learner passage cumulant j +
            secondDeviation learner passage cumulant j) ^ 2 +
          ∑ j, (exactMain learner passage cumulant j - reference j +
            mainDeviation learner passage cumulant j) ^ 2 := by
        apply add_le_add
        · exact Finset.sum_le_sum fun j _ =>
            (second_slot learner passage cumulant small finite bounded j).1
        · exact Finset.sum_le_sum fun j _ =>
            (main_slot learner passage cumulant small finite bounded reference inside j).1
    _ ≤ (t + |residual discount passage cumulant reference| * s +
          ((t + |residual discount passage cumulant reference| * s) / 4194304 + t / 4194304 +
            m / 2097152 + R)) ^ 2 := total
    _ = ((1 + 1 / 2097152) * t +
          (1 + 1 / 4194304) * |residual discount passage cumulant reference| * s +
          m / 2097152 + R) ^ 2 := by ring

/-- A question's step is its learner's step, except that a silent question at a zero signal
word keeps its state. -/
theorem question_step (question : Question discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    (question.step passage cumulant).learner =
      if question.silent && cumulant.bits == 0 then question.learner
      else question.learner.step passage cumulant := by
  rcases question with ⟨learner, silent, blank⟩
  simp only [Question.step]
  split <;> rfl

/-- A question stays silent exactly while it is silent and its signal word is zero. -/
theorem question_silent (question : Question discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) :
    (question.step passage cumulant).silent = (question.silent && cumulant.bits == 0) := by
  rcases question with ⟨learner, silent, blank⟩
  simp only [Question.step]
  split
  · rename_i kept
    have parts : silent = true ∧ cumulant.bits = 0 := by simpa using kept
    simp [parts.1, parts.2]
  · rename_i ended
    exact (Bool.eq_false_iff.mpr ended).symm

/-- Zero weights and a zero signal are a fixed point of Algorithm 2. Wherever
`Question.step` takes no step, the exact midpoint `p_m` and correction `δ_m − p_m` read from
the stored words are zero, so Algorithm 2 in exact arithmetic adds zero to every weight.
This concerns the exact step; that the executed learner step would write the same words is
not stated here. -/
theorem silent_fixed (question : Question discount dimension) (passage : Passage dimension)
    (cumulant : Binary32) (skipped : (question.silent && cumulant.bits == 0) = true) :
    exactMidpoint question.learner passage cumulant = 0 ∧
      exactCorrection question.learner passage cumulant = 0 := by
  have parts : question.silent = true ∧ cumulant.bits = 0 := by simpa using skipped
  have word : cumulant = .zero := by
    cases cumulant
    simp_all [Binary32.zero]
  subst word
  have zero : numerical32 Binary32.zero = 0 := by decide
  have blank := question.blank parts.1
  have sums {rule : ValueRule} (weights : WeightArray rule dimension)
      (stored : ∀ index : FeatIdx dimension, weights[index.val].value = .zero)
      (indices : List (FeatIdx dimension)) : exactSum weights indices = 0 := by
    unfold exactSum
    apply List.sum_eq_zero
    intro value member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    have word : (weights.get index).value = .zero := stored index
    rw [word, zero]
  have main := sums question.learner.main fun index => (blank index).1
  have second := sums question.learner.second fun index => (blank index).2
  simp [exactMidpoint, exactCorrection, exactGap, main, second, zero]

/-- **Energy over a question's step.** The bound of `step_energy` holds for the executed
step of every question, silent or not: a step not taken leaves the distance unchanged. -/
theorem question_energy (question : Question discount dimension)
    (passage : Passage dimension) (cumulant : Binary32) (small : dimension.capacity ≤ 65536)
    (finite : cumulant.Finite) (bounded : |numerical32 cumulant| ≤ 1)
    (reference : FeatIdx dimension → ℚ) (inside : ∀ j, |reference j| ≤ numerical32 discount.horizon)
    {t s m R : ℚ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hm : 0 ≤ m) (hR : 0 ≤ R)
    (start : distance question.learner reference ≤ t ^ 2)
    (push : numerical64 passage.step * exactTau passage ≤ s ^ 2)
    (size : ∑ j, reference j ^ 2 ≤ m ^ 2)
    (rounding : (2 * (passage.source.indices.length : ℚ) + passage.target.indices.length) /
      281474976710656 ≤ R ^ 2) :
    distance (question.step passage cumulant).learner reference ≤
      ((1 + 1 / 2097152) * t +
        (1 + 1 / 4194304) * |residual discount passage cumulant reference| * s +
        m / 2097152 + R) ^ 2 := by
  rw [question_step]
  split
  · have push' : 0 ≤ |residual discount passage cumulant reference| * s :=
      mul_nonneg (abs_nonneg _) hs
    have grown : t ≤ (1 + 1 / 2097152) * t +
        (1 + 1 / 4194304) * |residual discount passage cumulant reference| * s +
        m / 2097152 + R := by
      have : 0 ≤ m / 2097152 := div_nonneg hm (by norm_num)
      nlinarith
    exact start.trans (pow_le_pow_left₀ ht grown 2)
  · exact step_energy question.learner passage cumulant small finite bounded reference inside
      ht hs hm hR start push size rounding

end EnergyTheorem

/-! ## The step size keeps the guard -/

/-- For every transition in a space of at most `2^16` slots, the executed step size makes
`τ = h|x|` and `κ = h|a|²` at most `1/9`, so `τ(τ + 2κ) ≤ 1` and `κ ≤ 2 − τ`, the two
hypotheses of `AcornVerif.Extragradient.extragradient_energy`. -/
theorem step_guard {discount : Discount} (passage : Passage dimension)
    (small : dimension.capacity ≤ 65536) :
    0 ≤ exactTau passage ∧ exactTau passage ≤ 1 / 9 ∧
      0 ≤ exactCurvature discount passage ∧ exactCurvature discount passage ≤ 1 / 9 ∧
      exactTau passage * (exactTau passage + 2 * exactCurvature discount passage) ≤ 1 ∧
      exactCurvature discount passage ≤ 2 - exactTau passage := by
  obtain ⟨_, _, _, _, hPos, hScaled⟩ := passage_sizes passage small
  obtain ⟨_, gLower, gUpper⟩ := gamma_bounds discount
  have counts := class_counts passage
  have nSplit : (passage.source.indices.length : ℚ) =
      passage.onlySource.length + passage.both.length := by exact_mod_cast counts.1
  have mSplit : (passage.target.indices.length : ℚ) =
      passage.onlyTarget.length + passage.both.length := by exact_mod_cast counts.2
  have one : (0 : ℚ) ≤ passage.onlySource.length := Nat.cast_nonneg _
  have two : (0 : ℚ) ≤ passage.both.length := Nat.cast_nonneg _
  have three : (0 : ℚ) ≤ passage.onlyTarget.length := Nat.cast_nonneg _
  have hNonneg : 0 ≤ numerical64 passage.step := le_of_lt hPos
  have weights : passage.onlySource.length +
      numerical32 discount.gamma * numerical32 discount.gamma * passage.onlyTarget.length +
        (1 - numerical32 discount.gamma) * (1 - numerical32 discount.gamma) * passage.both.length ≤
      (passage.source.indices.length : ℚ) + passage.target.indices.length := by
    rw [nSplit, mSplit]
    have gg : numerical32 discount.gamma * numerical32 discount.gamma ≤ 1 := by nlinarith
    have cc : (1 - numerical32 discount.gamma) * (1 - numerical32 discount.gamma) ≤ 1 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right gg three, mul_le_mul_of_nonneg_right cc two]
  have weightsNonneg : 0 ≤ passage.onlySource.length +
      numerical32 discount.gamma * numerical32 discount.gamma * passage.onlyTarget.length +
        (1 - numerical32 discount.gamma) * (1 - numerical32 discount.gamma) *
          passage.both.length := by
    have := mul_nonneg (mul_nonneg gLower gLower) three
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr gUpper) (sub_nonneg.mpr gUpper)) two
    linarith
  have tauLe : exactTau passage ≤ 1 / 9 := by
    simp only [exactTau]
    have : (0 : ℚ) ≤ passage.target.indices.length := Nat.cast_nonneg _
    nlinarith
  have tauNonneg : 0 ≤ exactTau passage := mul_nonneg hNonneg (Nat.cast_nonneg _)
  have curvatureLe : exactCurvature discount passage ≤ 1 / 9 := by
    simp only [exactCurvature]
    have := mul_le_mul_of_nonneg_left weights hNonneg
    linarith
  have curvatureNonneg : 0 ≤ exactCurvature discount passage := mul_nonneg hNonneg weightsNonneg
  refine ⟨tauNonneg, tauLe, curvatureNonneg, curvatureLe, by nlinarith, by linarith⟩

/-! ## Lifecycle -/

/-- A transition is learned from exactly when the stored set is not empty, and the stored
set after a frame is that frame's active set when its action was selected with the option's
distribution and the empty set otherwise. -/
theorem advance_stores (preceding : Preceding dimension) (current : SwiftTd.ActiveSet dimension)
    (armed : Bool) :
    (preceding.advance current armed).2.features =
        (if armed then current else SwiftTd.ActiveSet.empty dimension) ∧
      ((preceding.advance current armed).1.isSome = !preceding.features.indices.isEmpty) := by
  rcases preceding with ⟨source, flags, agrees⟩
  unfold Preceding.advance
  dsimp only
  split
  · rename_i empty
    simp only [empty, List.isEmpty_nil, Bool.not_true]
    cases armed <;> simp
  · rename_i head tail nonempty
    simp only [nonempty, List.isEmpty_cons, Bool.not_false]
    cases armed <;> simp

/-- The passage of a transition joins the stored set to the current one. -/
theorem advance_passage (preceding : Preceding dimension) (current : SwiftTd.ActiveSet dimension)
    (armed : Bool) (passage : Passage dimension)
    (learned : (preceding.advance current armed).1 = some passage) :
    passage.source = preceding.features ∧ passage.target = current := by
  rcases preceding with ⟨source, flags, agrees⟩
  unfold Preceding.advance at learned
  dsimp only at learned
  split at learned
  · cases armed <;> simp at learned
  · cases armed <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at learned <;>
      (subst learned; exact ⟨rfl, rfl⟩)

/-- Retirement resets both weights of a learner at the retired slot and keeps every other
slot. -/
theorem learner_retire {discount : Discount} (learner : GradientLearner discount dimension)
    (feature query : FeatIdx dimension) :
    (learner.retire feature).main[query.val] =
        (if query = feature then Weight.project _ .zero else learner.main[query.val]) ∧
      (learner.retire feature).second[query.val] =
        (if query = feature then Weight.project _ .zero else learner.second[query.val]) := by
  rcases learner with ⟨main, second⟩
  by_cases same : query = feature
  · subst same
    simp [GradientLearner.retire]
  · have different : feature.val ≠ query.val := fun equal => same (Fin.ext equal).symm
    simp [GradientLearner.retire, same, Vector.getElem_set_ne feature.isLt query.isLt different]

/-- Retirement leaves a question's retired slot at zero and every other slot as it was:
a silent question already holds zero there, and any other question's learner resets it. -/
theorem question_retire {discount : Discount} (question : Question discount dimension)
    (feature query : FeatIdx dimension) :
    (question.retire feature).learner.main[query.val].value =
        (if query = feature then .zero else question.learner.main[query.val].value) ∧
      (question.retire feature).learner.second[query.val].value =
        (if query = feature then .zero else question.learner.second[query.val].value) := by
  rcases question with ⟨learner, silent, blank⟩
  simp only [Question.retire]
  split
  · rename_i quiet
    have stored := blank quiet query
    by_cases same : query = feature
    · subst same
      simp only [↓reduceIte]
      exact stored
    · simp only [same, ↓reduceIte, and_self]
  · have reset := learner_retire learner feature query
    by_cases same : query = feature
    · subst same
      rw [reset.1, reset.2]
      simp [Weight.project_zero]
    · rw [reset.1, reset.2]
      simp [same]

/-- After retirement the stored set does not hold the retired slot, and holds every other
slot it held. -/
theorem preceding_retire (preceding : Preceding dimension) (feature query : FeatIdx dimension) :
    feature ∉ (preceding.retire feature).features.indices ∧
      (query ≠ feature →
        (query ∈ (preceding.retire feature).features.indices ↔
          query ∈ preceding.features.indices)) := by
  rcases preceding with ⟨features, flags, agrees⟩
  simp only [Preceding.retire, List.mem_filter, bne_iff_ne, ne_eq, not_true_eq_false, and_false,
    not_false_eq_true, true_and]
  intro different
  simp [different]

/-- Fresh questions store no frame, so the first transition after a start, a restore or a
reinstallation trains nothing. -/
theorem questions_initial (dimension : Dimension) (discounts : List Discount) :
    (OptionQuestions.initial dimension discounts).preceding.features.indices = [] := rfl

/-- Questions store the frame exactly when they are armed by it. -/
theorem questions_follow {discounts : List Discount}
    (questions : OptionQuestions dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (cumulants : Cumulants discounts) (armed : Bool) :
    (questions.follow features cumulants armed).preceding.features =
      if armed then features else SwiftTd.ActiveSet.empty dimension := by
  rcases questions with ⟨learners, preceding⟩
  have stores := (advance_stores preceding features armed).1
  unfold OptionQuestions.follow
  dsimp only
  split <;> (rename_i equation; rw [equation] at stores; exact stores)

/-! ## Work and storage -/

/-- The lists one step folds over. The sums and writes of `GradientLearner.scalars` and
`GradientLearner.step` are folds over the three class lists, for the main weights, and over
`x`, for the second weights. The class lists hold `|x ∪ x'| = |x| + |x'| − |x ∩ x'|` slots.
That the folds write in place is the runtime's storage reuse, which is not proved. -/
theorem passage_work (passage : Passage dimension) :
    passage.onlySource.length + passage.both.length + passage.onlyTarget.length +
        passage.both.length =
      passage.source.indices.length + passage.target.indices.length := by
  have counts := class_counts passage
  omega


/-- Weights held by a bank of questions. -/
def bankWeights {discounts : List Discount} : GradientBank dimension discounts → Nat
  | .nil => 0
  | .cons question rest =>
    question.learner.main.toArray.size + question.learner.second.toArray.size + bankWeights rest

/-- A bank stores two weights per feature slot for each signal, and nothing else that grows
with the stream: `2·d·k` weights for `k` signals over `d` slots. -/
theorem bank_weights {discounts : List Discount} (bank : GradientBank dimension discounts) :
    bankWeights bank = 2 * dimension.capacity * discounts.length := by
  induction bank with
  | nil => rfl
  | cons question rest ih =>
    simp only [bankWeights, ih, Vector.size_toArray, List.length_cons]
    ring

end AcornVerif.CurrentOffPolicy
