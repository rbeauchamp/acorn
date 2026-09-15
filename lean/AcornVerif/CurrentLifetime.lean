/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentLifetimeArithmetic

/-!
# Current lifetime sum invariants

The update adds one projected observation and caps at the incremented count's
closed quantity bound. All unsigned counts, saturation, shared-history narrower
caps and raw observation encodings are included. Rounded conversion and ordered
binary64 operations use the same executing definitions as the native agent.
-/
set_option maxRecDepth 4096

namespace AcornVerif.CurrentLifetime
open Acorn Acorn.Lifetime
open CurrentFloat CurrentPower CurrentArithmetic CurrentOrder CurrentLifetimeArithmetic

/-- Integer enclosures for the closed machine reading caps, not real-horizon substitutions. -/
def quantityLow : Quantity → UInt64
  | .reward => 1
  | .squaredError .g90 => 399
  | .squaredError .g95 => 1599
  | .squaredError .g99 => 40000

/-- Upper integer enclosures account for the machine gamma and squared-bound rounding. -/
def quantityHigh : Quantity → UInt64
  | .reward => 1
  | .squaredError .g90 => 400
  | .squaredError .g95 => 1600
  | .squaredError .g99 => 40001

/-- Each closed bound lies within its machine-checked integer enclosure. -/
theorem quantity_enclosure (quantity : Quantity) :
    (quantityLow quantity).toNat ≤ numerical64 (Conversion.widen quantity.bound) ∧
      numerical64 (Conversion.widen quantity.bound) ≤ (quantityHigh quantity).toNat := by
  have finite : quantity.bound.Finite := (quantity.range).upperFinite
  have low := numerical64_order (Binary64.ofUInt64 (quantityLow quantity))
    (Conversion.widen quantity.bound) (count_model _).1 (Conversion.widen_finite _ finite)
  have high := numerical64_order (Conversion.widen quantity.bound)
    (Binary64.ofUInt64 (quantityHigh quantity)) (Conversion.widen_finite _ finite) (count_model _).1
  rw [numerical64_ofUInt64 _ (by cases quantity with
    | reward => decide
    | squaredError d => cases d <;> decide)] at low
  rw [numerical64_ofUInt64 _ (by cases quantity with
    | reward => decide
    | squaredError d => cases d <;> decide)] at high
  constructor
  · apply low.mpr
    cases quantity with
    | reward => decide
    | squaredError d => cases d <;> decide
  · apply high.mpr
    cases quantity with
    | reward => decide
    | squaredError d => cases d <;> decide

/-- The closed quantities have finite positive reading bounds. -/
theorem quantity_bound (quantity : Quantity) :
    quantity.bound.Finite ∧
      1 ≤ numerical64 (Conversion.widen quantity.bound) ∧
        numerical64 (Conversion.widen quantity.bound) ≤ 65536 := by
  have bounds := quantity_enclosure quantity
  have low : 1 ≤ (quantityLow quantity).toNat := by
    cases quantity with
    | reward => decide
    | squaredError d => cases d <;> decide
  have high : (quantityHigh quantity).toNat ≤ 65536 := by
    cases quantity with
    | reward => decide
    | squaredError d => cases d <;> decide
  exact ⟨quantity.range.upperFinite,
    le_trans (by exact_mod_cast low) bounds.1,
    le_trans bounds.2 (by exact_mod_cast high)⟩

/-- Distinct closed caps are separated enough for half-relative rounding enclosures. -/
theorem quantity_separation (left right : Quantity) (ordered : left.bound.key ≤ right.bound.key) :
    left = right ∨ 3 * numerical64 (Conversion.widen left.bound) ≤
      numerical64 (Conversion.widen right.bound) := by
  have separated : left = right ∨
      3 * (quantityHigh left).toNat ≤ (quantityLow right).toNat := by
    cases left with
    | reward => cases right with
      | reward => exact Or.inl rfl
      | squaredError d => right; cases d <;> decide
    | squaredError left => cases right with
      | reward => cases left <;> contradiction
      | squaredError right =>
        cases left <;> cases right <;> first | exact Or.inl rfl | (right; decide) | contradiction
  rcases separated with same | gap
  · exact Or.inl same
  · right
    have low := (quantity_enclosure right).1
    have high := (quantity_enclosure left).2
    have gap' : (3 : ℚ) * (quantityHigh left).toNat ≤ (quantityLow right).toNat := by
      exact_mod_cast gap
    linarith

/-- A zero count computes exactly the zero cap for every closed quantity. -/
theorem cap_zero (quantity : Quantity) : maximumSum quantity 0 = Binary64.ofUInt64 0 := by
  cases quantity with
  | reward => decide
  | squaredError discount => cases discount <;> decide

/-- Positive count caps are finite, with a loose relative enclosure and wide absolute bound. -/
theorem cap_positive (quantity : Quantity) (count : UInt64) (positive : 0 < count.toNat) :
    (maximumSum quantity count).Finite ∧
      (numerical64 (Binary64.ofUInt64 count) * numerical64 (Conversion.widen quantity.bound)) / 2 ≤
        numerical64 (maximumSum quantity count) ∧
      numerical64 (maximumSum quantity count) ≤
        3 * (numerical64 (Binary64.ofUInt64 count) *
          numerical64 (Conversion.widen quantity.bound)) / 2 ∧
      numerical64 (maximumSum quantity count) ≤ (2 : ℚ) ^ (82 : Int) := by
  have countBound := count_model count
  have countLower := (count_nonnegative count).2 positive
  have scalar := quantity_bound quantity
  have lower : (1 : ℚ) / 2 ≤ numerical64 (Binary64.ofUInt64 count) *
      numerical64 (Conversion.widen quantity.bound) := by nlinarith
  have upper : numerical64 (Binary64.ofUInt64 count) *
      numerical64 (Conversion.widen quantity.bound) ≤ (2 : ℚ) ^ (82 : Int) := by
    have countUpper := (abs_le.mp countBound.2.1).2
    norm_num at countUpper ⊢
    nlinarith [mul_le_mul countUpper scalar.2.2 (by linarith) (by norm_num)]
  have relative := mul_positive_relative _ _ countBound.1
    (Conversion.widen_finite quantity.bound scalar.1) lower upper
  have error := abs_le.mp relative.2
  refine ⟨relative.1, by dsimp only [maximumSum]; linarith,
    by dsimp only [maximumSum]; linarith, ?_⟩
  have countUpper := (abs_le.mp countBound.2.1).2
  norm_num at countUpper ⊢
  have product := mul_le_mul countUpper scalar.2.2 (by linarith) (by norm_num)
  dsimp only [maximumSum]
  nlinarith

/-- Every count cap is finite and nonnegative, including the exactly empty total. -/
theorem cap_bounds (quantity : Quantity) (count : UInt64) :
    (maximumSum quantity count).Finite ∧ 0 ≤ numerical64 (maximumSum quantity count) ∧
      numerical64 (maximumSum quantity count) ≤ (2 : ℚ) ^ (82 : Int) := by
  by_cases zero : count.toNat = 0
  · have same : count = 0 := UInt64.toNat_inj.mp zero
    subst count
    rw [cap_zero]
    exact ⟨(count_model 0).1, by decide, by
      rw [numerical64_ofUInt64 0 (by decide)]
      norm_num⟩
  · have positive : 0 < count.toNat := by omega
    have cap := cap_positive quantity count positive
    have scalar := quantity_bound quantity
    have countLower := (count_nonnegative count).2 positive
    exact ⟨cap.1, by nlinarith [cap.2.1], cap.2.2.2⟩

/-- Narrower per-channel history caps remain below the receiving widest quantity cap. -/
theorem cap_monotone (left right : Quantity) (ordered : left.bound.key ≤ right.bound.key)
    (count : UInt64) : (maximumSum left count).key ≤ (maximumSum right count).key := by
  by_cases zero : count.toNat = 0
  · have same : count = 0 := UInt64.toNat_inj.mp zero
    subst count
    rw [cap_zero, cap_zero]
  · have positive : 0 < count.toNat := by omega
    rcases quantity_separation left right ordered with same | separated
    · subst right; exact le_rfl
    · have leftCap := cap_positive left count positive
      have rightCap := cap_positive right count positive
      have countLower := (count_nonnegative count).2 positive
      apply (numerical64_order _ _ leftCap.1 rightCap.1).mp
      have product := mul_le_mul_of_nonneg_left separated (le_of_lt (by linarith :
        0 < numerical64 (Binary64.ofUInt64 count)))
      have scalar := quantity_bound left
      nlinarith [leftCap.2.2.1, rightCap.2.1]

/-- Reading projection supplies the finite nonnegative observation consumed by the machine sum. -/
theorem reading_bounds (quantity : Quantity) (value : Binary32) :
    (Conversion.widen (quantity.range.saturate value)).Finite ∧
      0 ≤ numerical64 (Conversion.widen (quantity.range.saturate value)) ∧
      numerical64 (Conversion.widen (quantity.range.saturate value)) ≤ 65536 := by
  have reading := quantity.range.saturate_contains value
  have low : 0 ≤ numerical32 (quantity.range.saturate value) :=
    (numerical32_order .zero _ (by decide) reading.1).mpr reading.2.1
  have high := (numerical32_order _ quantity.bound reading.1 quantity.range.upperFinite).mpr
    reading.2.2
  have bound := (quantity_bound quantity).2.2
  rw [numerical_widen_exact quantity.bound quantity.range.upperFinite] at bound
  refine ⟨Conversion.widen_finite _ reading.1, ?_, ?_⟩
  · rwa [numerical_widen_exact _ reading.1]
  · rw [numerical_widen_exact _ reading.1]
    exact high.trans bound

/-- One actual source-ordered write preserves the receiving numeric invariant, including
narrower channel writes into shared history and the complete saturated count domain. -/
theorem sumUpdate_legal (quantity written : Quantity) (count : UInt64) (sum : Binary64)
    (value : Binary32) (ordered : written.bound.key ≤ quantity.bound.key)
    (legal : LegalSum quantity count sum) :
    LegalSum quantity (sumUpdate written count sum value).1
      (sumUpdate written count sum value).2 := by
  have countPositive : 0 < (addCount count 1).toNat := by
    rw [addCount_exact]
    change 0 < min (count.toNat + 1) (2^64 - 1)
    omega
  have oldCap := cap_bounds quantity count
  have sumPositive : 0 ≤ numerical64 sum :=
    (numerical64_order (Binary64.ofUInt64 0) sum (count_model 0).1 legal.1).mpr legal.2.1
  have sumBound := (numerical64_order sum (maximumSum quantity count) legal.1 oldCap.1).mpr
    legal.2.2.1
  have reading := reading_bounds written value
  let added := sum.add (Conversion.widen (written.range.saturate value))
  have addedSafe : added.Finite ∧ 0 ≤ numerical64 added :=
    CurrentLifetimeArithmetic.add_nonnegative _ _ legal.1 reading.1 sumPositive reading.2.1 (by
      have high := oldCap.2.2
      norm_num at high ⊢
      linarith [reading.2.2])
  let cap := maximumSum written (addCount count 1)
  have capSafe := cap_bounds written (addCount count 1)
  have orderedCaps := cap_monotone written quantity ordered (addCount count 1)
  have empty : addCount count 1 = 0 → False := by
    intro zero
    rw [zero] at countPositive
    contradiction
  change LegalSum quantity (addCount count 1) (if cap.less added then cap else added)
  unfold LegalSum
  split
  · refine ⟨capSafe.1, ?_, orderedCaps, fun zero => False.elim (empty zero)⟩
    exact (numerical64_order (Binary64.ofUInt64 0) cap (count_model 0).1 capSafe.1).mp capSafe.2.1
  · rename_i below
    have numericalBelow : numerical64 added ≤ numerical64 cap := by
      rw [numerical64_less _ _ capSafe.1 addedSafe.1] at below
      simpa only [decide_eq_true_eq, not_lt] using below
    refine ⟨addedSafe.1, ?_, ?_, fun zero => False.elim (empty zero)⟩
    · exact (numerical64_order (Binary64.ofUInt64 0) added (count_model 0).1 addedSafe.1).mp
        addedSafe.2
    · exact ((numerical64_order added cap addedSafe.1 capSafe.1).mp numericalBelow).trans
        orderedCaps

/-- Erased admission provenance entails the actual numeric state invariant after every write. -/
theorem sum_admitted_legal (quantity : Quantity) (count : UInt64) (sum : Binary64)
    (admitted : SumAdmitted quantity count sum) : LegalSum quantity count sum := by
  induction admitted with
  | durable count sum legal => exact legal
  | observation count sum value written ordered prior ih =>
    exact sumUpdate_legal quantity written count sum value ordered ih

/-- Every stored total is finite, nonnegative, count-capped and zero when empty. -/
theorem stored_sum_legal {quantity : Quantity} (state : SumCount quantity) :
    LegalSum quantity state.count state.sum := sum_admitted_legal _ _ _ state.admitted

end AcornVerif.CurrentLifetime
