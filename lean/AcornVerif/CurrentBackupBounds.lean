/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentModels
import AcornVerif.CurrentRetirementRounding

/-!
# Machine rounding bounds for scalar backups

The pinned Lean 4.33.0 standard model's `Unpacked/Round.lean` and
`Unpacked/Operations/{Add,Mul,Sub}.lean` own these machine operations.
Nearest-even monotonicity follows from quotient ordering on a common grid and
separation of distinct binades, then extends through signed normalization.
The `Rounded` relation is established from those executing operations before it
is used to compare their outputs. Packing fits and finite-word correspondence
are discharged at each binary32 wrapper; native compiler/runtime correspondence
remains trusted. No real-arithmetic reassociation replaces a rounded operation.

The final contracts retain the actual rounded endpoints of scalar model backups.
The TD-error input intervals are explicit admission contracts, not an assertion
that arbitrary raw learner transients already inhabit those intervals.
-/
open Acorn
open Float.Model (Format UnpackedFloat totalExponent)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentArithmetic AcornVerif.CurrentPower
namespace AcornVerif.CurrentBackupBounds

/-- Nearest-even rounding preserves an integral upper endpoint on its output grid. -/
theorem nearest_upper (mantissa denominator upper : Nat) (positive : 0 < denominator)
    (bound : mantissa ≤ upper * denominator) :
    Rounding.nearestEven mantissa denominator ≤ upper := by
  have distance := (Rounding.nearestEven_distance mantissa denominator positive).2
  by_contra failure
  have greater : upper + 1 ≤ Rounding.nearestEven mantissa denominator := by omega
  have scaled := Nat.mul_le_mul_right denominator greater
  nlinarith

/-- Comparing dyadics on a common grid preserves the exact upper endpoint. -/
theorem dyadic_upper (mantissa upper : Nat) (exponent upperExponent : Int)
    (order : exponent ≤ upperExponent)
    (bound : (mantissa : ℚ) * 2 ^ exponent ≤ (upper : ℚ) * 2 ^ upperExponent) :
    mantissa ≤ upper * 2 ^ (upperExponent - exponent).toNat := by
  have power : (2 : ℚ) ^ upperExponent =
      (2 : ℚ) ^ (upperExponent - exponent).toNat * (2 : ℚ) ^ exponent := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    congr 1
    omega
  rw [power, ← mul_assoc] at bound
  have reduced := (mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0 : ℚ) < 2) exponent)).mp bound
  exact_mod_cast reduced

/-- Exact rounding preserves a normalized positive upper endpoint when no
left normalization is needed. -/
theorem round_grid_upper (mantissa upper : Nat) (exponent upperExponent : Int)
    (positive : 0 < mantissa) (upperPositive : 0 < upper)
    (normal : ModelNormalized Format.binary32 (.finite .positive upper upperExponent upperPositive))
    (targetOrder : exponent ≤ Format.binary32.targetExponent (totalExponent mantissa exponent))
    (bound : (mantissa : ℚ) * 2 ^ exponent ≤ (upper : ℚ) * 2 ^ upperExponent) :
    unpackedValue (roundWithAccuracy Format.binary32 .positive mantissa exponent .exact) ≤
      (upper : ℚ) * 2 ^ upperExponent := by
  let target := Format.binary32.targetExponent (totalExponent mantissa exponent)
  let shift := (target - exponent).toNat
  have shifted : exponent + shift = target := by dsimp [shift]; omega
  have totals := model_totalExponent_mono mantissa upper exponent upperExponent
    positive upperPositive bound
  have upperTarget := model_normalized_target Format.binary32 .positive upper upperExponent
    upperPositive normal
  have targetBound : target ≤ upperExponent := by
    rw [← upperTarget]
    dsimp [target, Format.targetExponent]
    omega
  have inputOrder := le_trans targetOrder targetBound
  have grid := dyadic_upper mantissa upper exponent upperExponent inputOrder bound
  have gap : (upperExponent - exponent).toNat =
      (upperExponent - target).toNat + shift := by dsimp [shift]; omega
  rw [gap, Nat.pow_add, ← Nat.mul_assoc] at grid
  have rounded := nearest_upper mantissa (2 ^ shift)
    (upper * 2 ^ (upperExponent - target).toNat) (Nat.two_pow_pos _) grid
  rw [model_round_exact_value]
  simp only [signCoefficient, one_mul]
  change (Rounding.nearestEven mantissa (2 ^ shift) : ℚ) * 2 ^ (exponent + shift) ≤ _
  rw [shifted]
  have power : (2 : ℚ) ^ upperExponent =
      (2 : ℚ) ^ (upperExponent - target).toNat * (2 : ℚ) ^ target := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    congr 1
    omega
  rw [power, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos (by norm_num) _))
  exact_mod_cast rounded

/-- Full positive binary32 rounding preserves each positive normalized upper endpoint. -/
theorem round_upper (mantissa upper : Nat) (exponent upperExponent : Int)
    (upperPositive : 0 < upper)
    (normal : ModelNormalized Format.binary32 (.finite .positive upper upperExponent upperPositive))
    (bound : (mantissa : ℚ) * 2 ^ exponent ≤ (upper : ℚ) * 2 ^ upperExponent) :
    unpackedValue (round Format.binary32 .positive mantissa exponent) ≤
      (upper : ℚ) * 2 ^ upperExponent := by
  by_cases zero : mantissa = 0
  · rw [zero, model_round_zero]
    simp only [unpackedValue]
    positivity
  have positive : 0 < mantissa := by omega
  let target := Format.binary32.targetExponent (totalExponent mantissa exponent)
  let shift := (exponent - target).toNat
  have total : totalExponent (mantissa * 2 ^ shift) (exponent - shift) =
      totalExponent mantissa exponent := by
    simp only [totalExponent, model_log2_scaled_positive mantissa shift positive]
    omega
  have order : exponent - shift ≤ target := by dsimp [shift]; omega
  have padded : ((mantissa * 2 ^ shift : Nat) : ℚ) * 2 ^ (exponent - shift) ≤
      (upper : ℚ) * 2 ^ upperExponent := by
    have exactValue := dyadic_padding_exact .positive mantissa shift exponent
    simp only [signCoefficient, one_mul] at exactValue
    rwa [exactValue]
  have result := round_grid_upper (mantissa * 2 ^ shift) upper (exponent - shift)
    upperExponent (Nat.mul_pos positive (Nat.two_pow_pos _)) upperPositive normal
    (by rwa [total]) padded
  simpa only [UnpackedFloat.round, decreaseExponent, Nat.shiftLeft_eq] using result

/-- The positive rounding branch is numerically nonnegative, including underflow to zero. -/
theorem round_nonnegative (mantissa : Nat) (exponent : Int) :
    0 ≤ unpackedValue (UnpackedFloat.round Format.binary32 .positive mantissa exponent) := by
  simp only [UnpackedFloat.round, model_round_exact_value, signCoefficient, one_mul]
  positivity

open AcornVerif.CurrentFloat AcornVerif.CurrentLearnerArithmetic
open AcornVerif.CurrentModelArithmetic AcornVerif.CurrentOperations

/-- Nearest-even quotient rounding is monotone even when the two positive
integer denominators differ. The tie decision uses the shared floor parity. -/
theorem nearest_fraction_mono (left ld right rd : Nat) (ldPositive : 0 < ld)
    (rdPositive : 0 < rd) (ordered : (left : ℚ) / ld ≤ (right : ℚ) / rd) :
    Rounding.nearestEven left ld ≤ Rounding.nearestEven right rd := by
  have lf := quotient_fraction_bracket left ld ldPositive
  have rf := quotient_fraction_bracket right rd rdPositive
  have floorOrder : left / ld ≤ right / rd := by
    by_contra failure
    have separated : right / rd + 1 ≤ left / ld := by omega
    have separatedQ : ((right / rd : Nat) : ℚ) + 1 ≤ (left / ld : Nat) := by
      exact_mod_cast separated
    linarith
  by_cases different : left / ld < right / rd
  · exact le_trans (Rounding.nearestEven_bracket _ _).2
      (le_trans (by omega) (Rounding.nearestEven_bracket _ _).1)
  have equalFloor : left / ld = right / rd := by omega
  have ldQ : (0 : ℚ) < ld := by exact_mod_cast ldPositive
  have rdQ : (0 : ℚ) < rd := by exact_mod_cast rdPositive
  have leftDecomp : (left : ℚ) / ld = (left / ld : Nat) + (left % ld : Nat) / (ld : ℚ) := by
    have eq := Nat.div_add_mod' left ld
    have cast : (left : ℚ) = (left / ld : Nat) * (ld : ℚ) + (left % ld : Nat) := by
      exact_mod_cast eq.symm
    rw [cast, add_div, mul_div_cancel_right₀ _ (ne_of_gt ldQ)]
  have rightDecomp : (right : ℚ) / rd = (right / rd : Nat) + (right % rd : Nat) / (rd : ℚ) := by
    have eq := Nat.div_add_mod' right rd
    have cast : (right : ℚ) = (right / rd : Nat) * (rd : ℚ) + (right % rd : Nat) := by
      exact_mod_cast eq.symm
    rw [cast, add_div, mul_div_cancel_right₀ _ (ne_of_gt rdQ)]
  have remainderOrder : ((left % ld : Nat) : ℚ) / ld ≤ ((right % rd : Nat) : ℚ) / rd := by
    rw [leftDecomp, rightDecomp, equalFloor] at ordered
    linarith
  dsimp only [Rounding.nearestEven]
  split
  · rename_i leftUp
    split
    · omega
    · rename_i rightDown
      have leftHalf : (1 : ℚ) / 2 ≤ (left % ld : Nat) / (ld : ℚ) := by
        apply (le_div_iff₀ ldQ).mpr
        have : ld ≤ 2 * (left % ld) := by omega
        have cast : (ld : ℚ) ≤ 2 * (left % ld : Nat) := by exact_mod_cast this
        linarith
      have rightHalf : (right % rd : Nat) / (rd : ℚ) ≤ (1 : ℚ) / 2 := by
        apply (div_le_iff₀ rdQ).mpr
        have : 2 * (right % rd) ≤ rd := by omega
        have cast : 2 * (right % rd : Nat) ≤ (rd : ℚ) := by exact_mod_cast this
        linarith
      have leftTie : ld = 2 * (left % ld) := by
        have eq : (left % ld : Nat) / (ld : ℚ) = 1 / 2 := by linarith
        have scaled := (div_eq_iff (ne_of_gt ldQ)).mp eq
        have cast : (ld : ℚ) = 2 * (left % ld : Nat) := by linarith
        exact_mod_cast cast
      have rightTie : rd = 2 * (right % rd) := by
        have eq : (right % rd : Nat) / (rd : ℚ) = 1 / 2 := by linarith
        have scaled := (div_eq_iff (ne_of_gt rdQ)).mp eq
        have cast : (rd : ℚ) = 2 * (right % rd : Nat) := by linarith
        exact_mod_cast cast
      omega
  · split <;> omega

/-- Positive full rounding admits a common-grid quotient representation, with
the exact input and rounded output sharing the same target unit. -/
theorem round_grid_representation (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa) :
    let target := Format.binary32.targetExponent (totalExponent mantissa exponent)
    ∃ numerator denominator : Nat, 0 < denominator ∧
      unpackedValue (UnpackedFloat.round Format.binary32 .positive mantissa exponent) =
        (Rounding.nearestEven numerator denominator : ℚ) * 2 ^ target ∧
      (mantissa : ℚ) * 2 ^ exponent = (numerator : ℚ) / denominator * 2 ^ target := by
  dsimp only
  let target := Format.binary32.targetExponent (totalExponent mantissa exponent)
  let pad := (exponent - target).toNat
  let initial := exponent - pad
  let numerator := mantissa * 2 ^ pad
  let shift := (target - initial).toNat
  have initialOrder : initial ≤ target := by dsimp [initial, pad]; omega
  have shifted : initial + shift = target := by dsimp [shift]; omega
  have total : totalExponent numerator initial = totalExponent mantissa exponent := by
    dsimp only [numerator, initial]
    simp only [totalExponent, model_log2_scaled_positive mantissa pad positive]
    omega
  refine ⟨numerator, 2 ^ shift, Nat.two_pow_pos _, ?_, ?_⟩
  · change unpackedValue (roundWithAccuracy Format.binary32 .positive
      (mantissa <<< pad) initial .exact) = _
    rw [Nat.shiftLeft_eq]
    change unpackedValue (roundWithAccuracy Format.binary32 .positive numerator initial .exact) = _
    rw [model_round_exact_value]
    simp only [signCoefficient, one_mul, total]
    change (Rounding.nearestEven numerator (2 ^ shift) : ℚ) * 2 ^ (initial + shift) = _
    rw [shifted]
  · have padded := dyadic_padding_exact .positive mantissa pad exponent
    simp only [signCoefficient, one_mul] at padded
    change (numerator : ℚ) * 2 ^ initial = (mantissa : ℚ) * 2 ^ exponent at padded
    rw [← padded]
    have power : (2 : ℚ) ^ target = (2 : ℚ) ^ shift * 2 ^ initial := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      congr 1
      omega
    rw [power, Nat.cast_pow, Nat.cast_ofNat]
    field_simp

/-- Full positive binary32 rounding is monotone for arbitrary positive dyadic
inputs, including changes of binade and subnormal target grids. -/
theorem round_positive_mono (left right : Nat) (le re : Int)
    (lp : 0 < left) (rp : 0 < right)
    (ordered : (left : ℚ) * 2 ^ le ≤ (right : ℚ) * 2 ^ re) :
    unpackedValue (UnpackedFloat.round Format.binary32 .positive left le) ≤
      unpackedValue (UnpackedFloat.round Format.binary32 .positive right re) := by
  let lt := Format.binary32.targetExponent (totalExponent left le)
  let rt := Format.binary32.targetExponent (totalExponent right re)
  have totalOrder := model_totalExponent_mono left right le re lp rp ordered
  have targetOrder : lt ≤ rt := by dsimp [lt, rt, Format.targetExponent]; omega
  by_cases same : lt = rt
  · obtain ⟨ln, ld, ldPositive, leftRound, leftExact⟩ := round_grid_representation left le lp
    obtain ⟨rn, rd, rdPositive, rightRound, rightExact⟩ := round_grid_representation right re rp
    change unpackedValue (UnpackedFloat.round Format.binary32 .positive left le) =
      (Rounding.nearestEven ln ld : ℚ) * 2 ^ lt at leftRound
    change unpackedValue (UnpackedFloat.round Format.binary32 .positive right re) =
      (Rounding.nearestEven rn rd : ℚ) * 2 ^ rt at rightRound
    change (left : ℚ) * 2 ^ le = (ln : ℚ) / ld * 2 ^ lt at leftExact
    change (right : ℚ) * 2 ^ re = (rn : ℚ) / rd * 2 ^ rt at rightExact
    rw [leftExact, rightExact, same] at ordered
    have fractions := (mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0 : ℚ) < 2) rt)).mp ordered
    have rounded := nearest_fraction_mono ln ld rn rd ldPositive rdPositive fractions
    rw [leftRound, rightRound, same]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast rounded
  · have strict : lt < rt := by omega
    have floor : -149 < rt := by
      have : -149 ≤ lt := by
        dsimp [lt, Format.targetExponent, Format.minExponent, Format.mantissaBits]
        omega
      omega
    have rightTotal : totalExponent right re = rt + 24 := by
      dsimp [rt, Format.targetExponent, Format.minExponent, Format.mantissaBits] at *
      omega
    have leftTotal : totalExponent left le ≤ rt + 23 := by
      dsimp [lt, Format.targetExponent, Format.minExponent, Format.mantissaBits] at strict
      omega
    have endpoint : ((8388608 : Nat) : ℚ) * 2 ^ rt = (2 : ℚ) ^ (rt + 23) := by
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      norm_num
      ring
    have rightBound : ((8388608 : Nat) : ℚ) * 2 ^ rt ≤ (right : ℚ) * 2 ^ re := by
      have window := (model_positive_dyadic_window right re rp).1
      rw [rightTotal] at window
      simpa only [endpoint, show rt + 24 - 1 = rt + 23 by omega] using window
    have leftBound : (left : ℚ) * 2 ^ le ≤ ((8388608 : Nat) : ℚ) * 2 ^ rt := by
      rw [endpoint]
      exact le_trans (model_positive_dyadic_window left le lp).2.le
        (zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) leftTotal)
    have normal : ModelNormalized Format.binary32 (.finite .positive 8388608 rt (by decide)) := by
      exact ⟨by decide, by change -149 ≤ rt; omega, Or.inr (by decide)⟩
    exact le_trans (round_upper left 8388608 le rt (by decide) normal leftBound)
      (AcornVerif.CurrentRetirementRounding.round_lower right 8388608 re rt rp
        (by decide) floor rightBound)

/-- Zero signed mantissas have exactly zero numerical rounding. -/
theorem normalize_zero (exponent : Int) (sign : Sign) :
    unpackedValue (normalize Format.binary32 0 exponent sign) = 0 := rfl

/-- A strictly positive signed mantissa uses the positive nearest-rounding branch. -/
theorem normalize_positive (mantissa exponent : Int) (sign : Sign) (positive : 0 < mantissa) :
    unpackedValue (normalize Format.binary32 mantissa exponent sign) =
      unpackedValue (UnpackedFloat.round Format.binary32 .positive mantissa.toNat exponent) := by
  rw [UnpackedFloat.normalize, Int.compare_eq_gt.mpr positive]

/-- A strictly negative signed mantissa uses the negative nearest-rounding branch. -/
theorem normalize_negative (mantissa exponent : Int) (sign : Sign)
    (negative : mantissa < 0) :
    unpackedValue (normalize Format.binary32 mantissa exponent sign) =
      -unpackedValue (UnpackedFloat.round Format.binary32 .positive
        (-mantissa).toNat exponent) := by
  rw [UnpackedFloat.normalize, Int.compare_eq_lt.mpr negative]
  exact AcornVerif.CurrentRetirementRounding.round_negative_value _ _

/-- Signed normalization preserves a nonnegative input sign, including underflow. -/
theorem normalize_nonnegative (mantissa exponent : Int) (sign : Sign) (h : 0 ≤ mantissa) :
    0 ≤ unpackedValue (normalize Format.binary32 mantissa exponent sign) := by
  rcases eq_or_lt_of_le h with zero | positive
  · rw [← zero, normalize_zero]
  · rw [normalize_positive _ _ _ positive]
    exact round_nonnegative _ _

/-- Signed normalization preserves a nonpositive input sign, including underflow. -/
theorem normalize_nonpositive (mantissa exponent : Int) (sign : Sign) (h : mantissa ≤ 0) :
    unpackedValue (normalize Format.binary32 mantissa exponent sign) ≤ 0 := by
  rcases lt_or_eq_of_le h with negative | zero
  · rw [normalize_negative _ _ _ negative]
    exact neg_nonpos.mpr (round_nonnegative _ _)
  · rw [zero, normalize_zero]

/-- Signed full binary32 normalization is monotone across all dyadic inputs,
including cancellation, either zero sign, subnormals and binade changes. -/
theorem normalize_mono (left right le re : Int) (ls rs : Sign)
    (ordered : (left : ℚ) * 2 ^ le ≤ (right : ℚ) * 2 ^ re) :
    unpackedValue (normalize Format.binary32 left le ls) ≤
      unpackedValue (normalize Format.binary32 right re rs) := by
  have lp : (0 : ℚ) < 2 ^ le := by positivity
  have rp : (0 : ℚ) < 2 ^ re := by positivity
  by_cases leftNonpositive : left ≤ 0
  · by_cases rightNonnegative : 0 ≤ right
    · exact le_trans (normalize_nonpositive _ _ _ leftNonpositive)
        (normalize_nonnegative _ _ _ rightNonnegative)
    have rightNegative : right < 0 := by omega
    have leftNegative : left < 0 := by
      have rightQ : (right : ℚ) < 0 := by exact_mod_cast rightNegative
      have exactNegative : (right : ℚ) * 2 ^ re < 0 := mul_neg_of_neg_of_pos rightQ rp
      have : (left : ℚ) < 0 := by
        by_contra failure
        have nonnegative := mul_nonneg (le_of_not_gt failure) lp.le
        linarith
      exact_mod_cast this
    rw [normalize_negative _ _ _ leftNegative, normalize_negative _ _ _ rightNegative]
    apply neg_le_neg
    have leftCast : ((-left).toNat : ℚ) = -(left : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -left)
    have rightCast : ((-right).toNat : ℚ) = -(right : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -right)
    apply round_positive_mono _ _ _ _ (by omega) (by omega)
    rw [leftCast, rightCast]
    linarith
  · have leftPositive : 0 < left := by omega
    have rightPositive : 0 < right := by
      have leftQ : (0 : ℚ) < left := by exact_mod_cast leftPositive
      have exactPositive : (0 : ℚ) < (left : ℚ) * 2 ^ le := mul_pos leftQ lp
      have : (0 : ℚ) < right :=
        (mul_pos_iff_of_pos_right rp).mp (lt_of_lt_of_le exactPositive ordered)
      exact_mod_cast this
    rw [normalize_positive _ _ _ leftPositive, normalize_positive _ _ _ rightPositive]
    have leftCast : (left.toNat : ℚ) = left := by
      exact_mod_cast Int.toNat_of_nonneg leftPositive.le
    have rightCast : (right.toNat : ℚ) = right := by
      exact_mod_cast Int.toNat_of_nonneg rightPositive.le
    apply round_positive_mono _ _ _ _ (by omega) (by omega)
    rwa [leftCast, rightCast]

/-- Signed normalization agrees numerically with the explicit sign constructor. -/
theorem normalize_sign_value (sign : Sign) (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa) :
    unpackedValue (normalize Format.binary32 (sign.apply mantissa) exponent .positive) =
      unpackedValue (UnpackedFloat.round Format.binary32 sign mantissa exponent) := by
  cases sign
  · rw [normalize_negative _ _ _ (by change -(mantissa : Int) < 0; omega)]
    change -unpackedValue (UnpackedFloat.round Format.binary32 .positive
      (-(-(mantissa : Int))).toNat exponent) = _
    rw [neg_neg, Int.toNat_natCast]
    exact (AcornVerif.CurrentRetirementRounding.round_negative_value _ _).symm
  · rw [normalize_positive _ _ _ (by change (0 : Int) < mantissa; omega)]
    rfl

/-- Already normalized finite components round to their exact numerical value. -/
theorem round_normalized_value (sign : Sign) (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa)
    (normal : ModelNormalized Format.binary32 (.finite sign mantissa exponent positive)) :
    unpackedValue (UnpackedFloat.round Format.binary32 sign mantissa exponent) =
      signCoefficient sign * mantissa * (2 : ℚ) ^ exponent := by
  have target := model_normalized_target Format.binary32 sign mantissa exponent positive normal
  simp only [UnpackedFloat.round, decreaseExponent, target, sub_self, Int.toNat_zero,
    Nat.shiftLeft_zero]
  simp [model_round_exact_value, target, Rounding.nearestEven]
  norm_num [Nat.mod_one]

/-- A dyadic source and its actual signed binary32 nearest-rounding result. -/
def Rounded (source result : ℚ) : Prop :=
  ∃ mantissa exponent : Int, source = (mantissa : ℚ) * 2 ^ exponent ∧
    result = unpackedValue (normalize Format.binary32 mantissa exponent .positive)

/-- Ordered exact dyadic sources have ordered rounded results. -/
theorem Rounded.mono {left right lresult rresult : ℚ}
    (l : Rounded left lresult) (r : Rounded right rresult) (ordered : left ≤ right) :
    lresult ≤ rresult := by
  obtain ⟨lm, le, lx, ly⟩ := l
  obtain ⟨rm, re, rx, ry⟩ := r
  rw [ly, ry]
  apply normalize_mono
  rwa [← lx, ← rx]

/-- Every canonical finite model word is exactly its own rounded dyadic source. -/
theorem rounded_normalized (value : UnpackedFloat)
    (normal : ModelNormalized Format.binary32 value) :
    Rounded (unpackedValue value) (unpackedValue value) := by
  cases value with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign => exact ⟨0, 0, by norm_num [unpackedValue], rfl⟩
  | finite sign mantissa exponent positive =>
    refine ⟨sign.apply mantissa, exponent, ?_, ?_⟩
    · simp only [unpackedValue, model_sign_apply_value]
    · rw [normalize_sign_value _ _ _ positive, round_normalized_value _ _ _ positive normal]
      rfl

/-- Every actual model addition is the nearest rounding of its exact dyadic sum. -/
theorem rounded_add (left right : UnpackedFloat)
    (leftNormal : ModelNormalized Format.binary32 left)
    (rightNormal : ModelNormalized Format.binary32 right) :
    Rounded (unpackedValue left + unpackedValue right)
      (unpackedValue (UnpackedFloat.add Format.binary32 left right)) := by
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right with
    | notANumber => contradiction
    | infinity s => contradiction
    | zero s =>
      cases sign <;> cases s <;> exact ⟨0, 0, by norm_num [unpackedValue], rfl⟩
    | finite s m e hp =>
      simpa [UnpackedFloat.add, unpackedValue] using
        (rounded_normalized (.finite s m e hp) rightNormal)
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero rightSign =>
      simpa [UnpackedFloat.add, unpackedValue] using
        (rounded_normalized (.finite leftSign lm le lp) leftNormal)
    | finite rightSign rm re rp =>
      let target := min le re
      let lmantissa := (decreaseExponent lm le target).1
      let rmantissa := (decreaseExponent rm re target).1
      let sum := leftSign.apply lmantissa + rightSign.apply rmantissa
      have hl := model_decrease_dyadic_value leftSign lm le target (Int.min_le_left _ _)
      have hr := model_decrease_dyadic_value rightSign rm re target (Int.min_le_right _ _)
      refine ⟨sum, target, ?_, rfl⟩
      change _ = ((leftSign.apply lmantissa + rightSign.apply rmantissa : Int) : ℚ) *
        (2 : ℚ) ^ target
      rw [Int.cast_add, add_mul, hl, hr]
      rfl

/-- Every actual model multiplication is the nearest rounding of its exact dyadic product. -/
theorem rounded_mul (left right : UnpackedFloat)
    (leftNormal : ModelNormalized Format.binary32 left)
    (rightNormal : ModelNormalized Format.binary32 right) :
    Rounded (unpackedValue left * unpackedValue right)
      (unpackedValue (UnpackedFloat.mul Format.binary32 left right)) := by
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right <;> first | contradiction |
      exact ⟨0, 0, by simp [unpackedValue], rfl⟩
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero rightSign => exact ⟨0, 0, by simp [unpackedValue], rfl⟩
    | finite rightSign rm re rp =>
      have ready := model_product_exponent_ready Format.binary32 lm rm le re leftSign
        rightSign lp rp leftNormal rightNormal
      refine ⟨(leftSign * rightSign).apply ((lm * rm : Nat) : Int), le + re, ?_, ?_⟩
      · rw [model_sign_apply_value, model_sign_product_value,
          zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        simp only [unpackedValue, Nat.cast_mul]
        ring
      · rw [normalize_sign_value _ _ _ (Nat.mul_pos lp rp)]
        simp only [UnpackedFloat.mul]
        rw [← model_round_without_padding Format.binary32 _ _ _ ready]

/-- Signed normalization commutes numerically with source negation. -/
theorem normalize_neg_value (mantissa exponent : Int) :
    unpackedValue (normalize Format.binary32 (-mantissa) exponent .positive) =
      -unpackedValue (normalize Format.binary32 mantissa exponent .positive) := by
  rcases lt_trichotomy mantissa 0 with negative | zero | positive
  · rw [normalize_positive _ _ _ (by omega), normalize_negative _ _ _ negative, neg_neg]
  · subst mantissa
    rw [neg_zero, normalize_zero, neg_zero]
  · rw [normalize_negative _ _ _ (by omega), normalize_positive _ _ _ positive, neg_neg]

/-- Negating an exact dyadic source negates its rounded numerical result. -/
theorem Rounded.neg {source result : ℚ} (rounded : Rounded source result) :
    Rounded (-source) (-result) := by
  obtain ⟨mantissa, exponent, exactValue, roundedValue⟩ := rounded
  refine ⟨-mantissa, exponent, ?_, ?_⟩
  · rw [exactValue, Int.cast_neg, neg_mul]
  · rw [normalize_neg_value, roundedValue]

/-- The actual finite binary32 word is exactly its own rounded dyadic source. -/
theorem binary32_rounded_exact (value : Binary32) (finite : value.Finite) :
    Rounded (numerical32 value) (numerical32 value) :=
  rounded_normalized _ (model_unpack_format Format.binary32 (by decide) value.bits.toBitVec
    ((model_decoded32_finite value).mpr finite)).1

/-- Actual binary32 addition is finite and follows signed nearest rounding
throughout the complete scalar-backup magnitude domain. -/
theorem binary32_rounded_add (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left + numerical32 right| ≤ 8589934592) :
    (left.add right).Finite ∧
      Rounded (numerical32 left + numerical32 right) (numerical32 (left.add right)) := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_add_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 33 bound
  have error : |unpackedValue (UnpackedFloat.add Format.binary32
      (decoded32 left) (decoded32 right)) -
      (numerical32 left + numerical32 right)| ≤ 512 := by
    apply le_trans operation.2
    norm_num [Format.mantissaBits, Format.minExponent]
  have fits : ModelFits Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right)) := by
    apply model_fits_of_value_bound Format.binary32 _
      (model_normalized_finite _ _ operation.1) 34 (by decide)
    have triangle := abs_add_le
      (unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right)) -
        (numerical32 left + numerical32 right)) (numerical32 left + numerical32 right)
    rw [sub_add_cancel] at triangle
    norm_num
    linarith
  have decoded := model_add32_decoded left right hl hr operation.1 fits
  constructor
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using rounded_add (decoded32 left) (decoded32 right) ln rn

/-- Actual small binary32 multiplication is finite and follows signed nearest rounding. -/
theorem binary32_rounded_mul (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left * numerical32 right| ≤ 512) :
    (left.mul right).Finite ∧
      Rounded (numerical32 left * numerical32 right) (numerical32 (left.mul right)) := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_mul_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 9 bound
  have error : |unpackedValue (UnpackedFloat.mul Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left * numerical32 right| ≤ 1 := by
    apply le_trans operation.2
    norm_num [Format.mantissaBits, Format.minExponent]
  have decoded := mul32_decoded left right hl hr operation.1
    (small_fits _ _ operation.1 bound error)
  refine ⟨(small_mul left right hl hr bound).1, ?_⟩
  simpa only [numerical32, decoded] using rounded_mul (decoded32 left) (decoded32 right) ln rn

/-- Actual small binary32 subtraction is finite and follows signed nearest rounding. -/
theorem binary32_rounded_sub (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left - numerical32 right| ≤ 512) :
    (left.sub right).Finite ∧
      Rounded (numerical32 left - numerical32 right) (numerical32 (left.sub right)) := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_sub_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 9 bound
  have error : |unpackedValue (UnpackedFloat.sub Format.binary32
      (decoded32 left) (decoded32 right)) - (numerical32 left - numerical32 right)| ≤ 1 := by
    apply le_trans operation.2
    norm_num [Format.mantissaBits, Format.minExponent]
  have decoded : decoded32 (left.sub right) =
      UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right) := by
    change unpack Format.binary32 (pack Format.binary32
      (UnpackedFloat.sub Format.binary32 (Float32.Model.ofBits left.bits).unpack
        (Float32.Model.ofBits right.bits).unpack)) = _
    rw [model_ofBits32_decoded left hl, model_ofBits32_decoded right hr]
    exact model_unpack_pack_normalized _ _ operation.1 (small_fits _ _ operation.1 bound error)
  refine ⟨(small_sub left right hl hr bound).1, ?_⟩
  simpa only [numerical32, decoded, model_sub_add_neg, model_neg_value, ← sub_eq_add_neg] using
    rounded_add (decoded32 left) (UnpackedFloat.neg (decoded32 right)) ln
      (model_neg_normalized _ _ rn)

/-- The executing centered model reward has exactly the capped magnitude bound.
Wan, Naik and Sutton, *Average-Reward Learning and Planning with Options*,
NeurIPS 34 (2021), section 5 equations (18)–(23).
This concerns the rounded reward-minus-gain-times-duration prefix, before continuation. -/
theorem centered_reward_bound (reward gain duration : Binary32)
    (rf : reward.Finite) (gf : gain.Finite) (df : duration.Finite)
    (rb : 0 ≤ numerical32 reward ∧ numerical32 reward ≤ 128)
    (gb : 0 ≤ numerical32 gain ∧ numerical32 gain ≤ 1)
    (db : 1 ≤ numerical32 duration ∧ numerical32 duration ≤ 128) :
    (reward.sub (gain.mul duration)).Finite ∧
      |numerical32 (reward.sub (gain.mul duration))| ≤ 128 := by
  have bound : |numerical32 gain * numerical32 duration| ≤ 128 := by
    rw [abs_of_nonneg (mul_nonneg gb.1 (by linarith [db.1]))]
    nlinarith [gb.2, db.2]
  have capValue : numerical32 (Binary32.mk 0x43000000) = 128 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-16 : Int) = 128
    norm_num
  have cap := binary32_rounded_exact (Binary32.mk 0x43000000) (by decide)
  rw [capValue] at cap
  have zero : Rounded 0 0 := ⟨0, 0, by norm_num, rfl⟩
  have product := binary32_rounded_mul gain duration gf df (by linarith)
  have low := Rounded.mono zero product.2 (mul_nonneg gb.1 (by linarith [db.1]))
  have high := Rounded.mono product.2 cap (le_trans (le_abs_self _) bound)
  have difference := binary32_rounded_sub reward (gain.mul duration) rf product.1
    (abs_le.mpr ⟨by linarith [rb.1], by linarith [rb.2]⟩)
  exact ⟨difference.1, abs_le.mpr
    ⟨Rounded.mono cap.neg difference.2 (by linarith [rb.1]),
      Rounded.mono difference.2 cap (by linarith [rb.2])⟩⟩

/-- The complete raw differential backup obeys the actual rounded aggregate-plus-cap
bound for every finite aggregate endpoint through 2^32. This includes every capacity
endpoint and all nearest-even ties in its addition of 128.
Wan, Naik and Sutton, *Average-Reward Learning and Planning with Options*,
NeurIPS 34 (2021), section 5 equations (18)–(23). -/
theorem differential_backup_bound (reward gain duration continuation bound : Binary32)
    (rf : reward.Finite) (gf : gain.Finite) (df : duration.Finite)
    (cf : continuation.Finite) (bf : bound.Finite)
    (rb : 0 ≤ numerical32 reward ∧ numerical32 reward ≤ 128)
    (gb : 0 ≤ numerical32 gain ∧ numerical32 gain ≤ 1)
    (db : 1 ≤ numerical32 duration ∧ numerical32 duration ≤ 128)
    (bb : 0 ≤ numerical32 bound ∧ numerical32 bound ≤ 4294967296)
    (cb : |numerical32 continuation| ≤ numerical32 bound) :
    let target := (reward.sub (gain.mul duration)).add continuation
    let targetBound := bound.add (Binary32.mk 0x43000000)
    target.Finite ∧ targetBound.Finite ∧ |numerical32 target| ≤ numerical32 targetBound := by
  have centered := centered_reward_bound reward gain duration rf gf df rb gb db
  have cap : numerical32 (Binary32.mk 0x43000000) = 128 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-16 : Int) = 128
    norm_num
  have exactBound : |numerical32 (reward.sub (gain.mul duration)) +
      numerical32 continuation| ≤ numerical32 bound + 128 :=
    le_trans (abs_add_le _ _) (by linarith [centered.2])
  have target := binary32_rounded_add (reward.sub (gain.mul duration)) continuation
    centered.1 cf (by linarith [bb.2])
  have endpoint := binary32_rounded_add bound (Binary32.mk 0x43000000) bf (by decide)
    (by rw [cap, abs_of_nonneg (by linarith [bb.1])]; linarith [bb.2])
  have lower := Rounded.mono endpoint.2.neg target.2
    (by rw [cap]; exact (abs_le.mp exactBound).1)
  have upper := Rounded.mono target.2 endpoint.2
    (by rw [cap]; exact (abs_le.mp exactBound).2)
  exact ⟨target.1, endpoint.1, abs_le.mpr ⟨lower, upper⟩⟩

/-- The bound applies directly to the executing differential model target, with
producer-owned reward, gain and duration ranges and a raw continuation assumption. -/
theorem model_prediction_differential_bound
    (prediction : Acorn.Features.ModelPrediction .differential) (gain : RewardRate)
    (bound : Binary32) (bf : bound.Finite)
    (bb : 0 ≤ numerical32 bound ∧ numerical32 bound ≤ 4294967296)
    (cf : prediction.continuation.Finite)
    (cb : |numerical32 prediction.continuation| ≤ numerical32 bound) :
    (prediction.target gain).Finite ∧ (bound.add (Binary32.mk 0x43000000)).Finite ∧
      |numerical32 (prediction.target gain)| ≤
        numerical32 (bound.add (Binary32.mk 0x43000000)) := by
  have rb := AcornVerif.CurrentModels.interval_numeric _ prediction.reward
  have db := AcornVerif.CurrentModels.interval_numeric _ prediction.duration
  have gb := AcornVerif.CurrentModels.interval_numeric _ gain
  have zero : numerical32 Binary32.zero = 0 := by decide
  have one : numerical32 Binary32.one = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  have cap : numerical32
      (Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64) = 128 := by
    rw [show Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64 =
      Binary32.mk 0x43000000 by decide]
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-16 : Int) = 128
    norm_num
  simp only [Acorn.Features.Criterion.modelRewardRange, zero, cap] at rb
  simp only [Acorn.Features.modelDurationRange, one, cap] at db
  change numerical32 (Binary32.mk 0x3f800000) = 1 at one
  simp only [rewardRange, zero, one] at gb
  exact differential_backup_bound prediction.reward.value gain.value prediction.duration.value
    prediction.continuation bound prediction.reward.legal.1 gain.legal.1 prediction.duration.legal.1
    cf bf rb gb db bb cb

/-- Numerical zero is exactly its own signed nearest rounding. -/
theorem rounded_zero : Rounded 0 0 := ⟨0, 0, by norm_num, rfl⟩

/-- Discount multiplication maps every admitted prediction to the interval
between zero and the actual rounded gamma-times-horizon endpoint. -/
theorem discounted_product_interval (gamma prediction horizon : Binary32)
    (gf : gamma.Finite) (pf : prediction.Finite) (hf : horizon.Finite)
    (gb : 0 ≤ numerical32 gamma ∧ numerical32 gamma ≤ 1)
    (pb : 0 ≤ numerical32 prediction ∧ numerical32 prediction ≤ numerical32 horizon)
    (hb : 0 ≤ numerical32 horizon ∧ numerical32 horizon ≤ 128) :
    (gamma.mul prediction).Finite ∧ (gamma.mul horizon).Finite ∧
      0 ≤ numerical32 (gamma.mul prediction) ∧
      numerical32 (gamma.mul prediction) ≤ numerical32 (gamma.mul horizon) ∧
      0 ≤ numerical32 (gamma.mul horizon) ∧
      numerical32 (gamma.mul horizon) ≤ numerical32 horizon := by
  have predictionBound : |numerical32 gamma * numerical32 prediction| ≤ 512 := by
    rw [abs_of_nonneg (mul_nonneg gb.1 pb.1)]
    nlinarith
  have horizonBound : |numerical32 gamma * numerical32 horizon| ≤ 512 := by
    rw [abs_of_nonneg (mul_nonneg gb.1 hb.1)]
    nlinarith
  have predictionRound := binary32_rounded_mul gamma prediction gf pf predictionBound
  have horizonRound := binary32_rounded_mul gamma horizon gf hf horizonBound
  refine ⟨predictionRound.1, horizonRound.1,
    Rounded.mono rounded_zero predictionRound.2 (mul_nonneg gb.1 pb.1),
    Rounded.mono predictionRound.2 horizonRound.2 (mul_le_mul_of_nonneg_left pb.2 gb.1),
    Rounded.mono rounded_zero horizonRound.2 (mul_nonneg gb.1 hb.1), ?_⟩
  exact Rounded.mono horizonRound.2 (binary32_rounded_exact horizon hf) (by nlinarith)

/-- Subtraction of bounded nonnegative predictions retains both asymmetric
representable endpoints through actual binary32 rounding. -/
theorem prediction_difference_interval (target old horizon upper : Binary32)
    (tf : target.Finite) (of : old.Finite) (hf : horizon.Finite) (uf : upper.Finite)
    (tb : 0 ≤ numerical32 target ∧ numerical32 target ≤ numerical32 upper)
    (ob : 0 ≤ numerical32 old ∧ numerical32 old ≤ numerical32 horizon)
    (hb : numerical32 horizon ≤ 256) (ub : numerical32 upper ≤ 256) :
    (target.sub old).Finite ∧
      -numerical32 horizon ≤ numerical32 (target.sub old) ∧
      numerical32 (target.sub old) ≤ numerical32 upper := by
  have bound : |numerical32 target - numerical32 old| ≤ 512 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have operation := binary32_rounded_sub target old tf of bound
  exact ⟨operation.1,
    Rounded.mono (binary32_rounded_exact horizon hf).neg operation.2 (by linarith [tb.1, ob.2]),
    Rounded.mono operation.2 (binary32_rounded_exact upper uf) (by linarith [tb.2, ob.1])⟩

/-- Every supported discount's actual generated gamma and computed horizon
lie in the common finite arithmetic domain. The closed enum owns this exhaustion. -/
theorem discount_arithmetic_domain (discount : Discount) :
    discount.gamma.Finite ∧ discount.horizon.Finite ∧
      (0 ≤ numerical32 discount.gamma ∧ numerical32 discount.gamma ≤ 1) ∧
      (1 ≤ numerical32 discount.horizon ∧ numerical32 discount.horizon ≤ 128) := by
  have gf : discount.gamma.Finite := by cases discount <;> decide
  have hf : discount.horizon.Finite := discount.predictionRange.upperFinite
  have zero : numerical32 Binary32.zero = 0 := by decide
  have one : numerical32 Binary32.one = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  have cap : numerical32 (Binary32.mk 0x43000000) = 128 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-16 : Int) = 128
    norm_num
  have gk : Binary32.zero.key ≤ discount.gamma.key ∧
      discount.gamma.key ≤ Binary32.one.key := by cases discount <;> decide
  have hk : Binary32.one.key ≤ discount.horizon.key ∧
      discount.horizon.key ≤ (Binary32.mk 0x43000000).key := by cases discount <;> decide
  have gl := (AcornVerif.CurrentOrder.numerical32_order _ _ (by decide) gf).mpr gk.1
  have gu := (AcornVerif.CurrentOrder.numerical32_order _ _ gf (by decide)).mpr gk.2
  have hl := (AcornVerif.CurrentOrder.numerical32_order _ _ (by decide) hf).mpr hk.1
  have hu := (AcornVerif.CurrentOrder.numerical32_order _ _ hf (by decide)).mpr hk.2
  rw [zero] at gl
  rw [one] at gu hl
  rw [cap] at hu
  exact ⟨gf, hf, ⟨gl, gu⟩, ⟨hl, hu⟩⟩

/-- Reward-plus-continuation addition preserves its actual rounded endpoint. -/
theorem reward_sum_interval (reward prediction upper : Binary32)
    (rf : reward.Finite) (pf : prediction.Finite) (uf : upper.Finite)
    (rb : 0 ≤ numerical32 reward ∧ numerical32 reward ≤ 1)
    (pb : 0 ≤ numerical32 prediction ∧ numerical32 prediction ≤ numerical32 upper)
    (ub : 0 ≤ numerical32 upper ∧ numerical32 upper ≤ 128) :
    (reward.add prediction).Finite ∧ (Binary32.one.add upper).Finite ∧
      0 ≤ numerical32 (reward.add prediction) ∧
      numerical32 (reward.add prediction) ≤ numerical32 (Binary32.one.add upper) ∧
      1 ≤ numerical32 (Binary32.one.add upper) ∧
      numerical32 (Binary32.one.add upper) ≤ 256 := by
  have one : numerical32 Binary32.one = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  have cap : numerical32 (Binary32.mk 0x43800000) = 256 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-15 : Int) = 256
    norm_num
  have sum := binary32_rounded_add reward prediction rf pf
    (by rw [abs_of_nonneg (by linarith [rb.1, pb.1])]; linarith [rb.2, pb.2, ub.2])
  have endpoint := binary32_rounded_add Binary32.one upper (by decide) uf
    (by rw [one, abs_of_nonneg (by linarith [ub.1])]; linarith [ub.2])
  have upperBound := Rounded.mono endpoint.2
    (binary32_rounded_exact (Binary32.mk 0x43800000) (by decide)) (by rw [one, cap]; linarith)
  have lowerBound := Rounded.mono (binary32_rounded_exact Binary32.one (by decide)) endpoint.2
    (by linarith [ub.1])
  rw [one] at lowerBound
  rw [cap] at upperBound
  exact ⟨sum.1, endpoint.1, Rounded.mono rounded_zero sum.2 (by linarith [rb.1, pb.1]),
    Rounded.mono sum.2 endpoint.2 (by rw [one]; linarith [rb.2, pb.2]),
    lowerBound, upperBound⟩

/-- Typed prediction admission denotes every finite nonnegative word below
its actual machine horizon. -/
theorem prediction_numeric_bounds (discount : Discount) (prediction : Prediction discount) :
    0 ≤ numerical32 prediction.value ∧
      numerical32 prediction.value ≤ numerical32 discount.horizon := by
  have result := AcornVerif.CurrentModels.interval_numeric _ prediction
  have zero : numerical32 Binary32.zero = 0 := by decide
  simpa only [Discount.predictionRange, zero] using result

/-- Termination-conditional option TD errors obey the original asymmetric
machine bounds over every supported discount and every admitted word.
Sutton, Machado et al., *Reward-Respecting Subtasks for Model-Based Reinforcement
Learning*, Artificial Intelligence 324 (2023), 104001, section 4 equations (15)–(17).
These are arithmetic input contracts; raw learner transients do not inherit
prediction admission merely because this conditional formula has a bound. -/
theorem option_td_error_termination_conditional (discount : Discount) (terminal : Bool)
    (reward : RewardRate) (oldR oldC nextR nextC : Prediction discount) (estimate : Binary32) :
    let deltaR := if terminal then reward.value.sub oldR.value
      else (reward.value.add (discount.gamma.mul nextR.value)).sub oldR.value
    let deltaC := (discount.gamma.mul
      (if terminal then (Prediction.project discount estimate).value else nextC.value)).sub
        oldC.value
    deltaR.Finite ∧ deltaC.Finite ∧
      -numerical32 discount.horizon ≤ numerical32 deltaR ∧
      numerical32 deltaR ≤ numerical32 (Binary32.one.add (discount.gamma.mul discount.horizon)) ∧
      -numerical32 discount.horizon ≤ numerical32 deltaC ∧
      numerical32 deltaC ≤ numerical32 (discount.gamma.mul discount.horizon) := by
  have domain := discount_arithmetic_domain discount
  have horizon : 0 ≤ numerical32 discount.horizon ∧ numerical32 discount.horizon ≤ 128 :=
    ⟨by linarith [domain.2.2.2.1], domain.2.2.2.2⟩
  have rewardBounds := AcornVerif.CurrentModels.interval_numeric _ reward
  have zero : numerical32 Binary32.zero = 0 := by decide
  have one : numerical32 (Binary32.mk 0x3f800000) = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  simp only [rewardRange, zero, one] at rewardBounds
  have productR := discounted_product_interval discount.gamma nextR.value discount.horizon
    domain.1 nextR.legal.1 domain.2.1 domain.2.2.1
    (prediction_numeric_bounds discount nextR) horizon
  have sum := reward_sum_interval reward.value (discount.gamma.mul nextR.value)
    (discount.gamma.mul discount.horizon) reward.legal.1 productR.1 productR.2.1 rewardBounds
    ⟨productR.2.2.1, productR.2.2.2.1⟩
    ⟨productR.2.2.2.2.1, le_trans productR.2.2.2.2.2 horizon.2⟩
  have continuingR := prediction_difference_interval
    (reward.value.add (discount.gamma.mul nextR.value)) oldR.value discount.horizon
    (Binary32.one.add (discount.gamma.mul discount.horizon)) sum.1 oldR.legal.1
    domain.2.1 sum.2.1 ⟨sum.2.2.1, sum.2.2.2.1⟩
    (prediction_numeric_bounds discount oldR) (by linarith [horizon.2]) sum.2.2.2.2.2
  have terminalR := prediction_difference_interval reward.value oldR.value discount.horizon
    (Binary32.one.add (discount.gamma.mul discount.horizon)) reward.legal.1 oldR.legal.1
    domain.2.1 sum.2.1 ⟨rewardBounds.1, by linarith [rewardBounds.2, sum.2.2.2.2.1]⟩
    (prediction_numeric_bounds discount oldR) (by linarith [horizon.2]) sum.2.2.2.2.2
  let chosen : Prediction discount :=
    if terminal then Prediction.project discount estimate else nextC
  have productC := discounted_product_interval discount.gamma chosen.value discount.horizon
    domain.1 chosen.legal.1 domain.2.1 domain.2.2.1
    (prediction_numeric_bounds discount chosen) horizon
  have continuation := prediction_difference_interval (discount.gamma.mul chosen.value) oldC.value
    discount.horizon (discount.gamma.mul discount.horizon) productC.1 oldC.legal.1
    domain.2.1 productC.2.1 ⟨productC.2.2.1, productC.2.2.2.1⟩
    (prediction_numeric_bounds discount oldC) (by linarith [horizon.2])
    (by linarith [productC.2.2.2.2.2, horizon.2])
  cases terminal
  · exact ⟨continuingR.1, continuation.1, continuingR.2.1, continuingR.2.2,
      continuation.2.1, continuation.2.2⟩
  · exact ⟨terminalR.1, continuation.1, terminalR.2.1, terminalR.2.2,
      continuation.2.1, continuation.2.2⟩

end AcornVerif.CurrentBackupBounds
