/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentIntervals
import Acorn.Lifetime

/-!
# Machine arithmetic for lifetime totals

The full unsigned count domain exceeds exact binary64 integer conversion.
Bounds below use the actual pinned standard rounding and packing owners; no
integer-exact conversion or unrounded-real addition is assumed. Native primitive
and compiler correspondence retain the declared machine trust boundary.
-/
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder

namespace AcornVerif.CurrentLifetimeArithmetic

/-- Positive rounding preserves the sign for all significands and exponent shifts. -/
theorem round_nonnegative (spec : Format) (mantissa : Nat) (exponent : Int) :
    0 ≤ unpackedValue (round spec .positive mantissa exponent) := by
  simp only [round, roundWithAccuracy]
  split
  · exact le_rfl
  · simp only [unpackedValue, signCoefficient, one_mul]
    positivity

/-- A deliberately loose relative error suffices to separate the closed lifetime caps. -/
theorem round_relative_half (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa)
    (floor : spec.minExponent ≤ totalExponent mantissa exponent - 1) :
    |unpackedValue (round spec sign mantissa exponent) -
        signCoefficient sign * mantissa * (2 : ℚ) ^ exponent| ≤
      (mantissa : ℚ) * (2 : ℚ) ^ exponent / 2 := by
  have target : spec.targetExponent (totalExponent mantissa exponent) ≤
      totalExponent mantissa exponent - 1 := by
    simp only [Format.targetExponent, Format.mantissaBits]
    omega
  calc
    _ ≤ (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) / 2 :=
      model_round_error spec sign mantissa exponent
    _ ≤ (2 : ℚ) ^ (totalExponent mantissa exponent-1) / 2 :=
      div_le_div_of_nonneg_right (zpow_le_zpow_right₀ (by norm_num) target) (by norm_num)
    _ ≤ (mantissa : ℚ) * (2 : ℚ) ^ exponent / 2 :=
      div_le_div_of_nonneg_right
        (model_positive_dyadic_window mantissa exponent positive).1 (by norm_num)

/-- At magnitudes at least one half, the binary64 subnormal floor cannot dominate relative error. -/
theorem half_floor (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (lower : (1 : ℚ) / 2 ≤ (mantissa : ℚ) * (2 : ℚ) ^ exponent) :
    Format.binary64.minExponent ≤ totalExponent mantissa exponent - 1 := by
  have high := (model_positive_dyadic_window mantissa exponent positive).2
  have total : 0 ≤ totalExponent mantissa exponent := by
    by_contra neg
    have bound : totalExponent mantissa exponent ≤ -1 := by omega
    have power := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) bound
    norm_num at power
    linarith
  change -1074 ≤ totalExponent mantissa exponent - 1
  omega

/-- The wide lifetime arithmetic envelope remains far below binary64 overflow. -/
theorem wide_fits (value : UnpackedFloat) (exactValue : ℚ)
    (normal : ModelNormalized Format.binary64 value)
    (bound : |exactValue| ≤ (2 : ℚ) ^ (82 : ℤ))
    (error : |unpackedValue value - exactValue| ≤ (2 : ℚ) ^ (29 : ℤ)) :
    ModelFits Format.binary64 value := by
  apply model_fits_of_value_bound Format.binary64 value
    (model_normalized_finite _ _ normal) 83 (by decide)
  calc
    |unpackedValue value| = |(unpackedValue value-exactValue) + exactValue| := by
        congr 1
        ring
    _ ≤ |unpackedValue value-exactValue| + |exactValue| := abs_add_le _ _
    _ ≤ (2 : ℚ) ^ (29 : ℤ) + (2 : ℚ) ^ (82 : ℤ) := add_le_add error bound
    _ ≤ (2 : ℚ) ^ (83 : ℤ) := by norm_num

/-- Full-domain unsigned conversion is finite with a conservative magnitude envelope. -/
theorem count_model (word : UInt64) :
    (Binary64.ofUInt64 word).Finite ∧
      |numerical64 (Binary64.ofUInt64 word)| ≤ (2 : ℚ) ^ (65 : ℤ) ∧
      decoded64 (Binary64.ofUInt64 word) = ofUInt64 Format.binary64 word := by
  have bound : |((word.toNat : Int) : ℚ) * (2 : ℚ) ^ (0 : Int)| ≤ (2 : ℚ) ^ (64 : Int) := by
    simp only [Int.cast_natCast, zpow_zero, mul_one,
      abs_of_nonneg (Nat.cast_nonneg word.toNat : (0 : ℚ) ≤ word.toNat)]
    norm_num
    exact_mod_cast Nat.le_of_lt word.toNat_lt
  have result := model_signed_round_value Format.binary64 (word.toNat : Int) 0 .positive 64 bound
  have error : |unpackedValue (ofUInt64 Format.binary64 word) - (word.toNat : ℚ)| ≤ 2048 := by
    convert result.2 using 1 <;>
      norm_num [ofUInt64, ofNat, ofInt, Format.mantissaBits, Format.minExponent]
  have magnitude : |unpackedValue (ofUInt64 Format.binary64 word)| ≤ (2 : ℚ) ^ (65 : Int) := by
    have natBound : (word.toNat : ℚ) ≤ (2 : ℚ) ^ (64 : Int) := by
      simpa using bound
    calc
      _ = |(unpackedValue (ofUInt64 Format.binary64 word) - (word.toNat : ℚ)) +
          (word.toNat : ℚ)| := by
        congr 1
        ring
      _ ≤ |unpackedValue (ofUInt64 Format.binary64 word) - (word.toNat : ℚ)| + |(word.toNat : ℚ)| :=
        abs_add_le _ _
      _ ≤ 2048 + (2 : ℚ) ^ (64 : Int) := add_le_add error (by simpa using natBound)
      _ ≤ (2 : ℚ) ^ (65 : Int) := by norm_num
  have normal : ModelNormalized Format.binary64 (ofUInt64 Format.binary64 word) := result.1
  have fits := model_fits_of_value_bound Format.binary64 (ofUInt64 Format.binary64 word)
    (model_normalized_finite _ _ normal) 65 (by decide) magnitude
  have decoded : decoded64 (Binary64.ofUInt64 word) = ofUInt64 Format.binary64 word := by
    change unpack Format.binary64 (pack Format.binary64
      (ofUInt64 Format.binary64 word)) = _
    exact model_unpack_pack_normalized _ _ normal fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ normal
  · exact ⟨by simpa only [numerical64, decoded] using magnitude, decoded⟩

/-- A positive unsigned count stays positive even beyond exact integer conversion. -/
theorem count_relative (word : UInt64) (positive : 0 < word.toNat) :
    |numerical64 (Binary64.ofUInt64 word) - (word.toNat : ℚ)| ≤ (word.toNat : ℚ) / 2 := by
  have decoded := (count_model word).2.2
  have cmp : compare (word.toNat : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  simp only [ofUInt64, ofNat, ofInt, normalize, cmp, Int.toNat_natCast] at decoded
  have floor : Format.binary64.minExponent ≤ totalExponent word.toNat 0 - 1 := by
    simp only [Format.minExponent, totalExponent]
    omega
  have relative := round_relative_half Format.binary64 .positive word.toNat 0 positive floor
  simpa only [numerical64, decoded, signCoefficient, one_mul, zpow_zero, mul_one] using relative

/-- Conversion is nonnegative for every count and bounded away from zero when nonempty. -/
theorem count_nonnegative (word : UInt64) :
    0 ≤ numerical64 (Binary64.ofUInt64 word) ∧
      (0 < word.toNat → (1 : ℚ) / 2 ≤ numerical64 (Binary64.ofUInt64 word)) := by
  by_cases zero : word.toNat = 0
  · have same : word = 0 := UInt64.toNat_inj.mp zero
    subst word
    constructor
    · decide
    · intro impossible; omega
  · have positive : 0 < word.toNat := by omega
    have relative := (abs_le.mp (count_relative word positive)).1
    have one : (1 : ℚ) ≤ word.toNat := by exact_mod_cast positive
    constructor <;> intros <;> linarith

/-- Half-relative rounding bound on the actual normalized multiplication. -/
theorem model_mul_relative (left right : UnpackedFloat)
    (leftNormal : ModelNormalized Format.binary64 left)
    (rightNormal : ModelNormalized Format.binary64 right)
    (lower : (1 : ℚ) / 2 ≤ |unpackedValue left * unpackedValue right|) :
    |unpackedValue (UnpackedFloat.mul Format.binary64 left right) -
      unpackedValue left * unpackedValue right| ≤
      |unpackedValue left * unpackedValue right| / 2 := by
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign => norm_num [unpackedValue] at lower
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero sign => norm_num [unpackedValue] at lower
    | finite rightSign rm re rp =>
      have ready := model_product_exponent_ready Format.binary64 lm rm le re leftSign rightSign
        lp rp leftNormal rightNormal
      have exactValue :
          signCoefficient (leftSign * rightSign) * (lm * rm : Nat) * (2 : ℚ) ^ (le + re) =
          unpackedValue (.finite leftSign lm le lp) *
            unpackedValue (.finite rightSign rm re rp) := by
        rw [model_sign_product_value, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        simp only [unpackedValue, Nat.cast_mul]
        ring
      have magnitude : (lm * rm : Nat) * (2 : ℚ) ^ (le + re) =
          |unpackedValue (.finite leftSign lm le lp) *
            unpackedValue (.finite rightSign rm re rp)| := by
        rw [abs_mul, model_finite_abs, model_finite_abs, Nat.cast_mul,
          zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        ring
      have positive : 0 < lm * rm := Nat.mul_pos lp rp
      have floor := half_floor (lm * rm) (le + re) positive (by simpa only [magnitude] using lower)
      simp only [UnpackedFloat.mul]
      rw [← model_round_without_padding Format.binary64 _ _ _ ready]
      simpa only [exactValue, magnitude] using
        round_relative_half Format.binary64 (leftSign * rightSign) (lm * rm) (le + re)
          positive floor

/-- Actual wide multiplication is finite and separates positive caps by relative error. -/
theorem mul_positive_relative (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (lower : (1 : ℚ) / 2 ≤ numerical64 left * numerical64 right)
    (upper : numerical64 left * numerical64 right ≤ (2 : ℚ) ^ (82 : Int)) :
    (left.mul right).Finite ∧
      |numerical64 (left.mul right) - numerical64 left * numerical64 right| ≤
        (numerical64 left * numerical64 right) / 2 := by
  have leftNormal := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rightNormal := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have positive : 0 ≤ numerical64 left * numerical64 right := by linarith
  have bound : |numerical64 left * numerical64 right| ≤ (2 : ℚ) ^ (82 : Int) := by
    rwa [abs_of_nonneg positive]
  have proof := model_mul_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    leftNormal rightNormal 82 bound
  have radius : (2 : ℚ) ^ (max ((82 : Int) + 1 - Format.binary64.mantissaBits)
      Format.binary64.minExponent) / 2 = (2 : ℚ) ^ (29 : Int) := by
    norm_num [Format.mantissaBits, Format.minExponent]
  have error : |unpackedValue (UnpackedFloat.mul Format.binary64 (decoded64 left)
      (decoded64 right)) - numerical64 left * numerical64 right| ≤ (2 : ℚ) ^ (29 : Int) := by
    simpa only [numerical64, radius] using proof.2
  have decoded := model_mul64_decoded left right leftFinite rightFinite proof.1
    (wide_fits _ _ proof.1 bound error)
  have relative := model_mul_relative (decoded64 left) (decoded64 right) leftNormal rightNormal
    (by rwa [← numerical64, ← numerical64, abs_of_nonneg positive])
  constructor
  · apply (model_decoded64_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ proof.1
  · change 0 ≤ unpackedValue (decoded64 left) * unpackedValue (decoded64 right) at positive
    simpa only [numerical64, decoded, abs_of_nonneg positive] using relative

/-- Normalizing a nonnegative aligned significand cannot introduce a negative result. -/
theorem normalize_nonnegative (mantissa : Int) (exponent : Int) (zeroSign : Sign)
    (positive : 0 ≤ mantissa) :
    0 ≤ unpackedValue (normalize Format.binary64 mantissa exponent zeroSign) := by
  unfold normalize
  split
  · rename_i negative
    have := Int.compare_eq_lt.mp negative
    omega
  · exact le_rfl
  · exact round_nonnegative _ _ _

/-- Nonnegative finite inputs retain their sign through exact alignment and rounding. -/
theorem model_add_nonnegative (left right : UnpackedFloat)
    (leftNormal : ModelNormalized Format.binary64 left)
    (rightNormal : ModelNormalized Format.binary64 right)
    (leftPositive : 0 ≤ unpackedValue left) (rightPositive : 0 ≤ unpackedValue right) :
    0 ≤ unpackedValue (UnpackedFloat.add Format.binary64 left right) := by
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero other => cases sign <;> cases other <;> exact le_rfl
    | finite s m e hp => exact rightPositive
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero sign => exact leftPositive
    | finite rightSign rm re rp =>
      let target := min le re
      let lm' := (decreaseExponent lm le target).1
      let rm' := (decreaseExponent rm re target).1
      let sum := leftSign.apply lm' + rightSign.apply rm'
      have hl := model_decrease_dyadic_value leftSign lm le target (Int.min_le_left _ _)
      have hr := model_decrease_dyadic_value rightSign rm re target (Int.min_le_right _ _)
      have exactValue : (sum : ℚ) * (2 : ℚ) ^ target =
          unpackedValue (.finite leftSign lm le lp) +
            unpackedValue (.finite rightSign rm re rp) := by
        change ((leftSign.apply lm' + rightSign.apply rm' : Int) : ℚ) * (2 : ℚ) ^ target = _
        rw [Int.cast_add, add_mul, hl, hr]
        rfl
      have nonnegative : (0 : ℚ) ≤ (sum : ℚ) * (2 : ℚ) ^ target := by
        rw [exactValue]
        exact add_nonneg leftPositive rightPositive
      have sumPositive : 0 ≤ sum := by
        have := (mul_nonneg_iff_of_pos_right (zpow_pos (by norm_num : (0 : ℚ) < 2) _)).mp
          nonnegative
        exact_mod_cast this
      exact normalize_nonnegative sum target .positive sumPositive

/-- Lifetime addition stays finite and nonnegative throughout its wide magnitude envelope. -/
theorem add_nonnegative (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (leftPositive : 0 ≤ numerical64 left)
    (rightPositive : 0 ≤ numerical64 right)
    (upper : numerical64 left + numerical64 right ≤ (2 : ℚ) ^ (83 : Int)) :
    (left.add right).Finite ∧ 0 ≤ numerical64 (left.add right) := by
  have leftNormal := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rightNormal := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have bound : |numerical64 left + numerical64 right| ≤ (2 : ℚ) ^ (83 : Int) := by
    rwa [abs_of_nonneg (add_nonneg leftPositive rightPositive)]
  have proof := model_add_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    leftNormal rightNormal 83 bound
  have radius : (2 : ℚ) ^ (max ((83 : Int) + 1 - Format.binary64.mantissaBits)
      Format.binary64.minExponent) / 2 = (2 : ℚ) ^ (30 : Int) := by
    norm_num [Format.mantissaBits, Format.minExponent]
  have error : |unpackedValue (UnpackedFloat.add Format.binary64 (decoded64 left)
      (decoded64 right)) - (numerical64 left + numerical64 right)| ≤ (2 : ℚ) ^ (30 : Int) := by
    simpa only [numerical64, radius] using proof.2
  have fits : ModelFits Format.binary64
      (UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64 right)) := by
    apply model_fits_of_value_bound _ _ (model_normalized_finite _ _ proof.1) 84 (by decide)
    have triangle := abs_add_le
      (unpackedValue (UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64 right)) -
        (numerical64 left + numerical64 right)) (numerical64 left + numerical64 right)
    norm_num at *
    linarith only [triangle, error, bound]
  have decoded := model_add64_decoded left right leftFinite rightFinite proof.1 fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ proof.1
  · simpa only [numerical64, decoded] using
      model_add_nonnegative (decoded64 left) (decoded64 right) leftNormal rightNormal
        leftPositive rightPositive

end AcornVerif.CurrentLifetimeArithmetic
