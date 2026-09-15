/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentArithmetic

/-! # One-sided binary32 rounding bounds for retirement rail arithmetic -/

open Acorn
open Float.Model (Format UnpackedFloat totalExponent)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentArithmetic

namespace AcornVerif.CurrentRetirementRounding

/-- Nearest-even quotient rounding cannot fall below any integer lower bound
on the exact quotient. -/
theorem nearest_lower (mantissa denominator lower : Nat) (positive : 0 < denominator)
    (bound : lower * denominator ≤ mantissa) :
    lower ≤ Rounding.nearestEven mantissa denominator := by
  exact le_trans ((Nat.le_div_iff_mul_le positive).mpr bound)
    (Rounding.nearestEven_bracket _ _).1

/-- Rounding to a coarser dyadic grid preserves every lower bound already on
that grid. The exponent relation accounts for all discarded source digits. -/
theorem rounded_grid_lower (mantissa floorMantissa shift gap : Nat)
    (bound : floorMantissa * 2 ^ (gap + shift) ≤ mantissa) :
    floorMantissa * 2 ^ gap ≤ Rounding.nearestEven mantissa (2 ^ shift) := by
  apply nearest_lower _ _ _ (Nat.two_pow_pos _)
  simpa only [Nat.pow_add, Nat.mul_assoc] using bound

/-- Comparing dyadics on an integral common grid is an exact natural-number
comparison, with no rational approximation. -/
theorem dyadic_lower (mantissa lower : Nat) (exponent floorExponent : Int)
    (order : exponent ≤ floorExponent)
    (bound : (lower : ℚ) * 2 ^ floorExponent ≤ (mantissa : ℚ) * 2 ^ exponent) :
    lower * 2 ^ (floorExponent - exponent).toNat ≤ mantissa := by
  have power : (2 : ℚ) ^ floorExponent =
      (2 : ℚ) ^ ((floorExponent - exponent).toNat) * (2 : ℚ) ^ exponent := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    congr 1
    omega
  rw [power, ← mul_assoc] at bound
  have positive := zpow_pos (by norm_num : (0 : ℚ) < 2) exponent
  have reduced := (mul_le_mul_iff_left₀ positive).mp bound
  exact_mod_cast reduced

/-- Exact binary32 rounding preserves a positive normal representable lower
bound when the input already needs no left normalization. -/
theorem round_grid_bound (mantissa lower : Nat) (exponent floorExponent : Int)
    (positive : 0 < mantissa) (lowerBound : lower < 2 ^ 24)
    (floorNormal : -149 < floorExponent)
    (targetOrder : exponent ≤ Format.binary32.targetExponent (totalExponent mantissa exponent))
    (bound : (lower : ℚ) * 2 ^ floorExponent ≤ (mantissa : ℚ) * 2 ^ exponent) :
    (lower : ℚ) * 2 ^ floorExponent ≤
      unpackedValue (roundWithAccuracy Format.binary32 .positive mantissa exponent .exact) := by
  let target := Format.binary32.targetExponent (totalExponent mantissa exponent)
  let shift := (target - exponent).toNat
  have shifted : exponent + shift = target := by dsimp [shift]; omega
  rw [model_round_exact_value]
  simp only [signCoefficient, one_mul]
  change (lower : ℚ) * 2 ^ floorExponent ≤
    (Rounding.nearestEven mantissa (2 ^ shift) : ℚ) * 2 ^ (exponent + shift)
  rw [shifted]
  by_cases small : target ≤ floorExponent
  · have order : exponent ≤ floorExponent := le_trans targetOrder small
    have lowerGrid := dyadic_lower mantissa lower exponent floorExponent order bound
    have gap : (floorExponent - exponent).toNat =
        (floorExponent - target).toNat + shift := by dsimp [shift]; omega
    rw [gap] at lowerGrid
    have rounded := rounded_grid_lower mantissa lower shift
      (floorExponent - target).toNat lowerGrid
    have power : (2 : ℚ) ^ floorExponent =
        (2 : ℚ) ^ (floorExponent - target).toNat * (2 : ℚ) ^ target := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      congr 1
      omega
    rw [power, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos (by norm_num) _))
    exact_mod_cast rounded
  · have leading := model_first_normalized_lower Format.binary32 mantissa exponent
      .exact positive targetOrder
    have retained : 2 ^ 23 ≤ Rounding.nearestEven mantissa (2 ^ shift) := by
      rcases leading with minimum | normal
      · change exponent + shift = -149 at minimum
        omega
      · have rounded := le_trans normal (model_rounded_not_below
          (shiftToTargetExponent Format.binary32 mantissa exponent .exact).1)
        simpa only [shiftToTargetExponent, shiftToExponent, model_round_shift_exact] using rounded
    have exponentBound : floorExponent + 1 ≤ target := by omega
    have power := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) exponentBound
    have magnitude : (lower : ℚ) ≤ 2 ^ 24 := by exact_mod_cast lowerBound.le
    have leadingQ : (2 : ℚ) ^ 23 ≤ Rounding.nearestEven mantissa (2 ^ shift) := by
      exact_mod_cast retained
    calc
      (lower : ℚ) * 2 ^ floorExponent ≤ (2 : ℚ) ^ 24 * 2 ^ floorExponent :=
        mul_le_mul_of_nonneg_right magnitude (le_of_lt (zpow_pos (by norm_num) _))
      _ = (2 : ℚ) ^ 23 * 2 ^ (floorExponent + 1) := by
        rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        norm_num
        ring
      _ ≤ (2 : ℚ) ^ 23 * 2 ^ target := mul_le_mul_of_nonneg_left power (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right leadingQ (by positivity)

/-- Full positive binary32 rounding preserves every positive normal lower
bound already representable in the target format. -/
theorem round_lower (mantissa lower : Nat) (exponent floorExponent : Int)
    (positive : 0 < mantissa) (lowerBound : lower < 2 ^ 24)
    (floorNormal : -149 < floorExponent)
    (bound : (lower : ℚ) * 2 ^ floorExponent ≤ (mantissa : ℚ) * 2 ^ exponent) :
    (lower : ℚ) * 2 ^ floorExponent ≤
      unpackedValue (round Format.binary32 .positive mantissa exponent) := by
  let target := Format.binary32.targetExponent (totalExponent mantissa exponent)
  let shift := (exponent - target).toNat
  have total : totalExponent (mantissa * 2 ^ shift) (exponent - shift) =
      totalExponent mantissa exponent := by
    simp only [totalExponent,
      AcornVerif.CurrentPower.model_log2_scaled_positive mantissa shift positive]
    omega
  have order : exponent - shift ≤ target := by dsimp [shift]; omega
  have padded : (lower : ℚ) * 2 ^ floorExponent ≤
      ((mantissa * 2 ^ shift : Nat) : ℚ) * 2 ^ (exponent - shift) := by
    have exactValue := dyadic_padding_exact .positive mantissa shift exponent
    simp only [signCoefficient, one_mul] at exactValue
    rwa [exactValue]
  have result := round_grid_bound (mantissa * 2 ^ shift) lower (exponent - shift)
    floorExponent (Nat.mul_pos positive (Nat.two_pow_pos _)) lowerBound floorNormal
    (by rwa [total]) padded
  simpa only [round, decreaseExponent, Nat.shiftLeft_eq] using result

/-- Reversing the sign in the full rounding model reverses its exact numerical
reading, including zero. -/
theorem round_negative_value (mantissa : Nat) (exponent : Int) :
    unpackedValue (round Format.binary32 .negative mantissa exponent) =
      -unpackedValue (round Format.binary32 .positive mantissa exponent) := by
  simp only [round, model_round_exact_value, signCoefficient]
  ring

/-- Signed normalization preserves every negative normal representable upper
bound, even when the normalized exponent will overflow during packing. -/
theorem normalize_negative_bound (mantissa : Int) (exponent : Int)
    (lower : Nat) (floorExponent : Int) (positive : 0 < lower)
    (lowerBound : lower < 2 ^ 24) (floorNormal : -149 < floorExponent)
    (bound : (mantissa : ℚ) * 2 ^ exponent ≤ -(lower : ℚ) * 2 ^ floorExponent) :
    ModelNormalized Format.binary32 (normalize Format.binary32 mantissa exponent .positive) ∧
    unpackedValue (normalize Format.binary32 mantissa exponent .positive) ≤
      -(lower : ℚ) * 2 ^ floorExponent := by
  have power : (0 : ℚ) < 2 ^ exponent := zpow_pos (by norm_num) _
  have negative : (mantissa : ℚ) < 0 := by
    have lowerPositive : (0 : ℚ) < (lower : ℚ) * 2 ^ floorExponent := by positivity
    nlinarith only [bound, power, lowerPositive]
  have negativeInt : mantissa < 0 := by exact_mod_cast negative
  have natural : ((-mantissa).toNat : ℚ) = -(mantissa : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -mantissa)
  have naturalPositive : 0 < (-mantissa).toNat := by omega
  have rounded := round_lower (-mantissa).toNat lower exponent floorExponent
    naturalPositive lowerBound floorNormal (by rw [natural]; linarith only [bound])
  unfold normalize
  rw [show compare mantissa 0 = Ordering.lt from Int.compare_eq_lt.mpr negativeInt]
  refine ⟨model_round_normalized _ _ _ _, ?_⟩
  rw [round_negative_value]
  linarith only [rounded]

end AcornVerif.CurrentRetirementRounding
