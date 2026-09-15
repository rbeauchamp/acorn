/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentOperations
/-!
# Executing division and residual rounding

These proofs connect the pinned Lean 4.33.0 standard model's
`Unpacked/Operations/Div.lean` quotient, exponent selection and residual-bit
rounding to the actual binary64 division wrapper. The bound uses the enclosing
integer quotient interval, so it holds for every residual-accuracy case without
claiming the tight half-unit bound for division. The admitted numerical domain
excludes a zero denominator and exceptional operands. Finite results, subnormal
normalization and packing guards follow from that domain; native primitive and
compiler/runtime correspondence remain the declared trusted boundary.
-/
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder AcornVerif.CurrentOperations
namespace AcornVerif.CurrentDivision

/-- Every residual-bit case follows the actual rounded significand and exact carry normalization.
-/
theorem model_round_accuracy_value (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy) :
    let first := shiftToTargetExponent spec mantissa exponent accuracy
    unpackedValue (roundWithAccuracy spec sign mantissa exponent accuracy) =
      signCoefficient sign * (first.1.roundedMantissa : ℚ) * (2:ℚ)^first.2 := by
  dsimp only
  rw [model_round_accuracy_components]
  let first := shiftToTargetExponent spec mantissa exponent accuracy
  by_cases carry : first.1.roundedMantissa = 2^spec.mantissaBits
  · change unpackedValue (if _ then _ else _) = _
    rw [if_pos carry, carry]
    simp only [unpackedValue, Nat.cast_pow, Nat.cast_ofNat, Format.mantissaBits]
    rw [zpow_add₀ (by norm_num : (2:ℚ) ≠ 0) _ 1, zpow_one, pow_add]
    ring
  · rw [if_neg carry]
    split
    · rename_i zero
      simp only [unpackedValue, zero, Nat.cast_zero, mul_zero, zero_mul]
    · rfl

/-- For every initial residual-accuracy case, rounding differs from the truncated dyadic input by
at most one selected unit before packing. -/
theorem model_round_accuracy_distance (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy) :
    let shift := (spec.targetExponent (totalExponent mantissa exponent) - exponent).toNat
    |unpackedValue (roundWithAccuracy spec sign mantissa exponent accuracy)-
      signCoefficient sign*mantissa*(2:ℚ)^exponent| ≤ (2:ℚ)^(exponent+shift) := by
  dsimp only
  rw [model_round_accuracy_value]
  let shift := (spec.targetExponent (totalExponent mantissa exponent)-exponent).toNat
  let first := shiftToTargetExponent spec mantissa exponent accuracy
  have hm : first.1.mantissa = mantissa/2^shift := by
    change (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy >>> shift).mantissa = _
    rw [model_shift_mantissa]
    cases accuracy with
    | exact => rfl
    | inexact ord => cases ord <;> rfl
  have hlo := model_rounded_not_below first.1
  have hhi := model_round_mantissa_ceiling first.1
  rw [hm] at hlo hhi
  have hd : 0 < 2^shift := Nat.two_pow_pos _
  have hf : (mantissa/2^shift)*2^shift ≤ mantissa := Nat.div_mul_le_self _ _
  have hc : mantissa < (mantissa/2^shift+1)*2^shift := by
    have rem := Nat.mod_lt mantissa hd
    have decomp := Nat.mod_add_div mantissa (2^shift)
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm (mantissa/2^shift) (2^shift)]
    omega
  simp only [Nat.add_mul, Nat.one_mul] at hc
  have lo : (mantissa:ℚ) ≤ (first.1.roundedMantissa:ℚ)*(2:ℚ)^shift+(2:ℚ)^shift := by
    have hh : mantissa ≤ first.1.roundedMantissa*2^shift+2^shift := by
      have hmul := Nat.mul_le_mul_right (2^shift) hlo
      omega
    exact_mod_cast hh
  have hi : (first.1.roundedMantissa:ℚ)*(2:ℚ)^shift ≤ (mantissa:ℚ)+(2:ℚ)^shift := by
    have hh : first.1.roundedMantissa*2^shift ≤ mantissa+2^shift := by
      have hmul := Nat.mul_le_mul_right (2^shift) hhi
      simp only [Nat.add_mul, Nat.one_mul] at hmul
      omega
    exact_mod_cast hh
  have hp : (0:ℚ) ≤ (2:ℚ)^exponent := le_of_lt (zpow_pos (by norm_num) _)
  have low := mul_le_mul_of_nonneg_right lo hp
  have high := mul_le_mul_of_nonneg_right hi hp
  have he : first.2 = exponent+shift := rfl
  change |signCoefficient sign*(first.1.roundedMantissa:ℚ)*(2:ℚ)^first.2-
    signCoefficient sign*mantissa*(2:ℚ)^exponent| ≤ (2:ℚ)^(exponent+shift)
  rw [he, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), zpow_natCast, abs_le]
  cases sign <;> simp only [signCoefficient] <;> constructor <;> nlinarith

/-- A quotient of positive significands and a positive dyadic scale is positive. -/
theorem model_ratio_positive (left right : Nat) (leftExponent rightExponent : Int)
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    (0 : ℚ) < ((left : ℚ) / right) * (2 : ℚ) ^ (leftExponent - rightExponent) :=
  mul_pos (div_pos (by exact_mod_cast leftPositive) (by exact_mod_cast rightPositive))
    (zpow_pos (by norm_num) _)

/-- The actual operand total exponents give a lower dyadic bound on their exact positive quotient.
-/
theorem model_ratio_window_lower (left right : Nat) (leftExponent rightExponent : Int)
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    (2 : ℚ) ^ (totalExponent left leftExponent - totalExponent right rightExponent - 1) ≤
      ((left : ℚ) / right) * (2 : ℚ) ^ (leftExponent - rightExponent) := by
  have leftLow := (model_positive_dyadic_window left leftExponent leftPositive).1
  have rightHigh := (model_positive_dyadic_window right rightExponent rightPositive).2
  have positive : (0:ℚ) < (right:ℚ)*(2:ℚ)^rightExponent :=
    mul_pos (by exact_mod_cast rightPositive) (zpow_pos (by norm_num) _)
  have product : (2:ℚ)^(totalExponent left leftExponent-totalExponent right rightExponent-1)*
      ((right:ℚ)*(2:ℚ)^rightExponent) ≤ (left:ℚ)*(2:ℚ)^leftExponent := by
    calc
      _ ≤ (2:ℚ)^(totalExponent left leftExponent-totalExponent right rightExponent-1)*
          (2:ℚ)^(totalExponent right rightExponent) :=
        mul_le_mul_of_nonneg_left (le_of_lt rightHigh)
          (le_of_lt (zpow_pos (by norm_num) _))
      _ = (2:ℚ)^(totalExponent left leftExponent-1) := by
        rw [← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
        congr 1
        omega
      _ ≤ _ := leftLow
  have result := (le_div_iff₀ positive).mpr product
  have identity : ((left:ℚ)*(2:ℚ)^leftExponent)/((right:ℚ)*(2:ℚ)^rightExponent) =
      ((left:ℚ)/right)*(2:ℚ)^(leftExponent-rightExponent) := by
    rw [zpow_sub₀ (by norm_num : (2:ℚ) ≠ 0)]
    ring
  simpa only [identity] using result

/-- The executing division core places its exact rational quotient between the truncated dyadic
significand and the next unit. -/
theorem model_divCore_bracket (spec : Format) (left right : Nat)
    (leftExponent rightExponent : Int) (rightPositive : 0 < right) :
    let core := divCore spec left leftExponent right rightExponent
    let ratio := ((left:ℚ)/right)*(2:ℚ)^(leftExponent-rightExponent)
    core.2.1 ≤ leftExponent-rightExponent ∧
      core.2.1 ≤ spec.targetExponent
        (totalExponent left leftExponent-totalExponent right rightExponent) ∧
      (core.1:ℚ)*(2:ℚ)^core.2.1 ≤ ratio ∧
      ratio < ((core.1:ℚ)+1)*(2:ℚ)^core.2.1 := by
  let target := min (leftExponent-rightExponent) (spec.targetExponent
    (totalExponent left leftExponent-totalExponent right rightExponent))
  let shift := (leftExponent-rightExponent-target).toNat
  let numerator := left*2^shift
  have ready : target ≤ leftExponent-rightExponent := Int.min_le_left _ _
  have shifted : (shift:Int)+target = leftExponent-rightExponent := by dsimp only [shift]; omega
  have identity : ((numerator:ℚ)/right)*(2:ℚ)^target =
      ((left:ℚ)/right)*(2:ℚ)^(leftExponent-rightExponent) := by
    have powers : (2:ℚ)^shift*(2:ℚ)^target = (2:ℚ)^(leftExponent-rightExponent) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), shifted]
    change ((((left*2^shift:Nat):ℚ)/right)*(2:ℚ)^target) = _
    push_cast
    calc
      _ = ((left:ℚ)/right)*((2:ℚ)^shift*(2:ℚ)^target) := by ring
      _ = _ := by rw [powers]
  have bracket := quotient_fraction_bracket numerator right rightPositive
  have positive : (0:ℚ) < (2:ℚ)^target := zpow_pos (by norm_num) _
  have lo := mul_le_mul_of_nonneg_right bracket.1 (le_of_lt positive)
  have hi := mul_lt_mul_of_pos_right bracket.2 positive
  rw [identity] at lo hi
  dsimp only [divCore]
  simp only [Nat.shiftLeft_eq]
  exact ⟨ready, Int.min_le_right _ _, lo, hi⟩

/-- Residual rounding of a zero significand is canonical when its exponent is at or below the
subnormal floor. -/
theorem model_round_accuracy_zero_normalized (spec : Format) (sign : Sign) (exponent : Int)
    (accuracy : Accuracy) (floor : exponent ≤ spec.minExponent) :
    ModelNormalized spec (roundWithAccuracy spec sign 0 exponent accuracy) := by
  let first := shiftToTargetExponent spec 0 exponent accuracy
  have zero : first.1.mantissa = 0 := by
    change (ExtendedMantissa.ofMantissaAndAccuracy 0 accuracy >>>
      (spec.targetExponent (totalExponent 0 exponent)-exponent).toNat).mantissa = 0
    rw [model_shift_mantissa]
    cases accuracy with
    | exact => simp [ExtendedMantissa.ofMantissaAndAccuracy]
    | inexact ord => cases ord <;> simp [ExtendedMantissa.ofMantissaAndAccuracy]
  have bound := model_round_mantissa_ceiling first.1
  rw [zero] at bound
  have full : 2 ≤ 2^spec.mantissaBits := by
    rw [Format.mantissaBits, Nat.add_comm, Nat.pow_succ]
    have := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit
    omega
  have target : first.2 = spec.minExponent := by
    change exponent+(max ((Nat.log2 0:Int)+1+exponent-spec.mantissaBits)
      spec.minExponent-exponent).toNat = _
    have : 0 < spec.mantissaBits := by simp [Format.mantissaBits]
    simp only [Nat.log2_zero, Nat.cast_zero, zero_add]
    omega
  rw [model_round_accuracy_components]
  have noCarry : first.1.roundedMantissa ≠ 2^spec.mantissaBits := by omega
  change ModelNormalized spec (if first.1.roundedMantissa = _ then _ else _)
  rw [if_neg noCarry]
  split
  · trivial
  · change first.1.roundedMantissa < 2^spec.mantissaBits ∧
      spec.minExponent ≤ first.2 ∧
        (first.2=spec.minExponent ∨ 2^spec.mantissaBitsWithoutImplicit ≤ first.1.roundedMantissa)
    exact ⟨by omega, le_of_eq target.symm, Or.inl target⟩

/-- The actual quotient exponent supplies enough significand bits for normalization, including
zero and subnormal quotients. -/
theorem model_divCore_ready (spec : Format) (left right : Nat)
    (leftExponent rightExponent : Int) (leftPositive : 0 < left) (rightPositive : 0 < right) :
    let core := divCore spec left leftExponent right rightExponent
    if core.1 = 0 then core.2.1 ≤ spec.minExponent
    else core.2.1 ≤ spec.targetExponent (totalExponent core.1 core.2.1) := by
  dsimp only
  let core := divCore spec left leftExponent right rightExponent
  let difference := totalExponent left leftExponent-totalExponent right rightExponent
  let ratio := ((left:ℚ)/right)*(2:ℚ)^(leftExponent-rightExponent)
  have bracket := model_divCore_bracket spec left right leftExponent rightExponent rightPositive
  change core.2.1 ≤ leftExponent-rightExponent ∧ core.2.1 ≤ spec.targetExponent difference ∧
    (core.1:ℚ)*(2:ℚ)^core.2.1 ≤ ratio ∧ ratio < ((core.1:ℚ)+1)*(2:ℚ)^core.2.1 at bracket
  have lower : (2:ℚ)^(difference-1) ≤ ratio :=
    model_ratio_window_lower left right leftExponent rightExponent leftPositive rightPositive
  have precision : 0 < spec.mantissaBits := by simp [Format.mantissaBits]
  change (if core.1=0 then core.2.1 ≤ spec.minExponent
    else core.2.1 ≤ spec.targetExponent (totalExponent core.1 core.2.1))
  by_cases zero : core.1=0
  · rw [if_pos zero]
    have comparison : (2:ℚ)^(difference-1) < (2:ℚ)^core.2.1 := by
      have h := lt_of_le_of_lt lower bracket.2.2.2
      simpa only [zero, Nat.cast_zero, zero_add, one_mul] using h
    have exponents := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ)<2)).mp comparison
    have ready := bracket.2.1
    dsimp only [Format.targetExponent] at ready
    omega
  · rw [if_neg zero]
    by_cases floor : core.2.1 ≤ spec.minExponent
    · dsimp only [Format.targetExponent]
      omega
    · have ready : core.2.1 ≤ difference-spec.mantissaBits := by
        have h := bracket.2.1
        dsimp only [Format.targetExponent] at h
        omega
      have power : (2:ℚ)^((spec.mantissaBitsWithoutImplicit:Int)+core.2.1) ≤
          (2:ℚ)^(difference-1) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2)
        have : spec.mantissaBits = spec.mantissaBitsWithoutImplicit+1 := by
          simp [Format.mantissaBits, Nat.add_comm]
        omega
      have cmp := lt_of_le_of_lt (le_trans power lower) bracket.2.2.2
      rw [zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), zpow_natCast] at cmp
      have significand := (mul_lt_mul_iff_left₀ (zpow_pos (by norm_num : (0:ℚ)<2) core.2.1)).mp cmp
      have leading : 2^spec.mantissaBitsWithoutImplicit ≤ core.1 := by
        have : 2^spec.mantissaBitsWithoutImplicit < core.1+1 := by exact_mod_cast significand
        omega
      have logBound := (Nat.le_log2 (by omega : core.1≠0)).mpr leading
      dsimp only [Format.targetExponent, totalExponent]
      have : spec.mantissaBits = spec.mantissaBitsWithoutImplicit+1 := by
          simp [Format.mantissaBits, Nat.add_comm]
      omega

/-- The executing quotient and residual rounding yield canonical components and a conservative
two-unit error bound derived from the exact quotient magnitude. -/
theorem model_divCore_error (spec : Format) (sign : Sign) (left right : Nat)
    (leftExponent rightExponent limit : Int)
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (bound : ((left : ℚ) / right) * (2 : ℚ) ^ (leftExponent - rightExponent) ≤ (2 : ℚ) ^ limit) :
    let core := divCore spec left leftExponent right rightExponent
    let result := roundWithAccuracy spec sign core.1 core.2.1 core.2.2
    ModelNormalized spec result ∧
      |unpackedValue result-signCoefficient sign*((left:ℚ)/right)*
        (2:ℚ)^(leftExponent-rightExponent)| ≤
        2*(2:ℚ)^(max (limit+1-spec.mantissaBits) spec.minExponent) := by
  dsimp only
  let core := divCore spec left leftExponent right rightExponent
  let difference := totalExponent left leftExponent-totalExponent right rightExponent
  let ratio := ((left:ℚ)/right)*(2:ℚ)^(leftExponent-rightExponent)
  let shift := (spec.targetExponent (totalExponent core.1 core.2.1)-core.2.1).toNat
  let radiusExponent := max (limit+1-spec.mantissaBits) spec.minExponent
  have bracket := model_divCore_bracket spec left right leftExponent rightExponent rightPositive
  change core.2.1 ≤ leftExponent-rightExponent ∧ core.2.1 ≤ spec.targetExponent difference ∧
    (core.1:ℚ)*(2:ℚ)^core.2.1 ≤ ratio ∧ ratio < ((core.1:ℚ)+1)*(2:ℚ)^core.2.1 at bracket
  have lower : (2:ℚ)^(difference-1) ≤ ratio :=
    model_ratio_window_lower left right leftExponent rightExponent leftPositive rightPositive
  have differenceBound : difference ≤ limit+1 := by
    have h := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℚ)<2)).mp (le_trans lower bound)
    omega
  have inputBound : core.2.1 ≤ radiusExponent := by
    have h := bracket.2.1
    dsimp only [Format.targetExponent] at h
    dsimp only [radiusExponent]
    omega
  have targetBound : spec.targetExponent (totalExponent core.1 core.2.1) ≤ radiusExponent := by
    by_cases zero : core.1=0
    · have precision : 0 < spec.mantissaBits := by simp [Format.mantissaBits]
      simp only [zero, totalExponent, Nat.log2_zero, Nat.cast_zero, zero_add,
        Format.targetExponent]
      dsimp only [radiusExponent] at *
      omega
    · have lo := (model_positive_dyadic_window core.1 core.2.1 (by omega)).1
      have h := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℚ)<2)).mp
        (le_trans lo (le_trans bracket.2.2.1 bound))
      dsimp only [Format.targetExponent, radiusExponent]
      omega
  have outputBound : core.2.1+shift ≤ radiusExponent := by
    dsimp only [shift]
    omega
  have normal : ModelNormalized spec
      (roundWithAccuracy spec sign core.1 core.2.1 core.2.2) := by
    have ready := model_divCore_ready spec left right leftExponent rightExponent
      leftPositive rightPositive
    change (if core.1=0 then core.2.1 ≤ spec.minExponent
      else core.2.1 ≤ spec.targetExponent (totalExponent core.1 core.2.1)) at ready
    by_cases zero : core.1=0
    · simp only [zero, ↓reduceIte] at ready
      rw [zero]
      exact model_round_accuracy_zero_normalized spec sign core.2.1 core.2.2 ready
    · simp only [zero, ↓reduceIte] at ready
      exact model_round_accuracy_normalized spec sign core.1 core.2.1 core.2.2 (by omega) ready
  have fractionError : |signCoefficient sign*(core.1:ℚ)*(2:ℚ)^core.2.1-
      signCoefficient sign*ratio| ≤ (2:ℚ)^core.2.1 := by
    rw [abs_le]
    cases sign <;> simp only [signCoefficient] <;> constructor <;>
      nlinarith [bracket.2.2.1, bracket.2.2.2]
  have approximation := model_round_accuracy_distance spec sign core.1 core.2.1 core.2.2
  change |unpackedValue (roundWithAccuracy spec sign core.1 core.2.1 core.2.2)-
    signCoefficient sign*(core.1:ℚ)*(2:ℚ)^core.2.1| ≤ (2:ℚ)^(core.2.1+shift) at approximation
  change ModelNormalized spec (roundWithAccuracy spec sign core.1 core.2.1 core.2.2) ∧ _
  refine ⟨normal, ?_⟩
  change |unpackedValue (roundWithAccuracy spec sign core.1 core.2.1 core.2.2)-
    signCoefficient sign*((left:ℚ)/right)*(2:ℚ)^(leftExponent-rightExponent)| ≤ _
  have identity : signCoefficient sign*((left:ℚ)/right)*(2:ℚ)^(leftExponent-rightExponent) =
      signCoefficient sign*ratio := mul_assoc _ _ _
  rw [identity]
  calc
    _ = |(unpackedValue (roundWithAccuracy spec sign core.1 core.2.1 core.2.2)-
        signCoefficient sign*(core.1:ℚ)*(2:ℚ)^core.2.1)+
        (signCoefficient sign*(core.1:ℚ)*(2:ℚ)^core.2.1-signCoefficient sign*ratio)| := by
      congr 1
      ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ (2:ℚ)^(core.2.1+shift)+(2:ℚ)^core.2.1 := add_le_add approximation fractionError
    _ ≤ (2:ℚ)^radiusExponent+(2:ℚ)^radiusExponent :=
      add_le_add (zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2) outputBound)
        (zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2) inputBound)
    _ = _ := by ring

/-- Division of signed dyadic values agrees with the executing sign division and positive
significand quotient. -/
theorem model_signed_ratio (leftSign rightSign : Sign) (left right : Nat)
    (leftExponent rightExponent : Int) :
    (signCoefficient leftSign * left * (2 : ℚ) ^ leftExponent) /
      (signCoefficient rightSign * right * (2 : ℚ) ^ rightExponent) =
      signCoefficient (leftSign / rightSign) * ((left : ℚ) / right) *
        (2 : ℚ) ^ (leftExponent - rightExponent) := by
  have signs : signCoefficient (leftSign/rightSign) =
      signCoefficient leftSign*signCoefficient rightSign := by
    rw [show leftSign/rightSign=leftSign*rightSign from by
      cases leftSign <;> cases rightSign <;> rfl]
    exact model_sign_product_value _ _
  rw [signs, zpow_sub₀ (by norm_num : (2:ℚ) ≠ 0)]
  cases leftSign <;> cases rightSign <;> simp only [signCoefficient] <;> ring

/-- Actual normalized finite division with a nonzero denominator has the derived magnitude-
dependent error bound. -/
theorem model_div_dyadic_local (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (nonzero : unpackedValue right ≠ 0) (limit : Int)
    (bound : |unpackedValue left / unpackedValue right| ≤ (2 : ℚ) ^ limit) :
    ModelNormalized spec (UnpackedFloat.div spec left right) ∧
      |unpackedValue (UnpackedFloat.div spec left right) -
        unpackedValue left / unpackedValue right| ≤
        2 * (2 : ℚ) ^ (max (limit + 1 - spec.mantissaBits) spec.minExponent) := by
  have epsilon : (0:ℚ) ≤ 2*(2:ℚ)^(max (limit+1-spec.mantissaBits) spec.minExponent) :=
    mul_nonneg (by norm_num) (le_of_lt (zpow_pos (by norm_num : (0:ℚ)<2) _))
  cases right with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign => exact False.elim (nonzero rfl)
  | finite rightSign rm re rp =>
    cases left with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero sign =>
      change True ∧ |(0:ℚ)-0/(signCoefficient rightSign*rm*(2:ℚ)^re)| ≤ _
      exact ⟨True.intro, by simpa only [zero_div, sub_self, abs_zero] using epsilon⟩
    | finite leftSign lm le lp =>
      have equality : unpackedValue (.finite leftSign lm le lp)/
          unpackedValue (.finite rightSign rm re rp) =
          signCoefficient (leftSign/rightSign)*((lm:ℚ)/rm)*(2:ℚ)^(le-re) :=
        model_signed_ratio leftSign rightSign lm rm le re
      have magnitude : |signCoefficient (leftSign/rightSign)*((lm:ℚ)/rm)*(2:ℚ)^(le-re)| =
          ((lm:ℚ)/rm)*(2:ℚ)^(le-re) := by
        have positive := model_ratio_positive lm rm le re lp rp
        cases (leftSign/rightSign) <;>
          simp only [signCoefficient, one_mul, neg_mul, abs_neg]
        all_goals exact abs_of_pos positive
      have ratioBound : ((lm:ℚ)/rm)*(2:ℚ)^(le-re) ≤ (2:ℚ)^limit := by
        simpa only [equality,magnitude] using bound
      have proof := model_divCore_error spec (leftSign/rightSign) lm rm le re limit lp rp ratioBound
      simpa only [UnpackedFloat.div, equality] using proof

/-- The executing binary64 division agrees with its actual unpacked model when the normalized
result satisfies the packing guard. -/
theorem model_div64_decoded (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (normal : ModelNormalized Format.binary64 (UnpackedFloat.div Format.binary64
      (decoded64 left) (decoded64 right)))
    (fits : ModelFits Format.binary64 (UnpackedFloat.div Format.binary64
      (decoded64 left) (decoded64 right))) :
    decoded64 (left.div right) =
      UnpackedFloat.div Format.binary64 (decoded64 left) (decoded64 right) := by
  change unpack Format.binary64 (pack Format.binary64
    (UnpackedFloat.div Format.binary64 (Float.Model.ofBits left.bits).unpack
      (Float.Model.ofBits right.bits).unpack)) = _
  rw [model_ofBits64_decoded left leftFinite, model_ofBits64_decoded right rightFinite]
  exact model_unpack_pack_normalized _ _ normal fits

/-- Actual binary64 division stays finite with error at most 2^-35 when its finite nonzero-
denominator exact quotient has magnitude at most 2^16. -/
theorem binary64_div_finite_error (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonzero : numerical64 right ≠ 0)
    (bound : |numerical64 left / numerical64 right| ≤ 65536) :
    (left.div right).Finite ∧
      |numerical64 (left.div right) - numerical64 left / numerical64 right| ≤ 1 / 34359738368 := by
  have leftNormal := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rightNormal := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have power : (2:ℚ)^(16:Int)=65536 := by norm_num
  have localProof := model_div_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    leftNormal rightNormal nonzero 16 (by simpa only [numerical64,power] using bound)
  have radius : 2*(2:ℚ)^(max ((16:Int)+1-Format.binary64.mantissaBits)
      Format.binary64.minExponent)=1/34359738368 := by
    norm_num [Format.mantissaBits,Format.minExponent]
  have error : |unpackedValue (UnpackedFloat.div Format.binary64 (decoded64 left)
      (decoded64 right))-numerical64 left/numerical64 right| ≤ 1/34359738368 := by
    simpa only [numerical64,radius] using localProof.2
  have fits : ModelFits Format.binary64 (UnpackedFloat.div Format.binary64
      (decoded64 left) (decoded64 right)) := by
    apply model_fits_of_value_bound Format.binary64 _
      (model_normalized_finite _ _ localProof.1) 17 (by decide)
    have ht := abs_add_le
      (unpackedValue (UnpackedFloat.div Format.binary64 (decoded64 left) (decoded64 right))-
        numerical64 left/numerical64 right) (numerical64 left/numerical64 right)
    have triangle : |unpackedValue (UnpackedFloat.div Format.binary64 (decoded64 left)
        (decoded64 right))| ≤ 1/34359738368+65536 := by
      have hs : unpackedValue (UnpackedFloat.div Format.binary64
          (decoded64 left) (decoded64 right))-
          numerical64 left/numerical64 right+numerical64 left/numerical64 right =
          unpackedValue (UnpackedFloat.div Format.binary64
            (decoded64 left) (decoded64 right)) := by ring
      rw [hs] at ht
      exact le_trans ht (add_le_add error bound)
    exact le_trans triangle (by norm_num)
  have exactDecoded := model_div64_decoded left right leftFinite rightFinite localProof.1 fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [exactDecoded]
    exact model_normalized_finite _ _ localProof.1
  · simpa only [numerical64,exactDecoded] using error

end AcornVerif.CurrentDivision
