/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentOrder
/-!
# Subtraction and finite truncation

Subtraction is related to addition of the negated unpacked value in the pinned
Lean 4.33.0 standard model (`Unpacked/Operations/Sub.lean`), then connected to
the actual binary64 wrapper. The integer conversion proofs use the executing
signed quotient and clamp definitions from `Acorn.Conversion`. Every numerical
statement excludes exceptional inputs explicitly. Native primitive and
compiler/runtime correspondence remain the declared trusted boundary.
-/
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder
namespace AcornVerif.CurrentOperations

/-- Negating the model sign negates its integer application for every integer. -/
theorem model_sign_neg_apply (sign : Sign) (value : Int) :
    (-sign).apply value = -(sign.apply value) := by
  cases sign <;> first | rfl | exact (neg_neg value).symm

/-- Actual standard-model subtraction equals addition of the negated second operand, including all
exceptional constructors. -/
theorem model_sub_add_neg (spec : Format) (left right : UnpackedFloat) :
    UnpackedFloat.sub spec left right = UnpackedFloat.add spec left (UnpackedFloat.neg right) := by
  cases left <;> cases right <;>
    simp [UnpackedFloat.sub, UnpackedFloat.add, UnpackedFloat.neg,
      model_sign_neg_apply, sub_eq_add_neg]

/-- Sign negation preserves every canonical component constraint. -/
theorem model_neg_normalized (spec : Format) (value : UnpackedFloat)
    (normal : ModelNormalized spec value) : ModelNormalized spec (UnpackedFloat.neg value) := by
  cases value <;> exact normal

/-- Sign negation commutes with the total rational extension; numerical uses additionally require
finite classification. -/
theorem model_neg_value (value : UnpackedFloat) :
    unpackedValue (UnpackedFloat.neg value) = -unpackedValue value := by
  cases value with
  | notANumber => simp [UnpackedFloat.neg, unpackedValue]
  | infinity sign => simp [UnpackedFloat.neg, unpackedValue]
  | zero sign => simp [UnpackedFloat.neg, unpackedValue]
  | finite sign m e hp => cases sign <;> simp [UnpackedFloat.neg, unpackedValue, signCoefficient]

/-- Actual finite normalized subtraction has the same derived magnitude-dependent rounding bound
as addition. -/
theorem model_sub_dyadic_local (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (limit : Int) (bound : |unpackedValue left - unpackedValue right| ≤ (2 : ℚ) ^ limit) :
    ModelNormalized spec (UnpackedFloat.sub spec left right) ∧
      |unpackedValue (UnpackedFloat.sub spec left right) -
        (unpackedValue left - unpackedValue right)| ≤
        (2 : ℚ)^(max (limit+1-spec.mantissaBits) spec.minExponent)/2 := by
  have proof := model_add_dyadic_local spec left (UnpackedFloat.neg right) leftNormal
    (model_neg_normalized spec right rightNormal) limit
    (by simpa only [model_neg_value, sub_eq_add_neg] using bound)
  simpa only [model_sub_add_neg, model_neg_value, sub_eq_add_neg] using proof

/-- The executing binary64 subtraction agrees with the actual unpacked model when its normalized
result satisfies the packing guard. -/
theorem model_sub64_decoded (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (normal : ModelNormalized Format.binary64 (UnpackedFloat.sub Format.binary64
      (decoded64 left) (decoded64 right)))
    (fits : ModelFits Format.binary64 (UnpackedFloat.sub Format.binary64
      (decoded64 left) (decoded64 right))) :
    decoded64 (left.sub right) =
      UnpackedFloat.sub Format.binary64 (decoded64 left) (decoded64 right) := by
  change unpack Format.binary64 (pack Format.binary64
    (UnpackedFloat.sub Format.binary64 (Float.Model.ofBits left.bits).unpack
      (Float.Model.ofBits right.bits).unpack)) = _
  rw [model_ofBits64_decoded left leftFinite, model_ofBits64_decoded right rightFinite]
  exact model_unpack_pack_normalized _ _ normal fits

/-- Actual binary64 subtraction stays finite with error at most 2^-37 when the exact difference of
its finite inputs has magnitude at most 2^16. -/
theorem binary64_sub_finite_error (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (bound : |numerical64 left - numerical64 right| ≤ 65536) :
    (left.sub right).Finite ∧
      |numerical64 (left.sub right) - (numerical64 left - numerical64 right)| ≤
        1 / 137438953472 := by
  have leftNormal := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rightNormal := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have power : (2 : ℚ) ^ (16 : Int) = 65536 := by norm_num
  have localProof := model_sub_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    leftNormal rightNormal 16 (by simpa only [numerical64, power] using bound)
  have error : |unpackedValue (UnpackedFloat.sub Format.binary64 (decoded64 left)
      (decoded64 right))-(numerical64 left-numerical64 right)| ≤ 1/137438953472 := by
    have radius : (2:ℚ)^(max ((16:Int)+1-Format.binary64.mantissaBits)
        Format.binary64.minExponent)/2 = 1/137438953472 := by
      norm_num [Format.mantissaBits, Format.minExponent]
    simpa only [numerical64, radius] using localProof.2
  have fits := model_local64_fits _ _ localProof.1 bound error
  have exactDecoded := model_sub64_decoded left right leftFinite rightFinite localProof.1 fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [exactDecoded]
    exact model_normalized_finite _ _ localProof.1
  · simpa only [numerical64, exactDecoded] using error

/-- A natural quotient is the floor of its exact rational fraction for every positive denominator.
-/
theorem quotient_fraction_bracket (numerator denominator : Nat) (positive : 0 < denominator) :
    (numerator/denominator : Nat) ≤ (numerator:ℚ)/denominator ∧
      (numerator:ℚ)/denominator < (numerator/denominator : Nat)+1 := by
  have hd : (0:ℚ) < denominator := by exact_mod_cast positive
  have lo : (numerator/denominator : Nat)*denominator ≤ numerator := Nat.div_mul_le_self _ _
  have hi : numerator < ((numerator/denominator : Nat)+1)*denominator := by
    have rem := Nat.mod_lt numerator positive
    have decomp := Nat.mod_add_div numerator denominator
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_comm denominator] at *
    omega
  constructor
  · apply (le_div_iff₀ hd).mpr
    exact_mod_cast lo
  · apply (div_lt_iff₀ hd).mpr
    exact_mod_cast hi

set_option exponentiation.threshold 2048 in
/-- The executing integer quotient truncates the finite numerical value toward its stored sign,
with strict one-unit bounds. -/
theorem numerical64_trunc_signed (value : Binary64) (finite : value.Finite) :
    if value.bits &&& 0x8000000000000000 != 0 then
      (Conversion.trunc64 value : ℚ)-1 < numerical64 value ∧
        numerical64 value ≤ (Conversion.trunc64 value : ℚ)
    else (Conversion.trunc64 value : ℚ) ≤ numerical64 value ∧
      numerical64 value < (Conversion.trunc64 value : ℚ)+1 := by
  have hb := quotient_fraction_bracket (Conversion.magnitudeUnits64 value) (2^1074)
    (Nat.two_pow_pos _)
  rw [numerical64_units value finite, model_word64_sign, Conversion.trunc64_signed_exact]
  have dyadic : (2:ℚ)^(-1074:Int) = ((2:ℚ)^1074)⁻¹ := by
    rw [show (-1074:Int) = -(1074:Nat) from rfl, zpow_neg, zpow_natCast]
  rw [dyadic]
  by_cases sign : (value.bits &&& 0x8000000000000000 != 0) = true
  · simp only [sign, ↓reduceIte, signCoefficient, Int.cast_neg, Int.cast_natCast]
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] at hb
    constructor <;> linarith [hb.1,hb.2]
  · have hf : (value.bits &&& 0x8000000000000000 != 0) = false := by simpa using sign
    simp only [hf, Bool.false_eq_true, ↓reduceIte, signCoefficient, Int.cast_natCast, one_mul]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hb

/-- The actual finite conversion truncates toward numerical zero, including either stored zero
sign. -/
theorem numerical64_trunc_toward_zero (value : Binary64) (finite : value.Finite) :
    if numerical64 value < 0 then
      (Conversion.trunc64 value : ℚ)-1 < numerical64 value ∧
        numerical64 value ≤ (Conversion.trunc64 value : ℚ)
    else (Conversion.trunc64 value : ℚ) ≤ numerical64 value ∧
      numerical64 value < (Conversion.trunc64 value : ℚ)+1 := by
  have signed := numerical64_trunc_signed value finite
  by_cases rawSign : (value.bits &&& 0x8000000000000000 != 0) = true
  · simp only [rawSign, ↓reduceIte] at signed
    have ht : (Conversion.trunc64 value : ℚ) ≤ 0 := by
      rw [Conversion.trunc64_signed_exact]
      simp only [rawSign, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    by_cases negative : numerical64 value < 0
    · simpa only [negative, ↓reduceIte] using signed
    · simp only [negative, ↓reduceIte]
      constructor <;> linarith [signed.2]
  · have rf : (value.bits &&& 0x8000000000000000 != 0) = false := by simpa using rawSign
    simp only [rf, Bool.false_eq_true, ↓reduceIte] at signed
    have ht : (0:ℚ) ≤ (Conversion.trunc64 value : ℚ) := by
      rw [Conversion.trunc64_signed_exact]
      simp only [rf, Bool.false_eq_true, ↓reduceIte, Int.cast_natCast]
      exact Nat.cast_nonneg _
    have positive : ¬ numerical64 value < 0 := by linarith [signed.1]
    simpa only [positive, ↓reduceIte] using signed

/-- Finite truncation never increases the absolute numerical value. -/
theorem numerical64_trunc_abs (value : Binary64) (finite : value.Finite) :
    |(Conversion.trunc64 value : ℚ)| ≤ |numerical64 value| := by
  have bracket := numerical64_trunc_signed value finite
  by_cases sign : (value.bits &&& 0x8000000000000000 != 0) = true
  · simp only [sign, ↓reduceIte] at bracket
    have ht : (Conversion.trunc64 value : ℚ) ≤ 0 := by
      rw [Conversion.trunc64_signed_exact]
      simp only [sign, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    rw [abs_of_nonpos ht, abs_of_nonpos (le_trans bracket.2 ht)]
    linarith [bracket.2]
  · have sf : (value.bits &&& 0x8000000000000000 != 0) = false := by simpa using sign
    simp only [sf, Bool.false_eq_true, ↓reduceIte] at bracket
    have ht : (0:ℚ) ≤ (Conversion.trunc64 value : ℚ) := by
      rw [Conversion.trunc64_signed_exact]
      simp only [sf, Bool.false_eq_true, ↓reduceIte, Int.cast_natCast]
      exact Nat.cast_nonneg _
    rw [abs_of_nonneg ht, abs_of_nonneg (le_trans ht bracket.1)]
    exact bracket.1

/-- The signed 32-bit clamp is inactive whenever the finite source magnitude is at most 2^16. -/
theorem numerical64_toI32_trunc (value : Binary64) (finite : value.Finite)
    (bound : |numerical64 value| ≤ 65536) :
    Conversion.toI32 value = Conversion.trunc64 value := by
  have hb := le_trans (numerical64_trunc_abs value finite) bound
  have lo : -(65536:Int) ≤ Conversion.trunc64 value := by
    have h := (abs_le.mp hb).1
    exact_mod_cast h
  have hi : Conversion.trunc64 value ≤ (65536:Int) := by
    have h := (abs_le.mp hb).2
    exact_mod_cast h
  rw [Conversion.toI32_eq_signedCast, Conversion.signedCast_finite _ value finite]
  unfold Conversion.clampInt
  omega

end AcornVerif.CurrentOperations
