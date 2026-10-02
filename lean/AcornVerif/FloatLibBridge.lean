/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentDivision
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

/-!
# Bridge from Acorn's machine words to FloatLib's real-valued rounding

Acorn's binary32 and binary64 arithmetic is Lean core's `Float32` and `Float`
applied to raw words, and `AcornVerif.CurrentArithmetic` reads those words
through the pinned Lean 4.34.0 model `Float.Model.UnpackedFloat`. FloatLib
(R. J. George, W. Adkisson and A. Anandkumar, *FloatLib*, 2026,
https://github.com/lean-dojo/FloatLib, commit `1e83f09`) proves real-valued
statements about that same model. This module is the only importer of
FloatLib. It connects the executing Acorn definitions to FloatLib's by proof,
so FloatLib's theorems apply to them; no executable definition changes.

The representation map views the same bits as FloatLib's `Model`. Both sides
unpack them with Lean core's decoder, so the map agrees with `decoded64` and
`decoded32` by definition. The operation theorems instantiate, from
`FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/LeanModel.lean`,
`toReal_ofModel_add_finite_eq_roundAt`, `toReal_ofModel_mul_finite_eq_roundAt`
and `toReal_ofModel_div_finite_eq_roundAt`. The multiplication and division
theorems there assume an exponent inequality for Lean core's
`roundWithAccuracy`; `model_product_exponent_ready` and `model_divCore_ready`
supply it for every canonically unpacked operand. The division theorem there
also assumes a nonzero provisional quotient, which holds exactly when the
exact quotient is at least the least positive subnormal; that condition is a
hypothesis of the division statements here.

The first consumers follow. The half-unit division bound uses the half-ulp
theorem `error_bound_ulp` of FloatLib's Flocq layer
(`FloatLib/Floats/Formats/Flocq/Theory/Rounding/Core.lean`). The decimal
constants use `toReal_roundRatScaled_eq_roundAt`
(`.../DirectedSemantics/Rational/RoundingSemantics/Executable.lean`): each word
equality with FloatLib's executable rational rounder is a closed computation
checked by the kernel, and that theorem gives it its real meaning.

Each statement concerns finite operands and a finite result: `roundAt` rounds
on a grid with no upper exponent bound, and exceptional words have no real
value. Native primitive and compiler correspondence remain the arithmetic
layer's declared trust boundary.
-/

open Acorn
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOperations AcornVerif.CurrentDivision
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model
open FloatLib.Floats.Formats (Flocq.bpow)
open FloatLib.Floats.Formats.Flocq (ulp ulp_abs ulp_bpow ulp_mono_pos error_bound_ulp
  nearestEven MonotoneExp)

namespace AcornVerif.FloatLibBridge

/-! ## Format-generic statements about Lean core's unpacked model -/

/-- Acorn's rational reading and FloatLib's real reading of an unpacked value
are the same number; both send exceptional constructors to zero. -/
theorem unpackedToReal_eq (value : UnpackedFloat) :
    unpackedToReal value = ((unpackedValue value : ℚ) : ℝ) := by
  cases value with
  | notANumber => simp [unpackedToReal, unpackedToDyadic?, unpackedValue]
  | infinity sign => simp [unpackedToReal, unpackedToDyadic?, unpackedValue]
  | zero sign => simp [unpackedValue]
  | finite sign mantissa exponent positive =>
    cases sign <;>
      simp [unpackedToReal, unpackedToDyadic?, unpackedValue, signCoefficient,
        FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand,
        modelSignBit]

/-- Packing a canonical value that fits the format and reading it back through
FloatLib's `toReal` returns its real value. -/
theorem toReal_ofModel_fits (fmt : FloatFormat) (ieee : fmt.isIEEE = true)
    (value : UnpackedFloat) (normal : ModelNormalized fmt.toModel value)
    (fits : ModelFits fmt.toModel value) :
    toReal (ofModel fmt value) = unpackedToReal value := by
  rw [toReal_eq_unpackedToReal_toModel ieee]
  change unpackedToReal (unpack fmt.toModel (pack fmt.toModel value)) = _
  rw [model_unpack_pack_normalized _ _ normal fits]

/-- Lean core's unpacked multiplication of canonical finite operands, when its
packed result is finite, is the exact real product rounded once to nearest-even. -/
theorem mul_roundAt (fmt : FloatFormat) (ieee : fmt.isIEEE = true)
    (left right : UnpackedFloat) (leftFinite : left.isFinite = true)
    (rightFinite : right.isFinite = true)
    (leftNormal : ModelNormalized fmt.toModel left)
    (rightNormal : ModelNormalized fmt.toModel right)
    (finite : isFinite (ofModel fmt (UnpackedFloat.mul fmt.toModel left right)) = true) :
    toReal (ofModel fmt (UnpackedFloat.mul fmt.toModel left right)) =
      roundAt fmt (unpackedToReal left * unpackedToReal right) := by
  cases left with
  | notANumber => simp [UnpackedFloat.isFinite] at leftFinite
  | infinity sign => simp [UnpackedFloat.isFinite] at leftFinite
  | zero sign =>
    cases right with
    | notANumber => simp [UnpackedFloat.isFinite] at rightFinite
    | infinity sign' => simp [UnpackedFloat.isFinite] at rightFinite
    | zero sign' =>
      simp only [UnpackedFloat.mul, unpackedToReal_zero, zero_mul, roundAt_zero]
      exact toReal_ofModel_zero _ ieee _
    | finite sign' mantissa' exponent' positive' =>
      simp only [UnpackedFloat.mul, unpackedToReal_zero, zero_mul, roundAt_zero]
      exact toReal_ofModel_zero _ ieee _
  | finite sign mantissa exponent positive =>
    cases right with
    | notANumber => simp [UnpackedFloat.isFinite] at rightFinite
    | infinity sign' => simp [UnpackedFloat.isFinite] at rightFinite
    | zero sign' =>
      simp only [UnpackedFloat.mul, unpackedToReal_zero, mul_zero, roundAt_zero]
      exact toReal_ofModel_zero _ ieee _
    | finite sign' mantissa' exponent' positive' =>
      exact toReal_ofModel_mul_finite_eq_roundAt fmt ieee sign sign' mantissa mantissa'
        exponent exponent' positive positive'
        (model_product_exponent_ready fmt.toModel mantissa mantissa' exponent exponent'
          sign sign' positive positive' leftNormal rightNormal) finite

/-- Lean core's unpacked addition of canonical finite operands that fit the
format, when its packed result is finite, is the exact real sum rounded once to
nearest-even. A zero operand returns the other operand, which is already on the
format's grid. -/
theorem add_roundAt (fmt : FloatFormat) (ieee : fmt.isIEEE = true)
    (left right : UnpackedFloat) (leftFinite : left.isFinite = true)
    (rightFinite : right.isFinite = true)
    (leftNormal : ModelNormalized fmt.toModel left) (leftFits : ModelFits fmt.toModel left)
    (rightNormal : ModelNormalized fmt.toModel right) (rightFits : ModelFits fmt.toModel right)
    (finite : isFinite (ofModel fmt (UnpackedFloat.add fmt.toModel left right)) = true) :
    toReal (ofModel fmt (UnpackedFloat.add fmt.toModel left right)) =
      roundAt fmt (unpackedToReal left + unpackedToReal right) := by
  cases left with
  | notANumber => simp [UnpackedFloat.isFinite] at leftFinite
  | infinity sign => simp [UnpackedFloat.isFinite] at leftFinite
  | zero sign =>
    cases right with
    | notANumber => simp [UnpackedFloat.isFinite] at rightFinite
    | infinity sign' => simp [UnpackedFloat.isFinite] at rightFinite
    | zero sign' =>
      simp only [UnpackedFloat.add, unpackedToReal_zero, add_zero, roundAt_zero]
      split <;> exact toReal_ofModel_zero _ ieee _
    | finite sign' mantissa' exponent' positive' =>
      have value := toReal_ofModel_fits fmt ieee _ rightNormal rightFits
      simp only [UnpackedFloat.add] at finite ⊢
      rw [unpackedToReal_zero, zero_add, ← value]
      exact (roundAt_toReal_eq _ finite).symm
  | finite sign mantissa exponent positive =>
    cases right with
    | notANumber => simp [UnpackedFloat.isFinite] at rightFinite
    | infinity sign' => simp [UnpackedFloat.isFinite] at rightFinite
    | zero sign' =>
      have value := toReal_ofModel_fits fmt ieee _ leftNormal leftFits
      simp only [UnpackedFloat.add] at finite ⊢
      rw [unpackedToReal_zero, add_zero, ← value]
      exact (roundAt_toReal_eq _ finite).symm
    | finite sign' mantissa' exponent' positive' =>
      exact toReal_ofModel_add_finite_eq_roundAt fmt ieee sign sign' mantissa mantissa'
        exponent exponent' positive positive' finite

/-- Sign change keeps a finite value finite. -/
theorem neg_isFinite (value : UnpackedFloat) (finite : value.isFinite = true) :
    (UnpackedFloat.neg value).isFinite = true := by
  cases value <;> exact finite

/-- Sign change keeps the packing exponent guard. -/
theorem neg_fits (spec : Format) (value : UnpackedFloat) (fits : ModelFits spec value) :
    ModelFits spec (UnpackedFloat.neg value) := by
  cases value <;> exact fits

/-- Sign change negates FloatLib's real reading. -/
theorem unpackedToReal_neg (value : UnpackedFloat) :
    unpackedToReal (UnpackedFloat.neg value) = -unpackedToReal value := by
  rw [unpackedToReal_eq, unpackedToReal_eq, model_neg_value, Rat.cast_neg]

/-- Lean core's unpacked subtraction of canonical finite operands that fit the
format, when its packed result is finite, is the exact real difference rounded
once to nearest-even. -/
theorem sub_roundAt (fmt : FloatFormat) (ieee : fmt.isIEEE = true)
    (left right : UnpackedFloat) (leftFinite : left.isFinite = true)
    (rightFinite : right.isFinite = true)
    (leftNormal : ModelNormalized fmt.toModel left) (leftFits : ModelFits fmt.toModel left)
    (rightNormal : ModelNormalized fmt.toModel right) (rightFits : ModelFits fmt.toModel right)
    (finite : isFinite (ofModel fmt (UnpackedFloat.sub fmt.toModel left right)) = true) :
    toReal (ofModel fmt (UnpackedFloat.sub fmt.toModel left right)) =
      roundAt fmt (unpackedToReal left - unpackedToReal right) := by
  rw [model_sub_add_neg] at finite ⊢
  rw [sub_eq_add_neg, ← unpackedToReal_neg]
  exact add_roundAt fmt ieee left _ leftFinite (neg_isFinite right rightFinite) leftNormal
    leftFits (model_neg_normalized _ right rightNormal) (neg_fits _ right rightFits) finite

/-- The magnitude of a quotient of signed dyadic values is the quotient of their
positive significands at the exponent difference. -/
theorem abs_ratio (leftSign rightSign : Sign) (left right : Nat)
    (leftExponent rightExponent : Int) (leftPositive : 0 < left) (rightPositive : 0 < right) :
    |(signCoefficient leftSign * left * (2 : ℚ) ^ leftExponent) /
        (signCoefficient rightSign * right * (2 : ℚ) ^ rightExponent)| =
      ((left : ℚ) / right) * (2 : ℚ) ^ (leftExponent - rightExponent) := by
  have ratio := model_ratio_positive left right leftExponent rightExponent leftPositive
    rightPositive
  rw [model_signed_ratio, mul_assoc, abs_mul, abs_of_pos ratio]
  cases leftSign / rightSign <;> simp [signCoefficient]

/-- Lean core's unpacked division of canonical finite operands by a nonzero
divisor, when the exact quotient is zero or at least the least positive
subnormal and the packed result is finite, is the exact real quotient rounded
once to nearest-even. Below the least subnormal the division core produces no
significant bit, the case FloatLib's theorem leaves out. -/
theorem div_roundAt (fmt : FloatFormat) (ieee : fmt.isIEEE = true)
    (left right : UnpackedFloat) (leftFinite : left.isFinite = true)
    (rightFinite : right.isFinite = true)
    (leftNormal : ModelNormalized fmt.toModel left)
    (rightNormal : ModelNormalized fmt.toModel right)
    (nonzero : unpackedValue right ≠ 0)
    (resolved : unpackedValue left = 0 ∨
      (2 : ℚ) ^ fmt.toModel.minExponent ≤ |unpackedValue left / unpackedValue right|)
    (finite : isFinite (ofModel fmt (UnpackedFloat.div fmt.toModel left right)) = true) :
    toReal (ofModel fmt (UnpackedFloat.div fmt.toModel left right)) =
      roundAt fmt (unpackedToReal left / unpackedToReal right) := by
  cases right with
  | notANumber => simp [UnpackedFloat.isFinite] at rightFinite
  | infinity sign' => simp [UnpackedFloat.isFinite] at rightFinite
  | zero sign' => exact absurd rfl nonzero
  | finite sign' mantissa' exponent' positive' =>
    cases left with
    | notANumber => simp [UnpackedFloat.isFinite] at leftFinite
    | infinity sign => simp [UnpackedFloat.isFinite] at leftFinite
    | zero sign =>
      simp only [UnpackedFloat.div, unpackedToReal_zero, zero_div, roundAt_zero]
      exact toReal_ofModel_zero _ ieee _
    | finite sign mantissa exponent positive =>
      let core := divCore fmt.toModel mantissa exponent mantissa' exponent'
      let ratio := ((mantissa : ℚ) / mantissa') * (2 : ℚ) ^ (exponent - exponent')
      have ready := model_divCore_ready fmt.toModel mantissa mantissa' exponent exponent'
        positive positive'
      have bracket := model_divCore_bracket fmt.toModel mantissa mantissa' exponent
        exponent' positive'
      change (if core.1 = 0 then core.2.1 ≤ fmt.toModel.minExponent
        else core.2.1 ≤ fmt.toModel.targetExponent
          (Float.Model.totalExponent core.1 core.2.1)) at ready
      change core.2.1 ≤ exponent - exponent' ∧ _ ∧ (core.1 : ℚ) * (2 : ℚ) ^ core.2.1 ≤ ratio ∧
        ratio < ((core.1 : ℚ) + 1) * (2 : ℚ) ^ core.2.1 at bracket
      have significant : core.1 ≠ 0 := by
        intro zero
        rw [ite_eq_left zero] at ready
        have upper : ratio < (2 : ℚ) ^ core.2.1 := by
          simpa only [zero, Nat.cast_zero, zero_add, one_mul] using bracket.2.2.2
        have floor : (2 : ℚ) ^ core.2.1 ≤ (2 : ℚ) ^ fmt.toModel.minExponent :=
          zpow_le_zpow_right₀ (by norm_num) ready
        rcases resolved with value | lower
        · have nonzeroValue : unpackedValue (.finite sign mantissa exponent positive) ≠ 0 := by
            have mantissaPositive : (0 : ℚ) < mantissa := by exact_mod_cast positive
            have power : (0 : ℚ) < (2 : ℚ) ^ exponent := zpow_pos (by norm_num) _
            cases sign <;> simp only [unpackedValue, signCoefficient] <;> nlinarith
          exact nonzeroValue value
        · rw [show |unpackedValue (.finite sign mantissa exponent positive) /
              unpackedValue (.finite sign' mantissa' exponent' positive')| = ratio from
            abs_ratio sign sign' mantissa mantissa' exponent exponent' positive positive'] at lower
          linarith
      rw [ite_eq_right significant] at ready
      exact toReal_ofModel_div_finite_eq_roundAt fmt ieee sign sign' mantissa mantissa'
        exponent exponent' positive positive' significant ready finite

/-! ## Binary64 -/

/-- The same 64 bits, viewed as FloatLib's `Model`. -/
def model64 (value : Binary64) : Model FloatFormat.binary64 := ⟨value.bits.toBitVec⟩

/-- FloatLib's binary64 descriptor denotes Lean core's binary64 format. -/
theorem format64 : FloatFormat.binary64.toModel = Format.binary64 := rfl

/-- Both sides unpack the same word with Lean core's decoder. -/
theorem toModel_model64 (value : Binary64) : toModel (model64 value) = decoded64 value := rfl

/-- FloatLib's real reading of the word is Acorn's rational reading, on every
word: both send exceptional words to zero. -/
theorem toReal_model64 (value : Binary64) :
    toReal (model64 value) = ((numerical64 value : ℚ) : ℝ) := by
  rw [toReal_eq_unpackedToReal_toModel rfl, toModel_model64, unpackedToReal_eq]
  rfl

/-- FloatLib's finiteness test on the word is Acorn's raw-word `Finite`. -/
theorem isFinite_model64 (value : Binary64) :
    isFinite (model64 value) = true ↔ value.Finite := by
  rw [← model_decoded64_finite value, decoded64, model_unpack_finite_exponent]
  have field := unpackExponent_toNat (model64 value)
  change (unpackExponent (spec := Format.binary64) value.bits.toBitVec).toNat =
    expField (model64 value) at field
  rw [field]
  have bound : expField (model64 value) < 2048 := expField_lt_pow2 (model64 value)
  have power : (2 : Nat) ^ Format.binary64.exponentBits - 1 = 2047 := rfl
  have ones : FloatFormat.expAllOnesNat FloatFormat.binary64 = 2047 := rfl
  rw [power]
  change IEEE.isFinite (model64 value) = true ↔ _
  unfold IEEE.isFinite
  rw [ones]
  generalize expField (model64 value) = field at bound ⊢
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  omega

/-- Every finite word decodes to canonical components that fit the format. -/
theorem canonical64 (value : Binary64) (finite : value.Finite) :
    (decoded64 value).isFinite = true ∧ ModelNormalized Format.binary64 (decoded64 value) ∧
      ModelFits Format.binary64 (decoded64 value) :=
  ⟨(model_decoded64_finite value).mpr finite,
    model_unpack_format Format.binary64 (by decide) value.bits.toBitVec
      ((model_decoded64_finite value).mpr finite)⟩

/-- On finite operands the executing addition is FloatLib's packing of Lean
core's unpacked sum, word for word. -/
theorem model64_add (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.add right) = ofModel FloatFormat.binary64
      (UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

/-- On finite operands the executing subtraction is FloatLib's packing of Lean
core's unpacked difference, word for word. -/
theorem model64_sub (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.sub right) = ofModel FloatFormat.binary64
      (UnpackedFloat.sub Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

/-- On finite operands the executing multiplication is FloatLib's packing of
Lean core's unpacked product, word for word. -/
theorem model64_mul (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.mul right) = ofModel FloatFormat.binary64
      (UnpackedFloat.mul Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

/-- On finite operands the executing division is FloatLib's packing of Lean
core's unpacked quotient, word for word. -/
theorem model64_div (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.div right) = ofModel FloatFormat.binary64
      (UnpackedFloat.div Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

/-- The executing binary64 addition, on finite operands with a finite result,
is the exact real sum rounded once to nearest-even. -/
theorem binary64_add_roundAt (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.add right).Finite) :
    ((numerical64 (left.add right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary64 ((numerical64 left : ℝ) + (numerical64 right : ℝ)) := by
  have l := canonical64 left leftFinite
  have r := canonical64 right rightFinite
  have packed := model64_add left right leftFinite rightFinite
  have packedFinite := (isFinite_model64 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary64
      (UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64 right))) =
      roundAt FloatFormat.binary64
        (unpackedToReal (decoded64 left) + unpackedToReal (decoded64 right)) :=
    add_roundAt FloatFormat.binary64 rfl (decoded64 left) (decoded64 right)
      l.1 r.1 l.2.1 l.2.2 r.2.1 r.2.2 packedFinite
  rw [← packed, toReal_model64, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-- The executing binary64 subtraction, on finite operands with a finite
result, is the exact real difference rounded once to nearest-even. -/
theorem binary64_sub_roundAt (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.sub right).Finite) :
    ((numerical64 (left.sub right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary64 ((numerical64 left : ℝ) - (numerical64 right : ℝ)) := by
  have l := canonical64 left leftFinite
  have r := canonical64 right rightFinite
  have packed := model64_sub left right leftFinite rightFinite
  have packedFinite := (isFinite_model64 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary64
      (UnpackedFloat.sub Format.binary64 (decoded64 left) (decoded64 right))) =
      roundAt FloatFormat.binary64
        (unpackedToReal (decoded64 left) - unpackedToReal (decoded64 right)) :=
    sub_roundAt FloatFormat.binary64 rfl (decoded64 left) (decoded64 right)
      l.1 r.1 l.2.1 l.2.2 r.2.1 r.2.2 packedFinite
  rw [← packed, toReal_model64, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-- The executing binary64 multiplication, on finite operands with a finite
result, is the exact real product rounded once to nearest-even. -/
theorem binary64_mul_roundAt (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.mul right).Finite) :
    ((numerical64 (left.mul right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary64 ((numerical64 left : ℝ) * (numerical64 right : ℝ)) := by
  have l := canonical64 left leftFinite
  have r := canonical64 right rightFinite
  have packed := model64_mul left right leftFinite rightFinite
  have packedFinite := (isFinite_model64 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary64
      (UnpackedFloat.mul Format.binary64 (decoded64 left) (decoded64 right))) =
      roundAt FloatFormat.binary64
        (unpackedToReal (decoded64 left) * unpackedToReal (decoded64 right)) :=
    mul_roundAt FloatFormat.binary64 rfl (decoded64 left) (decoded64 right)
      l.1 r.1 l.2.1 r.2.1 packedFinite
  rw [← packed, toReal_model64, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-- The executing binary64 division by a nonzero finite divisor, when the
exact quotient is zero or at least the least positive subnormal `2^(-1074)`
and the result is finite, is the exact real quotient rounded once to
nearest-even. -/
theorem binary64_div_roundAt (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonzero : numerical64 right ≠ 0)
    (resolved : numerical64 left = 0 ∨
      (2 : ℚ) ^ (-1074 : Int) ≤ |numerical64 left / numerical64 right|)
    (finite : (left.div right).Finite) :
    ((numerical64 (left.div right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary64 ((numerical64 left : ℝ) / (numerical64 right : ℝ)) := by
  have l := canonical64 left leftFinite
  have r := canonical64 right rightFinite
  have packed := model64_div left right leftFinite rightFinite
  have packedFinite := (isFinite_model64 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary64
      (UnpackedFloat.div Format.binary64 (decoded64 left) (decoded64 right))) =
      roundAt FloatFormat.binary64
        (unpackedToReal (decoded64 left) / unpackedToReal (decoded64 right)) :=
    div_roundAt FloatFormat.binary64 rfl (decoded64 left) (decoded64 right)
      l.1 r.1 l.2.1 r.2.1 nonzero resolved packedFinite
  rw [← packed, toReal_model64, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-! ## Binary32 -/

/-- The same 32 bits, viewed as FloatLib's `Model`. -/
def model32 (value : Binary32) : Model FloatFormat.binary32 := ⟨value.bits.toBitVec⟩

/-- FloatLib's binary32 descriptor denotes Lean core's binary32 format. -/
theorem format32 : FloatFormat.binary32.toModel = Format.binary32 := rfl

/-- Both sides unpack the same word with Lean core's decoder. -/
theorem toModel_model32 (value : Binary32) : toModel (model32 value) = decoded32 value := rfl

/-- FloatLib's real reading of the word is Acorn's rational reading, on every
word: both send exceptional words to zero. -/
theorem toReal_model32 (value : Binary32) :
    toReal (model32 value) = ((numerical32 value : ℚ) : ℝ) := by
  rw [toReal_eq_unpackedToReal_toModel rfl, toModel_model32, unpackedToReal_eq]
  rfl

/-- FloatLib's finiteness test on the word is Acorn's raw-word `Finite`. -/
theorem isFinite_model32 (value : Binary32) :
    isFinite (model32 value) = true ↔ value.Finite := by
  rw [← model_decoded32_finite value, decoded32, model_unpack_finite_exponent]
  have field := unpackExponent_toNat (model32 value)
  change (unpackExponent (spec := Format.binary32) value.bits.toBitVec).toNat =
    expField (model32 value) at field
  rw [field]
  have bound : expField (model32 value) < 256 := expField_lt_pow2 (model32 value)
  have power : (2 : Nat) ^ Format.binary32.exponentBits - 1 = 255 := rfl
  have ones : FloatFormat.expAllOnesNat FloatFormat.binary32 = 255 := rfl
  rw [power]
  change IEEE.isFinite (model32 value) = true ↔ _
  unfold IEEE.isFinite
  rw [ones]
  generalize expField (model32 value) = field at bound ⊢
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  omega

/-- Every finite word decodes to canonical components that fit the format. -/
theorem canonical32 (value : Binary32) (finite : value.Finite) :
    (decoded32 value).isFinite = true ∧ ModelNormalized Format.binary32 (decoded32 value) ∧
      ModelFits Format.binary32 (decoded32 value) :=
  ⟨(model_decoded32_finite value).mpr finite,
    model_unpack_format Format.binary32 (by decide) value.bits.toBitVec
      ((model_decoded32_finite value).mpr finite)⟩

/-- On finite operands the executing addition is FloatLib's packing of Lean
core's unpacked sum, word for word. -/
theorem model32_add (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.add right) = ofModel FloatFormat.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

/-- On finite operands the executing subtraction is FloatLib's packing of Lean
core's unpacked difference, word for word. -/
theorem model32_sub (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.sub right) = ofModel FloatFormat.binary32
      (UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

/-- On finite operands the executing multiplication is FloatLib's packing of
Lean core's unpacked product, word for word. -/
theorem model32_mul (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.mul right) = ofModel FloatFormat.binary32
      (UnpackedFloat.mul Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

/-- On finite operands the executing division is FloatLib's packing of Lean
core's unpacked quotient, word for word. -/
theorem model32_div (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.div right) = ofModel FloatFormat.binary32
      (UnpackedFloat.div Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

/-- The executing binary32 addition, on finite operands with a finite result,
is the exact real sum rounded once to nearest-even. -/
theorem binary32_add_roundAt (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.add right).Finite) :
    ((numerical32 (left.add right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 ((numerical32 left : ℝ) + (numerical32 right : ℝ)) := by
  have l := canonical32 left leftFinite
  have r := canonical32 right rightFinite
  have packed := model32_add left right leftFinite rightFinite
  have packedFinite := (isFinite_model32 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right))) =
      roundAt FloatFormat.binary32
        (unpackedToReal (decoded32 left) + unpackedToReal (decoded32 right)) :=
    add_roundAt FloatFormat.binary32 rfl (decoded32 left) (decoded32 right)
      l.1 r.1 l.2.1 l.2.2 r.2.1 r.2.2 packedFinite
  rw [← packed, toReal_model32, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-- The executing binary32 subtraction, on finite operands with a finite
result, is the exact real difference rounded once to nearest-even. -/
theorem binary32_sub_roundAt (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.sub right).Finite) :
    ((numerical32 (left.sub right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 ((numerical32 left : ℝ) - (numerical32 right : ℝ)) := by
  have l := canonical32 left leftFinite
  have r := canonical32 right rightFinite
  have packed := model32_sub left right leftFinite rightFinite
  have packedFinite := (isFinite_model32 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary32
      (UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right))) =
      roundAt FloatFormat.binary32
        (unpackedToReal (decoded32 left) - unpackedToReal (decoded32 right)) :=
    sub_roundAt FloatFormat.binary32 rfl (decoded32 left) (decoded32 right)
      l.1 r.1 l.2.1 l.2.2 r.2.1 r.2.2 packedFinite
  rw [← packed, toReal_model32, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-- The executing binary32 multiplication, on finite operands with a finite
result, is the exact real product rounded once to nearest-even. -/
theorem binary32_mul_roundAt (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.mul right).Finite) :
    ((numerical32 (left.mul right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 ((numerical32 left : ℝ) * (numerical32 right : ℝ)) := by
  have l := canonical32 left leftFinite
  have r := canonical32 right rightFinite
  have packed := model32_mul left right leftFinite rightFinite
  have packedFinite := (isFinite_model32 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary32
      (UnpackedFloat.mul Format.binary32 (decoded32 left) (decoded32 right))) =
      roundAt FloatFormat.binary32
        (unpackedToReal (decoded32 left) * unpackedToReal (decoded32 right)) :=
    mul_roundAt FloatFormat.binary32 rfl (decoded32 left) (decoded32 right)
      l.1 r.1 l.2.1 r.2.1 packedFinite
  rw [← packed, toReal_model32, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-- The executing binary32 division by a nonzero finite divisor, when the
exact quotient is zero or at least the least positive subnormal `2^(-149)`
and the result is finite, is the exact real quotient rounded once to
nearest-even. -/
theorem binary32_div_roundAt (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonzero : numerical32 right ≠ 0)
    (resolved : numerical32 left = 0 ∨
      (2 : ℚ) ^ (-149 : Int) ≤ |numerical32 left / numerical32 right|)
    (finite : (left.div right).Finite) :
    ((numerical32 (left.div right) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 ((numerical32 left : ℝ) / (numerical32 right : ℝ)) := by
  have l := canonical32 left leftFinite
  have r := canonical32 right rightFinite
  have packed := model32_div left right leftFinite rightFinite
  have packedFinite := (isFinite_model32 _).mpr finite
  rw [packed] at packedFinite
  have result : toReal (ofModel FloatFormat.binary32
      (UnpackedFloat.div Format.binary32 (decoded32 left) (decoded32 right))) =
      roundAt FloatFormat.binary32
        (unpackedToReal (decoded32 left) / unpackedToReal (decoded32 right)) :=
    div_roundAt FloatFormat.binary32 rfl (decoded32 left) (decoded32 right)
      l.1 r.1 l.2.1 r.2.1 nonzero resolved packedFinite
  rw [← packed, toReal_model32, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

/-! ## First consumers -/

/-- Nearest-even rounding to binary64 moves a real of magnitude at most `2^16`
by at most half the grid spacing at that magnitude, `2^(-37)`. -/
theorem roundAt64_error (x : ℝ) (bound : |x| ≤ 65536) :
    |roundAt FloatFormat.binary64 x - x| ≤ 1 / 137438953472 := by
  by_cases zero : x = 0
  · rw [zero, roundAt_zero]
    norm_num
  have monotone : MonotoneExp (fexpOf FloatFormat.binary64) :=
    ⟨fun _ _ order => max_le_max (sub_le_sub_right order _) le_rfl⟩
  have half := error_bound_ulp (β := FloatLib.Numerics.binaryRadix)
    (fexp := fexpOf FloatFormat.binary64) nearestEven x
  have power : Flocq.bpow FloatLib.Numerics.binaryRadix 16 = 65536 := by
    norm_num [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  have exponent : fexpOf FloatFormat.binary64 (16 + 1) = -36 := by decide
  have spacing : ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary64) x ≤
      1 / 68719476736 := by
    rw [← ulp_abs]
    calc
      ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary64) |x| ≤
          ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary64)
            (Flocq.bpow FloatLib.Numerics.binaryRadix 16) :=
        ulp_mono_pos (abs_pos.mpr zero) (by rw [power]; exact bound)
      _ = Flocq.bpow FloatLib.Numerics.binaryRadix (-36) := by rw [ulp_bpow, exponent]
      _ = 1 / 68719476736 := by
        norm_num [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  calc
    |roundAt FloatFormat.binary64 x - x| ≤
        ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary64) x / 2 := half
    _ ≤ 1 / 137438953472 := by linarith

/-- The executing binary64 division stays finite and is within half the grid
spacing, `2^(-37)`, of the exact quotient whenever that quotient has magnitude
at most `2^16`. This is one quarter of the two-unit radius in
`binary64_div_finite_error`, under the same hypotheses. A quotient of magnitude
at least the least positive subnormal is correctly rounded by
`binary64_div_roundAt`; a smaller one is within `2^(-1073)` by the executing
division core's own bound. -/
theorem binary64_div_half_unit_error (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonzero : numerical64 right ≠ 0)
    (bound : |numerical64 left / numerical64 right| ≤ 65536) :
    (left.div right).Finite ∧
      |numerical64 (left.div right) - numerical64 left / numerical64 right| ≤
        1 / 137438953472 := by
  have finite := (binary64_div_finite_error left right leftFinite rightFinite nonzero bound).1
  refine ⟨finite, ?_⟩
  by_cases resolved : numerical64 left = 0 ∨
      (2 : ℚ) ^ (-1074 : Int) ≤ |numerical64 left / numerical64 right|
  · have rounded := binary64_div_roundAt left right leftFinite rightFinite nonzero resolved
      finite
    have realBound : |(numerical64 left : ℝ) / (numerical64 right : ℝ)| ≤ 65536 := by
      exact_mod_cast bound
    have error := roundAt64_error _ realBound
    rw [← rounded] at error
    exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)
  · have tiny : |numerical64 left / numerical64 right| ≤ (2 : ℚ) ^ (-1074 : Int) :=
      le_of_lt (not_le.mp (not_or.mp resolved).2)
    have l := canonical64 left leftFinite
    have r := canonical64 right rightFinite
    have localProof := model_div_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
      l.2.1 r.2.1 nonzero (-1074) tiny
    have radius : 2 * (2 : ℚ) ^ (max ((-1074 : Int) + 1 - Format.binary64.mantissaBits)
        Format.binary64.minExponent) = (2 : ℚ) ^ (-1073 : Int) := by
      rw [show max ((-1074 : Int) + 1 - Format.binary64.mantissaBits)
        Format.binary64.minExponent = -1074 from by decide,
        show (-1073 : Int) = 1 + -1074 from rfl, zpow_add₀ (by norm_num), zpow_one]
    have small : (2 : ℚ) ^ (-1073 : Int) ≤ 1 / 137438953472 := by
      calc
        (2 : ℚ) ^ (-1073 : Int) ≤ (2 : ℚ) ^ (-37 : Int) :=
          zpow_le_zpow_right₀ (by norm_num) (by norm_num)
        _ = 1 / 137438953472 := by norm_num
    have error : |unpackedValue (UnpackedFloat.div Format.binary64 (decoded64 left)
        (decoded64 right)) - numerical64 left / numerical64 right| ≤ (2 : ℚ) ^ (-1073 : Int) := by
      simpa only [numerical64, radius] using localProof.2
    have fits : ModelFits Format.binary64 (UnpackedFloat.div Format.binary64 (decoded64 left)
        (decoded64 right)) := by
      apply model_fits_of_value_bound Format.binary64 _
        (model_normalized_finite _ _ localProof.1) 17 (by decide)
      have triangle := abs_add_le
        (unpackedValue (UnpackedFloat.div Format.binary64 (decoded64 left) (decoded64 right)) -
          numerical64 left / numerical64 right) (numerical64 left / numerical64 right)
      rw [sub_add_cancel] at triangle
      have large : (65536 : ℚ) + 1 / 137438953472 ≤ (2 : ℚ) ^ (17 : Int) := by norm_num
      linarith
    have exactDecoded := model_div64_decoded left right leftFinite rightFinite localProof.1 fits
    have result : |numerical64 (left.div right) - numerical64 left / numerical64 right| ≤
        (2 : ℚ) ^ (-1073 : Int) := by
      simpa only [numerical64, exactDecoded] using error
    exact le_trans result small

/-- Acorn's integer nearest-even quotient and FloatLib's are the same function,
so FloatLib's quotient-rounding theorems apply to the executing word paths. -/
theorem nearestEven_eq_roundQuotientEven (numerator denominator : Nat) :
    Rounding.nearestEven numerator denominator =
      FloatLib.Numerics.roundQuotientEven numerator denominator := by
  unfold Rounding.nearestEven FloatLib.Numerics.roundQuotientEven
  dsimp only
  have parity := Nat.mod_two_eq_zero_or_one (numerator / denominator)
  by_cases below : 2 * (numerator % denominator) < denominator
  · have stay : ¬ (denominator < 2 * (numerator % denominator) ∨
        (denominator = 2 * (numerator % denominator) ∧ numerator / denominator % 2 = 1)) := by
      omega
    rw [ite_eq_right stay, ite_eq_left below]
  · by_cases above : denominator < 2 * (numerator % denominator)
    · rw [ite_eq_left (Or.inl above), ite_eq_right below, ite_eq_left above]
    · rw [ite_eq_right below, ite_eq_right above]
      rcases parity with even | odd
      · have stay : ¬ (denominator < 2 * (numerator % denominator) ∨
            (denominator = 2 * (numerator % denominator) ∧
              numerator / denominator % 2 = 1)) := by omega
        rw [ite_eq_right stay]
        simp [even]
      · have up : denominator < 2 * (numerator % denominator) ∨
            (denominator = 2 * (numerator % denominator) ∧
              numerator / denominator % 2 = 1) := by omega
        rw [ite_eq_left up]
        simp [odd]

/-- A finite binary32 word that FloatLib's executable rational rounder returns
for a positive fraction has, as its value, that fraction rounded once to
nearest-even. The word equality is a closed computation; the real statement is
FloatLib's `toReal_roundRatScaled_eq_roundAt`. -/
theorem nearest32 (word : UInt32) (numerator denominator : Nat) (value : ℝ)
    (finite : (Binary32.mk word).Finite) (numeratorPositive : numerator ≠ 0)
    (denominatorPositive : denominator ≠ 0)
    (exact : (numerator : ℝ) / (denominator : ℝ) = value)
    (rounded : (roundRat FloatFormat.binary32 false numerator denominator).bits.toNat =
      word.toNat) :
    ((numerical32 (Binary32.mk word) : ℚ) : ℝ) = roundAt FloatFormat.binary32 value := by
  have same : roundRat FloatFormat.binary32 false numerator denominator =
      model32 (Binary32.mk word) := by
    cases packed : roundRat FloatFormat.binary32 false numerator denominator with
    | mk bits =>
      rw [packed] at rounded
      exact congrArg Model.mk (BitVec.eq_of_toNat_eq rounded)
  have packedFinite := (isFinite_model32 (Binary32.mk word)).mpr finite
  rw [← same] at packedFinite
  have real := toReal_roundRatScaled_eq_roundAt FloatFormat.binary32 false numerator
    denominator 0 rfl numeratorPositive denominatorPositive packedFinite
  change toReal (roundRat FloatFormat.binary32 false numerator denominator) = _ at real
  rw [same, toReal_model32] at real
  rw [real, ← exact]
  congr 1
  simp [signedScaledRatToReal, scaledRatToReal, Model.bpow]

/-! ### Decimal constants

Each binary32 constant in `Acorn.Constants` that names a decimal value is that
value rounded once to nearest-even. `CurrentConstants` records the exact dyadic
value of each word; these theorems tie the word to the decimal it is named for. -/

/-- `band030Bits` is `0.3` rounded to nearest-even binary32. -/
theorem band030_nearest :
    ((numerical32 (Binary32.mk Constants.band030Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.3 :=
  nearest32 Constants.band030Bits 3 10 0.3 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `band0335Bits` is `0.335` rounded to nearest-even binary32. -/
theorem band0335_nearest :
    ((numerical32 (Binary32.mk Constants.band0335Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.335 :=
  nearest32 Constants.band0335Bits 335 1000 0.335 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `band060Bits` is `0.6` rounded to nearest-even binary32. -/
theorem band060_nearest :
    ((numerical32 (Binary32.mk Constants.band060Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.6 :=
  nearest32 Constants.band060Bits 6 10 0.6 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `band072Bits` is `0.72` rounded to nearest-even binary32. -/
theorem band072_nearest :
    ((numerical32 (Binary32.mk Constants.band072Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.72 :=
  nearest32 Constants.band072Bits 72 100 0.72 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `band080Bits` is `0.8` rounded to nearest-even binary32. -/
theorem band080_nearest :
    ((numerical32 (Binary32.mk Constants.band080Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.8 :=
  nearest32 Constants.band080Bits 8 10 0.8 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `moist040Bits` is `0.4` rounded to nearest-even binary32. -/
theorem moist040_nearest :
    ((numerical32 (Binary32.mk Constants.moist040Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.4 :=
  nearest32 Constants.moist040Bits 4 10 0.4 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `gamma90Bits` is `0.9` rounded to nearest-even binary32. -/
theorem gamma90_nearest :
    ((numerical32 (Binary32.mk Constants.gamma90Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.9 :=
  nearest32 Constants.gamma90Bits 9 10 0.9 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `gamma95Bits` is `0.95` rounded to nearest-even binary32. -/
theorem gamma95_nearest :
    ((numerical32 (Binary32.mk Constants.gamma95Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.95 :=
  nearest32 Constants.gamma95Bits 95 100 0.95 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `gamma99Bits` is `0.99` rounded to nearest-even binary32. -/
theorem gamma99_nearest :
    ((numerical32 (Binary32.mk Constants.gamma99Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.99 :=
  nearest32 Constants.gamma99Bits 99 100 0.99 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `alphaInit5e5Bits` is `0.00005` rounded to nearest-even binary32. -/
theorem alphaInit5e5_nearest :
    ((numerical32 (Binary32.mk Constants.alphaInit5e5Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.00005 :=
  nearest32 Constants.alphaInit5e5Bits 5 100000 0.00005 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `alphaInit1e4Bits` is `0.0001` rounded to nearest-even binary32. -/
theorem alphaInit1e4_nearest :
    ((numerical32 (Binary32.mk Constants.alphaInit1e4Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.0001 :=
  nearest32 Constants.alphaInit1e4Bits 1 10000 0.0001 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `epsilon1e5Bits` is `0.00001` rounded to nearest-even binary32. -/
theorem epsilon1e5_nearest :
    ((numerical32 (Binary32.mk Constants.epsilon1e5Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.00001 :=
  nearest32 Constants.epsilon1e5Bits 1 100000 0.00001 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `eta01Bits` is `0.1` rounded to nearest-even binary32. -/
theorem eta01_nearest :
    ((numerical32 (Binary32.mk Constants.eta01Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.1 :=
  nearest32 Constants.eta01Bits 1 10 0.1 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `eta025Bits` is `0.25` rounded to nearest-even binary32. -/
theorem eta025_nearest :
    ((numerical32 (Binary32.mk Constants.eta025Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.25 :=
  nearest32 Constants.eta025Bits 25 100 0.25 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `etaMin1e10Bits` is `0.0000000001` rounded to nearest-even binary32. -/
theorem etaMin1e10_nearest :
    ((numerical32 (Binary32.mk Constants.etaMin1e10Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.0000000001 :=
  nearest32 Constants.etaMin1e10Bits 1 10000000000 0.0000000001 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `decay0999Bits` is `0.999` rounded to nearest-even binary32. -/
theorem decay0999_nearest :
    ((numerical32 (Binary32.mk Constants.decay0999Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.999 :=
  nearest32 Constants.decay0999Bits 999 1000 0.999 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `meta1e3Bits` is `0.001` rounded to nearest-even binary32. -/
theorem meta1e3_nearest :
    ((numerical32 (Binary32.mk Constants.meta1e3Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.001 :=
  nearest32 Constants.meta1e3Bits 1 1000 0.001 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `meta3e2Bits` is `0.03` rounded to nearest-even binary32. -/
theorem meta3e2_nearest :
    ((numerical32 (Binary32.mk Constants.meta3e2Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.03 :=
  nearest32 Constants.meta3e2Bits 3 100 0.03 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `tie1e6Bits` is `0.000001` rounded to nearest-even binary32. -/
theorem tie1e6_nearest :
    ((numerical32 (Binary32.mk Constants.tie1e6Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.000001 :=
  nearest32 Constants.tie1e6Bits 1 1000000 0.000001 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `epsStartBits` is `0.5` rounded to nearest-even binary32. -/
theorem epsStart_nearest :
    ((numerical32 (Binary32.mk Constants.epsStartBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.5 :=
  nearest32 Constants.epsStartBits 5 10 0.5 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `epsMinBits` is `0.05` rounded to nearest-even binary32. -/
theorem epsMin_nearest :
    ((numerical32 (Binary32.mk Constants.epsMinBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.05 :=
  nearest32 Constants.epsMinBits 5 100 0.05 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `epsDecayBits` is `0.99999` rounded to nearest-even binary32. -/
theorem epsDecay_nearest :
    ((numerical32 (Binary32.mk Constants.epsDecayBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.99999 :=
  nearest32 Constants.epsDecayBits 99999 100000 0.99999 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `optionEpsilonBits` is `0.1` rounded to nearest-even binary32. -/
theorem optionEpsilon_nearest :
    ((numerical32 (Binary32.mk Constants.optionEpsilonBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.1 :=
  nearest32 Constants.optionEpsilonBits 1 10 0.1 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

/-- `exploreRate1e2Bits` is `0.01` rounded to nearest-even binary32. -/
theorem exploreRate1e2_nearest :
    ((numerical32 (Binary32.mk Constants.exploreRate1e2Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.01 :=
  nearest32 Constants.exploreRate1e2Bits 1 100 0.01 (by decide) (by decide) (by decide)
    (by norm_num) (by decide +kernel)

end AcornVerif.FloatLibBridge
