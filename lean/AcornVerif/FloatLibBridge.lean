import AcornVerif.CurrentDivision
import Acorn.Host.Geometry
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

open Acorn
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOperations AcornVerif.CurrentDivision
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model
open FloatLib.Floats.Formats (Flocq.bpow)
open FloatLib.Floats.Formats.Flocq (ulp ulp_abs ulp_bpow ulp_mono_pos error_bound_ulp
  nearestEven MonotoneExp magnitude cexp scaledMantissa bpow_magnitude_sub_one_le
  magnitude_eq_of_bpow_bounds nearestEven_eq_floor_of_frac_lt_half
  nearestEven_eq_ceil_of_frac_gt_half)

namespace AcornVerif.FloatLibBridge

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

theorem toReal_ofModel_fits (fmt : FloatFormat) (ieee : fmt.isIEEE = true)
    (value : UnpackedFloat) (normal : ModelNormalized fmt.toModel value)
    (fits : ModelFits fmt.toModel value) :
    toReal (ofModel fmt value) = unpackedToReal value := by
  rw [toReal_eq_unpackedToReal_toModel ieee]
  change unpackedToReal (unpack fmt.toModel (pack fmt.toModel value)) = _
  rw [model_unpack_pack_normalized _ _ normal fits]

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
      exact toReal_ofModel_zero _ (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt ieee) _
    | finite sign' mantissa' exponent' positive' =>
      simp only [UnpackedFloat.mul, unpackedToReal_zero, zero_mul, roundAt_zero]
      exact toReal_ofModel_zero _ (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt ieee) _
  | finite sign mantissa exponent positive =>
    cases right with
    | notANumber => simp [UnpackedFloat.isFinite] at rightFinite
    | infinity sign' => simp [UnpackedFloat.isFinite] at rightFinite
    | zero sign' =>
      simp only [UnpackedFloat.mul, unpackedToReal_zero, mul_zero, roundAt_zero]
      exact toReal_ofModel_zero _ (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt ieee) _
    | finite sign' mantissa' exponent' positive' =>
      exact toReal_ofModel_mul_finite_eq_roundAt fmt ieee sign sign' mantissa mantissa'
        exponent exponent' positive positive'
        (model_product_exponent_ready fmt.toModel mantissa mantissa' exponent exponent'
          sign sign' positive positive' leftNormal rightNormal) finite

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
      split <;>
        exact toReal_ofModel_zero _ (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt ieee) _
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

theorem neg_isFinite (value : UnpackedFloat) (finite : value.isFinite = true) :
    (UnpackedFloat.neg value).isFinite = true := by
  cases value <;> exact finite

theorem neg_fits (spec : Format) (value : UnpackedFloat) (fits : ModelFits spec value) :
    ModelFits spec (UnpackedFloat.neg value) := by
  cases value <;> exact fits

theorem unpackedToReal_neg (value : UnpackedFloat) :
    unpackedToReal (UnpackedFloat.neg value) = -unpackedToReal value := by
  rw [unpackedToReal_eq, unpackedToReal_eq, model_neg_value, Rat.cast_neg]

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

theorem div_roundAt (fmt : FloatFormat) (ieee : fmt.isIEEE = true)
    (left right : UnpackedFloat) (leftFinite : left.isFinite = true)
    (rightFinite : right.isFinite = true) (nonzero : unpackedValue right ≠ 0)
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
      exact toReal_ofModel_zero _ (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt ieee) _
    | finite sign mantissa exponent positive =>
      exact toReal_ofModel_div_finite_eq_roundAt fmt ieee sign sign' mantissa
        mantissa' exponent exponent' positive positive' finite

def model64 (value : Binary64) : Model FloatFormat.binary64 := ⟨value.bits.toBitVec⟩

theorem format64 : FloatFormat.binary64.toModel = Format.binary64 := rfl

theorem toModel_model64 (value : Binary64) : toModel (model64 value) = decoded64 value := rfl

theorem toReal_model64 (value : Binary64) :
    toReal (model64 value) = ((numerical64 value : ℚ) : ℝ) := by
  rw [toReal_eq_unpackedToReal_toModel rfl, toModel_model64, unpackedToReal_eq]
  rfl

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

theorem canonical64 (value : Binary64) (finite : value.Finite) :
    (decoded64 value).isFinite = true ∧ ModelNormalized Format.binary64 (decoded64 value) ∧
      ModelFits Format.binary64 (decoded64 value) :=
  ⟨(model_decoded64_finite value).mpr finite,
    model_unpack_format Format.binary64 (by decide) value.bits.toBitVec
      ((model_decoded64_finite value).mpr finite)⟩

theorem model64_add (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.add right) = ofModel FloatFormat.binary64
      (UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

theorem model64_sub (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.sub right) = ofModel FloatFormat.binary64
      (UnpackedFloat.sub Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

theorem model64_mul (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.mul right) = ofModel FloatFormat.binary64
      (UnpackedFloat.mul Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

theorem model64_div (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model64 (left.div right) = ofModel FloatFormat.binary64
      (UnpackedFloat.div Format.binary64 (decoded64 left) (decoded64 right)) := by
  rw [← model_ofBits64_decoded left leftFinite, ← model_ofBits64_decoded right rightFinite]
  rfl

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

theorem binary64_div_roundAt (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonzero : numerical64 right ≠ 0)
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
      l.1 r.1 nonzero packedFinite
  rw [← packed, toReal_model64, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

def model32 (value : Binary32) : Model FloatFormat.binary32 := ⟨value.bits.toBitVec⟩

theorem format32 : FloatFormat.binary32.toModel = Format.binary32 := rfl

theorem toModel_model32 (value : Binary32) : toModel (model32 value) = decoded32 value := rfl

theorem toReal_model32 (value : Binary32) :
    toReal (model32 value) = ((numerical32 value : ℚ) : ℝ) := by
  rw [toReal_eq_unpackedToReal_toModel rfl, toModel_model32, unpackedToReal_eq]
  rfl

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

theorem canonical32 (value : Binary32) (finite : value.Finite) :
    (decoded32 value).isFinite = true ∧ ModelNormalized Format.binary32 (decoded32 value) ∧
      ModelFits Format.binary32 (decoded32 value) :=
  ⟨(model_decoded32_finite value).mpr finite,
    model_unpack_format Format.binary32 (by decide) value.bits.toBitVec
      ((model_decoded32_finite value).mpr finite)⟩

theorem model32_add (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.add right) = ofModel FloatFormat.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

theorem model32_sub (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.sub right) = ofModel FloatFormat.binary32
      (UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

theorem model32_mul (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.mul right) = ofModel FloatFormat.binary32
      (UnpackedFloat.mul Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

theorem model32_div (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    model32 (left.div right) = ofModel FloatFormat.binary32
      (UnpackedFloat.div Format.binary32 (decoded32 left) (decoded32 right)) := by
  rw [← model_ofBits32_decoded left leftFinite, ← model_ofBits32_decoded right rightFinite]
  rfl

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

theorem binary32_div_roundAt (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonzero : numerical32 right ≠ 0)
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
      l.1 r.1 nonzero packedFinite
  rw [← packed, toReal_model32, unpackedToReal_eq, unpackedToReal_eq] at result
  exact result

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

theorem binary64_div_half_unit_error (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonzero : numerical64 right ≠ 0)
    (bound : |numerical64 left / numerical64 right| ≤ 65536) :
    (left.div right).Finite ∧
      |numerical64 (left.div right) - numerical64 left / numerical64 right| ≤
        1 / 137438953472 := by
  have finite := (binary64_div_finite_error left right leftFinite rightFinite nonzero bound).1
  refine ⟨finite, ?_⟩
  have rounded := binary64_div_roundAt left right leftFinite rightFinite nonzero finite
  have realBound : |(numerical64 left : ℝ) / (numerical64 right : ℝ)| ≤ 65536 := by
    exact_mod_cast bound
  have error := roundAt64_error _ realBound
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

theorem roundAt32_error_unit (x : ℝ) (bound : |x| ≤ 128) :
    |roundAt FloatFormat.binary32 x - x| ≤ 1 / 131072 := by
  by_cases zero : x = 0
  · rw [zero, roundAt_zero]
    norm_num
  have monotone : MonotoneExp (fexpOf FloatFormat.binary32) :=
    ⟨fun _ _ order => max_le_max (sub_le_sub_right order _) le_rfl⟩
  have half := error_bound_ulp (β := FloatLib.Numerics.binaryRadix)
    (fexp := fexpOf FloatFormat.binary32) nearestEven x
  have power : Flocq.bpow FloatLib.Numerics.binaryRadix 7 = 128 := by
    norm_num [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  have exponent : fexpOf FloatFormat.binary32 (7 + 1) = -16 := by decide
  have spacing : ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) x ≤
      1 / 65536 := by
    rw [← ulp_abs]
    calc
      ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) |x| ≤
          ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32)
            (Flocq.bpow FloatLib.Numerics.binaryRadix 7) :=
        ulp_mono_pos (abs_pos.mpr zero) (by rw [power]; exact bound)
      _ = Flocq.bpow FloatLib.Numerics.binaryRadix (-16) := by rw [ulp_bpow, exponent]
      _ = 1 / 65536 := by
        norm_num [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  calc
    |roundAt FloatFormat.binary32 x - x| ≤
        ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) x / 2 := half
    _ ≤ 1 / 131072 := by linarith

theorem roundAt32_error_sum (x : ℝ) (bound : |x| ≤ 8192) :
    |roundAt FloatFormat.binary32 x - x| ≤ 1 / 2048 := by
  by_cases zero : x = 0
  · rw [zero, roundAt_zero]
    norm_num
  have monotone : MonotoneExp (fexpOf FloatFormat.binary32) :=
    ⟨fun _ _ order => max_le_max (sub_le_sub_right order _) le_rfl⟩
  have half := error_bound_ulp (β := FloatLib.Numerics.binaryRadix)
    (fexp := fexpOf FloatFormat.binary32) nearestEven x
  have power : Flocq.bpow FloatLib.Numerics.binaryRadix 13 = 8192 := by
    norm_num [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  have exponent : fexpOf FloatFormat.binary32 (13 + 1) = -10 := by decide
  have spacing : ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) x ≤
      1 / 1024 := by
    rw [← ulp_abs]
    calc
      ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) |x| ≤
          ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32)
            (Flocq.bpow FloatLib.Numerics.binaryRadix 13) :=
        ulp_mono_pos (abs_pos.mpr zero) (by rw [power]; exact bound)
      _ = Flocq.bpow FloatLib.Numerics.binaryRadix (-10) := by rw [ulp_bpow, exponent]
      _ = 1 / 1024 := by
        norm_num [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  calc
    |roundAt FloatFormat.binary32 x - x| ≤
        ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) x / 2 := half
    _ ≤ 1 / 2048 := by linarith

theorem roundAt32_relative (x : ℝ) :
    |roundAt FloatFormat.binary32 x - x| ≤ |x| / 16777216 + 1 / 2 ^ 150 := by
  by_cases zero : x = 0
  · rw [zero, roundAt_zero]
    norm_num
  have half := error_bound_ulp (β := FloatLib.Numerics.binaryRadix)
    (fexp := fexpOf FloatFormat.binary32) nearestEven x
  have ulpEq : ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) x =
      Flocq.bpow FloatLib.Numerics.binaryRadix
        (max (magnitude FloatLib.Numerics.binaryRadix x - 24) (-149)) := by
    rw [ulp.of_ne_zero _ _ _ zero]
    rfl
  have ulpBound : ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) x ≤
      |x| / 8388608 + 1 / 2 ^ 149 := by
    rw [ulpEq]
    by_cases subnormal : magnitude FloatLib.Numerics.binaryRadix x - 24 ≤ -149
    · rw [max_eq_right subnormal]
      have under : Flocq.bpow FloatLib.Numerics.binaryRadix (-149) = 1 / 2 ^ 149 := by
        norm_num [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
      rw [under]
      linarith [abs_nonneg x]
    · have subnormal := not_le.mp subnormal
      rw [max_eq_left (le_of_lt subnormal)]
      have magLe := bpow_magnitude_sub_one_le FloatLib.Numerics.binaryRadix x zero
      have shift : Flocq.bpow FloatLib.Numerics.binaryRadix
          (magnitude FloatLib.Numerics.binaryRadix x - 24) =
          Flocq.bpow FloatLib.Numerics.binaryRadix
            (magnitude FloatLib.Numerics.binaryRadix x - 1) / 8388608 := by
        have split : magnitude FloatLib.Numerics.binaryRadix x - 24 =
            (magnitude FloatLib.Numerics.binaryRadix x - 1) + (-23) := by omega
        rw [split]
        simp only [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
        rw [zpow_add₀ (by norm_num)]
        norm_num
        ring
      rw [shift]
      have pos : (0 : ℝ) ≤ 1 / 2 ^ 149 := by positivity
      linarith
  calc
    |roundAt FloatFormat.binary32 x - x| ≤
        ulp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) x / 2 := half
    _ ≤ |x| / 16777216 + 1 / 2 ^ 150 := by linarith

theorem binary32_add_relative (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.add right).Finite) :
    |numerical32 (left.add right) - (numerical32 left + numerical32 right)| ≤
      |numerical32 left + numerical32 right| / 16777216 + 1 / 2 ^ 150 := by
  have rounded := binary32_add_roundAt left right leftFinite rightFinite finite
  have error := roundAt32_relative ((numerical32 left : ℝ) + (numerical32 right : ℝ))
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

theorem binary32_sub_relative (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.sub right).Finite) :
    |numerical32 (left.sub right) - (numerical32 left - numerical32 right)| ≤
      |numerical32 left - numerical32 right| / 16777216 + 1 / 2 ^ 150 := by
  have rounded := binary32_sub_roundAt left right leftFinite rightFinite finite
  have error := roundAt32_relative ((numerical32 left : ℝ) - (numerical32 right : ℝ))
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

theorem binary32_mul_relative (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.mul right).Finite) :
    |numerical32 (left.mul right) - numerical32 left * numerical32 right| ≤
      |numerical32 left * numerical32 right| / 16777216 + 1 / 2 ^ 150 := by
  have rounded := binary32_mul_roundAt left right leftFinite rightFinite finite
  have error := roundAt32_relative ((numerical32 left : ℝ) * (numerical32 right : ℝ))
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

theorem binary32_mul_unit_error (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.mul right).Finite)
    (bound : |numerical32 left * numerical32 right| ≤ 128) :
    |numerical32 (left.mul right) - numerical32 left * numerical32 right| ≤ 1 / 131072 := by
  have rounded := binary32_mul_roundAt left right leftFinite rightFinite finite
  have realBound : |(numerical32 left : ℝ) * (numerical32 right : ℝ)| ≤ 128 := by
    exact_mod_cast bound
  have error := roundAt32_error_unit _ realBound
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

theorem binary32_add_unit_error (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.add right).Finite)
    (bound : |numerical32 left + numerical32 right| ≤ 128) :
    |numerical32 (left.add right) - (numerical32 left + numerical32 right)| ≤ 1 / 131072 := by
  have rounded := binary32_add_roundAt left right leftFinite rightFinite finite
  have realBound : |(numerical32 left : ℝ) + (numerical32 right : ℝ)| ≤ 128 := by
    exact_mod_cast bound
  have error := roundAt32_error_unit _ realBound
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

theorem binary32_add_sum_error (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (finite : (left.add right).Finite)
    (bound : |numerical32 left + numerical32 right| ≤ 8192) :
    |numerical32 (left.add right) - (numerical32 left + numerical32 right)| ≤ 1 / 2048 := by
  have rounded := binary32_add_roundAt left right leftFinite rightFinite finite
  have realBound : |(numerical32 left : ℝ) + (numerical32 right : ℝ)| ≤ 8192 := by
    exact_mod_cast bound
  have error := roundAt32_error_sum _ realBound
  rw [← rounded] at error
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact error)

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

theorem nearest32 (word : UInt32) (numerator denominator : Nat) (value : ℝ)
    (expOk : 1 ≤ word.toNat / 2 ^ 23 ∧ word.toNat / 2 ^ 23 ≤ 126)
    (denominatorPositive : denominator ≠ 0)
    (exact : (numerator : ℝ) / (denominator : ℝ) = value)
    (wordValue : toDyadic? (model32 (Binary32.mk word)) =
      some ⟨false, 2 ^ 23 + word.toNat % 2 ^ 23, -((150 - word.toNat / 2 ^ 23 : Nat) : ℤ)⟩)
    (inBinade : denominator ≤ numerator * 2 ^ (127 - word.toNat / 2 ^ 23) ∧
      numerator * 2 ^ (126 - word.toNat / 2 ^ 23) < denominator)
    (close : Int.natAbs (2 * (numerator : ℤ) * (2 : ℤ) ^ (150 - word.toNat / 2 ^ 23) -
      2 * ((2 ^ 23 + word.toNat % 2 ^ 23 : Nat) : ℤ) * (denominator : ℤ)) < denominator) :
    ((numerical32 (Binary32.mk word) : ℚ) : ℝ) = roundAt FloatFormat.binary32 value := by
  set exp : Nat := word.toNat / 2 ^ 23
  set shift : Nat := 150 - exp
  set m : Nat := 2 ^ 23 + word.toNat % 2 ^ 23
  set e : ℤ := -(shift : ℤ)
  have hdenPos : (0 : ℝ) < denominator := by exact_mod_cast Nat.pos_of_ne_zero denominatorPositive
  have hbpow2 : ∀ k : ℤ, Flocq.bpow FloatLib.Numerics.binaryRadix k = (2 : ℝ) ^ k := fun k => by
    simp [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  have he23 : e + 23 = -((127 - exp : Nat) : ℤ) := by omega
  have he24 : e + 24 = -((126 - exp : Nat) : ℤ) := by omega
  have hlo : Flocq.bpow FloatLib.Numerics.binaryRadix (e + 23) ≤ value := by
    rw [hbpow2, he23, zpow_neg, zpow_natCast, ← exact]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hdenPos, one_mul]
    exact_mod_cast inBinade.1
  have hhi : value < Flocq.bpow FloatLib.Numerics.binaryRadix (e + 24) := by
    rw [hbpow2, he24, zpow_neg, zpow_natCast, ← exact]
    rw [inv_eq_one_div, div_lt_div_iff₀ hdenPos (by positivity), one_mul]
    exact_mod_cast inBinade.2
  have hpos : 0 < value := lt_of_lt_of_le (Flocq.bpow.pos _ _) hlo
  have hmag : magnitude FloatLib.Numerics.binaryRadix value = e + 24 := by
    refine magnitude_eq_of_bpow_bounds FloatLib.Numerics.binaryRadix value (e + 24) ?_ ?_
    · rw [abs_of_pos hpos, show e + 24 - 1 = e + 23 by omega]
      exact hlo
    · rw [abs_of_pos hpos]
      exact hhi
  have hcexp : cexp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) value = e := by
    change max (magnitude FloatLib.Numerics.binaryRadix value - 24) (-149) = e
    rw [hmag]
    omega
  set s : ℝ := scaledMantissa FloatLib.Numerics.binaryRadix
    (fexpOf FloatFormat.binary32) value
  have hsEq : s = (numerator : ℝ) * (2 : ℝ) ^ shift / (denominator : ℝ) := by
    change value * Flocq.bpow FloatLib.Numerics.binaryRadix
      (-cexp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) value) = _
    rw [hcexp, show -e = (shift : ℤ) by omega, hbpow2, zpow_natCast, ← exact]
    ring
  have hcloseReal : |s - (m : ℝ)| < 1 / 2 := by
    have hcloseInt : |(2 * (numerator : ℝ) * (2 : ℝ) ^ shift - 2 * (m : ℝ) * (denominator : ℝ))| <
        (denominator : ℝ) := by
      have hcast : ((Int.natAbs (2 * (numerator : ℤ) * (2 : ℤ) ^ shift -
          2 * (m : ℤ) * (denominator : ℤ)) : ℕ) : ℝ) < (denominator : ℝ) := by
        exact_mod_cast close
      rwa [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_mul,
        Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_natCast, Int.cast_natCast] at hcast
    have hdiff : s - (m : ℝ) =
        (2 * (numerator : ℝ) * (2 : ℝ) ^ shift - 2 * (m : ℝ) * (denominator : ℝ)) /
          (2 * (denominator : ℝ)) := by
      rw [hsEq]
      field_simp
    rw [hdiff, abs_div, abs_of_pos (mul_pos (by norm_num) hdenPos)]
    rw [div_lt_iff₀ (mul_pos (by norm_num) hdenPos)]
    linarith
  have hnear : nearestEven s = (m : ℤ) := by
    have hbounds := abs_lt.mp hcloseReal
    by_cases hle : (m : ℝ) ≤ s
    · have hfl : ⌊s⌋ = (m : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast hle, by
        push_cast; linarith⟩
      rw [nearestEven_eq_floor_of_frac_lt_half s (by rw [hfl]; push_cast; linarith), hfl]
    · have hlt := not_le.mp hle
      have hfl : ⌊s⌋ = (m : ℤ) - 1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by
        push_cast; linarith⟩
      rw [nearestEven_eq_ceil_of_frac_gt_half s (by rw [hfl]; push_cast; linarith), hfl]
      omega
  have hround : roundAt FloatFormat.binary32 value = (m : ℝ) / (2 : ℝ) ^ shift := by
    change ((nearestEven s : ℤ) : ℝ) * Flocq.bpow FloatLib.Numerics.binaryRadix
      (cexp FloatLib.Numerics.binaryRadix (fexpOf FloatFormat.binary32) value) = _
    rw [hnear, hcexp, hbpow2, zpow_neg, zpow_natCast, Int.cast_natCast, div_eq_mul_inv]
  have hwordReal : ((numerical32 (Binary32.mk word) : ℚ) : ℝ) = (m : ℝ) / (2 : ℝ) ^ shift := by
    rw [← toReal_model32, toReal_eq, wordValue]
    simp [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand,
      e, div_eq_mul_inv]
  rw [hwordReal, hround]

theorem band030_nearest :
    ((numerical32 (Binary32.mk Constants.band030Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.3 :=
  nearest32 Constants.band030Bits 3 10 0.3 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem band0335_nearest :
    ((numerical32 (Binary32.mk Constants.band0335Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.335 :=
  nearest32 Constants.band0335Bits 335 1000 0.335 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem band060_nearest :
    ((numerical32 (Binary32.mk Constants.band060Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.6 :=
  nearest32 Constants.band060Bits 6 10 0.6 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem band072_nearest :
    ((numerical32 (Binary32.mk Constants.band072Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.72 :=
  nearest32 Constants.band072Bits 72 100 0.72 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem band080_nearest :
    ((numerical32 (Binary32.mk Constants.band080Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.8 :=
  nearest32 Constants.band080Bits 8 10 0.8 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem moist040_nearest :
    ((numerical32 (Binary32.mk Constants.moist040Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.4 :=
  nearest32 Constants.moist040Bits 4 10 0.4 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem gamma90_nearest :
    ((numerical32 (Binary32.mk Constants.gamma90Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.9 :=
  nearest32 Constants.gamma90Bits 9 10 0.9 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem gamma95_nearest :
    ((numerical32 (Binary32.mk Constants.gamma95Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.95 :=
  nearest32 Constants.gamma95Bits 95 100 0.95 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem gamma99_nearest :
    ((numerical32 (Binary32.mk Constants.gamma99Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.99 :=
  nearest32 Constants.gamma99Bits 99 100 0.99 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem alphaInit5e5_nearest :
    ((numerical32 (Binary32.mk Constants.alphaInit5e5Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.00005 :=
  nearest32 Constants.alphaInit5e5Bits 5 100000 0.00005 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem alphaInit1e4_nearest :
    ((numerical32 (Binary32.mk Constants.alphaInit1e4Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.0001 :=
  nearest32 Constants.alphaInit1e4Bits 1 10000 0.0001 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem epsilon1e5_nearest :
    ((numerical32 (Binary32.mk Constants.epsilon1e5Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.00001 :=
  nearest32 Constants.epsilon1e5Bits 1 100000 0.00001 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem eta01_nearest :
    ((numerical32 (Binary32.mk Constants.eta01Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.1 :=
  nearest32 Constants.eta01Bits 1 10 0.1 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem eta025_nearest :
    ((numerical32 (Binary32.mk Constants.eta025Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.25 :=
  nearest32 Constants.eta025Bits 25 100 0.25 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem etaMin1e10_nearest :
    ((numerical32 (Binary32.mk Constants.etaMin1e10Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.0000000001 :=
  nearest32 Constants.etaMin1e10Bits 1 10000000000 0.0000000001 (by decide) (by decide)
    (by norm_num) (by decide) (by decide) (by decide)

theorem decay0999_nearest :
    ((numerical32 (Binary32.mk Constants.decay0999Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.999 :=
  nearest32 Constants.decay0999Bits 999 1000 0.999 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem meta1e3_nearest :
    ((numerical32 (Binary32.mk Constants.meta1e3Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.001 :=
  nearest32 Constants.meta1e3Bits 1 1000 0.001 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem meta3e2_nearest :
    ((numerical32 (Binary32.mk Constants.meta3e2Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.03 :=
  nearest32 Constants.meta3e2Bits 3 100 0.03 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem tie1e6_nearest :
    ((numerical32 (Binary32.mk Constants.tie1e6Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.000001 :=
  nearest32 Constants.tie1e6Bits 1 1000000 0.000001 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem epsStart_nearest :
    ((numerical32 (Binary32.mk Constants.epsStartBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.5 :=
  nearest32 Constants.epsStartBits 5 10 0.5 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem epsMin_nearest :
    ((numerical32 (Binary32.mk Constants.epsMinBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.05 :=
  nearest32 Constants.epsMinBits 5 100 0.05 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem epsDecay_nearest :
    ((numerical32 (Binary32.mk Constants.epsDecayBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.99999 :=
  nearest32 Constants.epsDecayBits 99999 100000 0.99999 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem optionEpsilon_nearest :
    ((numerical32 (Binary32.mk Constants.optionEpsilonBits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.1 :=
  nearest32 Constants.optionEpsilonBits 1 10 0.1 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

theorem exploreRate1e2_nearest :
    ((numerical32 (Binary32.mk Constants.exploreRate1e2Bits) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 0.01 :=
  nearest32 Constants.exploreRate1e2Bits 1 100 0.01 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)

section WorldAdmissionBridge

open Acorn.Host
open Float.Model (totalExponent)
open AcornVerif.CurrentOrder

set_option exponentiation.threshold 2048

private theorem toReal_bpow_neg (k : Nat) :
    Flocq.bpow FloatLib.Numerics.binaryRadix (-(k : Int)) = ((2 : ℝ) ^ k)⁻¹ := by
  simp [Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal, zpow_neg]

private theorem pow2_word_toReal (bits : UInt32) (expShift k : Nat)
    (hfin : (⟨bits⟩ : Binary32).Finite)
    (hunits : Conversion.magnitudeUnits32 ⟨bits⟩ = 2 ^ 23 * 2 ^ expShift)
    (hs : unpackSign (spec := Format.binary32) (⟨bits⟩ : Binary32).bits.toBitVec = 0)
    (hexp : 23 + expShift = k + 1074) :
    (model32 ⟨bits⟩).toReal = ((2 ^ k : Nat) : ℝ) := by
  rw [toReal_model32, numerical32_units _ hfin, hunits, ← Nat.pow_add, hexp, hs,
    show signCoefficient (Sign.ofBitVec (0 : BitVec 1)) = 1 from rfl,
    Nat.pow_add, one_mul, Nat.cast_mul, Nat.cast_pow (2 : Nat) 1074, Nat.cast_ofNat,
    mul_assoc, ← zpow_natCast (2 : ℚ) 1074, ← zpow_add₀ (by decide : (2 : ℚ) ≠ 0),
    show ((1074 : Nat) : Int) + -1074 = 0 from rfl, zpow_zero, mul_one, Rat.cast_natCast]

theorem pow2_word_eq_rat (bits : UInt32) (expShift k : Nat)
    (hfin : (⟨bits⟩ : Binary32).Finite)
    (hunits : Conversion.magnitudeUnits32 ⟨bits⟩ = 2 ^ 23 * 2 ^ expShift)
    (hs : unpackSign (spec := Format.binary32) (⟨bits⟩ : Binary32).bits.toBitVec = 0)
    (hexp : 23 + expShift = k + 1074) :
    numerical32 ⟨bits⟩ = ((2 ^ k : Nat) : ℚ) := by
  have h := pow2_word_toReal bits expShift k hfin hunits hs hexp
  rw [toReal_model32] at h
  exact_mod_cast h

theorem roundAt_pow2 (bits : UInt32) (expShift k : Nat)
    (hfin : (⟨bits⟩ : Binary32).Finite)
    (hunits : Conversion.magnitudeUnits32 ⟨bits⟩ = 2 ^ 23 * 2 ^ expShift)
    (hs : unpackSign (spec := Format.binary32) (⟨bits⟩ : Binary32).bits.toBitVec = 0)
    (hexp : 23 + expShift = k + 1074) :
    roundAt FloatFormat.binary32 ((2 ^ k : Nat) : ℝ) = ((2 ^ k : Nat) : ℝ) := by
  rw [← pow2_word_toReal bits expShift k hfin hunits hs hexp]
  exact roundAt_toReal_eq (model32 ⟨bits⟩) ((isFinite_model32 _).mpr hfin)

private theorem isFinite_ofModel32 (u : UnpackedFloat) (norm : ModelNormalized Format.binary32 u)
    (fits : ModelFits Format.binary32 u) :
    (ofModel FloatFormat.binary32 u).isFinite = true := by
  have fin_u : u.isFinite = true := model_normalized_finite _ _ norm
  have hunpack : unpack Format.binary32 (pack Format.binary32 u) = u :=
    model_unpack_pack_normalized Format.binary32 u norm fits
  have hdec : (decoded32 ⟨UInt32.ofBitVec (pack Format.binary32 u)⟩).isFinite = true := by
    change (unpack Format.binary32 (pack Format.binary32 u)).isFinite = true
    rw [hunpack]
    exact fin_u
  have hfin32 := (model_decoded32_finite ⟨UInt32.ofBitVec (pack Format.binary32 u)⟩).mp hdec
  have heq : model32 ⟨UInt32.ofBitVec (pack Format.binary32 u)⟩ =
      ofModel FloatFormat.binary32 u := rfl
  rw [← heq]
  exact (isFinite_model32 _).mpr hfin32

private theorem log2_mul_pow2 (n shift : Nat) (hpos : 0 < n) :
    (n * 2 ^ shift).log2 = n.log2 + shift := by
  have hk_lo : 2 ^ n.log2 ≤ n := Nat.log2_self_le (Nat.ne_of_gt hpos)
  have hk_hi : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hmpos : n * 2 ^ shift ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hpos (Nat.two_pow_pos shift))
  apply le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.log2_lt hmpos).mpr (by
      calc n * 2 ^ shift < 2 ^ (n.log2 + 1) * 2 ^ shift :=
            Nat.mul_lt_mul_of_pos_right hk_hi (Nat.two_pow_pos shift)
        _ = 2 ^ (n.log2 + shift + 1) := by rw [← Nat.pow_add]; congr 1; omega))
  · exact (Nat.le_log2 hmpos).mpr (by
      calc 2 ^ (n.log2 + shift) = 2 ^ n.log2 * 2 ^ shift := by rw [Nat.pow_add]
        _ ≤ n * 2 ^ shift := Nat.mul_le_mul_right _ hk_lo)

private theorem magnitude_xor_sign (x : Binary32) :
    (⟨x.bits ^^^ 0x80000000⟩ : Binary32).magnitude = x.magnitude := by
  unfold Binary32.magnitude
  change (x.bits.toNat ^^^ 2 ^ 31) &&& (2 ^ 31 - 1) = x.bits.toNat &&& (2 ^ 31 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro i
  change ((x.bits.toNat ^^^ 2 ^ 31) % 2 ^ 31).testBit i = (x.bits.toNat % 2 ^ 31).testBit i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < 31
  · simp only [hi, Nat.testBit_xor, Nat.testBit_two_pow]
    simp [show 31 ≠ i by omega]
  · simp [hi]

private theorem finite_xor_sign (x : Binary32) (hx : x.Finite) :
    (⟨x.bits ^^^ 0x80000000⟩ : Binary32).Finite := by
  unfold Binary32.Finite at *
  rwa [magnitude_xor_sign]

theorem unpack_xor_sign (b : BitVec 32) :
    unpack Format.binary32 (b ^^^ 0x80000000#32) = (unpack Format.binary32 b).neg := by
  have hm : unpackMantissa (spec := Format.binary32) (b ^^^ 0x80000000#32) =
      unpackMantissa (spec := Format.binary32) b := by
    unfold unpackMantissa
    ext i hi
    have hlt : i < 23 := hi
    have hbit : (0x80000000#32).getLsbD i = false := by
      change Nat.testBit (2 ^ 31) i = false
      rw [Nat.testBit_two_pow]
      simp [show 31 ≠ i by omega]
    simp [hbit]
  have he : unpackExponent (spec := Format.binary32) (b ^^^ 0x80000000#32) =
      unpackExponent (spec := Format.binary32) b := by
    unfold unpackExponent
    ext i hi
    have hlt : i < 8 := hi
    have hbit : (0x80000000#32).getLsbD (23 + i) = false := by
      change Nat.testBit (2 ^ 31) (23 + i) = false
      rw [Nat.testBit_two_pow]
      simp [show 31 ≠ 23 + i by omega]
    simp [hbit]
  have hs : unpackSign (spec := Format.binary32) (b ^^^ 0x80000000#32) =
      unpackSign (spec := Format.binary32) b ^^^ 1#1 := by
    unfold unpackSign
    ext i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp
  have hsb : ∀ s : BitVec 1, Sign.ofBitVec (s ^^^ 1#1) = -(Sign.ofBitVec s) := by
    intro s; cases s using BitVec.casesOn with | ofFin s => fin_cases s <;> rfl
  unfold unpack
  dsimp only
  simp only [hm, he, hs, hsb]
  by_cases hexp1 : unpackExponent (spec := Format.binary32) b = -1#Format.binary32.exponentBits
  · by_cases hm0 :
        unpackMantissa (spec := Format.binary32) b = 0#Format.binary32.mantissaBitsWithoutImplicit
    · simp [hexp1, hm0, UnpackedFloat.neg]
    · simp [hexp1, hm0, UnpackedFloat.neg]
  · by_cases hexp0 : unpackExponent (spec := Format.binary32) b = 0#Format.binary32.exponentBits
    · by_cases hm0 :
          unpackMantissa (spec := Format.binary32) b = 0#Format.binary32.mantissaBitsWithoutImplicit
      · simp [hexp0, hm0, UnpackedFloat.neg]
      · simp [hexp0, hm0, UnpackedFloat.neg]
    · rw [ite_eq_right hexp1, ite_eq_right hexp0, ite_eq_right hexp1, ite_eq_right hexp0]
      rfl

theorem div_xor_sign_finite (a b : Binary32) (ha : a.Finite) (hb : b.Finite) :
    (⟨a.bits ^^^ 0x80000000⟩ : Binary32).div ⟨b.bits ^^^ 0x80000000⟩ = a.div b := by
  have ha' := finite_xor_sign a ha
  have hb' := finite_xor_sign b hb
  have hm1 := model32_div ⟨a.bits ^^^ 0x80000000⟩ ⟨b.bits ^^^ 0x80000000⟩ ha' hb'
  have hm2 := model32_div a b ha hb
  have hda : decoded32 ⟨a.bits ^^^ 0x80000000⟩ = (decoded32 a).neg := by
    change unpack Format.binary32 (a.bits.toBitVec ^^^ 0x80000000#32) = _
    exact unpack_xor_sign a.bits.toBitVec
  have hdb : decoded32 ⟨b.bits ^^^ 0x80000000⟩ = (decoded32 b).neg := by
    change unpack Format.binary32 (b.bits.toBitVec ^^^ 0x80000000#32) = _
    exact unpack_xor_sign b.bits.toBitVec
  have hsdiv : ∀ s1 s2 : Sign, (-s1) / (-s2) = s1 / s2 := by
    intro s1 s2; cases s1 <;> cases s2 <;> rfl
  have hneg_div : ∀ u v : UnpackedFloat,
      UnpackedFloat.div Format.binary32 u.neg v.neg = UnpackedFloat.div Format.binary32 u v := by
    intro u v
    cases u <;> cases v <;> simp [UnpackedFloat.neg, UnpackedFloat.div, hsdiv]
  rw [hda, hdb, hneg_div, ← hm2] at hm1
  have hbits :
      ((⟨a.bits ^^^ 0x80000000⟩ : Binary32).div
        ⟨b.bits ^^^ 0x80000000⟩).bits = (a.div b).bits :=
    UInt32.eq_of_toBitVec_eq (congrArg Model.toBits hm1)
  cases h1 : (⟨a.bits ^^^ 0x80000000⟩ : Binary32).div ⟨b.bits ^^^ 0x80000000⟩
  cases h2 : a.div b
  rw [h1, h2] at hbits
  exact congrArg Binary32.mk hbits

theorem ofNat32_finite_and_roundAt (n : Nat) (hn : n ≤ 2 ^ 63) :
    (Binary32.ofUInt64 n.toUInt64).Finite ∧
      ((numerical32 (Binary32.ofUInt64 n.toUInt64) : ℚ) : ℝ) =
        roundAt FloatFormat.binary32 (n : ℝ) := by
  have hn_lt : n < UInt64.size := by change n < 2 ^ 64; omega
  have hn_mod : n.toUInt64.toNat = n := by
    change UInt64.toNat (UInt64.ofNat n) = n
    exact UInt64.toNat_ofNat_of_lt' hn_lt
  have m_eq : model32 (Binary32.ofUInt64 n.toUInt64) =
      ofModel FloatFormat.binary32 (UnpackedFloat.ofNat Format.binary32 n) := by
    change ofModel FloatFormat.binary32 (UnpackedFloat.ofNat Format.binary32 n.toUInt64.toNat) = _
    rw [hn_mod]
  have hnorm_err := model_signed_round_value Format.binary32 n 0 .positive 63 (by
    rw [zpow_zero, mul_one, abs_of_nonneg (by positivity)]
    exact_mod_cast hn)
  change ModelNormalized Format.binary32 (UnpackedFloat.ofNat Format.binary32 n) ∧
      |unpackedValue (UnpackedFloat.ofNat Format.binary32 n) -
        (n : ℚ) * (2 : ℚ) ^ (0 : Int)| ≤ _
    at hnorm_err
  have hfin_u : (UnpackedFloat.ofNat Format.binary32 n).isFinite = true :=
    model_normalized_finite _ _ hnorm_err.1
  have hfits : ModelFits Format.binary32 (UnpackedFloat.ofNat Format.binary32 n) := by
    apply model_fits_of_value_bound Format.binary32 _ hfin_u 64 (by decide)
    have h2 := hnorm_err.2
    simp only [zpow_zero, mul_one, Format.mantissaBits, Format.minExponent] at h2
    have htri := abs_add_le
      (unpackedValue (UnpackedFloat.ofNat Format.binary32 n) - (n : ℚ)) (n : ℚ)
    rw [sub_add_cancel] at htri
    have hn_q : |(n : ℚ)| ≤ (2 : ℚ) ^ 63 := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hn
    norm_num at h2 ⊢
    linarith
  have hm_fin : (model32 (Binary32.ofUInt64 n.toUInt64)).isFinite = true := by
    rw [m_eq]
    exact isFinite_ofModel32 _ hnorm_err.1 hfits
  have hfin32 : (Binary32.ofUInt64 n.toUInt64).Finite := (isFinite_model32 _).mp hm_fin
  refine ⟨hfin32, ?_⟩
  rw [← toReal_model32, m_eq]
  by_cases h0 : n = 0
  · subst h0
    have hz : UnpackedFloat.ofNat Format.binary32 0 = .zero .positive := rfl
    rw [hz, toReal_ofModel_zero _ rfl _, Nat.cast_zero, roundAt_zero]
  · have hpos : 0 < n := Nat.pos_of_ne_zero h0
    have hcomp : compare (n : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
    have hof : UnpackedFloat.ofNat Format.binary32 n =
        UnpackedFloat.round Format.binary32 .positive n 0 := by
      simp [UnpackedFloat.ofNat, UnpackedFloat.ofInt, UnpackedFloat.normalize, hcomp]
    set target := Format.binary32.targetExponent (totalExponent n 0)
    set shift := (0 - target).toNat
    have hunfold : UnpackedFloat.ofNat Format.binary32 n =
        roundWithAccuracy Format.binary32 .positive (n * 2 ^ shift) (-(shift : Int)) .exact := by
      rw [hof]
      unfold UnpackedFloat.round
      dsimp only
      have hdec : decreaseExponent n 0 target = (n * 2 ^ shift, -(shift : Int)) := by
        simp [decreaseExponent, shift, Nat.shiftLeft_eq]
      rw [show Format.binary32.targetExponent (totalExponent n 0) = target from rfl, hdec]
    have htot_eq : totalExponent (n * 2 ^ shift) (-(shift : Int)) = totalExponent n 0 := by
      simp [totalExponent, log2_mul_pow2 n shift hpos]
      omega
    have hle : (-(shift : Int)) ≤ Format.binary32.targetExponent
        (totalExponent (n * 2 ^ shift) (-(shift : Int))) := by
      rw [htot_eq]
      change -(shift : Int) ≤ target
      dsimp [shift]
      omega
    have hm_fin' : (ofModel FloatFormat.binary32
        (roundWithAccuracy FloatFormat.binary32.toModel .positive (n * 2 ^ shift)
          (-(shift : Int)) .exact)).isFinite = true := by
      change (ofModel FloatFormat.binary32
          (roundWithAccuracy Format.binary32 .positive (n * 2 ^ shift)
            (-(shift : Int)) .exact)).isFinite = true
      rwa [← hunfold, ← m_eq]
    rw [hunfold]
    change (ofModel FloatFormat.binary32
        (roundWithAccuracy FloatFormat.binary32.toModel .positive (n * 2 ^ shift)
          (-(shift : Int)) .exact)).toReal = _
    rw [toReal_ofModel_roundWithAccuracy_eq_roundAt FloatFormat.binary32 rfl .positive
        (n * 2 ^ shift) (-(shift : Int)) .exact ((n * 2 ^ shift : Nat) : ℝ)
        (by simp [AccuracyRepresents]) hle hm_fin']
    congr 1
    simp only [modelSignBit, Bool.false_eq_true, ↓reduceIte, one_mul, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [toReal_bpow_neg shift]
    have hp2 : ((2 : ℝ) ^ shift) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hp2]

theorem ofNat32_pos_of_pos (n : Nat) (hpos : 0 < n) (hn : n ≤ 2 ^ 63) :
    0 < numerical32 (Binary32.ofUInt64 n.toUInt64) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
  have hround1 : roundAt FloatFormat.binary32 (1 : ℝ) = 1 := by
    have h := roundAt_pow2 0x3f800000 1051 0 (by decide)
      (by rw [show Conversion.magnitudeUnits32 ⟨0x3f800000⟩ = 2 ^ 23 * 2 ^ 1051 by rfl])
      (by decide) (by decide)
    simpa only [pow_zero, Nat.cast_one] using h
  have hm := roundAt_mono FloatFormat.binary32 h1
  rw [hround1, ← (ofNat32_finite_and_roundAt n hn).2] at hm
  exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hm

private theorem packComponents_pos_finite (exp : BitVec 8) (man : BitVec 23)
    (hexp : exp.toNat < 255) :
    let q : Binary32 := ⟨UInt32.ofBitVec (packComponents Format.binary32 .positive exp man)⟩
    q.Finite ∧ ¬ q.Negative := by
  dsimp only
  have hman_lt : man.toNat < 2 ^ 23 := man.isLt
  have hbits_eq : (packComponents Format.binary32 .positive exp man).toNat =
      (exp.toNat * 2 ^ 23) ||| man.toNat := by
    unfold packComponents
    simp only [Sign.toBitVec]
    change ((0#1 ++ exp) ++ man).toNat = _
    rw [BitVec.toNat_append, BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.shiftLeft_eq]
    have h0 : 0 * 2 ^ 8 ||| exp.toNat = exp.toNat := by simp
    rw [h0]
  have hdiv : ((exp.toNat * 2 ^ 23) ||| man.toNat) / 2 ^ 23 = exp.toNat := by
    rw [Nat.or_div_two_pow, Nat.mul_div_cancel _ (by decide), Nat.div_eq_of_lt hman_lt, Nat.or_zero]
  have hbits_lt : (packComponents Format.binary32 .positive exp man).toNat < 255 * 2 ^ 23 := by
    rw [hbits_eq]
    omega
  have hmag :
      (⟨UInt32.ofBitVec (packComponents Format.binary32 .positive exp man)⟩ :
        Binary32).magnitude =
      (packComponents Format.binary32 .positive exp man).toNat := by
    unfold Binary32.magnitude
    change ((packComponents Format.binary32 .positive exp man).toNat &&&
        (0x7fffffff : UInt32).toNat) = _
    rw [show (0x7fffffff : UInt32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · unfold Binary32.Finite
    rw [hmag]
    exact hbits_lt
  · unfold Binary32.Negative
    change ¬ 2 ^ 31 ≤ (packComponents Format.binary32 .positive exp man).toNat
    omega

private theorem pack_roundWithAccuracy_pos_class (q : Binary32) (m : Nat) (e : Int)
    (acc : Accuracy)
    (hq : q = ⟨UInt32.ofBitVec
      (pack Format.binary32 (roundWithAccuracy Format.binary32 .positive m e acc))⟩) :
    (q.Finite ∧ ¬ q.Negative) ∨ q = ⟨0x7f800000⟩ := by
  subst hq
  set u := roundWithAccuracy Format.binary32 .positive m e acc
  have hu : u = .zero .positive ∨ ∃ mf ef hp, u = .finite .positive mf ef hp := by
    dsimp [u, roundWithAccuracy]
    set p := shiftToTargetExponent Format.binary32
        (shiftToTargetExponent Format.binary32 m e acc).1.roundedMantissa
        (shiftToTargetExponent Format.binary32 m e acc).2 Accuracy.exact
    by_cases h0 : p.1.mantissa = 0
    · exact Or.inl (by simp [h0])
    · exact Or.inr ⟨p.1.mantissa, p.2, Nat.pos_of_ne_zero h0, by simp [h0]⟩
  rcases hu with hzero | ⟨mf, ef, hp, hfin⟩
  · left
    rw [hzero]
    exact ⟨by decide, by decide⟩
  · rw [hfin]
    unfold pack
    dsimp only
    split
    · right; rfl
    · rename_i hlt
      left
      change ¬ 2 ^ 8 ≤
          (ef + ↑Format.binary32.exponentBias +
            ↑Format.binary32.mantissaBitsWithoutImplicit).toNat + 1 at hlt
      rw [show (Format.binary32.exponentBias : Int) = 127 from rfl,
        show (Format.binary32.mantissaBitsWithoutImplicit : Int) = 23 from rfl] at hlt ⊢
      have hexp_lt : (ef + 127 + 23).toNat < 255 := by omega
      split
      · exact packComponents_pos_finite _ _ (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact hexp_lt)
      · exact packComponents_pos_finite _ _ (by decide)

private theorem packComponents_neg_ge (exp : BitVec 8) (man : BitVec 23) :
    2 ^ 31 ≤ (packComponents Format.binary32 .negative exp man).toNat := by
  unfold packComponents Sign.toBitVec
  change 2 ^ 31 ≤ ((1#1 ++ exp) ++ man).toNat
  rw [BitVec.append_assoc, BitVec.toNat_cast, BitVec.toNat_append,
    BitVec.toNat_ofNat, Nat.one_mod, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.left_le_or

private theorem pack_neg_not_pastLast (u : UnpackedFloat)
    (hs : match u with
      | .infinity .negative | .zero .negative | .finite .negative _ _ _ => True
      | _ => False) :
    isPastLast ⟨UInt32.ofBitVec (pack Format.binary32 u)⟩ = false := by
  have hge : 2 ^ 31 ≤ (pack Format.binary32 u).toNat := by
    cases u with
    | notANumber => contradiction
    | infinity s =>
      cases s with
      | positive => contradiction
      | negative => decide
    | zero s =>
      cases s with
      | positive => contradiction
      | negative => decide
    | finite s m e hm =>
      cases s with
      | positive => contradiction
      | negative =>
        unfold pack
        dsimp only
        split
        · decide
        · split
          · exact packComponents_neg_ge _ _
          · exact packComponents_neg_ge _ _
  unfold isPastLast
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right
  change ¬ (pack Format.binary32 u).toNat ≤ 0x7f800000
  omega

private theorem pack_roundWithAccuracy_neg_not_pastLast (q : Binary32) (m : Nat) (e : Int)
    (acc : Accuracy)
    (hq : q = ⟨UInt32.ofBitVec
      (pack Format.binary32 (roundWithAccuracy Format.binary32 .negative m e acc))⟩) :
    isPastLast q = false := by
  subst hq
  apply pack_neg_not_pastLast
  dsimp [roundWithAccuracy]
  split_ifs <;> trivial

theorem isPastLast_lt_threshold (q : Binary32) (fin : q.Finite) (nneg : ¬ q.Negative) :
    isPastLast q = false ↔ numerical32 q < ((2 ^ 63 : Nat) : ℚ) := by
  have hb : q.bits.toNat < 2 ^ 31 := by unfold Binary32.Negative at nneg; omega
  have hmag : q.magnitude = q.bits.toNat := by
    unfold Binary32.magnitude
    rw [UInt32.toNat_and, show (0x7fffffff : UInt32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hb]
  have hp : isPastLast q = false ↔ q.bits.toNat < 0x5f000000 := by
    have hfin_lt : q.bits.toNat < 0x7f800000 := by unfold Binary32.Finite at fin; omega
    unfold isPastLast
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  rw [hp]
  have h263_fin : (⟨0x5f000000⟩ : Binary32).Finite := by decide
  have h263_val : numerical32 ⟨0x5f000000⟩ = ((2 ^ 63 : Nat) : ℚ) :=
    pow2_word_eq_rat 0x5f000000 (190 + 924) 63 h263_fin rfl (by decide) (by decide)
  have hnneg_b : q.negative = false := by
    cases hb' : q.negative with
    | false => rfl
    | true => exact absurd ((Binary32.negative_iff q).mp hb') nneg
  have hkey : q.key = (q.bits.toNat : Int) := by
    rw [Binary32.key_eq_negative]
    simp [hnneg_b, hmag]
  have hlt := numerical32_strict_order q ⟨0x5f000000⟩ fin h263_fin
  rw [hkey, show (⟨0x5f000000⟩ : Binary32).key = (0x5f000000 : Int) by rfl] at hlt
  have hlt_nat : q.bits.toNat < 0x5f000000 ↔ numerical32 q < numerical32 ⟨0x5f000000⟩ := by
    rw [hlt]; exact Int.ofNat_lt.symm
  rwa [← h263_val]

private theorem decoded32_signed_finite (v : Binary32) (hf : v.Finite) :
    (0 < numerical32 v → ∃ m e hpos, decoded32 v = .finite .positive m e hpos) ∧
    (numerical32 v < 0 → ∃ m e hpos, decoded32 v = .finite .negative m e hpos) := by
  have cv := canonical32 v hf
  constructor
  · intro hp
    cases hdv : decoded32 v with
    | notANumber => rw [hdv] at cv; simp [UnpackedFloat.isFinite] at cv
    | infinity _ => rw [hdv] at cv; simp [UnpackedFloat.isFinite] at cv
    | zero _ => unfold numerical32 at hp; rw [hdv] at hp; simp [unpackedValue] at hp
    | finite sv mv ev hmv =>
      cases sv with
      | positive => exact ⟨mv, ev, hmv, rfl⟩
      | negative =>
        have hneg : numerical32 v < 0 := by
          unfold numerical32; rw [hdv]; simp only [unpackedValue, signCoefficient, neg_mul, one_mul]
          have hpos_q : (0 : ℚ) < (mv : ℚ) * (2 : ℚ) ^ ev := by positivity
          linarith
        exact absurd hneg (not_lt_of_gt hp)
  · intro hn
    cases hdv : decoded32 v with
    | notANumber => rw [hdv] at cv; simp [UnpackedFloat.isFinite] at cv
    | infinity _ => rw [hdv] at cv; simp [UnpackedFloat.isFinite] at cv
    | zero _ => unfold numerical32 at hn; rw [hdv] at hn; simp [unpackedValue] at hn
    | finite sv mv ev hmv =>
      cases sv with
      | negative => exact ⟨mv, ev, hmv, rfl⟩
      | positive =>
        have hpos : 0 < numerical32 v := by
          unfold numerical32; rw [hdv]; simp only [unpackedValue, signCoefficient, one_mul]
          positivity
        exact absurd hpos (not_lt_of_gt hn)

private theorem div_eq_pack (sa sb : Sign) (a b : Binary32) (ma : Nat) (ea : Int) (hma : 0 < ma)
    (ha : a.Finite) (hda : decoded32 a = .finite sa ma ea hma)
    (mb : Nat) (eb : Int) (hmb : 0 < mb) (hb : b.Finite)
    (hdb : decoded32 b = .finite sb mb eb hmb) :
    a.div b = ⟨UInt32.ofBitVec (pack Format.binary32
      (roundWithAccuracy Format.binary32 (sa / sb) (divCore Format.binary32 ma ea mb eb).1
        (divCore Format.binary32 ma ea mb eb).2.1
        (divCore Format.binary32 ma ea mb eb).2.2))⟩ := by
  have hm := model32_div a b ha hb
  have hdiv_unfold : UnpackedFloat.div Format.binary32 (decoded32 a) (decoded32 b) =
      roundWithAccuracy Format.binary32 (sa / sb) (divCore Format.binary32 ma ea mb eb).1
        (divCore Format.binary32 ma ea mb eb).2.1
        (divCore Format.binary32 ma ea mb eb).2.2 := by
    rw [hda, hdb]
    rfl
  rw [hdiv_unfold] at hm
  have hbits : (a.div b).bits = UInt32.ofBitVec (pack Format.binary32
      (roundWithAccuracy Format.binary32 (sa / sb) (divCore Format.binary32 ma ea mb eb).1
        (divCore Format.binary32 ma ea mb eb).2.1
        (divCore Format.binary32 ma ea mb eb).2.2)) := by
    apply UInt32.eq_of_toBitVec_eq
    change (model32 (a.div b)).toBits = (ofModel FloatFormat.binary32 _).toBits
    rw [hm]
  cases hd : a.div b
  rw [hd] at hbits
  exact congrArg Binary32.mk hbits

private theorem div_pos_pos_class (a s : Binary32) (ha : a.Finite) (hs : s.Finite)
    (hapos : 0 < numerical32 a) (hspos : 0 < numerical32 s) :
    ((a.div s).Finite ∧ ¬ (a.div s).Negative) ∨ a.div s = ⟨0x7f800000⟩ := by
  obtain ⟨ma, ea, hma, hda⟩ := (decoded32_signed_finite a ha).1 hapos
  obtain ⟨ms, es, hms, hds⟩ := (decoded32_signed_finite s hs).1 hspos
  exact pack_roundWithAccuracy_pos_class (a.div s) _ _ _
    (div_eq_pack .positive .positive a s ma ea hma ha hda ms es hms hs hds)

private theorem div_pos_finite_of_bound (a s : Binary32) (ha : a.Finite) (hs : s.Finite)
    (hapos : 0 < numerical32 a) (hspos : 0 < numerical32 s) (k : Int) (hk : 24 ≤ k ∧ k ≤ 100)
    (hbound : |numerical32 a / numerical32 s| ≤ (2 : ℚ) ^ k) :
    (a.div s).Finite ∧ ¬ (a.div s).Negative := by
  have hs_nz : numerical32 s ≠ 0 := ne_of_gt hspos
  have hdiv_local := model_div_dyadic_local Format.binary32 (decoded32 a) (decoded32 s)
    (canonical32 a ha).2.1 (canonical32 s hs).2.1
    (by unfold numerical32 at hs_nz; exact hs_nz) k hbound
  have hfits : ModelFits Format.binary32
      (UnpackedFloat.div Format.binary32 (decoded32 a) (decoded32 s)) := by
    apply model_fits_of_value_bound Format.binary32 _
      (model_normalized_finite _ _ hdiv_local.1) (k + 1)
    · rw [show Format.binary32.exponentBits = 8 from rfl,
        show (Format.binary32.exponentBias : Int) = 127 from rfl,
        show (Format.binary32.mantissaBitsWithoutImplicit : Int) = 23 from rfl]
      omega
    have h2 := hdiv_local.2
    simp only [Format.mantissaBits, Format.minExponent] at h2
    rw [show (1 + 23 : Nat) = 24 from rfl,
      show (3 - (2 : Int) ^ (8 - 1) - ((24 : Nat) : Int)) = -149 from rfl] at h2
    have hmax : max (k + 1 - (24 : Nat)) (-149 : Int) = k + 1 - 24 := by omega
    rw [hmax, show (2 : ℚ) * (2 : ℚ) ^ (k + 1 - 24) = (2 : ℚ) ^ (k + 2 - 24) by
      rw [← zpow_one_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; congr 1; omega] at h2
    have h2le : (2 : ℚ) ^ (k + 2 - 24) ≤ (2 : ℚ) ^ k :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have htri := abs_add_le
      (unpackedValue (UnpackedFloat.div Format.binary32 (decoded32 a) (decoded32 s)) -
        unpackedValue (decoded32 a) / unpackedValue (decoded32 s))
      (unpackedValue (decoded32 a) / unpackedValue (decoded32 s))
    rw [sub_add_cancel] at htri
    change |unpackedValue (decoded32 a) / unpackedValue (decoded32 s)| ≤ (2 : ℚ) ^ k at hbound
    rw [show (2 : ℚ) ^ (k + 1) = (2 : ℚ) ^ k + (2 : ℚ) ^ k by
      rw [zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0), mul_two]]
    linarith [htri, h2, h2le, hbound]
  have hfin : (a.div s).Finite := by
    have hm := isFinite_ofModel32 _ hdiv_local.1 hfits
    rw [← model32_div a s ha hs] at hm
    exact (isFinite_model32 _).mp hm
  have hnneg : ¬ (a.div s).Negative := by
    rcases div_pos_pos_class a s ha hs hapos hspos with h | hinf
    · exact h.2
    · rw [hinf] at hfin
      exact absurd hfin (by decide)
  exact ⟨hfin, hnneg⟩

theorem div_pastLast_of_le (x y s : Binary32)
    (hx : x.Finite) (hy : y.Finite) (hs : s.Finite)
    (hxpos : 0 < numerical32 x) (hxy : numerical32 x ≤ numerical32 y) (hspos : 0 < numerical32 s)
    (hyok : isPastLast (y.div s) = false) :
    isPastLast (x.div s) = false := by
  have hy_pos : 0 < numerical32 y := lt_of_lt_of_le hxpos hxy
  have hy_fn : (y.div s).Finite ∧ ¬ (y.div s).Negative := by
    rcases div_pos_pos_class y s hy hs hy_pos hspos with h | hinf
    · exact h
    · rw [hinf] at hyok
      exact absurd hyok (by decide)
  have hy_lt63_q : numerical32 (y.div s) < ((2 ^ 63 : Nat) : ℚ) :=
    (isPastLast_lt_threshold (y.div s) hy_fn.1 hy_fn.2).mp hyok
  have hy_lt63 : ((numerical32 (y.div s) : ℚ) : ℝ) < ((2 ^ 63 : Nat) : ℝ) := by
    exact_mod_cast hy_lt63_q
  have hs_nz : numerical32 s ≠ 0 := ne_of_gt hspos
  have hy_round : ((numerical32 (y.div s) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 ((numerical32 y : ℝ) / (numerical32 s : ℝ)) :=
    binary32_div_roundAt y s hy hs hs_nz hy_fn.1
  have h263_round : roundAt FloatFormat.binary32 ((2 ^ 63 : Nat) : ℝ) = ((2 ^ 63 : Nat) : ℝ) :=
    roundAt_pow2 0x5f000000 (190 + 924) 63 (by decide)
      (by rw [show Conversion.magnitudeUnits32 ⟨0x5f000000⟩ = 2 ^ 23 * 2 ^ (190 + 924) by rfl])
      (by decide) (by decide)
  have hry_lt : (numerical32 y : ℝ) / (numerical32 s : ℝ) < ((2 ^ 63 : Nat) : ℝ) := by
    by_contra hge
    have hm := roundAt_mono FloatFormat.binary32 (le_of_not_gt hge)
    rw [h263_round, ← hy_round] at hm
    exact absurd (lt_of_le_of_lt hm hy_lt63) (lt_irrefl _)
  have hrx_le_ry :
      (numerical32 x : ℝ) / (numerical32 s : ℝ) ≤
        (numerical32 y : ℝ) / (numerical32 s : ℝ) := by
    have hs_r : (0 : ℝ) < (numerical32 s : ℝ) := by exact_mod_cast hspos
    exact div_le_div_of_nonneg_right (by exact_mod_cast hxy) (le_of_lt hs_r)
  have hx_q_bound : |numerical32 x / numerical32 s| ≤ (2 : ℚ) ^ (63 : Int) := by
    rw [abs_of_pos (div_pos hxpos hspos)]
    have hr : ((numerical32 x / numerical32 s : ℚ) : ℝ) < ((2 ^ 63 : Nat) : ℝ) := by
      push_cast; exact lt_of_le_of_lt hrx_le_ry hry_lt
    have hq : numerical32 x / numerical32 s < ((2 ^ 63 : Nat) : ℚ) := by exact_mod_cast hr
    have hcast : ((2 ^ 63 : Nat) : ℚ) = (2 : ℚ) ^ (63 : Int) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]; rfl
    exact le_of_lt (hcast ▸ hq)
  have hx_fn := div_pos_finite_of_bound x s hx hs hxpos hspos 63 (by omega) hx_q_bound
  have hx_round : ((numerical32 (x.div s) : ℚ) : ℝ) =
      roundAt FloatFormat.binary32 ((numerical32 x : ℝ) / (numerical32 s : ℝ)) :=
    binary32_div_roundAt x s hx hs hs_nz hx_fn.1
  have hx_lt63 : numerical32 (x.div s) < ((2 ^ 63 : Nat) : ℚ) := by
    have hr : ((numerical32 (x.div s) : ℚ) : ℝ) < ((2 ^ 63 : Nat) : ℝ) := by
      rw [hx_round]
      exact lt_of_le_of_lt (roundAt_mono FloatFormat.binary32 hrx_le_ry)
        (by rw [← hy_round]; exact hy_lt63)
    exact_mod_cast hr
  exact (isPastLast_lt_threshold (x.div s) hx_fn.1 hx_fn.2).mpr hx_lt63

private theorem coordinateFloat_pos_eq (c : Coordinate) (hpos : 0 ≤ c.val) :
    coordinateFloat c = Binary32.ofUInt64 c.val.natAbs.toUInt64 := by
  rw [coordinateFloat_eq, ite_eq_right (by omega)]

private theorem coordinateFloat_neg_eq (c : Coordinate) (hneg : c.val < 0) :
    coordinateFloat c = ⟨(Binary32.ofUInt64 c.val.natAbs.toUInt64).bits ^^^ 0x80000000⟩ := by
  rw [coordinateFloat_eq, ite_eq_left hneg]

private theorem coordinate_natAbs_le (c : Coordinate) : c.val.natAbs ≤ 2 ^ 63 := by
  have := c.property
  omega

theorem coordinateFloat_finite (c : Coordinate) : (coordinateFloat c).Finite := by
  have hf := (ofNat32_finite_and_roundAt c.val.natAbs (coordinate_natAbs_le c)).1
  by_cases hneg : c.val < 0
  · rw [coordinateFloat_neg_eq c hneg]
    exact finite_xor_sign _ hf
  · rw [coordinateFloat_pos_eq c (by omega)]
    exact hf

private theorem numerical32_xor_sign (x : Binary32) :
    numerical32 ⟨x.bits ^^^ 0x80000000⟩ = -numerical32 x := by
  unfold numerical32
  have hxor : decoded32 ⟨x.bits ^^^ 0x80000000⟩ = (decoded32 x).neg := by
    change unpack Format.binary32 (x.bits.toBitVec ^^^ 0x80000000#32) = _
    exact unpack_xor_sign x.bits.toBitVec
  rw [hxor]
  cases decoded32 x with
  | notANumber => rfl
  | infinity _ => rfl
  | zero _ => simp [UnpackedFloat.neg, unpackedValue]
  | finite sg _ _ _ => cases sg <;> simp [UnpackedFloat.neg, unpackedValue, signCoefficient]

private theorem coordinateFloat_neg_lt_zero (c : Coordinate) (hneg : c.val < 0) :
    numerical32 (coordinateFloat c) < 0 := by
  have hpos : 0 < numerical32 (Binary32.ofUInt64 c.val.natAbs.toUInt64) :=
    ofNat32_pos_of_pos c.val.natAbs (Int.natAbs_pos.mpr (by omega)) (coordinate_natAbs_le c)
  rw [coordinateFloat_neg_eq c hneg, numerical32_xor_sign]
  linarith

theorem coordinateFloat_abs_le (c : Coordinate) :
    |numerical32 (coordinateFloat c)| ≤ (2 : ℚ) ^ 63 := by
  have hr := ofNat32_finite_and_roundAt c.val.natAbs (coordinate_natAbs_le c)
  have h263_round : roundAt FloatFormat.binary32 ((2 ^ 63 : Nat) : ℝ) = ((2 ^ 63 : Nat) : ℝ) :=
    roundAt_pow2 0x5f000000 (190 + 924) 63 (by decide)
      (by rw [show Conversion.magnitudeUnits32 ⟨0x5f000000⟩ = 2 ^ 23 * 2 ^ (190 + 924) by rfl])
      (by decide) (by decide)
  have hmag_le : numerical32 (Binary32.ofUInt64 c.val.natAbs.toUInt64) ≤ (2 : ℚ) ^ 63 := by
    have hle_r : (c.val.natAbs : ℝ) ≤ ((2 ^ 63 : Nat) : ℝ) :=
      by exact_mod_cast coordinate_natAbs_le c
    have hm := roundAt_mono FloatFormat.binary32 hle_r
    rw [h263_round, ← hr.2] at hm
    have hq : numerical32 (Binary32.ofUInt64 c.val.natAbs.toUInt64) ≤ ((2 ^ 63 : Nat) : ℚ) := by
      exact_mod_cast hm
    rw [Nat.cast_pow, Nat.cast_ofNat] at hq
    exact hq
  have hmag_nonneg : 0 ≤ numerical32 (Binary32.ofUInt64 c.val.natAbs.toUInt64) := by
    by_cases hc0 : c.val.natAbs = 0
    · rw [hc0]
      have h0 : Binary32.ofUInt64 (0 : Nat).toUInt64 = .zero := by decide
      rw [h0]
      decide
    · exact le_of_lt (ofNat32_pos_of_pos c.val.natAbs (Nat.pos_of_ne_zero hc0)
        (coordinate_natAbs_le c))
  by_cases hneg : c.val < 0
  · rw [coordinateFloat_neg_eq c hneg, numerical32_xor_sign, abs_neg, abs_of_nonneg hmag_nonneg]
    exact hmag_le
  · rw [coordinateFloat_pos_eq c (by omega), abs_of_nonneg hmag_nonneg]
    exact hmag_le

private theorem nonfinite_unpack (s : Binary32) (hnf : ¬ s.Finite) :
    (Float32.Model.ofBits s.bits).unpack = .notANumber ∨
      ∃ sg, (Float32.Model.ofBits s.bits).unpack = .infinity sg := by
  have huf : (decoded32 s).isFinite = false := by
    cases hb : (decoded32 s).isFinite with
    | false => rfl
    | true => exact absurd ((model_decoded32_finite s).mp hb) hnf
  have hpack : Float32.Model.ofBits s.bits = Float32.Model.pack (decoded32 s) := rfl
  rw [hpack]
  cases hdu : decoded32 s with
  | notANumber => left; rfl
  | infinity sg => right; exact ⟨sg, by cases sg <;> rfl⟩
  | zero _ => rw [hdu] at huf; simp [UnpackedFloat.isFinite] at huf
  | finite _ _ _ _ => rw [hdu] at huf; simp [UnpackedFloat.isFinite] at huf

private theorem div_zero_not_pastLast (s : Binary32) :
    isPastLast ((⟨0⟩ : Binary32).div s) = false := by
  have h0_unpack : (Float32.Model.ofBits (0 : UInt32)).unpack = .zero .positive := rfl
  change isPastLast ⟨(Float32.Model.pack (UnpackedFloat.div Format.binary32
      (Float32.Model.ofBits (0 : UInt32)).unpack
      (Float32.Model.ofBits s.bits).unpack)).toBits⟩ = false
  rw [h0_unpack]
  cases (Float32.Model.ofBits s.bits).unpack with
  | notANumber =>
    exact (by decide : isPastLast ⟨UInt32.ofBitVec (pack Format.binary32 .notANumber)⟩ = false)
  | infinity sg =>
    cases sg with
    | positive =>
      exact (by decide :
        isPastLast ⟨UInt32.ofBitVec (pack Format.binary32 (.zero .positive))⟩ = false)
    | negative =>
      exact (by decide :
        isPastLast ⟨UInt32.ofBitVec (pack Format.binary32 (.zero .negative))⟩ = false)
  | zero _ =>
    exact (by decide : isPastLast ⟨UInt32.ofBitVec (pack Format.binary32 .notANumber)⟩ = false)
  | finite sg _ _ _ =>
    cases sg with
    | positive =>
      exact (by decide :
        isPastLast ⟨UInt32.ofBitVec (pack Format.binary32 (.zero .positive))⟩ = false)
    | negative =>
      exact (by decide :
        isPastLast ⟨UInt32.ofBitVec (pack Format.binary32 (.zero .negative))⟩ = false)

theorem coordinateFloat_div_pastLast_interval (lo c hi : Coordinate)
    (hlo_neg : lo.val < 0) (hhi_pos : 0 < hi.val)
    (hlo_le : lo.val ≤ c.val) (hc_le : c.val ≤ hi.val) (s : Binary32)
    (hlo : isPastLast ((coordinateFloat lo).div s) = false)
    (hhi : isPastLast ((coordinateFloat hi).div s) = false) :
    isPastLast ((coordinateFloat c).div s) = false := by
  by_cases hc0 : c.val = 0
  · have hcf0 : coordinateFloat c = ⟨0⟩ := by
      rw [coordinateFloat_pos_eq c (by omega), show c.val.natAbs = 0 by omega]
      decide
    rw [hcf0]
    exact div_zero_not_pastLast s
  · by_cases hsf : s.Finite
    · have hds_eq : (Float32.Model.ofBits s.bits).unpack = decoded32 s :=
        model_ofBits32_decoded s hsf
      have hnonzero : ∀ (hsz : numerical32 s = 0), False := by
        intro hsz
        have cs := canonical32 s hsf
        cases hs_d : decoded32 s with
        | notANumber => rw [hs_d] at cs; simp [UnpackedFloat.isFinite] at cs
        | infinity _ => rw [hs_d] at cs; simp [UnpackedFloat.isFinite] at cs
        | finite _ ms _ hms =>
          unfold numerical32 at hsz; rw [hs_d] at hsz
          simp only [unpackedValue, mul_eq_zero] at hsz
          rcases hsz with h1 | h2
          · rcases h1 with hsign | hm0
            · cases ‹Sign› <;> simp [signCoefficient] at hsign
            · exact absurd hm0 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hms))
          · exact absurd h2 (zpow_ne_zero _ (by norm_num))
        | zero sg =>
          cases sg with
          | positive =>
            have hhi_f := coordinateFloat_finite hi
            obtain ⟨mhi, ehi, hmhi, hdhi⟩ :=
              (decoded32_signed_finite (coordinateFloat hi) hhi_f).1 (by
                rw [coordinateFloat_pos_eq hi (by omega)]
                exact ofNat32_pos_of_pos hi.val.natAbs (by omega) (coordinate_natAbs_le hi))
            have hinf : (coordinateFloat hi).div s = ⟨0x7f800000⟩ := by
              change (⟨(Float32.Model.pack (UnpackedFloat.div Format.binary32
                  (Float32.Model.ofBits (coordinateFloat hi).bits).unpack
                  (Float32.Model.ofBits s.bits).unpack)).toBits⟩ : Binary32) = _
              rw [model_ofBits32_decoded _ hhi_f, hds_eq, hdhi, hs_d,
                show UnpackedFloat.div Format.binary32 (.finite .positive mhi ehi hmhi)
                  (.zero .positive) = .infinity .positive from rfl]
              decide
            rw [hinf] at hhi
            exact absurd hhi (by decide)
          | negative =>
            have hlo_f := coordinateFloat_finite lo
            have hlo_n := coordinateFloat_neg_lt_zero lo hlo_neg
            obtain ⟨mlo, elo, hmlo, hdlo⟩ :=
              (decoded32_signed_finite (coordinateFloat lo) hlo_f).2 hlo_n
            have hinf : (coordinateFloat lo).div s = ⟨0x7f800000⟩ := by
              change (⟨(Float32.Model.pack (UnpackedFloat.div Format.binary32
                  (Float32.Model.ofBits (coordinateFloat lo).bits).unpack
                  (Float32.Model.ofBits s.bits).unpack)).toBits⟩ : Binary32) = _
              rw [model_ofBits32_decoded _ hlo_f, hds_eq, hdlo, hs_d,
                show UnpackedFloat.div Format.binary32 (.finite .negative mlo elo hmlo)
                  (.zero .negative) = .infinity .positive from rfl]
              decide
            rw [hinf] at hlo
            exact absurd hlo (by decide)
      rcases lt_trichotomy (numerical32 s) 0 with hs_neg | hs_zero | hs_pos
      · obtain ⟨ms, es, hms, hds⟩ := (decoded32_signed_finite s hsf).2 hs_neg
        by_cases hc_pos : 0 < c.val
        · have hcf := coordinateFloat_finite c
          obtain ⟨mc, ec, hmc, hdc⟩ := (decoded32_signed_finite (coordinateFloat c) hcf).1 (by
            rw [coordinateFloat_pos_eq c (by omega)]
            exact ofNat32_pos_of_pos c.val.natAbs (by omega) (coordinate_natAbs_le c))
          exact pack_roundWithAccuracy_neg_not_pastLast ((coordinateFloat c).div s) _ _ _
            (div_eq_pack .positive .negative (coordinateFloat c) s
              mc ec hmc hcf hdc ms es hms hsf hds)
        · have hc_neg : c.val < 0 := by omega
          have hs_opp_f : (⟨s.bits ^^^ 0x80000000⟩ : Binary32).Finite := finite_xor_sign s hsf
          have hs_opp_pos : 0 < numerical32 ⟨s.bits ^^^ 0x80000000⟩ := by
            rw [numerical32_xor_sign]; linarith
          have hcm_f := (ofNat32_finite_and_roundAt c.val.natAbs (coordinate_natAbs_le c)).1
          have hlom_f := (ofNat32_finite_and_roundAt lo.val.natAbs (coordinate_natAbs_le lo)).1
          have hcm_pos := ofNat32_pos_of_pos c.val.natAbs
            (Int.natAbs_pos.mpr hc0) (coordinate_natAbs_le c)
          have hcm_le_lom : numerical32 (Binary32.ofUInt64 c.val.natAbs.toUInt64) ≤
              numerical32 (Binary32.ofUInt64 lo.val.natAbs.toUInt64) := by
            have h1 := (ofNat32_finite_and_roundAt c.val.natAbs (coordinate_natAbs_le c)).2
            have h2 := (ofNat32_finite_and_roundAt lo.val.natAbs (coordinate_natAbs_le lo)).2
            have hle_n : (c.val.natAbs : ℝ) ≤ (lo.val.natAbs : ℝ) :=
              by exact_mod_cast (by omega : c.val.natAbs ≤ lo.val.natAbs)
            have hm := roundAt_mono FloatFormat.binary32 hle_n
            rw [← h1, ← h2] at hm
            exact_mod_cast hm
          have hs_inv : (⟨s.bits ^^^ 0x80000000 ^^^ 0x80000000⟩ : Binary32) = s := by
            cases s with | mk b =>
              congr 1
              exact UInt32.eq_of_toBitVec_eq (by
                rw [UInt32.toBitVec_xor, UInt32.toBitVec_xor, BitVec.xor_assoc,
                  BitVec.xor_self, BitVec.xor_zero])
          have hc_div : (coordinateFloat c).div s =
              (Binary32.ofUInt64 c.val.natAbs.toUInt64).div ⟨s.bits ^^^ 0x80000000⟩ := by
            rw [coordinateFloat_neg_eq c hc_neg]
            have := div_xor_sign_finite (Binary32.ofUInt64 c.val.natAbs.toUInt64)
              ⟨s.bits ^^^ 0x80000000⟩ hcm_f hs_opp_f
            simpa [hs_inv] using this
          have hlo_div : (coordinateFloat lo).div s =
              (Binary32.ofUInt64 lo.val.natAbs.toUInt64).div ⟨s.bits ^^^ 0x80000000⟩ := by
            rw [coordinateFloat_neg_eq lo hlo_neg]
            have := div_xor_sign_finite (Binary32.ofUInt64 lo.val.natAbs.toUInt64)
              ⟨s.bits ^^^ 0x80000000⟩ hlom_f hs_opp_f
            simpa [hs_inv] using this
          rw [hc_div]
          rw [hlo_div] at hlo
          exact div_pastLast_of_le _ _ _ hcm_f hlom_f hs_opp_f hcm_pos hcm_le_lom hs_opp_pos hlo
      · exact False.elim (hnonzero hs_zero)
      · obtain ⟨ms, es, hms, hds⟩ := (decoded32_signed_finite s hsf).1 hs_pos
        by_cases hc_pos : 0 < c.val
        · have hcf := coordinateFloat_finite c
          have hhif := coordinateFloat_finite hi
          have hc_p : 0 < numerical32 (coordinateFloat c) := by
            rw [coordinateFloat_pos_eq c (by omega)]
            exact ofNat32_pos_of_pos c.val.natAbs (by omega) (coordinate_natAbs_le c)
          have hc_le_hi : numerical32 (coordinateFloat c) ≤ numerical32 (coordinateFloat hi) := by
            rw [coordinateFloat_pos_eq c (by omega), coordinateFloat_pos_eq hi (by omega)]
            have h1 := (ofNat32_finite_and_roundAt c.val.natAbs (coordinate_natAbs_le c)).2
            have h2 := (ofNat32_finite_and_roundAt hi.val.natAbs (coordinate_natAbs_le hi)).2
            have hle_n : (c.val.natAbs : ℝ) ≤ (hi.val.natAbs : ℝ) :=
              by exact_mod_cast (by omega : c.val.natAbs ≤ hi.val.natAbs)
            have hm := roundAt_mono FloatFormat.binary32 hle_n
            rw [← h1, ← h2] at hm
            exact_mod_cast hm
          exact div_pastLast_of_le (coordinateFloat c) (coordinateFloat hi) s
            hcf hhif hsf hc_p hc_le_hi hs_pos hhi
        · have hc_neg : c.val < 0 := by omega
          have hcf := coordinateFloat_finite c
          have hcn := coordinateFloat_neg_lt_zero c hc_neg
          obtain ⟨mc, ec, hmc, hdc⟩ := (decoded32_signed_finite (coordinateFloat c) hcf).2 hcn
          exact pack_roundWithAccuracy_neg_not_pastLast ((coordinateFloat c).div s) _ _ _
            (div_eq_pack .negative .positive (coordinateFloat c) s
              mc ec hmc hcf hdc ms es hms hsf hds)
    · have hcf := coordinateFloat_finite c
      have hcd := canonical32 (coordinateFloat c) hcf
      rcases nonfinite_unpack s hsf with hnan | ⟨sg, hinf⟩
      · have hdiv_nan : (coordinateFloat c).div s =
            ⟨UInt32.ofBitVec (pack Format.binary32 .notANumber)⟩ := by
          change (⟨(Float32.Model.pack (UnpackedFloat.div Format.binary32
              (Float32.Model.ofBits (coordinateFloat c).bits).unpack
              (Float32.Model.ofBits s.bits).unpack)).toBits⟩ : Binary32) = _
          rw [hnan]
          cases (Float32.Model.ofBits (coordinateFloat c).bits).unpack <;> rfl
        rw [hdiv_nan]
        decide
      · cases hu : (Float32.Model.ofBits (coordinateFloat c).bits).unpack with
        | notANumber =>
          rw [model_ofBits32_decoded _ hcf] at hu
          rw [hu] at hcd; simp [UnpackedFloat.isFinite] at hcd
        | infinity _ =>
          rw [model_ofBits32_decoded _ hcf] at hu
          rw [hu] at hcd; simp [UnpackedFloat.isFinite] at hcd
        | zero sc =>
          have hdiv_z : (coordinateFloat c).div s =
              ⟨UInt32.ofBitVec (pack Format.binary32 (.zero (sc / sg)))⟩ := by
            change (⟨(Float32.Model.pack (UnpackedFloat.div Format.binary32
                (Float32.Model.ofBits (coordinateFloat c).bits).unpack
                (Float32.Model.ofBits s.bits).unpack)).toBits⟩ : Binary32) = _
            rw [hu, hinf]
            rfl
          rw [hdiv_z]
          cases (sc / sg) <;> decide
        | finite sc _ _ _ =>
          have hdiv_z : (coordinateFloat c).div s =
              ⟨UInt32.ofBitVec (pack Format.binary32 (.zero (sc / sg)))⟩ := by
            change (⟨(Float32.Model.pack (UnpackedFloat.div Format.binary32
                (Float32.Model.ofBits (coordinateFloat c).bits).unpack
                (Float32.Model.ofBits s.bits).unpack)).toBits⟩ : Binary32) = _
            rw [hu, hinf]
            rfl
          rw [hdiv_z]
          cases (sc / sg) <;> decide

theorem binary32_mul_two_bounds (x : Binary32) (hx : x.Finite)
    (hlo : 8 ≤ numerical32 x) (hhi : numerical32 x ≤ 2 ^ 31) :
    (x.mul ⟨0x40000000⟩).Finite ∧
      8 ≤ numerical32 (x.mul ⟨0x40000000⟩) ∧
      numerical32 (x.mul ⟨0x40000000⟩) ≤ 2 * 2 ^ 31 := by
  have h2_fin : (⟨0x40000000⟩ : Binary32).Finite := by decide
  have h2_val : numerical32 ⟨0x40000000⟩ = 2 := by
    have h := pow2_word_eq_rat 0x40000000 (128 + 924) 1 h2_fin
      (by rw [show Conversion.magnitudeUnits32 ⟨0x40000000⟩ = 2 ^ 23 * 2 ^ (128 + 924) by rfl])
      (by decide) (by decide)
    simpa using h
  have hc := canonical32 x hx
  have hc2 := canonical32 ⟨0x40000000⟩ h2_fin
  have hnorm_err := model_mul_dyadic_local Format.binary32
    (decoded32 x) (decoded32 ⟨0x40000000⟩)
    hc.2.1 hc2.2.1 32 (by
      change |numerical32 x * numerical32 ⟨0x40000000⟩| ≤ 2 ^ 32
      rw [h2_val, abs_of_nonneg (by linarith)]
      linarith [show (2 : ℚ) ^ 31 * 2 = 2 ^ 32 by norm_num])
  have hfits : ModelFits Format.binary32
      (UnpackedFloat.mul Format.binary32 (decoded32 x) (decoded32 ⟨0x40000000⟩)) := by
    apply model_fits_of_value_bound Format.binary32 _ (model_normalized_finite _ _ hnorm_err.1) 33
      (by decide)
    have h2 := hnorm_err.2
    simp only [Format.mantissaBits, Format.minExponent] at h2
    have htri := abs_add_le
      (unpackedValue (UnpackedFloat.mul Format.binary32
          (decoded32 x) (decoded32 ⟨0x40000000⟩)) -
        unpackedValue (decoded32 x) * unpackedValue (decoded32 ⟨0x40000000⟩))
      (unpackedValue (decoded32 x) * unpackedValue (decoded32 ⟨0x40000000⟩))
    rw [sub_add_cancel] at htri
    change _ ≤ (2 : ℚ) ^ 33
    change |unpackedValue (UnpackedFloat.mul Format.binary32 (decoded32 x)
        (decoded32 ⟨0x40000000⟩)) - numerical32 x * numerical32 ⟨0x40000000⟩| ≤ _ at h2
    rw [h2_val] at h2
    have h2_q : numerical32 x * 2 =
        unpackedValue (decoded32 x) * unpackedValue (decoded32 ⟨0x40000000⟩) := by
      change numerical32 x * 2 = numerical32 x * numerical32 ⟨0x40000000⟩
      rw [h2_val]
    rw [← h2_q] at htri
    have h_abs : |numerical32 x * 2| ≤ 4294967296 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    norm_num at h2 ⊢
    linarith [htri, h_abs]
  have hfin : (x.mul ⟨0x40000000⟩).Finite := by
    have hm := isFinite_ofModel32 _ hnorm_err.1 hfits
    rw [← model32_mul x ⟨0x40000000⟩ hx h2_fin] at hm
    exact (isFinite_model32 _).mp hm
  have hmul_round := binary32_mul_roundAt x ⟨0x40000000⟩ hx h2_fin hfin
  rw [h2_val, Rat.cast_ofNat] at hmul_round
  have h8_round : roundAt FloatFormat.binary32 ((2 ^ 3 : Nat) : ℝ) = ((2 ^ 3 : Nat) : ℝ) :=
    roundAt_pow2 0x41000000 (130 + 924) 3 (by decide)
      (by rw [show Conversion.magnitudeUnits32 ⟨0x41000000⟩ = 2 ^ 23 * 2 ^ (130 + 924) by rfl])
      (by decide) (by decide)
  have h232_round :
      roundAt FloatFormat.binary32 ((2 ^ 32 : Nat) : ℝ) = ((2 ^ 32 : Nat) : ℝ) :=
    roundAt_pow2 0x4f800000 (159 + 924) 32 (by decide)
      (by rw [show Conversion.magnitudeUnits32 ⟨0x4f800000⟩ = 2 ^ 23 * 2 ^ (159 + 924) by rfl])
      (by decide) (by decide)
  refine ⟨hfin, ?_, ?_⟩
  · have hm := roundAt_mono FloatFormat.binary32
        (show ((2 ^ 3 : Nat) : ℝ) ≤ (numerical32 x : ℝ) * 2 by
          have : (8 : ℝ) ≤ (numerical32 x : ℝ) := by exact_mod_cast hlo
          norm_num; linarith)
    rw [h8_round, ← hmul_round] at hm
    have hq : ((2 ^ 3 : Nat) : ℚ) ≤ numerical32 (x.mul ⟨0x40000000⟩) := by exact_mod_cast hm
    norm_num at hq; exact hq
  · have hm := roundAt_mono FloatFormat.binary32
        (show (numerical32 x : ℝ) * 2 ≤ ((2 ^ 32 : Nat) : ℝ) by
          have : (numerical32 x : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hhi
          norm_num; linarith)
    rw [h232_round, ← hmul_round] at hm
    have hq : numerical32 (x.mul ⟨0x40000000⟩) ≤ ((2 ^ 32 : Nat) : ℚ) := by
      exact_mod_cast hm
    norm_num at hq ⊢; exact hq

theorem binary32_mul_two_le_finite (x upper : Binary32) (hx : x.Finite) (hu : upper.Finite)
    (hlo : 8 ≤ numerical32 x) (hhi : numerical32 x ≤ 2 ^ 31)
    (hupper : numerical32 x * 2 ≤ numerical32 upper) :
    (x.mul ⟨0x40000000⟩).Finite ∧
      8 ≤ numerical32 (x.mul ⟨0x40000000⟩) ∧
      numerical32 (x.mul ⟨0x40000000⟩) ≤ numerical32 upper := by
  have hb := binary32_mul_two_bounds x hx hlo hhi
  refine ⟨hb.1, hb.2.1, ?_⟩
  have h2_fin : (⟨0x40000000⟩ : Binary32).Finite := by decide
  have h2_val : numerical32 ⟨0x40000000⟩ = 2 := by
    have h := pow2_word_eq_rat 0x40000000 (128 + 924) 1 h2_fin
      (by rw [show Conversion.magnitudeUnits32 ⟨0x40000000⟩ = 2 ^ 23 * 2 ^ (128 + 924) by rfl])
      (by decide) (by decide)
    simpa using h
  have hmul_round := binary32_mul_roundAt x ⟨0x40000000⟩ hx h2_fin hb.1
  rw [h2_val, Rat.cast_ofNat] at hmul_round
  have hu_round : roundAt FloatFormat.binary32 (numerical32 upper : ℝ) = numerical32 upper := by
    rw [← toReal_model32]
    exact roundAt_toReal_eq (model32 upper) ((isFinite_model32 _).mpr hu)
  have hm := roundAt_mono FloatFormat.binary32
    (show (numerical32 x : ℝ) * 2 ≤ numerical32 upper by exact_mod_cast hupper)
  rw [hu_round, ← hmul_round] at hm
  exact_mod_cast hm

theorem coordinateFloat_div_ge_eight_not_pastLast (c : Coordinate) (s : Binary32)
    (hs : s.Finite) (hs8 : 8 ≤ numerical32 s) :
    isPastLast ((coordinateFloat c).div s) = false := by
  have hs_pos : 0 < numerical32 s := by linarith
  have hs_nz : numerical32 s ≠ 0 := ne_of_gt hs_pos
  have hcf := coordinateFloat_finite c
  by_cases hc0 : c.val = 0
  · have hcf0 : coordinateFloat c = ⟨0⟩ := by
      rw [coordinateFloat_pos_eq c (by omega), show c.val.natAbs = 0 by omega]
      decide
    rw [hcf0]
    exact div_zero_not_pastLast s
  · by_cases hneg : c.val < 0
    · obtain ⟨ms, es, hms, hds⟩ := (decoded32_signed_finite s hs).1 hs_pos
      have hcn := coordinateFloat_neg_lt_zero c hneg
      obtain ⟨mc, ec, hmc, hdc⟩ := (decoded32_signed_finite (coordinateFloat c) hcf).2 hcn
      exact pack_roundWithAccuracy_neg_not_pastLast ((coordinateFloat c).div s) _ _ _
        (div_eq_pack .negative .positive (coordinateFloat c) s
          mc ec hmc hcf hdc ms es hms hs hds)
    · have hc_pos : 0 < numerical32 (coordinateFloat c) := by
        rw [coordinateFloat_pos_eq c (by omega)]
        exact ofNat32_pos_of_pos c.val.natAbs (by omega) (coordinate_natAbs_le c)
      have hbound :
          |numerical32 (coordinateFloat c) / numerical32 s| ≤ (2 : ℚ) ^ (60 : Int) := by
        have hc_abs := coordinateFloat_abs_le c
        rw [abs_div, div_le_iff₀ (abs_pos.mpr hs_nz), abs_of_pos hs_pos]
        exact le_trans hc_abs (by nlinarith [show (2 : ℚ) ^ 63 = (2 : ℚ) ^ 60 * 8 by norm_num])
      have hdiv_fn := div_pos_finite_of_bound (coordinateFloat c) s hcf hs hc_pos hs_pos
        60 (by omega) hbound
      have hdiv_round := binary32_div_roundAt (coordinateFloat c) s hcf hs hs_nz hdiv_fn.1
      have h260_round :
          roundAt FloatFormat.binary32 ((2 ^ 60 : Nat) : ℝ) = ((2 ^ 60 : Nat) : ℝ) :=
        roundAt_pow2 0x5d800000 (187 + 924) 60 (by decide)
          (by rw [show Conversion.magnitudeUnits32 ⟨0x5d800000⟩ =
            2 ^ 23 * 2 ^ (187 + 924) by rfl])
          (by decide) (by decide)
      have hlt63 : numerical32 ((coordinateFloat c).div s) < ((2 ^ 63 : Nat) : ℚ) := by
        have hr_le : (numerical32 (coordinateFloat c) : ℝ) / (numerical32 s : ℝ) ≤
            ((2 ^ 60 : Nat) : ℝ) := by
          have hq : numerical32 (coordinateFloat c) / numerical32 s ≤ ((2 ^ 60 : Nat) : ℚ) := by
            have hle := (abs_le.mp hbound).2
            have hcast : ((2 ^ 60 : Nat) : ℚ) = (2 : ℚ) ^ (60 : Int) := by
              rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]; rfl
            exact hcast ▸ hle
          exact_mod_cast hq
        have hm := roundAt_mono FloatFormat.binary32 hr_le
        rw [h260_round, ← hdiv_round] at hm
        have hpow : ((2 ^ 60 : Nat) : ℝ) < ((2 ^ 63 : Nat) : ℝ) := by
          exact_mod_cast (by decide : (2 ^ 60 : Nat) < 2 ^ 63)
        exact_mod_cast lt_of_le_of_lt hm hpow
      exact (isPastLast_lt_threshold ((coordinateFloat c).div s) hdiv_fn.1 hdiv_fn.2).mpr hlt63

theorem octaveScale_ofNat_not_pastLast (sNat : Nat) (hs_lo : 8 ≤ sNat) (hs_hi : sNat ≤ 2 ^ 28)
    (c : Coordinate) (octave : Nat) (hoct : octave < 4) :
    isPastLast ((coordinateFloat c).div
      (octaveScale (Binary32.ofUInt64 sNat.toUInt64) octave)) = false := by
  have hs_r := ofNat32_finite_and_roundAt sNat (by omega)
  have h8_round : roundAt FloatFormat.binary32 ((2 ^ 3 : Nat) : ℝ) = ((2 ^ 3 : Nat) : ℝ) :=
    roundAt_pow2 0x41000000 (130 + 924) 3 (by decide)
      (by rw [show Conversion.magnitudeUnits32 ⟨0x41000000⟩ = 2 ^ 23 * 2 ^ (130 + 924) by rfl])
      (by decide) (by decide)
  have h228_fin : (⟨0x4d800000⟩ : Binary32).Finite := by decide
  have h228_round :
      roundAt FloatFormat.binary32 ((2 ^ 28 : Nat) : ℝ) = ((2 ^ 28 : Nat) : ℝ) :=
    roundAt_pow2 0x4d800000 (155 + 924) 28 h228_fin
      (by rw [show Conversion.magnitudeUnits32 ⟨0x4d800000⟩ =
        2 ^ 23 * 2 ^ (155 + 924) by rfl]) (by decide) (by decide)
  have hs0_lo : 8 ≤ numerical32 (Binary32.ofUInt64 sNat.toUInt64) := by
    have hm := roundAt_mono FloatFormat.binary32
      (show ((2 ^ 3 : Nat) : ℝ) ≤ (sNat : ℝ) by exact_mod_cast (by omega : 2 ^ 3 ≤ sNat))
    rw [h8_round, ← hs_r.2] at hm
    have hq : ((2 ^ 3 : Nat) : ℚ) ≤ numerical32 (Binary32.ofUInt64 sNat.toUInt64) :=
      by exact_mod_cast hm
    norm_num at hq; exact hq
  have hs0_hi28 : numerical32 (Binary32.ofUInt64 sNat.toUInt64) ≤ ((2 ^ 28 : Nat) : ℚ) := by
    have hm := roundAt_mono FloatFormat.binary32
      (show (sNat : ℝ) ≤ ((2 ^ 28 : Nat) : ℝ) by exact_mod_cast hs_hi)
    rw [h228_round, ← hs_r.2] at hm
    exact_mod_cast hm
  have hs0_hi31 : numerical32 (Binary32.ofUInt64 sNat.toUInt64) ≤ 2 ^ 31 := by
    have hq : ((2 ^ 28 : Nat) : ℚ) ≤ 2 ^ 31 := by norm_num
    exact le_trans hs0_hi28 hq
  have h229_fin : (⟨0x4e000000⟩ : Binary32).Finite := by decide
  have h229_val : numerical32 ⟨0x4e000000⟩ = ((2 ^ 29 : Nat) : ℚ) :=
    pow2_word_eq_rat 0x4e000000 (156 + 924) 29 h229_fin
      (by rw [show Conversion.magnitudeUnits32 ⟨0x4e000000⟩ =
        2 ^ 23 * 2 ^ (156 + 924) by rfl]) (by decide) (by decide)
  have h230_fin : (⟨0x4e800000⟩ : Binary32).Finite := by decide
  have h230_val : numerical32 ⟨0x4e800000⟩ = ((2 ^ 30 : Nat) : ℚ) :=
    pow2_word_eq_rat 0x4e800000 (157 + 924) 30 h230_fin
      (by rw [show Conversion.magnitudeUnits32 ⟨0x4e800000⟩ =
        2 ^ 23 * 2 ^ (157 + 924) by rfl]) (by decide) (by decide)
  have h231_fin : (⟨0x4f000000⟩ : Binary32).Finite := by decide
  have h231_val : numerical32 ⟨0x4f000000⟩ = ((2 ^ 31 : Nat) : ℚ) :=
    pow2_word_eq_rat 0x4f000000 (158 + 924) 31 h231_fin
      (by rw [show Conversion.magnitudeUnits32 ⟨0x4f000000⟩ =
        2 ^ 23 * 2 ^ (158 + 924) by rfl]) (by decide) (by decide)
  have hs1 := binary32_mul_two_le_finite (Binary32.ofUInt64 sNat.toUInt64) ⟨0x4e000000⟩
    hs_r.1 h229_fin hs0_lo hs0_hi31 (by
      rw [h229_val]
      have hmul := mul_le_mul_of_nonneg_right hs0_hi28 (by norm_num : (0 : ℚ) ≤ 2)
      norm_num at hmul ⊢; exact hmul)
  have hs1_hi31 : numerical32 (octaveScale (Binary32.ofUInt64 sNat.toUInt64) 1) ≤ 2 ^ 31 := by
    change numerical32 ((Binary32.ofUInt64 sNat.toUInt64).mul ⟨0x40000000⟩) ≤ 2 ^ 31
    have hq : numerical32 ⟨0x4e000000⟩ ≤ 2 ^ 31 := by rw [h229_val]; norm_num
    exact le_trans hs1.2.2 hq
  have hs2 := binary32_mul_two_le_finite
    (octaveScale (Binary32.ofUInt64 sNat.toUInt64) 1) ⟨0x4e800000⟩
    hs1.1 h230_fin hs1.2.1 hs1_hi31 (by
      rw [h230_val]
      have h1_le : numerical32 (octaveScale (Binary32.ofUInt64 sNat.toUInt64) 1) ≤
          ((2 ^ 29 : Nat) : ℚ) := by rw [← h229_val]; exact hs1.2.2
      have hmul := mul_le_mul_of_nonneg_right h1_le (by norm_num : (0 : ℚ) ≤ 2)
      norm_num at hmul ⊢; exact hmul)
  have hs2_hi31 : numerical32 (octaveScale (Binary32.ofUInt64 sNat.toUInt64) 2) ≤ 2 ^ 31 := by
    change numerical32 ((octaveScale (Binary32.ofUInt64 sNat.toUInt64) 1).mul ⟨0x40000000⟩) ≤
      2 ^ 31
    have hq : numerical32 ⟨0x4e800000⟩ ≤ 2 ^ 31 := by rw [h230_val]; norm_num
    exact le_trans hs2.2.2 hq
  have hs3 := binary32_mul_two_le_finite
    (octaveScale (Binary32.ofUInt64 sNat.toUInt64) 2) ⟨0x4f000000⟩
    hs2.1 h231_fin hs2.2.1 hs2_hi31 (by
      rw [h231_val]
      have h2_le : numerical32 (octaveScale (Binary32.ofUInt64 sNat.toUInt64) 2) ≤
          ((2 ^ 30 : Nat) : ℚ) := by rw [← h230_val]; exact hs2.2.2
      have hmul := mul_le_mul_of_nonneg_right h2_le (by norm_num : (0 : ℚ) ≤ 2)
      norm_num at hmul ⊢; exact hmul)
  have hoct_fin : (octaveScale (Binary32.ofUInt64 sNat.toUInt64) octave).Finite ∧
      8 ≤ numerical32 (octaveScale (Binary32.ofUInt64 sNat.toUInt64) octave) := by
    rcases octave with _ | _ | _ | _ | _
    · exact ⟨hs_r.1, hs0_lo⟩
    · exact ⟨hs1.1, hs1.2.1⟩
    · exact ⟨hs2.1, hs2.2.1⟩
    · exact ⟨hs3.1, hs3.2.1⟩
    · omega
  exact coordinateFloat_div_ge_eight_not_pastLast c _ hoct_fin.1 hoct_fin.2

end WorldAdmissionBridge

end AcornVerif.FloatLibBridge
