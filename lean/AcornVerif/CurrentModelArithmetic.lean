/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentLearnerArithmetic

/-!
# Machine arithmetic for raw scalar backups

The small reward-duration intermediate is bounded before its addition to the
raw aggregate continuation. These lemmas connect the executing binary32
wrappers to the pinned standard model; native compiler/runtime correspondence
remains trusted. No real-arithmetic identity is substituted for rounded execution.
-/
open Acorn
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOperations AcornVerif.CurrentLearnerArithmetic
namespace AcornVerif.CurrentModelArithmetic

/-- A normalized small intermediate with at most unit rounding error fits binary32. -/
theorem small_fits (value : UnpackedFloat) (exactValue : ℚ)
    (normal : ModelNormalized Format.binary32 value) (bound : |exactValue| ≤ 512)
    (error : |unpackedValue value - exactValue| ≤ 1) : ModelFits Format.binary32 value := by
  apply model_fits_of_value_bound Format.binary32 value
    (model_normalized_finite _ _ normal) 10 (by decide)
  have triangle := abs_add_le (unpackedValue value - exactValue) exactValue
  rw [sub_add_cancel] at triangle
  norm_num
  linarith only [triangle, bound, error]

/-- Actual small binary32 multiplication is finite and has at most unit absolute error. -/
theorem small_mul (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left * numerical32 right| ≤ 512) :
    (left.mul right).Finite ∧
      |numerical32 (left.mul right) - numerical32 left * numerical32 right| ≤ 1 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_mul_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 9 (by norm_num [numerical32] at bound ⊢; exact bound)
  have error : |unpackedValue (UnpackedFloat.mul Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left * numerical32 right| ≤ 1 := by
    apply le_trans operation.2
    norm_num [Format.mantissaBits, Format.minExponent]
  have decoded := mul32_decoded left right hl hr operation.1
    (small_fits _ _ operation.1 bound error)
  constructor
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using error

/-- Actual small binary32 subtraction is finite and has at most unit absolute error. -/
theorem small_sub (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left - numerical32 right| ≤ 512) :
    (left.sub right).Finite ∧
      |numerical32 (left.sub right) - (numerical32 left - numerical32 right)| ≤ 1 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_sub_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 9 (by norm_num [numerical32] at bound ⊢; exact bound)
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
  constructor
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using error

end AcornVerif.CurrentModelArithmetic
