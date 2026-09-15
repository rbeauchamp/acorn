/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.AgreementReturn
import AcornVerif.AgreementPrecision

/-!
# Precision of the emitted process-session instrument

Exact integer allowances are interpreted in the same least-subnormal coordinate
as executed forecasts and returns. Rational admission, maximum and ceiling
projection preserve conservative bounds without floating arithmetic.
-/
namespace AcornVerif.AgreementTelemetryPrecision
open Acorn Acorn.Agreement AcornVerif.CurrentAgreement AcornVerif.AgreementReturn
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder

/-- Successful ratio admission retains its exact numerator and denominator. -/
theorem admit_fields (n d : Nat) (ratio : Ratio) (admitted : Ratio.admit n d = some ratio) :
    ratio.numerator = n ∧ ratio.denominator = d := by
  unfold Ratio.admit at admitted
  split at admitted
  · split at admitted
    · cases admitted; exact ⟨rfl, rfl⟩
    · contradiction
  · contradiction

/-- The executable return allowance is exactly the proved binary32 error radius. -/
theorem return_units (steps : Nat) :
    (returnRoundingUnits steps : ℚ) / 2^unitExponent = returnRadius steps := by
  norm_num [returnRoundingUnits, returnRadius, unitExponent, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]
  ring

/-- The executable power allowance is exactly the per-multiplication error sum. -/
theorem power_units (steps : Nat) :
    (powerRoundingUnits steps : ℚ) / 2^unitExponent = (steps : ℚ) / 8388608 := by
  norm_num [powerRoundingUnits, unitExponent, Nat.cast_mul]
  ring

/-- Maximum merging retains a bound for both included populations. -/
theorem maximum_bounds (left right : Ratio) :
    (left.numerator : ℚ) / left.denominator ≤
      ((left.maximum right).numerator : ℚ) / (left.maximum right).denominator ∧
    (right.numerator : ℚ) / right.denominator ≤
      ((left.maximum right).numerator : ℚ) / (left.maximum right).denominator := by
  have lp : (0 : ℚ) < left.denominator := by exact_mod_cast left.positive
  have rp : (0 : ℚ) < right.denominator := by exact_mod_cast right.positive
  unfold Ratio.maximum
  split
  · constructor
    · apply (div_le_div_iff₀ lp rp).mpr
      assumption_mod_cast
    · exact le_rfl
  · constructor
    · exact le_rfl
    · apply (div_le_div_iff₀ rp lp).mpr
      rename_i h
      exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge h)

/-- Ceiling projection never understates an exact allowance. -/
theorem upperUnits_bound (ratio : Ratio) :
    (ratio.numerator : ℚ) / ratio.denominator ≤ (ratio.upperUnits : ℚ) / displayScale := by
  have denominator : (0 : ℚ) < ratio.denominator := by exact_mod_cast ratio.positive
  have scale : (0 : ℚ) < displayScale := by norm_num [displayScale]
  apply (div_le_div_iff₀ denominator scale).mpr
  have division := Nat.mod_lt
    (ratio.numerator * displayScale + ratio.denominator - 1) ratio.positive
  have reconstruction := Nat.mod_add_div (ratio.numerator * displayScale + ratio.denominator - 1)
    ratio.denominator
  have bound : ratio.numerator * displayScale ≤ ratio.upperUnits * ratio.denominator := by
    unfold Ratio.upperUnits
    have positive := ratio.positive
    have comm := Nat.mul_comm ratio.denominator
      ((ratio.numerator * displayScale + ratio.denominator - 1) / ratio.denominator)
    omega
  exact_mod_cast bound

/-- Native precision admission preserves both exact integer fractions. -/
theorem precision_fields (discount : Discount) (steps : Nat) (power : Binary32)
    (value : Precision) (admitted : precision discount steps power = some value) :
    value.rounding.numerator = returnRoundingUnits steps ∧
    value.rounding.denominator = envelopeUnits discount ∧
    value.tail.numerator = (magnitudeUnits power + powerRoundingUnits steps) * 2^unitExponent ∧
    value.tail.denominator =
      (2^unitExponent - magnitudeUnits discount.gamma) * envelopeUnits discount := by
  unfold precision at admitted
  split at admitted
  · contradiction
  · cases tailEquation : Ratio.admit
        ((magnitudeUnits power + powerRoundingUnits steps) * 2^unitExponent)
        ((2^unitExponent - magnitudeUnits discount.gamma) * envelopeUnits discount) with
    | none => simp [tailEquation] at admitted
    | some tail =>
      cases roundingEquation : Ratio.admit (returnRoundingUnits steps) (envelopeUnits discount) with
      | none => simp [tailEquation, roundingEquation] at admitted
      | some rounding =>
        simp only [tailEquation, roundingEquation, Option.pure_def] at admitted
        cases admitted
        obtain ⟨rnum, rden⟩ := admit_fields _ _ _ roundingEquation
        obtain ⟨tnum, tden⟩ := admit_fields _ _ _ tailEquation
        exact ⟨rnum, rden, tnum, tden⟩

/-- Unsigned word coordinates denote the absolute numerical operand. -/
theorem magnitude_value (word : Binary32) (finite : word.Finite) :
    (magnitudeUnits word : ℚ) / 2^unitExponent = |numerical32 word| := by
  rw [numerical32_abs_units word finite, ← magnitudeUnits_exact]
  norm_num [unitExponent]
  ring

/-- The admitted envelope is strictly positive in the actual word interpretation. -/
theorem envelope_positive (discount : Discount) : 0 < numerical32 (errorEnvelope discount) := by
  rw [(envelope_twice discount).2]
  have domain := geometric_domain discount
  linarith [domain.2.2.2.2.1]

/-- Envelope coordinates use the same positive scale as the actual error bound. -/
theorem envelope_value (discount : Discount) :
    (envelopeUnits discount : ℚ) / 2^unitExponent = numerical32 (errorEnvelope discount) := by
  rw [envelopeUnits, magnitude_value _ (envelope_twice discount).1,
    abs_of_pos (envelope_positive discount)]

/-- The decoded discount is strictly below one whole dyadic unit. -/
theorem gamma_coordinate (discount : Discount) :
    magnitudeUnits discount.gamma < 2^unitExponent := by
  cases discount <;> decide

/-- Executed discount coordinates retain their exact rational interpretation. -/
theorem gamma_value (discount : Discount) :
    (magnitudeUnits discount.gamma : ℚ) / 2^unitExponent = numerical32 discount.gamma := by
  rw [magnitude_value _ (geometric_domain discount).1,
    abs_of_nonneg (geometric_domain discount).2.1]

/-- Positive envelope coordinates follow from their numerical interpretation. -/
theorem envelope_coordinate_positive (discount : Discount) : 0 < envelopeUnits discount := by
  have value := envelope_positive discount
  rw [← envelope_value] at value
  have scale : (0 : ℚ) < 2^unitExponent := by positivity
  have := (div_pos_iff_of_pos_right scale).mp value
  exact_mod_cast this

/-- Raw arithmetic coordinates already have the analytic interpretation before admission. -/
theorem rounding_fraction (discount : Discount) (steps : Nat) :
    (returnRoundingUnits steps : ℚ) / envelopeUnits discount =
      returnRadius steps / numerical32 (errorEnvelope discount) := by
  rw [← return_units, ← envelope_value]
  norm_num [unitExponent]
  ring

/-- Raw tail coordinates already have the analytic interpretation before admission. -/
theorem tail_fraction (discount : Discount) (steps : Nat) (power : Binary32)
    (finite : power.Finite) :
    (((magnitudeUnits power + powerRoundingUnits steps) * 2^unitExponent : Nat) : ℚ) /
      ((2^unitExponent - magnitudeUnits discount.gamma) * envelopeUnits discount : Nat) =
      (|numerical32 power| + (steps : ℚ) / 8388608) /
        ((1 - numerical32 discount.gamma) * numerical32 (errorEnvelope discount)) := by
  simp only [Nat.cast_mul, Nat.cast_sub (gamma_coordinate discount).le,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [← magnitude_value power finite, ← power_units, ← gamma_value, ← envelope_value]
  push_cast
  have scale : (2 : ℚ)^unitExponent ≠ 0 := by positivity
  field_simp

/-- Twice the rounded horizon leaves a strict margin above the initial geometric tail. -/
theorem tail_margin (discount : Discount) :
    (3 : ℚ)/2 < (1 - numerical32 discount.gamma) * numerical32 (errorEnvelope discount) := by
  have domain := geometric_domain discount
  have gap : 0 < 1 - numerical32 discount.gamma := by linarith [domain.2.2.1]
  have horizon := (div_le_iff₀ gap).mp domain.2.2.2.2.2
  rw [(envelope_twice discount).2]
  nlinarith [domain.2.1]

/-- Every tracked legal prefix passes both exact precision receivers without clipping. -/
theorem precision_available (discount : Discount) (sample : Lifetime.PendingPrediction discount)
    (steps : Nat) (returned power : ℚ) (room : steps ≤ FeatureConstants.maxSettlement)
    (tracked : Tracks sample steps returned power)
    (ideal : IdealBound (numerical32 discount.gamma) returned power) :
    (precision discount steps sample.discountPower).isSome = true := by
  have ep := envelope_coordinate_positive discount
  have tp : 0 < (2^unitExponent - magnitudeUnits discount.gamma) * envelopeUnits discount :=
    Nat.mul_pos (Nat.sub_pos_of_lt (gamma_coordinate discount)) ep
  have er : (0 : ℚ) < envelopeUnits discount := by exact_mod_cast ep
  have tr : (0 : ℚ) <
      ((2^unitExponent - magnitudeUnits discount.gamma) * envelopeUnits discount : Nat) := by
    exact_mod_cast tp
  have radius := returnRadius_small steps room
  have roundingBound : returnRoundingUnits steps ≤ envelopeUnits discount := by
    have fraction : (returnRoundingUnits steps : ℚ) / envelopeUnits discount ≤ 1 := by
      rw [rounding_fraction]
      apply (div_le_one (envelope_positive discount)).mpr
      rw [(envelope_twice discount).2]
      linarith [(geometric_domain discount).2.2.2.2.1]
    exact_mod_cast (div_le_one er).mp fraction
  have stepBound : (steps : ℚ) ≤ 600 := by exact_mod_cast room
  have errorBound : (steps : ℚ)/8388608 < 1/4 := by linarith
  have powerBound : |numerical32 sample.discountPower| ≤ 1 + (steps : ℚ)/8388608 := by
    have triangle := abs_add_le (numerical32 sample.discountPower - power) power
    rw [sub_add_cancel, abs_of_nonneg ideal.2.1] at triangle
    linarith [tracked.2.2.2.2, ideal.2.2.1]
  have tailBound : (magnitudeUnits sample.discountPower + powerRoundingUnits steps) *
      2^unitExponent ≤
      (2^unitExponent - magnitudeUnits discount.gamma) * envelopeUnits discount := by
    have fraction :
        (((magnitudeUnits sample.discountPower + powerRoundingUnits steps) *
          2^unitExponent : Nat) : ℚ) /
          ((2^unitExponent - magnitudeUnits discount.gamma) *
            envelopeUnits discount : Nat) ≤ 1 := by
      rw [tail_fraction _ _ _ tracked.2.1]
      have margin := tail_margin discount
      apply (div_le_one (by linarith : 0 <
        (1 - numerical32 discount.gamma) * numerical32 (errorEnvelope discount))).mpr
      linarith
    exact_mod_cast (div_le_one tr).mp fraction
  simp [precision, Ratio.admit, tracked.2.1, Nat.not_lt.mpr room, tp, ep,
    roundingBound, tailBound]

/-- The emitted arithmetic ratio equals the proved return radius divided by its envelope. -/
theorem rounding_value (discount : Discount) (steps : Nat) (power : Binary32)
    (value : Precision) (admitted : precision discount steps power = some value) :
    (value.rounding.numerator : ℚ) / value.rounding.denominator =
      returnRadius steps / numerical32 (errorEnvelope discount) := by
  obtain ⟨rn, rd, _, _⟩ := precision_fields _ _ _ _ admitted
  rw [rn, rd, ← return_units, ← envelope_value]
  norm_num [unitExponent]
  ring

/-- The emitted tail ratio uses the rounded power plus its full analytic allowance. -/
theorem tail_value (discount : Discount) (steps : Nat) (power : Binary32)
    (finite : power.Finite) (value : Precision)
    (admitted : precision discount steps power = some value) :
    (value.tail.numerator : ℚ) / value.tail.denominator =
      (|numerical32 power| + (steps : ℚ) / 8388608) /
        ((1 - numerical32 discount.gamma) * numerical32 (errorEnvelope discount)) := by
  obtain ⟨_, _, tn, td⟩ := precision_fields _ _ _ _ admitted
  have ep : (0 : ℚ) < envelopeUnits discount := by
    have := value.rounding.positive
    rw [(precision_fields _ _ _ _ admitted).2.1] at this
    exact_mod_cast this
  have gp : (0 : ℚ) < 2^unitExponent - (magnitudeUnits discount.gamma : ℚ) := by
    have := gamma_coordinate discount
    have casted : (magnitudeUnits discount.gamma : ℚ) < 2^unitExponent := by exact_mod_cast this
    linarith
  rw [tn, td]
  simp only [Nat.cast_mul, Nat.cast_sub (gamma_coordinate discount).le,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [← magnitude_value power finite, ← power_units,
    ← gamma_value, ← envelope_value]
  push_cast
  have scale : (2 : ℚ)^unitExponent ≠ 0 := by positivity
  field_simp

/-- A tracked finite prefix is covered by the exact emitted arithmetic ratio. -/
theorem tracked_rounding (discount : Discount) (sample : Lifetime.PendingPrediction discount)
    (steps : Nat) (returned power : ℚ) (tracked : Tracks sample steps returned power)
    (value : Precision)
    (admitted : precision discount steps sample.discountPower = some value) :
    |numerical32 sample.returnSum - returned| / numerical32 (errorEnvelope discount) ≤
      (value.rounding.numerator : ℚ) / value.rounding.denominator := by
  rw [rounding_value _ _ _ _ admitted]
  exact div_le_div_of_nonneg_right tracked.2.2.2.1 (envelope_positive discount).le

/-- A tracked power bounds the ideal omitted geometric mass by the emitted tail ratio. -/
theorem tracked_tail (discount : Discount) (sample : Lifetime.PendingPrediction discount)
    (steps : Nat) (returned power : ℚ) (tracked : Tracks sample steps returned power)
    (value : Precision)
    (admitted : precision discount steps sample.discountPower = some value) :
    power / (1 - numerical32 discount.gamma) / numerical32 (errorEnvelope discount) ≤
      (value.tail.numerator : ℚ) / value.tail.denominator := by
  rw [tail_value _ _ _ tracked.2.1 _ admitted, div_div]
  have difference := abs_le.mp tracked.2.2.2.2
  have bound : power ≤ |numerical32 sample.discountPower| + (steps : ℚ) / 8388608 := by
    linarith [le_abs_self (numerical32 sample.discountPower)]
  exact div_le_div_of_nonneg_right bound
    (mul_nonneg (by linarith [(geometric_domain discount).2.2.1]) (envelope_positive discount).le)

end AcornVerif.AgreementTelemetryPrecision
