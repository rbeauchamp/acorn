/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Lifetime
import AcornVerif.CurrentLearnerArithmetic
import AcornVerif.CurrentConstants
import AcornVerif.CurrentAgreement

/-!
# Rounded finite-return arithmetic

Local error bounds apply to the executed binary32 operations through the pinned
standard unpack/round/pack model. They are deterministic arithmetic allowances,
not statistical uncertainty, a noise floor, or evidence of predictive usefulness.
-/
namespace AcornVerif.AgreementReturn
open Acorn
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentLearnerArithmetic

/-- Normalized results within the finite-return working envelope fit binary32. -/
theorem return_fits (value : UnpackedFloat) (exactValue : ℚ)
    (normal : ModelNormalized Format.binary32 value) (bound : |exactValue| ≤ 1024)
    (error : |unpackedValue value - exactValue| ≤ 1) : ModelFits Format.binary32 value := by
  apply model_fits_of_value_bound Format.binary32 value
    (model_normalized_finite _ _ normal) 11 (by decide)
  have triangle := abs_add_le (unpackedValue value - exactValue) exactValue
  rw [sub_add_cancel] at triangle
  norm_num
  linarith only [triangle, bound, error]

/-- A return-addition working magnitude of 1024 gives a 2^-14 local rounding allowance. -/
theorem return_add (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left + numerical32 right| ≤ 1024) :
    (left.add right).Finite ∧
      |numerical32 (left.add right) - (numerical32 left + numerical32 right)| ≤ 1/16384 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_add_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 10 (by norm_num [numerical32] at bound ⊢; exact bound)
  have error : |unpackedValue (UnpackedFloat.add Format.binary32
      (decoded32 left) (decoded32 right)) - (numerical32 left + numerical32 right)| ≤
      1/16384 := by
    convert operation.2 using 1 <;> norm_num [numerical32, Format.mantissaBits, Format.minExponent]
  have decoded := model_add32_decoded left right hl hr operation.1
    (return_fits _ _ operation.1 bound (le_trans error (by norm_num)))
  constructor
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using error

/-- A product magnitude of two gives a 2^-23 local rounding allowance. -/
theorem return_mul (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (bound : |numerical32 left * numerical32 right| ≤ 2) :
    (left.mul right).Finite ∧
      |numerical32 (left.mul right) - numerical32 left * numerical32 right| ≤ 1/8388608 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_mul_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn 1 (by norm_num [numerical32] at bound ⊢; exact bound)
  have error : |unpackedValue (UnpackedFloat.mul Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left * numerical32 right| ≤
      1/8388608 := by
    convert operation.2 using 1 <;> norm_num [numerical32, Format.mantissaBits, Format.minExponent]
  have decoded := mul32_decoded left right hl hr operation.1
    (return_fits _ _ operation.1 (le_trans bound (by norm_num))
      (le_trans error (by norm_num)))
  constructor
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using error

/-- Accumulated allowance for ordered multiply/add return accounting. -/
def returnRadius (steps : Nat) : ℚ :=
  steps / 16384 + (steps : ℚ) * (steps + 1) / (2 * 8388608)

/-- The radius is the sum of one addition allowance and the growing power allowance. -/
theorem returnRadius_succ (steps : Nat) :
    returnRadius (steps + 1) = returnRadius steps + 1/16384 + ((steps : ℚ) + 1)/8388608 := by
  simp only [returnRadius, Nat.cast_add, Nat.cast_one]
  ring

/-- The fixed pending horizon keeps all rounding allowances strictly below one. -/
theorem returnRadius_small (steps : Nat) (bounded : steps ≤ Acorn.FeatureConstants.maxSettlement) :
    0 ≤ returnRadius steps ∧ returnRadius steps < 1 ∧ (steps : ℚ)/8388608 < 1 := by
  have bound : (steps : ℚ) ≤ 600 := by exact_mod_cast bounded
  have nonnegative : (0 : ℚ) ≤ steps := Nat.cast_nonneg _
  unfold returnRadius
  constructor
  · positivity
  constructor <;> nlinarith

/-- Every immutable current discount has a true geometric horizon below 101.
Its rounded forecast rail exceeds nine; constants come from their checked owner. -/
theorem geometric_domain (discount : Discount) :
    discount.gamma.Finite ∧ 0 ≤ numerical32 discount.gamma ∧ numerical32 discount.gamma < 1 ∧
    1 / (1 - numerical32 discount.gamma) ≤ 101 ∧ 9 < numerical32 discount.horizon ∧
    1 / (1 - numerical32 discount.gamma) ≤ numerical32 discount.horizon + 1/131072 := by
  have values := AcornVerif.CurrentConstants.discount_values discount
  have finite : discount.gamma.Finite := by cases discount <;> decide
  refine ⟨finite, ?_⟩
  cases discount <;>
    simp only at values <;>
    obtain ⟨gamma, horizon⟩ := Prod.mk.inj values <;>
    rw [gamma, horizon] <;>
    norm_num [ModelConstants.gammaG90, ModelConstants.gammaG95, ModelConstants.gammaG99,
      ModelConstants.horizonG90, ModelConstants.horizonG95, ModelConstants.horizonG99]

/-- Exact discounted reference state: remaining mass times the geometric horizon
plus accumulated return cannot exceed that horizon. -/
def IdealBound (gamma returned power : ℚ) : Prop :=
  0 ≤ returned ∧ 0 ≤ power ∧ power ≤ 1 ∧
    returned + power / (1 - gamma) ≤ 1 / (1 - gamma)

/-- A new indicator preserves the geometric budget by the identity
`1 + gamma/(1-gamma) = 1/(1-gamma)`. -/
theorem ideal_step (gamma returned power cumulant : ℚ)
    (gammaLower : 0 ≤ gamma) (gammaUpper : gamma < 1)
    (prior : IdealBound gamma returned power) (signal : 0 ≤ cumulant ∧ cumulant ≤ 1) :
    IdealBound gamma (returned + power * cumulant) (power * gamma) := by
  have denominator : 0 < 1 - gamma := by linarith
  have returnedLower := prior.1
  have powerLower := prior.2.1
  have cumulantLower := signal.1
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · nlinarith [prior.2.2.1]
  · have budget := prior.2.2.2
    apply (le_div_iff₀ denominator).mpr
    have budget' := (le_div_iff₀ denominator).mp budget
    have cancel : power / (1 - gamma) * (1 - gamma) = power :=
      div_mul_cancel₀ _ (ne_of_gt denominator)
    have nextCancel : power * gamma / (1 - gamma) * (1 - gamma) = power * gamma :=
      div_mul_cancel₀ _ (ne_of_gt denominator)
    nlinarith [mul_nonneg (mul_nonneg powerLower (sub_nonneg.mpr signal.2)) denominator.le]

/-- The budget bounds the accumulated reference sum independently of stream length. -/
theorem ideal_return_bound (gamma returned power : ℚ) (gammaUpper : gamma < 1)
    (prior : IdealBound gamma returned power) : returned ≤ 1 / (1 - gamma) := by
  have nonnegative : 0 ≤ power / (1 - gamma) := div_nonneg prior.2.1 (by linarith)
  linarith [prior.2.2.2]

/-- Multiplication by a unit signal carries the preceding power error and one rounding allowance. -/
theorem tracked_mul (word signal : Binary32) (expected budget : ℚ)
    (wordFinite : word.Finite) (signalFinite : signal.Finite)
    (expectedBounds : 0 ≤ expected ∧ expected ≤ 1)
    (signalBounds : 0 ≤ numerical32 signal ∧ numerical32 signal ≤ 1)
    (budgetSmall : budget < 1) (tracked : |numerical32 word - expected| ≤ budget) :
    (word.mul signal).Finite ∧
      |numerical32 (word.mul signal) - expected * numerical32 signal| ≤ budget + 1/8388608 := by
  have wordBounds := abs_le.mp tracked
  have wordAbs : |numerical32 word| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [expectedBounds.1, expectedBounds.2]
  have signalAbs : |numerical32 signal| ≤ 1 := by
    rw [abs_of_nonneg signalBounds.1]
    exact signalBounds.2
  have product : |numerical32 word * numerical32 signal| ≤ 2 := by
    rw [abs_mul]
    calc
      _ ≤ |numerical32 word| * 1 := mul_le_mul_of_nonneg_left signalAbs (abs_nonneg _)
      _ ≤ 2 := by simpa using wordAbs
  have operation := return_mul word signal wordFinite signalFinite product
  refine ⟨operation.1, ?_⟩
  calc
    _ = |(numerical32 (word.mul signal) - numerical32 word * numerical32 signal) +
        (numerical32 word - expected) * numerical32 signal| := by congr 1; ring
    _ ≤ |numerical32 (word.mul signal) - numerical32 word * numerical32 signal| +
        |(numerical32 word - expected) * numerical32 signal| := abs_add_le _ _
    _ ≤ 1/8388608 + budget := add_le_add operation.2 (by
      rw [abs_mul]
      calc
        _ ≤ |numerical32 word - expected| * 1 :=
          mul_le_mul_of_nonneg_left signalAbs (abs_nonneg _)
        _ ≤ budget := by simpa using tracked)
    _ = budget + 1/8388608 := add_comm _ _

/-- Correspondence invariant for the actual pending-return state after a finite prefix. -/
def Tracks {discount : Discount} (sample : Lifetime.PendingPrediction discount)
    (steps : Nat) (returned power : ℚ) : Prop :=
  sample.returnSum.Finite ∧ sample.discountPower.Finite ∧ sample.age.val = steps ∧
    |numerical32 sample.returnSum - returned| ≤ returnRadius steps ∧
    |numerical32 sample.discountPower - power| ≤ (steps : ℚ)/8388608

/-- Initial capture is the empty reference sum, before any evaluated future. -/
theorem initial_tracks (discount : Discount) (clock : UInt64) (prediction : Prediction discount) :
    Tracks (Lifetime.PendingPrediction.initial clock prediction) 0 0 1 := by
  simp only [Tracks, Lifetime.PendingPrediction.initial]
  refine ⟨by decide, by decide, trivial, ?_, ?_⟩
  · change |(0 : ℚ) - 0| ≤ returnRadius 0
    norm_num [returnRadius]
  · change |((1 : ℚ) * 8388608 * 2^(-23 : Int)) - 1| ≤ 0/8388608
    norm_num

/-- Every executed advance preserves the reference correspondence and its analytic allowance. -/
theorem advance_tracks {discount : Discount} (sample : Lifetime.PendingPrediction discount)
    (steps : Nat) (returned power : ℚ) (cumulant : Binary32)
    (stepsBound : steps < Acorn.FeatureConstants.maxSettlement)
    (prior : Tracks sample steps returned power)
    (ideal : IdealBound (numerical32 discount.gamma) returned power)
    (cumulantFinite : cumulant.Finite)
    (signal : 0 ≤ numerical32 cumulant ∧ numerical32 cumulant ≤ 1) :
    Tracks (sample.advance cumulant) (steps + 1)
      (returned + power * numerical32 cumulant) (power * numerical32 discount.gamma) := by
  have domain := geometric_domain discount
  have radii := returnRadius_small steps stepsBound.le
  have product := tracked_mul sample.discountPower cumulant power ((steps : ℚ)/8388608)
    prior.2.1 cumulantFinite ⟨ideal.2.1, ideal.2.2.1⟩ signal radii.2.2 prior.2.2.2.2
  have nextPower := tracked_mul sample.discountPower discount.gamma power ((steps : ℚ)/8388608)
    prior.2.1 domain.1 ⟨ideal.2.1, ideal.2.2.1⟩ ⟨domain.2.1, domain.2.2.1.le⟩
    radii.2.2 prior.2.2.2.2
  have returnedBound := le_trans (ideal_return_bound _ _ _ domain.2.2.1 ideal) domain.2.2.2.1
  have rawReturn := abs_le.mp prior.2.2.2.1
  have rawProduct := abs_le.mp product.2
  have idealProduct : 0 ≤ power * numerical32 cumulant ∧ power * numerical32 cumulant ≤ 1 :=
    ⟨mul_nonneg ideal.2.1 signal.1, by nlinarith [ideal.2.2.1]⟩
  have magnitude :
      |numerical32 sample.returnSum + numerical32 (sample.discountPower.mul cumulant)| ≤ 1024 := by
    rw [abs_le]
    constructor <;> linarith [ideal.1, radii.2.1, radii.2.2, idealProduct.1, idealProduct.2]
  have addition := return_add sample.returnSum (sample.discountPower.mul cumulant)
    prior.1 product.1 magnitude
  refine ⟨addition.1, nextPower.1, ?_, ?_, ?_⟩
  · simp only [Lifetime.PendingPrediction.advance]
    rw [prior.2.2.1, Nat.min_eq_left (by omega)]
  · change |numerical32 (sample.returnSum.add (sample.discountPower.mul cumulant)) - _| ≤ _
    rw [returnRadius_succ]
    have localError := abs_le.mp addition.2
    rw [abs_le]
    constructor <;> linarith [rawReturn.1, rawReturn.2, rawProduct.1, rawProduct.2]
  · change |numerical32 (sample.discountPower.mul discount.gamma) - _| ≤ _
    simpa only [Nat.cast_add, Nat.cast_one, add_div, one_div] using nextPower.2

/-- The closed envelope's multiplication by two is exact for all current horizons. -/
theorem envelope_twice (discount : Discount) :
    (Agreement.errorEnvelope discount).Finite ∧
    numerical32 (Agreement.errorEnvelope discount) = 2 * numerical32 discount.horizon := by
  constructor
  · cases discount <;> decide
  · cases discount with
    | g90 =>
      change (1 : ℚ) * 10485758 * 2^(-19 : Int) = 2 * ((1 : ℚ) * 10485758 * 2^(-20 : Int))
      norm_num
    | g95 =>
      change (1 : ℚ) * 10485758 * 2^(-18 : Int) = 2 * ((1 : ℚ) * 10485758 * 2^(-19 : Int))
      norm_num
    | g99 =>
      change (1 : ℚ) * 13107213 * 2^(-16 : Int) = 2 * ((1 : ℚ) * 13107213 * 2^(-17 : Int))
      norm_num

/-- A forecast and the rounded finite continuation fit the existing envelope.
The allowance is derived from actual nonnegative prediction and indicator owners;
no discrepancy projection appears in the statistic. -/
theorem admitted_error_bound {discount : Discount} (sample : Lifetime.PendingPrediction discount)
    (steps : Nat) (returned power : ℚ)
    (stepsBound : steps ≤ Acorn.FeatureConstants.maxSettlement)
    (tracked : Tracks sample steps returned power)
    (ideal : IdealBound (numerical32 discount.gamma) returned power) :
    |numerical32 sample.prediction.value - numerical32 sample.returnSum| ≤
      numerical32 (Agreement.errorEnvelope discount) := by
  have domain := geometric_domain discount
  have radius := returnRadius_small steps stepsBound
  have exactBound := ideal_return_bound _ _ _ domain.2.2.1 ideal
  have forecast := sample.prediction.legal
  have lower := (AcornVerif.CurrentOrder.numerical32_order Binary32.zero sample.prediction.value
    (by decide) forecast.1).mpr forecast.2.1
  have upper := (AcornVerif.CurrentOrder.numerical32_order sample.prediction.value discount.horizon
    forecast.1 discount.predictionRange.upperFinite).mpr forecast.2.2
  have zero : numerical32 Binary32.zero = 0 := by decide
  rw [zero] at lower
  have error := abs_le.mp tracked.2.2.2.1
  rw [(envelope_twice discount).2, abs_le]
  constructor <;> linarith [domain.2.2.2.2.1, domain.2.2.2.2.2, ideal.1]

/-- Mathematical reference update for correspondence, never retained by the agent. -/
def referenceAdvance (discount : Discount) (state : ℚ × ℚ) (cumulant : Binary32) : ℚ × ℚ :=
  (state.1 + state.2 * numerical32 cumulant, state.2 * numerical32 discount.gamma)

/-- Induction links an arbitrary admitted future prefix to the actual executed fold.
The quantified list is proof data, not an application trajectory buffer. -/
theorem fold_tracks {discount : Discount} (inputs : List Binary32)
    (sample : Lifetime.PendingPrediction discount) (steps : Nat) (returned power : ℚ)
    (room : steps + inputs.length ≤ Acorn.FeatureConstants.maxSettlement)
    (signals : ∀ word ∈ inputs, word.Finite ∧ 0 ≤ numerical32 word ∧ numerical32 word ≤ 1)
    (tracked : Tracks sample steps returned power)
    (ideal : IdealBound (numerical32 discount.gamma) returned power) :
    let actual := inputs.foldl Lifetime.PendingPrediction.advance sample
    let reference := inputs.foldl (referenceAdvance discount) (returned, power)
    Tracks actual (steps + inputs.length) reference.1 reference.2 ∧
      IdealBound (numerical32 discount.gamma) reference.1 reference.2 := by
  induction inputs generalizing sample steps returned power with
  | nil => simpa using And.intro tracked ideal
  | cons word tail ih =>
    have signal := signals word (by simp)
    have stepRoom : steps < Acorn.FeatureConstants.maxSettlement := by
      simp only [List.length_cons] at room
      omega
    have next := advance_tracks sample steps returned power word stepRoom tracked ideal
      signal.1 signal.2
    have domain := geometric_domain discount
    have nextIdeal := ideal_step (numerical32 discount.gamma) returned power (numerical32 word)
      domain.2.1 domain.2.2.1 ideal signal.2
    have rest := ih (sample.advance word) (steps + 1) (returned + power * numerical32 word)
      (power * numerical32 discount.gamma) (by simp only [List.length_cons] at room; omega)
      (fun value member => signals value (by simp [member])) next nextIdeal
    simpa only [List.foldl_cons, referenceAdvance, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

/-- Every admitted finite prefix from a real capture satisfies the discrepancy envelope. -/
theorem captured_return_bound (discount : Discount) (clock : UInt64)
    (prediction : Prediction discount) (inputs : List Binary32)
    (room : inputs.length ≤ Acorn.FeatureConstants.maxSettlement)
    (signals : ∀ word ∈ inputs, word.Finite ∧ 0 ≤ numerical32 word ∧ numerical32 word ≤ 1) :
    let sample := inputs.foldl Lifetime.PendingPrediction.advance
      (Lifetime.PendingPrediction.initial clock prediction)
    sample.returnSum.Finite ∧
      |numerical32 sample.prediction.value - numerical32 sample.returnSum| ≤
        numerical32 (Agreement.errorEnvelope discount) := by
  have tracked := fold_tracks inputs (Lifetime.PendingPrediction.initial clock prediction) 0 0 1
    (by simpa using room) signals (initial_tracks discount clock prediction) (by simp [IdealBound])
  exact ⟨tracked.1.1, admitted_error_bound _ _ _ _ (by simpa using room) tracked.1 tracked.2⟩

/-- The linked reference fold is exactly the finite discounted sum in start order. -/
theorem reference_formula (discount : Discount) (stream : Nat → Binary32) (count : Nat) :
    ((List.range count).map stream).foldl (referenceAdvance discount) (0, 1) =
      (∑ i ∈ Finset.range count, numerical32 discount.gamma ^ i * numerical32 (stream i),
        numerical32 discount.gamma ^ count) := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil, ih, referenceAdvance,
      Finset.sum_range_succ, pow_succ]

/-- Captured legal prefixes are available to the executed exact-square receiver. -/
theorem captured_admission (discount : Discount) (clock : UInt64)
    (prediction : Prediction discount) (inputs : List Binary32)
    (room : inputs.length ≤ Acorn.FeatureConstants.maxSettlement)
    (signals : ∀ word ∈ inputs, word.Finite ∧ 0 ≤ numerical32 word ∧ numerical32 word ≤ 1) :
    let sample := inputs.foldl Lifetime.PendingPrediction.advance
      (Lifetime.PendingPrediction.initial clock prediction)
    (Agreement.admitSquared (Agreement.envelopeUnits discount)
      sample.prediction.value sample.returnSum).isSome = true := by
  have bound := captured_return_bound discount clock prediction inputs room signals
  exact AcornVerif.CurrentAgreement.admitSquared_available _ _ _
    (inputs.foldl Lifetime.PendingPrediction.advance
      (Lifetime.PendingPrediction.initial clock prediction)).prediction.legal.1
    bound.1 (envelope_twice discount).1 (bound.2.trans (le_abs_self _))

end AcornVerif.AgreementReturn
