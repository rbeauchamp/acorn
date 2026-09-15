/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Agreement
import AcornVerif.CurrentOrder
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# Executed discrepancy coordinates and agreement direction

The numerical statements concern all finite binary32 encodings, with the
standard arithmetic and native compiler boundaries declared by CurrentOrder.
The score is Acorn's descriptive complement of normalized RMSE. Its integer
presentation rounds error downward by less than one millionth; this display
precision is separate from finite-return truncation and arithmetic error.
-/
namespace AcornVerif.CurrentAgreement
open Acorn Acorn.Agreement AcornVerif.CurrentOrder
open AcornVerif.CurrentFloat AcornVerif.CurrentArithmetic

/-- The executable magnitude decoder is the existing proved field interpretation. -/
theorem magnitudeUnits_exact (value : Binary32) :
    magnitudeUnits value = fieldUnits 23 value.magnitude := rfl

/-- Signed executable coordinates agree with the common proved signed field owner. -/
theorem units_exact (value : Binary32) : units value = signedFieldUnits 23 value.key := by
  rw [Binary32.key, signedFieldUnits_sign]
  rfl

/-- Every finite operand has exactly its executed integer coordinate at the binary32 scale. -/
theorem units_numerical (value : Binary32) (finite : value.Finite) :
    numerical32 value = (units value : ℚ) * (2 : ℚ)^(-149 : Int) := by
  rw [numerical32_key_units value finite, units_exact]

/-- Executed subtraction and squaring preserve the exact discrepancy between finite words. -/
theorem squaredUnits_numerical (forecast outcome : Binary32)
    (forecastFinite : forecast.Finite) (outcomeFinite : outcome.Finite) :
    (squaredUnits forecast outcome : ℚ) * ((2 : ℚ)^(-149 : Int))^2 =
      (numerical32 forecast - numerical32 outcome)^2 := by
  rw [units_numerical forecast forecastFinite, units_numerical outcome outcomeFinite]
  have square := congrArg (fun x : Int => (x : ℚ))
    (Int.natAbs_sq (units forecast - units outcome))
  simp only [Int.cast_pow, Int.cast_natCast, Int.cast_sub] at square
  simp only [squaredUnits, Nat.cast_pow]
  rw [square]
  ring

/-- Exact admitted normalized squared error belongs to the unit interval. -/
theorem ratio_bounds (ratio : Ratio) :
    0 ≤ (ratio.numerator : ℚ) / ratio.denominator ∧
      (ratio.numerator : ℚ) / ratio.denominator ≤ 1 := by
  have positive : (0 : ℚ) < ratio.denominator := by exact_mod_cast ratio.positive
  constructor
  · positivity
  · apply (div_le_one positive).mpr
    exact_mod_cast ratio.bounded

/-- The actual square-root display cannot exceed its scale. -/
theorem errorUnits_bound (ratio : Ratio) : ratio.errorUnits ≤ displayScale := by
  have quotient : ratio.numerator * displayScale^2 / ratio.denominator ≤ displayScale^2 := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (displayScale^2) ratio.bounded
  have root := Nat.sqrt_le_sqrt quotient
  simpa [Ratio.errorUnits] using root

/-- Natural subtraction is an exact complement here, never an underflow clamp. -/
theorem agreementUnits_complement (ratio : Ratio) :
    ratio.agreementUnits + ratio.errorUnits = displayScale := by
  exact Nat.sub_add_cancel (errorUnits_bound ratio)

/-- The executed increasing indicator always belongs to its admitted scale. -/
theorem agreementUnits_bound (ratio : Ratio) : ratio.agreementUnits ≤ displayScale :=
  Nat.sub_le _ _

/-- Greater exact normalized squared error cannot improve the displayed agreement. -/
theorem agreementUnits_antitone (left right : Ratio)
    (ordered : left.numerator * right.denominator ≤ right.numerator * left.denominator) :
    right.agreementUnits ≤ left.agreementUnits := by
  have orderQ : left.numerator * displayScale^2 / left.denominator ≤
      right.numerator * displayScale^2 / right.denominator := by
    apply (Nat.le_div_iff_mul_le right.positive).mpr
    have floor := Nat.div_mul_le_self (left.numerator * displayScale^2) left.denominator
    have scaled := Nat.mul_le_mul_right (displayScale^2) ordered
    have multiplied := Nat.mul_le_mul_right right.denominator floor
    have positive := left.positive
    nlinarith only [scaled, multiplied, positive]
  exact Nat.sub_le_sub_left (Nat.sqrt_le_sqrt orderQ) displayScale

/-- Exact integer brackets connect the executed root to the normalized mean;
the upper bracket is strict even when integer division discards a remainder. -/
theorem errorUnits_bracket (ratio : Ratio) :
    ratio.errorUnits^2 * ratio.denominator ≤ ratio.numerator * displayScale^2 ∧
    ratio.numerator * displayScale^2 < (ratio.errorUnits + 1)^2 * ratio.denominator := by
  constructor
  · exact le_trans
      (Nat.mul_le_mul_right ratio.denominator (Nat.sqrt_le' _))
      (Nat.div_mul_le_self _ _)
  · apply (Nat.div_lt_iff_lt_mul ratio.positive).mp
    exact Nat.lt_succ_sqrt' _

/-- Display RMSE rounds downward by strictly less than one display unit. -/
theorem errorUnits_precision (ratio : Ratio) :
    (ratio.errorUnits : ℝ) / displayScale ≤
        Real.sqrt ((ratio.numerator : ℝ) / ratio.denominator) ∧
    Real.sqrt ((ratio.numerator : ℝ) / ratio.denominator) <
        ((ratio.errorUnits : ℝ) + 1) / displayScale := by
  have denominator : (0 : ℝ) < ratio.denominator := by exact_mod_cast ratio.positive
  have scale : (0 : ℝ) < displayScale := by norm_num [displayScale]
  have mean : (0 : ℝ) ≤ ratio.numerator / ratio.denominator := by positivity
  have brackets := errorUnits_bracket ratio
  constructor
  · apply (Real.le_sqrt (by positivity) mean).mpr
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos scale) denominator).mpr
    exact_mod_cast brackets.1
  · apply (Real.sqrt_lt mean (by positivity)).mpr
    rw [div_pow]
    apply (div_lt_div_iff₀ denominator (sq_pos_of_pos scale)).mpr
    exact_mod_cast brackets.2

/-- The aggregate update is addition of one normalized question, without count weighting. -/
theorem aggregate_add_value (aggregate : Aggregate) (ratio : Ratio) :
    ((aggregate.add ratio).numerator : ℚ) / (aggregate.add ratio).denominator =
      (aggregate.numerator : ℚ) / aggregate.denominator +
      (ratio.numerator : ℚ) / ratio.denominator := by
  have left : (aggregate.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt aggregate.positive
  have right : (ratio.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ratio.positive
  simp only [Aggregate.add, Nat.cast_add, Nat.cast_mul]
  field_simp

/-- Each successful list fold includes exactly its supplied entries. The current
question inventory, rather than this general reducer, owns distinct identities. -/
theorem aggregateAll_count (ratios : List (Option Ratio)) (aggregate : Aggregate)
    (present : aggregateAll ratios = some aggregate) : aggregate.questions = ratios.length := by
  induction ratios generalizing aggregate with
  | nil => cases present; rfl
  | cons head tail ih =>
    cases head with
    | none => simp [aggregateAll] at present
    | some head =>
      simp only [aggregateAll, Option.map_eq_some_iff] at present
      obtain ⟨prior, priorPresent, rfl⟩ := present
      simpa only [Aggregate.add, List.length_cons] using congrArg (· + 1) (ih prior priorPresent)

/-- The strict near-perfect text threshold uses the exact squared ratio. -/
theorem nearPerfect_meaning (ratio : Ratio)
    (near : ratio.numerator * 100000000 < ratio.denominator) :
    (9999 : ℝ) / 100 < 100 * (1 - Real.sqrt ((ratio.numerator : ℝ) / ratio.denominator)) := by
  have den : (0 : ℝ) < ratio.denominator := by exact_mod_cast ratio.positive
  have positive : (0 : ℝ) ≤ ratio.numerator / ratio.denominator := by positivity
  have root : Real.sqrt ((ratio.numerator : ℝ) / ratio.denominator) < 1/10000 := by
    apply (Real.sqrt_lt positive (by norm_num)).mpr
    apply (div_lt_iff₀ den).mpr
    have bound : (ratio.numerator : ℝ) * 100000000 < ratio.denominator := by exact_mod_cast near
    nlinarith
  linarith

/-- The strict near-zero text threshold also uses the exact squared ratio. -/
theorem nearZero_meaning (ratio : Ratio)
    (near : ratio.denominator * 99980001 < ratio.numerator * 100000000) :
    100 * (1 - Real.sqrt ((ratio.numerator : ℝ) / ratio.denominator)) < (1 : ℝ)/100 := by
  have den : (0 : ℝ) < ratio.denominator := by exact_mod_cast ratio.positive
  have rootSquare := Real.sq_sqrt (show (0 : ℝ) ≤ ratio.numerator / ratio.denominator by positivity)
  have fraction : (9999/10000 : ℝ)^2 < (ratio.numerator : ℝ) / ratio.denominator := by
    apply (lt_div_iff₀ den).mpr
    have bound : (ratio.denominator : ℝ) * 99980001 < (ratio.numerator : ℝ) * 100000000 := by
      exact_mod_cast near
    nlinarith
  have rootPositive := Real.sqrt_nonneg ((ratio.numerator : ℝ) / ratio.denominator)
  nlinarith

/-- A successful complete fold sums each supplied question exactly once. -/
theorem aggregateAll_value (ratios : List Ratio) (aggregate : Aggregate)
    (present : aggregateAll (ratios.map some) = some aggregate) :
    (aggregate.numerator : ℚ) / aggregate.denominator =
      (ratios.map (fun ratio => (ratio.numerator : ℚ) / ratio.denominator)).sum := by
  induction ratios generalizing aggregate with
  | nil => cases present; norm_num [Aggregate.empty]
  | cons head tail ih =>
    simp only [List.map_cons, aggregateAll, Option.map_eq_some_iff] at present
    obtain ⟨prior, priorPresent, rfl⟩ := present
    rw [aggregate_add_value, ih prior priorPresent]
    simp [List.map_cons, List.sum_cons, add_comm]

/-- The aggregate ratio divides its exact question sum by its question count. -/
theorem aggregate_ratio_value (aggregate : Aggregate) (ratio : Ratio)
    (present : aggregate.ratio = some ratio) :
    (ratio.numerator : ℚ) / ratio.denominator =
      ((aggregate.numerator : ℚ) / aggregate.denominator) / aggregate.questions := by
  unfold Aggregate.ratio at present
  split at present
  · cases present
    simp only [Nat.cast_mul, div_div]
    ring
  · contradiction

/-- Every finite discrepancy inside its numerical envelope passes exact sample admission. -/
theorem admitSquared_available (forecast outcome envelope : Binary32)
    (forecastFinite : forecast.Finite) (outcomeFinite : outcome.Finite)
    (envelopeFinite : envelope.Finite)
    (bound : |numerical32 forecast - numerical32 outcome| ≤ |numerical32 envelope|) :
    (admitSquared (magnitudeUnits envelope) forecast outcome).isSome = true := by
  have squared := pow_le_pow_left₀ (abs_nonneg _) bound 2
  rw [sq_abs, numerical32_abs_units envelope envelopeFinite, ← magnitudeUnits_exact,
    mul_pow, ← squaredUnits_numerical forecast outcome forecastFinite outcomeFinite] at squared
  have scale : (0 : ℚ) < ((2 : ℚ)^(-149 : Int))^2 := by positivity
  have rational := (mul_le_mul_iff_left₀ scale).mp squared
  have integral : squaredUnits forecast outcome ≤ (magnitudeUnits envelope)^2 := by
    exact_mod_cast rational
  simp [admitSquared, forecastFinite, outcomeFinite, Nat.lt_succ_of_le integral]

end AcornVerif.CurrentAgreement
