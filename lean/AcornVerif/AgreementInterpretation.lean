/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Probability.CondVar
import Mathlib.Tactic.Ring

/-!
# Squared-loss interpretation

These are conditional real-probability statements, not identification claims
about one evolving stream. They reuse Mathlib's conditional expectation and
conditional variance. A forecast must be measurable with respect to the
information available at capture; both forecast and return must be square
integrable. No independence of overlapping returns is assumed or concluded.
-/
namespace AcornVerif.AgreementInterpretation
open MeasureTheory ProbabilityTheory Filter

/-- Conditional squared loss separates forecast discrepancy from outcome variance.
The mathematical conditional mean is not estimated by this instrument. -/
theorem squared_loss_decomposition {Ω : Type*} {m₀ m : MeasurableSpace Ω}
    (hm : m ≤ m₀) (μ : Measure[m₀] Ω) [IsFiniteMeasure μ]
    (forecast outcome : Ω → ℝ) (forecastKnown : StronglyMeasurable[m] forecast)
    (forecastSquare : MemLp forecast 2 μ) (outcomeSquare : MemLp outcome 2 μ) :
    Filter.EventuallyEq (MeasureTheory.ae μ) (condExp m μ ((outcome - forecast)^2))
      ((forecast - condExp m μ outcome)^2 + condVar m outcome μ) := by
  have outcomeIntegrable : Integrable (outcome^2) μ := outcomeSquare.integrable_sq
  have crossIntegrable : Integrable (2 * outcome * forecast) μ := by
    rw [mul_assoc]
    exact (memLp_one_iff_integrable.1 (forecastSquare.mul outcomeSquare)).const_mul _
  have forecastIntegrable : Integrable (forecast^2) μ := forecastSquare.integrable_sq
  have expanded : (outcome - forecast)^2 = outcome^2 - 2 * outcome * forecast + forecast^2 := by
    ring
  rw [expanded]
  filter_upwards [condExp_add (m := m) (outcomeIntegrable.sub crossIntegrable) forecastIntegrable,
    condExp_sub (m := m) outcomeIntegrable crossIntegrable,
    condExp_mul_of_stronglyMeasurable_right forecastKnown crossIntegrable
      ((outcomeSquare.integrable one_le_two).const_mul 2),
    condExp_ofNat (m := m) 2 outcome,
    condVar_ae_eq_condExp_sq_sub_sq_condExp hm outcomeSquare]
    with ω added subtracted pulled scaled variance
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply] at *
  rw [added, subtracted, pulled, scaled,
    condExp_of_stronglyMeasurable hm (forecastKnown.pow 2) forecastIntegrable]
  simp only [Pi.pow_apply]
  rw [variance]
  ring

/-- Every information-measurable forecast has conditional squared loss at least
the conditional variance; equality requires zero conditional-mean discrepancy. -/
theorem conditional_mean_minimizes {Ω : Type*} {m₀ m : MeasurableSpace Ω}
    (hm : m ≤ m₀) (μ : Measure[m₀] Ω) [IsFiniteMeasure μ]
    (forecast outcome : Ω → ℝ) (forecastKnown : StronglyMeasurable[m] forecast)
    (forecastSquare : MemLp forecast 2 μ) (outcomeSquare : MemLp outcome 2 μ) :
    Filter.EventuallyLE (MeasureTheory.ae μ) (condVar m outcome μ)
      (condExp m μ ((outcome - forecast)^2)) := by
  filter_upwards [squared_loss_decomposition hm μ forecast outcome forecastKnown
    forecastSquare outcomeSquare] with ω decomposition
  rw [decomposition]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The conditional mean belongs to the same information-measurable square-integrable class. -/
theorem conditional_mean_admissible {Ω : Type*} {m₀ m : MeasurableSpace Ω}
    (μ : Measure[m₀] Ω) (outcome : Ω → ℝ) (square : MemLp outcome 2 μ) :
    StronglyMeasurable[m] (condExp m μ outcome) ∧ MemLp (condExp m μ outcome) 2 μ :=
  ⟨stronglyMeasurable_condExp, MemLp.condExp one_le_two square⟩

/-- The admissible conditional mean attains the lower bound by variance's exact definition. -/
theorem conditional_mean_attains {Ω : Type*} {m₀ m : MeasurableSpace Ω}
    (μ : Measure[m₀] Ω) (outcome : Ω → ℝ) :
    condExp m μ ((outcome - condExp m μ outcome)^2) = condVar m outcome μ := rfl

end AcornVerif.AgreementInterpretation
