/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Deterministic precision propagation

Geometric domination bounds an omitted continuation of unit-bounded nonnegative
signals. The normalized Euclidean norm is exactly RMS. Its reverse triangle
inequality propagates per-outcome bounds to per-question RMSE and, again, across
the equal-question aggregate. These are deterministic bounds, not confidence
intervals; they require the same outcome population on both sides.
-/
namespace AcornVerif.AgreementPrecision
open scoped BigOperators

/-- A finite discounted prefix omits at most the remaining geometric mass. -/
theorem omitted_tail (gamma : ℝ) (lower : 0 ≤ gamma) (upper : gamma < 1)
    (signal : Nat → ℝ) (signals : ∀ n, 0 ≤ signal n ∧ signal n ≤ 1) (horizon : Nat) :
    Summable (fun n => gamma^n * signal n) ∧
      |(∑' n, gamma^n * signal n) -
        ∑ n ∈ Finset.range horizon, gamma^n * signal n| ≤ gamma^horizon / (1 - gamma) := by
  have normGamma : ‖gamma‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg lower] using upper
  have geometric := summable_geometric_of_norm_lt_one normGamma
  have actual := geometric.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg lower _) (signals n).1)
    (fun n => mul_le_of_le_one_right (pow_nonneg lower _) (signals n).2)
  have tailBound (n : Nat) :
      gamma^(n + horizon) * signal (n + horizon) ≤ gamma^horizon * gamma^n := by
    calc
      _ ≤ gamma^(n + horizon) :=
        mul_le_of_le_one_right (pow_nonneg lower _) (signals _).2
      _ = _ := by rw [pow_add]; ring
  have tailNonnegative (n : Nat) : 0 ≤ gamma^(n + horizon) * signal (n + horizon) :=
    mul_nonneg (pow_nonneg lower _) (signals _).1
  have geometricTail := geometric.mul_left (gamma^horizon)
  have actualTail := geometricTail.of_nonneg_of_le tailNonnegative tailBound
  have bound := actualTail.tsum_le_tsum tailBound geometricTail
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one normGamma, ← div_eq_mul_inv] at bound
  have decomposition := actual.sum_add_tsum_nat_add horizon
  have tailPositive : (0 : ℝ) ≤ ∑' n, gamma^(n + horizon) * signal (n + horizon) :=
    tsum_nonneg tailNonnegative
  refine ⟨actual, ?_⟩
  have difference : (∑' n, gamma^n * signal n) -
      ∑ n ∈ Finset.range horizon, gamma^n * signal n =
        ∑' n, gamma^(n + horizon) * signal (n + horizon) := by linarith
  rw [difference, abs_of_nonneg tailPositive]
  exact bound

/-- RMS is the normalized Euclidean norm over a fixed, nonempty population. -/
noncomputable def rms {ι : Type*} [Fintype ι] (values : EuclideanSpace ℝ ι) : ℝ :=
  ‖values‖ / Real.sqrt (Fintype.card ι)

/-- The norm definition is exactly the mean-square/root convention used by the instrument. -/
theorem rms_formula {ι : Type*} [Fintype ι] (values : EuclideanSpace ℝ ι) :
    rms values = Real.sqrt ((∑ i, (values.ofLp i)^2) / Fintype.card ι) := by
  have nonnegative : (0 : ℝ) ≤ ∑ i, (values.ofLp i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [rms, EuclideanSpace.norm_eq, Real.sqrt_div nonnegative]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Uniform per-coordinate precision propagates through RMS without an independence assumption. -/
theorem rms_precision {ι : Type*} [Fintype ι] (nonempty : 0 < Fintype.card ι)
    (left right : EuclideanSpace ℝ ι) (radius : ℝ) (radiusNonnegative : 0 ≤ radius)
    (coordinate : ∀ i, |left.ofLp i - right.ofLp i| ≤ radius) :
    |rms left - rms right| ≤ radius := by
  have countPositive : (0 : ℝ) < Fintype.card ι := by exact_mod_cast nonempty
  have rootPositive := Real.sqrt_pos.mpr countPositive
  have rootSquare := Real.sq_sqrt countPositive.le
  have squareBound : ‖left - right‖^2 ≤ (Fintype.card ι : ℝ) * radius^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι, radius^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
          (sq_le_sq₀ (abs_nonneg _) radiusNonnegative).mpr (coordinate i))
      _ = _ := by simp
  have normBound : ‖left - right‖ ≤ Real.sqrt (Fintype.card ι) * radius := by
    nlinarith [norm_nonneg (left - right), mul_nonneg rootPositive.le radiusNonnegative]
  rw [rms, rms, ← sub_div, abs_div, abs_of_pos rootPositive]
  apply (div_le_iff₀ rootPositive).mpr
  exact le_trans (abs_norm_sub_norm_le left right) (by simpa [mul_comm] using normBound)

/-- Complementing error reverses endpoints and scales the precision by 100 points. -/
theorem agreement_precision (measured reference radius : ℝ)
    (bound : |measured - reference| ≤ radius) :
    100 * (1 - measured) - 100 * radius ≤ 100 * (1 - reference) ∧
      100 * (1 - reference) ≤ 100 * (1 - measured) + 100 * radius := by
  have interval := abs_le.mp bound
  constructor <;> linarith

end AcornVerif.AgreementPrecision
