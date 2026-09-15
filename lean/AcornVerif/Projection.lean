/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import AcornVerif.Generated

/-!
# The value-range projection

For a cumulant in `[0,1]` and discount `0 ≤ γ < 1`, the discounted return lies
in `[0, 1/(1-γ)]`. `projectR` models symmetric projection onto `[-b,b]` over
ℝ. Its range, identity and non-expansiveness theorems state their hypotheses
explicitly; non-expansiveness requires the target to lie in the interval.

`horizon_covers_true_bound` checks the rational discount/horizon pairs in
`AcornVerif.Generated`. The current finite constant interface is checked in
`AcornVerif.CurrentConstants`. Machine-word totality, NaNs, infinities and
rounding require the executable admission and arithmetic contracts; they are
outside this real-arithmetic projection model.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- Symmetric real projection: clamp `v` into `[-b, b]`. -/
def projectR (b v : ℝ) : ℝ := max (-b) (min b v)

/-- Real projection lands inside every nonnegative bound. -/
theorem project_mem_range (b v : ℝ) (hb : 0 ≤ b) :
    -b ≤ projectR b v ∧ projectR b v ≤ b := by
  constructor
  · exact le_max_left _ _
  · unfold projectR
    rcases le_total (-b) (min b v) with h | h
    · rw [max_eq_right h]
      exact min_le_left _ _
    · rw [max_eq_left h]
      linarith

/-- Real projection fixes every value already inside the interval. -/
theorem project_id_of_mem (b v : ℝ) (h1 : -b ≤ v) (h2 : v ≤ b) :
    projectR b v = v := by
  unfold projectR
  rw [min_eq_right h2, max_eq_right h1]

/-- **Projection is non-expansive** toward any target inside the bound.

The target is assumed to lie inside the rail. This establishes non-increasing
distance, not strict contraction, convergence, or admissibility of that rail
for each coefficient of a learned representation. -/
theorem project_nonexpansive (b v t : ℝ) (ht1 : -b ≤ t) (ht2 : t ≤ b) :
    |projectR b v - t| ≤ |v - t| := by
  have hb : (0 : ℝ) ≤ b := by linarith
  unfold projectR
  rcases le_total v (-b) with h | h
  · have hmin : min b v = v := min_eq_right (by linarith)
    rw [hmin, max_eq_left h, abs_of_nonpos (by linarith : -b - t ≤ 0),
      abs_of_nonpos (by linarith : v - t ≤ 0)]
    linarith
  · rcases le_total v b with h2 | h2
    · rw [min_eq_right h2, max_eq_right h]
    · rw [min_eq_left h2, max_eq_right (by linarith : (-b : ℝ) ≤ b),
        abs_of_nonneg (by linarith : 0 ≤ b - t),
        abs_of_nonneg (by linarith : 0 ≤ v - t)]
      linarith

/-- Every rational discount/horizon pair in `Generated.discounts` bounds the
corresponding real discounted return. Current constant compatibility is checked
separately by `AcornVerif.CurrentConstants`. -/
theorem horizon_covers_true_bound :
    ∀ p ∈ Generated.discounts, 1 / (1 - p.1) ≤ p.2 := by
  intro p hp
  simp only [Generated.discounts] at hp
  fin_cases hp <;>
    norm_num [Generated.gammaG90, Generated.gammaG95, Generated.gammaG99,
      Generated.horizonG90, Generated.horizonG95, Generated.horizonG99]

/-- **The fixed point of a constant-cumulant GVF.**

If the cumulant is the constant `c` at every step, the TD target `v = c + γ·v`
has the unique solution `c / (1 - γ)`. For `c = 1` and `γ = 0.99` that is
exactly `100`.

This is stated because a learner's convergence to it is the one property worth
knowing about a constant-reward problem, and it is *decidable* — a sampled run
that watches an estimate approach 100 observes one trajectory, where this
settles every one. It also says what `Discount.horizon` is: the fixed point of
the largest cumulant the demons admit, which is why projecting onto it discards
nothing reachable. -/
theorem constant_cumulant_fixed_point (c γ : ℝ) (hγ : γ < 1) :
    c / (1 - γ) = c + γ * (c / (1 - γ)) := by
  have h : (1 : ℝ) - γ ≠ 0 := by linarith
  field_simp
  ring

/-- The fixed point is *unique*: nothing else satisfies the TD equation, so a
learner that reaches a stationary point of a constant-cumulant problem has
reached this value and no other. -/
theorem constant_cumulant_fixed_point_unique (c γ v : ℝ) (hγ : γ < 1)
    (hv : v = c + γ * v) : v = c / (1 - γ) := by
  have h : (1 : ℝ) - γ ≠ 0 := by linarith
  rw [eq_div_iff h]
  linear_combination hv

/-- Every discount in the closed set is a proper contraction. -/
theorem gamma_is_contraction :
    ∀ p ∈ Generated.discounts, 0 < p.1 ∧ p.1 < 1 := by
  intro p hp
  simp only [Generated.discounts] at hp
  fin_cases hp <;>
    norm_num [Generated.gammaG90, Generated.gammaG95, Generated.gammaG99]

end AcornVerif
