/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Step-size invariants of SwiftTD

Real-arithmetic models of Algorithm 1 in Javed, Sharifnassab & Sutton,
*SwiftTD: A Fast and Robust Algorithm for Temporal Difference Learning*,
Reinforcement Learning Journal, vol. 2 (2024), pp. 840–863.
The meta-gradient recurrence is covered separately in `AcornVerif.MetaGradient`.

Theorems here concern real guards and bounds. Machine effects such as underflow
of `exp β` to zero require separate execution contracts; these real models do
not establish a refinement of the rounded learner.
-/

namespace AcornVerif

open Real

noncomputable section

/-- The step-size clip of SwiftTD's first loop
(the first update loop): if the step size
`exp β` exceeds the budget `η`, reset `β := log η`; if it falls below
the floor `ηmin`, reset `β := log ηmin`; otherwise leave `β` unchanged. -/
def clipBeta (β η ηmin : ℝ) : ℝ :=
  if Real.exp β > η then Real.log η
  else if Real.exp β < ηmin then Real.log ηmin
  else β

/-- After clipping, the step size is strictly positive: `α = exp β > 0`.

Over the reals, `Real.exp_pos` establishes positivity for every `β`, independently
of clipping and the hypotheses. The `ηmin` floor addresses floating-point
underflow of `exp β` to `0.0`; that machine-arithmetic behavior lies outside this
real-arithmetic model. -/
theorem step_size_pos_after_clip (β η ηmin : ℝ) (hη : 0 < η) (hm : 0 < ηmin) :
    0 < Real.exp (clipBeta β η ηmin) := by
  unfold clipBeta
  by_cases h1 : Real.exp β > η
  · simp [h1, Real.exp_log hη, hη]
  · by_cases h2 : Real.exp β < ηmin
    · simp [h1, h2, Real.exp_log hm, hm]
    · simp [h1, h2, Real.exp_pos]

/-- After clipping, the step size never exceeds the budget `η`
(requires the floor below the budget, which holds for every configured η:
`ηmin = 1e-10` against `η = 0.1` for `SwiftTdConfig::demon` and `::control`,
and `η = 0.25` for `::option_skill`). -/
theorem step_size_upper_after_clip (β η ηmin : ℝ) (hm : 0 < ηmin) (h : ηmin ≤ η) :
    Real.exp (clipBeta β η ηmin) ≤ η := by
  unfold clipBeta
  by_cases h1 : Real.exp β > η
  · simp [h1, Real.exp_log (lt_of_lt_of_le hm h)]
  · by_cases h2 : Real.exp β < ηmin
    · simp [h1, h2, Real.exp_log hm, h]
    · simp [h1, h2, le_of_not_gt]

/-- After clipping, the step size is at least the floor `ηmin`. -/
theorem step_size_lower_after_clip (β η ηmin : ℝ) (hm : 0 < ηmin) (h : ηmin ≤ η) :
    ηmin ≤ Real.exp (clipBeta β η ηmin) := by
  unfold clipBeta
  by_cases h1 : Real.exp β > η
  · simp [h1, Real.exp_log (lt_of_lt_of_le hm h), h]
  · by_cases h2 : Real.exp β < ηmin
    · simp [h1, h2, Real.exp_log hm]
    · simp [h1, h2, le_of_not_gt]

/-- The effective-rate denominator: `E = max η (Σ α φ²)` with `φ ∈ {0,1}`
after construction unique, so this is the deployed sum of
The second update loop. Paper eq. (7), RLJ vol. 2
p. 845: `τ_t = Σ_i α_t[i] φ_t[i]²`. The scalar `rate` *is* that sum. -/
def overshootE (η rate : ℝ) : ℝ := max η rate

/-- The trace increment for feature `i`: `zδᵢ = (η / E) · αᵢ`
(`learn_second_loop`: `z_delta[i] = (eta / e) * exp(beta[i])`). -/
def traceIncrement (η α : ℝ) (E : ℝ) : ℝ := (η / E) * α

/-- Total trace increment across the active set is bounded by `η`:
`Σ zδ = (η/E)·Σα ≤ η`. This is the SwiftTD paper's *bound on the
effective learning rate*: no matter how large individual step sizes
grow, the per-step total rate cannot exceed the budget. -/
theorem total_trace_increment_bounded (η rate : ℝ) (hη : 0 < η) :
    (η / overshootE η rate) * rate ≤ η := by
  unfold overshootE
  by_cases hle : rate ≤ η
  · have hmax : max η rate = η := max_eq_left hle
    rw [hmax]
    field_simp [ne_of_gt hη]
    exact hle
  · have hgt : η < rate := lt_of_not_ge hle
    have hmax : max η rate = rate := max_eq_right (le_of_lt hgt)
    rw [hmax]
    have hrate : rate ≠ 0 := ne_of_gt (lt_of_lt_of_le hη (le_of_lt hgt))
    field_simp [hrate]
    norm_num

/-- Each feature's trace increment is bounded by its own step size:
`zδᵢ = (η/E)·αᵢ ≤ αᵢ` (because `η/E ≤ 1` and `αᵢ ≥ 0`). -/
theorem trace_increment_le_step_size (η rate α : ℝ) (hη : 0 < η) (hα : 0 ≤ α) :
    traceIncrement η α (overshootE η rate) ≤ α := by
  unfold traceIncrement overshootE
  have hEpos : 0 < max η rate := lt_of_lt_of_le hη (le_max_left η rate)
  have hratio : η / max η rate ≤ 1 := (div_le_one hEpos).2 (le_max_left η rate)
  exact mul_le_of_le_one_left hα hratio

/-- The step-size decay branch (`β += ln decay`, `0 < decay ≤ 1`,
`learn_second_loop` when the budget is exceeded) can only shrink a
step size: `exp(β + ln d) = d·exp β ≤ exp β`. (The reference
implementation re-clips on the next step's first loop; only the
monotonicity of the decay is load-bearing here.) -/
theorem decay_shrinks_step_size (β d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    Real.exp (β + Real.log d) ≤ Real.exp β := by
  rw [Real.exp_add, Real.exp_log hd0, mul_comm]
  exact mul_le_of_le_one_left (le_of_lt (Real.exp_pos β)) hd1

end

end AcornVerif
