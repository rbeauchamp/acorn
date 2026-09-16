/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.ModelConstants
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The εz-greedy duration law

A real-arithmetic model of a duration draw: for `u ∈ (0,1]`, take `⌊1/u⌋`
and cap the result at the supplied maximum.

**Prior-art pin (PAR-8 / D3).** Dabney, Ostrovski & Barreto,
*Temporally-Extended ε-Greedy Exploration*, ICLR 2021, arXiv:2006.01782v1
opened. No running page number on that PDF's face. File page 5 of 20, §4.2:
the option `ω_a^n` "takes action a for n steps and then terminates". File
page 14 Algorithm 1 serves n+1. This file proves the capped floor-inverse-uniform
surrogate (`⌊1/u⌋`, cap); the paper uses a ζ(μ=2) law. Containment at `cap = 1`
is the family including plain ε-greedy.

Two facts, different in kind:

* **Bounded work.** A duration is at least one step and never exceeds the cap, so
  each draw therefore commits to a bounded number of steps.
* **Containment.** At `cap = 1` the law returns `1` for *every* admissible `u`, so
  every exploratory run is a single step — which is plain ε-greedy exactly. This
  discharges the first claim of the adoption rule in
  `docs/learned-only-binding.md` §4: the replacement's family contains the rule it
  replaced, so εz-greedy can do whatever ε-greedy does.

The model uses real arithmetic and integer floors. The theorems below cover
positive durations, the cap and single-step policy containment at `cap = 1`.
Floating-point draws and saturating word conversion are separate implementation
boundaries. The predecessor `EzGreedy::begin` consumed an extra random draw for
duration even at `cap = 1`, so its generator advanced differently from ordinary
ε-greedy. The containment identity concerns the duration law.
-/

namespace AcornVerif

noncomputable section

/-- The duration `EzGreedy::begin` commits to: `⌊1/u⌋`, capped.

`u` is `1 - next_f64()`, so it ranges over `(0, 1]` and the reciprocal is finite —
positivity excludes a zero divisor. -/
noncomputable def ezDuration (u : ℝ) (cap : ℤ) : ℤ :=
  if ⌊(1 : ℝ) / u⌋ ≥ cap then cap else ⌊(1 : ℝ) / u⌋

/-- The draw is at least one: for `u ∈ (0, 1]`, `1 ≤ ⌊1/u⌋`.

This is what makes the reciprocal's floor a usable duration without a guard —
it cannot come out zero or negative anywhere on the admissible range. -/
theorem one_le_floor_inv {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) : 1 ≤ ⌊(1 : ℝ) / u⌋ := by
  have h : (1 : ℝ) ≤ 1 / u := one_le_one_div h0 h1
  exact Int.le_floor.mpr (by exact_mod_cast h)

/-- A duration never exceeds the cap, so `EzGreedy::MAX_DURATION` is a bound on
per-step commitment. -/
theorem ez_duration_le_cap (u : ℝ) (cap : ℤ) : ezDuration u cap ≤ cap := by
  unfold ezDuration
  split_ifs with h
  · exact le_refl cap
  · exact le_of_lt (lt_of_not_ge h)

/-- A duration is at least one step, so `begin` always has an action to serve. -/
theorem ez_duration_pos {u : ℝ} {cap : ℤ} (h0 : 0 < u) (h1 : u ≤ 1) (hc : 1 ≤ cap) :
    1 ≤ ezDuration u cap := by
  unfold ezDuration
  split_ifs with h
  · exact hc
  · exact one_le_floor_inv h0 h1

/-- **Containment.** At `cap = 1` the duration law is constantly `1` over the whole
admissible range of `u`, so every exploratory run lasts exactly one step.

At this parameter setting, every exploratory run is a single-step commitment. -/
theorem ez_contains_epsilon_greedy {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    ezDuration u 1 = 1 := by
  unfold ezDuration
  rw [if_pos (one_le_floor_inv h0 h1)]

/-- And so the residual run length is zero: the action is served once and the next
step is a fresh decision point. `EzGreedy::serve` returns `None` at
`remaining = 0`, which is ε-greedy's behaviour exactly. -/
theorem ez_remaining_zero_at_cap_one {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    ezDuration u 1 - 1 = 0 := by
  rw [ez_contains_epsilon_greedy h0 h1]; ring

/-- The bound at the model cap in `ModelConstants.ezMaxDuration`. Current constant
compatibility is checked separately by `AcornVerif.CurrentConstants`. -/
theorem ez_duration_le_shipped_cap (u : ℝ) :
    ezDuration u (ModelConstants.ezMaxDuration : ℤ) ≤ (ModelConstants.ezMaxDuration : ℤ) :=
  ez_duration_le_cap u _

-- Non-vacuity: the hypotheses are inhabited, and the cap does bind.
example : ezDuration 1 1 = 1 := by norm_num [ezDuration]
example : ezDuration (1 / 1000) 128 = 128 := by norm_num [ezDuration]

end

end AcornVerif
