/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Eligibility-trace invariants of SwiftTD

Real-arithmetic contracts for trace decay, geometric bounds and pruning.
The model separates pure decay from the active-loop trace increment.
-/

namespace AcornVerif

/-- The pure trace-decay dynamics: `zₙ₊₁ = c·zₙ` with `c = γλ`
(the `z *= gamma * lambda` line of `learn_first_loop`). -/
def traceAfter (z₀ c : ℝ) (n : ℕ) : ℝ := z₀ * c ^ n

/-- The decay *step* is monotone when `0 ≤ c ≤ 1` and `z₀ ≥ 0`: the pure-decay
sequence `z₀ * c^n` never grows.

Scope, because the obvious reading is wrong: this does **not** say traces never
grow in the algorithm. `learn_second_loop` grows them on every step
(`z += z_delta * (1 - t)`); that
increment is modelled separately as `traceIncrement` in `StepSize.lean`. What is
proven here is that the decay factor alone is non-increasing. -/
theorem trace_decay_monotone (z₀ c : ℝ) (hz : 0 ≤ z₀) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ n : ℕ, traceAfter z₀ c (n + 1) ≤ traceAfter z₀ c n := by
  intro n
  unfold traceAfter
  rw [pow_succ, ← mul_assoc, mul_comm]
  exact mul_le_of_le_one_left (mul_nonneg hz (pow_nonneg hc0 n)) hc1

/-- The geometric bound: a trace never exceeds its initial value under
the same assumptions (`0 ≤ c ≤ 1`). This is what makes the pruning
threshold meaningful. -/
theorem trace_geometric_bound (z₀ c : ℝ) (hz : 0 ≤ z₀) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ n : ℕ, traceAfter z₀ c n ≤ z₀ := by
  intro n
  unfold traceAfter
  have hpow : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1
  rw [mul_comm]
  exact mul_le_of_le_one_left hz hpow

/-- Pruning bound (`learn_first_loop`): if a trace has decayed to
`≤ ε · lastAlpha` with `ε ≤ 1` and `lastAlpha ≥ 0`, then `z ≤ lastAlpha`.

Read the bound literally. The proof discards the `ε` factor, so what is
established is "at most one `lastAlpha`", *not* "negligible" — with
`ε = 1e-5` the true bound is far tighter than this theorem states. `0 < ε` is
not a hypothesis. The name is weaker than it sounds, so cite the statement
rather than the name when relying on it. -/
theorem pruning_implies_negligible (z lastAlpha ε : ℝ) (ha : 0 ≤ lastAlpha)
    (he1 : ε ≤ 1) (hprune : z ≤ ε * lastAlpha) :
    z ≤ lastAlpha := by
  calc
    z ≤ ε * lastAlpha := hprune
    _ ≤ 1 * lastAlpha := mul_le_mul_of_nonneg_right he1 ha
    _ = lastAlpha := one_mul _

end AcornVerif
