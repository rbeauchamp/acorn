import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

namespace AcornVerif

def traceAfter (z₀ c : ℝ) (n : ℕ) : ℝ := z₀ * c ^ n

theorem trace_decay_monotone (z₀ c : ℝ) (hz : 0 ≤ z₀) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ n : ℕ, traceAfter z₀ c (n + 1) ≤ traceAfter z₀ c n := by
  intro n
  unfold traceAfter
  rw [pow_succ, ← mul_assoc, mul_comm]
  exact mul_le_of_le_one_left (mul_nonneg hz (pow_nonneg hc0 n)) hc1

theorem trace_geometric_bound (z₀ c : ℝ) (hz : 0 ≤ z₀) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ n : ℕ, traceAfter z₀ c n ≤ z₀ := by
  intro n
  unfold traceAfter
  have hpow : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1
  rw [mul_comm]
  exact mul_le_of_le_one_left hz hpow

theorem pruning_implies_negligible (z lastAlpha ε : ℝ) (ha : 0 ≤ lastAlpha)
    (he1 : ε ≤ 1) (hprune : z ≤ ε * lastAlpha) :
    z ≤ lastAlpha := by
  calc
    z ≤ ε * lastAlpha := hprune
    _ ≤ 1 * lastAlpha := mul_le_mul_of_nonneg_right he1 ha
    _ = lastAlpha := one_mul _

end AcornVerif
