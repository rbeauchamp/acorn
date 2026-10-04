/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.ModelConstants
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
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

**Exploratory share (D6).** Under a uniform `u` on `(0, 1]` the capped duration
has mean `H_cap`, the harmonic number (`ez_duration_mean`, a Lebesgue integral).
A cycle of the behaviour explores for a run with probability `ε`, otherwise
takes one greedy step; `explorationShare` is its expected exploratory steps over
its expected length. The cycle is the behaviour's as a whole: over the executed
selection every decision is a served step of a run or one persistent draw, by
primitive control or by the executing option (`CurrentTemporal.select_persistent`),
at D6's rate under the declared policy (`TemporalSupport.select_declared`). At
D6's rate and the checked cap the share is below 6% (`declared_share_lt`). A
single-step draw has share exactly `ε` (`explorationShare_single`): that is the
meta-controller's draw over meta actions, and the behaviour's own share at
`cap = 1`. The rational rate and cap are checked against the executed words by
`CurrentConstants`; the exact branch mass of the executed draw is
`TemporalSupport.declared_branch_card`. The model assumes independent uniform
draws, which the deterministic generator does not supply, and it does not model
binary64 rounding of the executed reciprocal.
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
  rw [ite_eq_left (one_le_floor_inv h0 h1)]

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

/-- Tail law: on the admissible range a duration reaches level `n ≤ cap`
exactly when `u ≤ 1/n`, so `P(D ≥ n) = 1/n` under a uniform `u`. -/
theorem ez_duration_tail {u : ℝ} (h0 : 0 < u) {n cap : ℤ} (hn : 1 ≤ n) (hcap : n ≤ cap) :
    n ≤ ezDuration u cap ↔ u ≤ 1 / n := by
  have reach : n ≤ ezDuration u cap ↔ n ≤ ⌊(1 : ℝ) / u⌋ := by
    unfold ezDuration
    split_ifs with h
    · exact ⟨fun _ => le_trans hcap h, fun _ => hcap⟩
    · exact Iff.rfl
  have npos : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℤ) < n by omega)
  rw [reach, Int.le_floor, le_div_iff₀ h0, le_div_iff₀ npos, mul_comm]

/-- Each duration counts the tail levels it reaches, pointwise on the admissible
range: `D = Σ_{n=1}^{cap} 1[u ∈ (0, 1/n]]`. -/
theorem ez_duration_levels {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) (cap : ℕ) (hc : 1 ≤ cap) :
    (ezDuration u cap : ℝ) =
      ∑ n ∈ Finset.range cap, (Set.Ioc (0 : ℝ) (1 / ((n : ℝ) + 1))).indicator 1 u := by
  have lower := ez_duration_pos h0 h1 (show (1 : ℤ) ≤ cap by exact_mod_cast hc)
  have upper := ez_duration_le_cap u (cap : ℤ)
  have level : ∀ n ∈ Finset.range cap,
      (Set.Ioc (0 : ℝ) (1 / ((n : ℝ) + 1))).indicator 1 u =
        if n < (ezDuration u cap).toNat then (1 : ℝ) else 0 := by
    intro n member
    rw [Finset.mem_range] at member
    have tail := ez_duration_tail h0 (n := (n : ℤ) + 1) (cap := cap) (by omega) (by omega)
    push_cast at tail
    by_cases reached : u ≤ 1 / ((n : ℝ) + 1)
    · have below : n < (ezDuration u cap).toNat := by
        have := tail.mpr reached
        omega
      simp only [Set.indicator_apply, Set.mem_Ioc, h0, reached, below, and_self, Pi.one_apply,
        ↓reduceIte]
    · have above : ¬ n < (ezDuration u cap).toNat := by
        intro below
        exact reached (tail.mp (by omega))
      simp only [Set.indicator_apply, Set.mem_Ioc, h0, reached, above, and_false, ↓reduceIte]
  rw [Finset.sum_congr rfl level, Finset.sum_boole]
  have count : ((Finset.range cap).filter (fun n => n < (ezDuration u cap).toNat)).card =
      (ezDuration u cap).toNat := by
    have same : (Finset.range cap).filter (fun n => n < (ezDuration u cap).toNat) =
        Finset.range (ezDuration u cap).toNat := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [same, Finset.card_range]
  rw [count]
  have exact := Int.toNat_of_nonneg (show 0 ≤ ezDuration u cap by omega)
  exact_mod_cast exact.symm

/-- Under a uniform `u` on `(0, 1]` the capped duration has mean `H_cap`,
the harmonic number `Σ_{n=1}^{cap} 1/n`. -/
theorem ez_duration_mean (cap : ℕ) (hc : 1 ≤ cap) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
      (fun u => (ezDuration u cap : ℝ)) = harmonic cap := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    (by intro u member; exact ez_duration_levels member.1 member.2 cap hc)]
  rw [MeasureTheory.integral_finsetSum _ (fun _ _ => by
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator measurableSet_Ioc)]
  have level : ∀ n ∈ Finset.range cap,
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
        (fun u => (Set.Ioc (0 : ℝ) (1 / ((n : ℝ) + 1))).indicator 1 u) = 1 / ((n : ℝ) + 1) := by
    intro n _
    have positive : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have within : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc_right within)]
    simp only [Pi.one_apply, MeasureTheory.setIntegral_const,
      Real.volume_real_Ioc_of_le positive.le, smul_eq_mul, mul_one, sub_zero]
  rw [Finset.sum_congr rfl level, harmonic]
  push_cast
  simp only [one_div]

/-- Expected exploratory share of one cycle of the behaviour: with branch mass
`ε` a run of mean length `h` is exploratory, otherwise one greedy step is taken.
It is the ratio of expected exploratory steps to expected cycle length. -/
noncomputable def explorationShare (ε h : ℝ) : ℝ := ε * h / (ε * h + (1 - ε))

/-- The share never exceeds `ε` times the mean run length. -/
theorem explorationShare_le {ε h : ℝ} (h0 : 0 ≤ ε) (hh : 1 ≤ h) :
    explorationShare ε h ≤ ε * h := by
  unfold explorationShare
  have runs : 0 ≤ ε * h := mul_nonneg h0 (by linarith)
  have cycle : 1 ≤ ε * h + (1 - ε) := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg runs (by linarith : (0 : ℝ) ≤ ε * h + (1 - ε) - 1)]

/-- A single-step draw explores on exactly an `ε` share of its draws: the
meta-controller's draw over meta actions, and the behaviour at a unit cap. -/
theorem explorationShare_single (ε : ℝ) : explorationShare ε 1 = ε := by
  unfold explorationShare
  rw [show ε * 1 + (1 - ε) = 1 by ring]
  simp

/-- At D6's rate and the executed cap's mean duration `H_128`, the expected
exploratory share of the behaviour's cycles is below 6%. The bound uses
`H_n ≤ 1 + ln n` and `ln 2 < 0.6931471808`. -/
theorem declared_share_lt :
    explorationShare (ModelConstants.exploreRate : ℝ) (harmonic ModelConstants.ezMaxDuration) <
      6 / 100 := by
  have rate : (ModelConstants.exploreRate : ℝ) = 10737418 / 1073741824 := by
    norm_num [ModelConstants.exploreRate]
  have atLeastOne : (1 : ℝ) ≤ harmonic ModelConstants.ezMaxDuration := by
    have first : (((0 + 1 : ℕ) : ℚ))⁻¹ ≤ harmonic ModelConstants.ezMaxDuration :=
      Finset.single_le_sum (f := fun i : ℕ => ((↑(i + 1) : ℚ))⁻¹)
        (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.mem_range.mpr (show 0 < ModelConstants.ezMaxDuration by decide))
    rw [show (((0 + 1 : ℕ) : ℚ))⁻¹ = 1 by norm_num] at first
    exact_mod_cast first
  have mean : (harmonic ModelConstants.ezMaxDuration : ℝ) ≤ 1 + Real.log 128 := by
    have bound := harmonic_le_one_add_log ModelConstants.ezMaxDuration
    rwa [show ((ModelConstants.ezMaxDuration : ℕ) : ℝ) = 128 by
      norm_num [ModelConstants.ezMaxDuration]] at bound
  have logarithm : Real.log 128 < 7 * 0.6931471808 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  calc explorationShare (ModelConstants.exploreRate : ℝ) (harmonic ModelConstants.ezMaxDuration)
      ≤ (ModelConstants.exploreRate : ℝ) * harmonic ModelConstants.ezMaxDuration :=
        explorationShare_le (by rw [rate]; norm_num) atLeastOne
    _ ≤ (ModelConstants.exploreRate : ℝ) * (1 + 7 * 0.6931471808) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [rate]; norm_num)
    _ < 6 / 100 := by rw [rate]; norm_num

/-- Persistence never lowers the share below the single-step share: for a rate in
`[0, 1]` and a mean run length of at least one step, `ε ≤ explorationShare ε h`. -/
theorem explorationShare_ge {ε h : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hh : 1 ≤ h) :
    ε ≤ explorationShare ε h := by
  unfold explorationShare
  have cycle : 0 < ε * h + (1 - ε) := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr hh)]
  rw [le_div_iff₀ cycle]
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (sub_nonneg.mpr hh)]

/-- At D6's rate and the executed cap's mean duration `H_128`, the expected
exploratory share of the behaviour's cycles is above 4.6%, more than four times
the single-step share. The bound uses `ln (n + 1) ≤ H_n` and `0.6931471803 < ln 2`. -/
theorem declared_share_gt :
    46 / 1000 < explorationShare (ModelConstants.exploreRate : ℝ)
      (harmonic ModelConstants.ezMaxDuration) := by
  have rate : (ModelConstants.exploreRate : ℝ) = 10737418 / 1073741824 := by
    norm_num [ModelConstants.exploreRate]
  have logarithm : 7 * 0.6931471803 < Real.log 128 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9]
  have mean : Real.log 128 ≤ (harmonic ModelConstants.ezMaxDuration : ℝ) := by
    refine le_trans (Real.log_le_log (by norm_num) ?_)
      (log_add_one_le_harmonic ModelConstants.ezMaxDuration)
    norm_num [ModelConstants.ezMaxDuration]
  unfold explorationShare
  rw [rate, lt_div_iff₀ (by linarith)]
  linarith

end

end AcornVerif
