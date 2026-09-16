/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Projection

/-!
# Differential return contracts

Wan, Naik and Sutton, *Learning and Planning in Average-Reward Markov Decision
Processes*, ICML 2021, PMLR 139:10653–10662, §2 eqs. (3)–(5) and §4 eq. (10),
define the differential Bellman residual and its additive freedom.
<https://proceedings.mlr.press/v139/wan21a/wan21a.pdf>

Wan, Naik and Sutton, *Average-Reward Learning and Planning with Options*,
NeurIPS 2021, §2 eqs. (1)–(2), give the option return with reward rate charged
per primitive transition.
<https://proceedings.neurips.cc/paper_files/paper/2021/file/c058f544c737782deacefa532d9add4c-Paper.pdf>

Sutton and Barto, *Reinforcement Learning: An Introduction*, 2nd ed.,
MIT Press (2018), §10.3 Exercise 10.8, p. 252, admits the reward-residual
gain update. Its constant-step affine recurrence is characterized below.

These algebraic contracts are over real numbers. The two-state
identities characterize an entire family: bounded rewards alone supply no
transition-independent bound on differential value span. A numerical
projection therefore declares its numerical budget separately from true-value
containment. Acorn retains the existing control weight rail (PAR-15).
-/

namespace AcornVerif

/-- Compose a growing-step invariant and its capped endpoint over every finite
ordered fold. The induction assumes the stated step premises; binary32
addition correspondence is a separate execution obligation. -/
theorem capped_fold_invariant {State Input : Type}
    (valid : ℕ → State → Prop) (step : State → Input → State) (cap : ℕ)
    (hgrow : ∀ n, n < cap → ∀ s w, valid n s → valid (n + 1) (step s w))
    (hcap : ∀ s w, valid cap s → valid cap (step s w))
    (inputs : List Input) (n : ℕ) (state : State) (h : valid (min n cap) state) :
    valid (min (n + inputs.length) cap) (inputs.foldl step state) := by
  induction inputs generalizing n state with
  | nil => simpa using h
  | cons w rest ih =>
    have next : valid (min (n + 1) cap) (step state w) := by
      by_cases hn : n < cap
      · rw [Nat.min_eq_left (by omega)]
        apply hgrow n hn
        simpa [Nat.min_eq_left (by omega : n ≤ cap)] using h
      · rw [Nat.min_eq_right (by omega)]
        apply hcap
        simpa [Nat.min_eq_right (by omega : cap ≤ n)] using h
    have result := ih (n + 1) (step state w) next
    simpa only [List.foldl_cons, List.length_cons,
      show n + (rest.length + 1) = n + 1 + rest.length by omega] using result

/-- A unique feature list indexed by the learner's own space has at most N
members. Together with the capped-fold invariant this gives the capacity bound. -/
theorem active_features_count_bound {N : ℕ} (features : List (Fin N))
    (h : features.Nodup) : features.length ≤ N := by
  simpa using h.length_le_card

/-- Append one generic model input only when it is absent; the base order is
preserved. This is the age-indicator construction in `ActiveSet::with_feature`. -/
def withModelFeature {α : Type} [DecidableEq α] (features : List α) (age : α) : List α :=
  if age ∈ features then features else features ++ [age]

/-- Every unique input remains unique after the optional age feature. Hash
collisions choose the existing member rather than duplicating its weight. -/
theorem with_model_feature_nodup {α : Type} [DecidableEq α]
    (features : List α) (age : α) (h : features.Nodup) :
    (withModelFeature features age).Nodup := by
  unfold withModelFeature
  split_ifs with ha
  · exact h
  · simp only [List.nodup_append, h, List.nodup_singleton, true_and]
    intro a hmem b hb hab
    have hb' : b = age := by simpa using hb
    exact ha ((hab.trans hb') ▸ hmem)

/-- The unchanged base is a prefix and the requested indicator is present,
whether its hash collides or appends a new index. -/
theorem with_model_feature_preserves {α : Type} [DecidableEq α]
    (features : List α) (age : α) :
    features.IsPrefix (withModelFeature features age) ∧ age ∈ withModelFeature features age := by
  unfold withModelFeature
  split_ifs with ha
  · exact ⟨⟨[], by simp⟩, ha⟩
  · exact ⟨⟨[age], rfl⟩, by simp⟩

/-- Age augmentation requires at most one more active feature, independently
of observation size, run lifetime or the size of the weight array. -/
theorem with_model_feature_length {α : Type} [DecidableEq α]
    (features : List α) (age : α) :
    (withModelFeature features age).length ≤ features.length + 1 := by
  unfold withModelFeature
  split_ifs <;> simp

/-- The ideal reward EMA with reciprocal horizon has this fixed mean age.
Sutton and Barto (2018), §10.3 Exercise 10.8; the horizon is Acorn's explicit
lag budget, not an optimum or an independence claim about observations. -/
theorem ema_horizon_mean_age (horizon : ℝ) (hh : horizon ≠ 0) :
    (1 - 1 / horizon) * ((horizon - 1) + 1) = horizon - 1 := by
  field_simp [hh]
  ring

/-- The ideal EMA squared-coefficient-mass recurrence has this fixed point.
A noise-variance interpretation additionally requires uncorrelated noise. -/
theorem ema_horizon_squared_mass (horizon : ℝ)
    (hh : horizon ≠ 0) (hd : 2 * horizon - 1 ≠ 0) :
    (1 - 1 / horizon) ^ 2 * (1 / (2 * horizon - 1)) +
      (1 / horizon) ^ 2 = 1 / (2 * horizon - 1) := by
  have hc : (2 * horizon - 1) * (2 * horizon - 1)⁻¹ = 1 := mul_inv_cancel₀ hd
  field_simp [hh]
  ring_nf at hc ⊢
  nlinarith [hc]

/-- Differential one-step residual (Wan, Naik and Sutton, ICML 2021,
§4 eq. (12), on-policy specialization). No geometric discount occurs. -/
def differentialError (reward rate next previous : ℝ) : ℝ :=
  reward - rate + next - previous

/-- Every common additive value offset cancels in the differential residual.
This does not justify comparing estimates with different offsets. -/
theorem differential_error_shift (reward rate next previous offset : ℝ) :
    differentialError reward rate (next + offset) (previous + offset) =
      differentialError reward rate next previous := by
  unfold differentialError
  ring

/-- A mismatch between two learners' additive offsets survives as exactly
their difference. The identity quantifies over all estimates and offsets. -/
theorem differential_error_offset_mismatch
    (reward rate next previous nextOffset previousOffset : ℝ) :
    differentialError reward rate (next + nextOffset) (previous + previousOffset) -
      differentialError reward rate next previous = nextOffset - previousOffset := by
  unfold differentialError
  ring

/-- A finite differential return, charging the same reward rate on every
primitive transition, as in Wan, Naik and Sutton, NeurIPS 2021, §2 eq. (1). -/
def differentialReturn (rate : ℝ) : List ℝ → ℝ
  | [] => 0
  | reward :: rest => reward - rate + differentialReturn rate rest

/-- Every finite option span owes its duration times the reward rate.
The empty span is included; no infinite random-series convergence is assumed. -/
theorem differential_return_duration (rate : ℝ) (rewards : List ℝ) :
    differentialReturn rate rewards = rewards.sum - (rewards.length : ℝ) * rate := by
  induction rewards with
  | nil => simp [differentialReturn]
  | cons reward rest ih =>
    simp only [differentialReturn, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, ih]
    ring

/-- Changing a fixed gain in an option backup changes the residual by duration
times the gain discrepancy. A reward model centered at an old gain cannot be
reused at a new gain without this correction. -/
theorem differential_return_rate_change (oldRate newRate : ℝ) (rewards : List ℝ) :
    differentialReturn newRate rewards - differentialReturn oldRate rewards =
      (rewards.length : ℝ) * (oldRate - newRate) := by
  rw [differential_return_duration, differential_return_duration]
  ring

/-- Reward-residual gain update from Sutton and Barto (2018), §10.3
Exercise 10.8. The step is fixed independently of the observed reward. -/
def rewardRateStep (step rate reward : ℝ) : ℝ := rate + step * (reward - rate)

/-- The source recurrence is exactly a convex mixture when the step lies in
[0,1]; no state-dependent reward weighting is introduced. -/
theorem reward_rate_step_convex (step rate reward : ℝ) :
    rewardRateStep step rate reward = (1 - step) * rate + step * reward := by
  unfold rewardRateStep
  ring

/-- Every legal gain/reward pair stays in [0,1] under every convex step.
Floating-point construction and restoration require separate execution contracts. -/
theorem reward_rate_step_bounded (step rate reward : ℝ)
    (ha : 0 ≤ step) (ha1 : step ≤ 1) (hg : 0 ≤ rate) (hg1 : rate ≤ 1)
    (hr : 0 ≤ reward) (hr1 : reward ≤ 1) :
    0 ≤ rewardRateStep step rate reward ∧ rewardRateStep step rate reward ≤ 1 := by
  rw [reward_rate_step_convex]
  constructor
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hg1),
      mul_nonneg ha (sub_nonneg.mpr hr1)]

/-- Iterate the constant-target affine recurrence. This is an algebraic model,
not a claim that a changing stochastic reward stream is constant. -/
def rewardRateIter (step reward rate : ℝ) : ℕ → ℝ
  | 0 => rate
  | n + 1 => rewardRateStep step (rewardRateIter step reward rate n) reward

/-- The constant-target error is exactly geometric for every initial value,
target, step and iteration count. Persistent random error is not claimed to
vanish under a constant step. -/
theorem reward_rate_constant_error (step reward rate : ℝ) (n : ℕ) :
    rewardRateIter step reward rate n - reward = (1 - step) ^ n * (rate - reward) := by
  induction n with
  | zero => simp [rewardRateIter]
  | succ n ih =>
    calc
      rewardRateIter step reward rate (n + 1) - reward =
          (1 - step) * (rewardRateIter step reward rate n - reward) := by
        simp only [rewardRateIter, rewardRateStep]
        ring
      _ = (1 - step) * ((1 - step) ^ n * (rate - reward)) := by rw [ih]
      _ = (1 - step) ^ (n + 1) * (rate - reward) := by rw [pow_succ]; ring

/-- An unprojected model backup owns raw expected reward and duration separately (Wan,
Naik and Sutton, NeurIPS 2021, §2 eq. (1)). Changing gain therefore has the
exact duration correction without retraining a reward model. -/
theorem differential_model_gain_correction
    (reward duration continuation oldRate newRate : ℝ) :
    (reward - duration * newRate + continuation) -
      (reward - duration * oldRate + continuation) = duration * (oldRate - newRate) := by
  ring

/-- The unprojected differential scalar backup preserves every distance between terminal
values; its coefficient is one, not a strict discount contraction. This is an
identity for all rewards, gains, durations and continuations. -/
theorem differential_backup_distance
    (reward rate duration left right : ℝ) :
    |(reward - duration * rate + left) - (reward - duration * rate + right)| =
      |left - right| := by
  congr 1
  ring

/-- Changing the target policy changes the continuation and, in general, its
gain. Wan, Naik and Sutton, NeurIPS 2021, §2 eqs. (1)–(2), distinguish
evaluation gain from optimal gain. This identity exposes both discrepancies;
a common value offset does not cancel a difference in target policy. -/
theorem differential_policy_target_discrepancy
    (reward duration evaluationRate controlRate evaluationValue controlValue : ℝ) :
    (reward - duration * controlRate + controlValue) -
      (reward - duration * evaluationRate + evaluationValue) =
        duration * (evaluationRate - controlRate) + controlValue - evaluationValue := by
  ring

/-- In the entire one-state, two-action family, exact behavior evaluation
leaves this optimistic residual when the option uses a greedy continuation.
Wan, Naik and Sutton, NeurIPS 2021, §2 eqs. (1)–(2), distinguish these
equations and their gains. All rewards, values and nonzero probabilities are
quantified; the identity is independent of the additive value reference. -/
theorem differential_optimistic_backup_residual
    (lo hi probability q0 q1 : ℝ) (hp : probability ≠ 0) (hreward : lo < hi)
    (hevaluation : lo - ((1 - probability) * lo + probability * hi) +
      ((1 - probability) * q0 + probability * q1) - q0 = 0) :
    hi - ((1 - probability) * lo + probability * hi) + max q0 q1 - q1 =
      (1 - probability) * (hi - lo) := by
  have hz : probability * (q1 - q0 - (hi - lo)) = 0 := by
    nlinarith [hevaluation]
  have hgap : q1 - q0 - (hi - lo) = 0 := (mul_eq_zero.mp hz).resolve_left hp
  have hmax : q0 ≤ q1 := by linarith
  rw [max_eq_right hmax]
  ring

/-- Every strictly exploratory probability and strict reward gap in that
family forces a positive greedy residual at the evaluation target. Clipping
may suppress the residual at a numerical rail; it does not establish a common
target-policy interpretation. -/
theorem differential_optimistic_backup_positive
    (lo hi probability q0 q1 : ℝ) (hp : 0 < probability) (hp1 : probability < 1)
    (hreward : lo < hi)
    (hevaluation : lo - ((1 - probability) * lo + probability * hi) +
      ((1 - probability) * q0 + probability * q1) - q0 = 0) :
    0 < hi - ((1 - probability) * lo + probability * hi) + max q0 q1 - q1 := by
  rw [differential_optimistic_backup_residual lo hi probability q0 q1
    (ne_of_gt hp) hreward hevaluation]
  exact mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hreward)

/-- The clipped planning expression has two distinct projection errors: the
continuation-scalar restriction and the combined-backup restriction. This is an
identity over all real inputs, not a claim that the numerical rail contains
the true differential value (PAR-15 adaptation of NeurIPS 2021 §2 eq. (1)).
Clipping the training target before expectation and model estimation error
are separate from this scalar/read projection identity. -/
theorem differential_projected_backup_discrepancy
    (bound reward rate duration continuation : ℝ) :
    projectR bound (reward - rate * duration + projectR bound continuation) -
      (reward - rate * duration + continuation) =
        (projectR bound (reward - rate * duration + projectR bound continuation) -
          (reward - rate * duration + projectR bound continuation)) +
        (projectR bound continuation - continuation) := by
  ring

/-- The same clipped expression agrees with the unprojected target whenever
both intermediate and final values lie in the declared rail. Model estimation
error and floating-point rounding are separate obligations. -/
theorem differential_projected_backup_agrees
    (bound reward rate duration continuation : ℝ)
    (hcLower : -bound ≤ continuation) (hcUpper : continuation ≤ bound)
    (htLower : -bound ≤ reward - rate * duration + continuation)
    (htUpper : reward - rate * duration + continuation ≤ bound) :
    projectR bound (reward - rate * duration + projectR bound continuation) =
      reward - rate * duration + continuation := by
  rw [project_id_of_mem bound continuation hcLower hcUpper]
  exact project_id_of_mem bound _ htLower htUpper

/-- Gain correction after output projection includes the change in projection
error. The exact unprojected duration identity cannot be attributed unchanged
to a saturated planning target. -/
theorem differential_projected_gain_discrepancy
    (bound reward duration continuation oldRate newRate : ℝ) :
    (projectR bound (reward - duration * newRate + continuation) -
      projectR bound (reward - duration * oldRate + continuation)) -
        duration * (oldRate - newRate) =
    (projectR bound (reward - duration * newRate + continuation) -
      (reward - duration * newRate + continuation)) -
    (projectR bound (reward - duration * oldRate + continuation) -
      (reward - duration * oldRate + continuation)) := by
  ring

/-- Dividing a fixed expected residual by a positive expected duration
preserves its zeros. Wan, Naik and Sutton, NeurIPS 2021, §3 eqs. (6)–(10)
and the remark on p. 4 use expected duration; this does not commute division
by a random sampled duration with expectation. -/
theorem differential_expected_duration_zero_iff (residual duration : ℝ)
    (hd : 0 < duration) : residual / duration = 0 ↔ residual = 0 := by
  simp [div_eq_zero_iff, ne_of_gt hd]

/-- For the symmetric two-state chain with rewards 0 and 1 and cross-transition
probability p, both Poisson equations force gain 1/2. This characterizes every
solution, not a selected trajectory; valid irreducible aperiodic chains have
0 < p < 1. Equations follow the ICML 2021 §4 eq. (10) definition. -/
theorem two_state_differential_rate (p rate low high : ℝ)
    (hlow : low = -rate + (1 - p) * low + p * high)
    (hhigh : high = 1 - rate + p * low + (1 - p) * high) :
    rate = 1 / 2 := by
  nlinarith [hlow, hhigh]

/-- The same family has differential span 1/(2p), for every nonzero p and
every solution. Even with exactly two states and reward range [0,1], a span
bound therefore needs a restriction on transition probabilities. An additive
normalization cannot change this span. -/
theorem two_state_differential_span (p rate low high : ℝ) (hp : p ≠ 0)
    (hlow : low = -rate + (1 - p) * low + p * high)
    (hhigh : high = 1 - rate + p * low + (1 - p) * high) :
    high - low = 1 / (2 * p) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hp)).2
  nlinarith [hlow, hhigh]

/-- Every nonzero transition parameter admits this centered solution of both
Poisson equations. This establishes non-vacuity of the entire family used in
the rate and span identities; it is not a selected counterexample. -/
theorem two_state_centered_solution (p : ℝ) (hp : p ≠ 0) :
    (-1 / (4 * p) : ℝ) = -(1 / 2) + (1 - p) * (-1 / (4 * p)) + p * (1 / (4 * p)) ∧
      (1 / (4 * p) : ℝ) = 1 - 1 / 2 + p * (-1 / (4 * p)) + (1 - p) * (1 / (4 * p)) := by
  constructor <;> field_simp <;> ring

/-- For every proposed nonnegative uniform span bound B, the transition
parameter 1/(2(B+1)) defines an irreducible aperiodic two-state chain whose
span is exactly B+1. The whole open family defeats a bound based only on
state count and reward range, even after fixing the additive normalization. -/
theorem two_state_span_exceeds_budget (budget : ℝ) (hb : 0 ≤ budget) :
    let p := 1 / (2 * (budget + 1))
    0 < p ∧ p < 1 ∧ 1 / (2 * p) = budget + 1 ∧ budget < 1 / (2 * p) := by
  dsimp
  have hd : 0 < 2 * (budget + 1) := by positivity
  have hi : 1 / (2 * (1 / (2 * (budget + 1)))) = budget + 1 := by
    field_simp
  refine ⟨one_div_pos.mpr hd, ?_, hi, ?_⟩
  · apply (div_lt_one hd).mpr
    linarith
  · rw [hi]
    linarith

end AcornVerif
