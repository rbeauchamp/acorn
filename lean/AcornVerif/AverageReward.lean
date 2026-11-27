import AcornVerif.Projection
import Mathlib.Data.Fintype.Card

namespace AcornVerif

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

theorem active_features_count_bound {N : ℕ} (features : List (Fin N))
    (h : features.Nodup) : features.length ≤ N := by
  simpa using h.length_le_card

def withModelFeature {α : Type} [DecidableEq α] (features : List α) (age : α) : List α :=
  if age ∈ features then features else features ++ [age]

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

theorem with_model_feature_preserves {α : Type} [DecidableEq α]
    (features : List α) (age : α) :
    features.IsPrefix (withModelFeature features age) ∧ age ∈ withModelFeature features age := by
  unfold withModelFeature
  split_ifs with ha
  · exact ⟨⟨[], by simp⟩, ha⟩
  · exact ⟨⟨[age], rfl⟩, by simp⟩

theorem with_model_feature_length {α : Type} [DecidableEq α]
    (features : List α) (age : α) :
    (withModelFeature features age).length ≤ features.length + 1 := by
  unfold withModelFeature
  split_ifs <;> simp

theorem ema_horizon_mean_age (horizon : ℝ) (hh : horizon ≠ 0) :
    (1 - 1 / horizon) * ((horizon - 1) + 1) = horizon - 1 := by
  field_simp [hh]
  ring

theorem ema_horizon_squared_mass (horizon : ℝ)
    (hh : horizon ≠ 0) (hd : 2 * horizon - 1 ≠ 0) :
    (1 - 1 / horizon) ^ 2 * (1 / (2 * horizon - 1)) +
      (1 / horizon) ^ 2 = 1 / (2 * horizon - 1) := by
  have hc : (2 * horizon - 1) * (2 * horizon - 1)⁻¹ = 1 := mul_inv_cancel₀ hd
  field_simp [hh]
  ring_nf at hc ⊢
  nlinarith [hc]

def differentialError (reward rate next previous : ℝ) : ℝ :=
  reward - rate + next - previous

theorem differential_error_shift (reward rate next previous offset : ℝ) :
    differentialError reward rate (next + offset) (previous + offset) =
      differentialError reward rate next previous := by
  unfold differentialError
  ring

theorem differential_error_offset_mismatch
    (reward rate next previous nextOffset previousOffset : ℝ) :
    differentialError reward rate (next + nextOffset) (previous + previousOffset) -
      differentialError reward rate next previous = nextOffset - previousOffset := by
  unfold differentialError
  ring

def differentialReturn (rate : ℝ) : List ℝ → ℝ
  | [] => 0
  | reward :: rest => reward - rate + differentialReturn rate rest

theorem differential_return_duration (rate : ℝ) (rewards : List ℝ) :
    differentialReturn rate rewards = rewards.sum - (rewards.length : ℝ) * rate := by
  induction rewards with
  | nil => simp [differentialReturn]
  | cons reward rest ih =>
    simp only [differentialReturn, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, ih]
    ring

theorem differential_return_rate_change (oldRate newRate : ℝ) (rewards : List ℝ) :
    differentialReturn newRate rewards - differentialReturn oldRate rewards =
      (rewards.length : ℝ) * (oldRate - newRate) := by
  rw [differential_return_duration, differential_return_duration]
  ring

def rewardRateStep (step rate reward : ℝ) : ℝ := rate + step * (reward - rate)

theorem reward_rate_step_convex (step rate reward : ℝ) :
    rewardRateStep step rate reward = (1 - step) * rate + step * reward := by
  unfold rewardRateStep
  ring

theorem reward_rate_step_bounded (step rate reward : ℝ)
    (ha : 0 ≤ step) (ha1 : step ≤ 1) (hg : 0 ≤ rate) (hg1 : rate ≤ 1)
    (hr : 0 ≤ reward) (hr1 : reward ≤ 1) :
    0 ≤ rewardRateStep step rate reward ∧ rewardRateStep step rate reward ≤ 1 := by
  rw [reward_rate_step_convex]
  constructor
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hg1),
      mul_nonneg ha (sub_nonneg.mpr hr1)]

def rewardRateIter (step reward rate : ℝ) : ℕ → ℝ
  | 0 => rate
  | n + 1 => rewardRateStep step (rewardRateIter step reward rate n) reward

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

theorem differential_model_gain_correction
    (reward duration continuation oldRate newRate : ℝ) :
    (reward - duration * newRate + continuation) -
      (reward - duration * oldRate + continuation) = duration * (oldRate - newRate) := by
  ring

theorem differential_backup_distance
    (reward rate duration left right : ℝ) :
    |(reward - duration * rate + left) - (reward - duration * rate + right)| =
      |left - right| := by
  congr 1
  ring

theorem differential_policy_target_discrepancy
    (reward duration evaluationRate controlRate evaluationValue controlValue : ℝ) :
    (reward - duration * controlRate + controlValue) -
      (reward - duration * evaluationRate + evaluationValue) =
        duration * (evaluationRate - controlRate) + controlValue - evaluationValue := by
  ring

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

theorem differential_optimistic_backup_positive
    (lo hi probability q0 q1 : ℝ) (hp : 0 < probability) (hp1 : probability < 1)
    (hreward : lo < hi)
    (hevaluation : lo - ((1 - probability) * lo + probability * hi) +
      ((1 - probability) * q0 + probability * q1) - q0 = 0) :
    0 < hi - ((1 - probability) * lo + probability * hi) + max q0 q1 - q1 := by
  rw [differential_optimistic_backup_residual lo hi probability q0 q1
    (ne_of_gt hp) hreward hevaluation]
  exact mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hreward)

theorem differential_projected_backup_discrepancy
    (bound reward rate duration continuation : ℝ) :
    projectR bound (reward - rate * duration + projectR bound continuation) -
      (reward - rate * duration + continuation) =
        (projectR bound (reward - rate * duration + projectR bound continuation) -
          (reward - rate * duration + projectR bound continuation)) +
        (projectR bound continuation - continuation) := by
  ring

theorem differential_projected_backup_agrees
    (bound reward rate duration continuation : ℝ)
    (hcLower : -bound ≤ continuation) (hcUpper : continuation ≤ bound)
    (htLower : -bound ≤ reward - rate * duration + continuation)
    (htUpper : reward - rate * duration + continuation ≤ bound) :
    projectR bound (reward - rate * duration + projectR bound continuation) =
      reward - rate * duration + continuation := by
  rw [project_id_of_mem bound continuation hcLower hcUpper]
  exact project_id_of_mem bound _ htLower htUpper

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

theorem differential_expected_duration_zero_iff (residual duration : ℝ)
    (hd : 0 < duration) : residual / duration = 0 ↔ residual = 0 := by
  simp [div_eq_zero_iff, ne_of_gt hd]

theorem two_state_differential_rate (p rate low high : ℝ)
    (hlow : low = -rate + (1 - p) * low + p * high)
    (hhigh : high = 1 - rate + p * low + (1 - p) * high) :
    rate = 1 / 2 := by
  nlinarith [hlow, hhigh]

theorem two_state_differential_span (p rate low high : ℝ) (hp : p ≠ 0)
    (hlow : low = -rate + (1 - p) * low + p * high)
    (hhigh : high = 1 - rate + p * low + (1 - p) * high) :
    high - low = 1 / (2 * p) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hp)).2
  nlinarith [hlow, hhigh]

theorem two_state_centered_solution (p : ℝ) (hp : p ≠ 0) :
    (-1 / (4 * p) : ℝ) = -(1 / 2) + (1 - p) * (-1 / (4 * p)) + p * (1 / (4 * p)) ∧
      (1 / (4 * p) : ℝ) = 1 - 1 / 2 + p * (-1 / (4 * p)) + (1 - p) * (1 / (4 * p)) := by
  constructor <;> field_simp <;> ring

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
