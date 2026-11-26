import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import AcornVerif.ModelConstants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace AcornVerif

def shapedCumulant (reward gamma nextPotential previousPotential : ℝ) : ℝ :=
  reward + gamma * nextPotential - previousPotential

def terminalCumulant (reward stopping previousPotential : ℝ) : ℝ :=
  reward + stopping - previousPotential

def rewardReturn (gamma : ℝ) : List ℝ → ℝ
  | [] => 0
  | reward :: rest => reward + gamma * rewardReturn gamma rest

def shapedReturn (gamma currentPotential : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => -currentPotential
  | (reward, nextPotential) :: rest =>
      shapedCumulant reward gamma nextPotential currentPotential +
        gamma * shapedReturn gamma nextPotential rest

theorem terminal_correction (reward stopping potential : ℝ) :
    terminalCumulant reward stopping potential + potential = reward + stopping := by
  simp [terminalCumulant]

def shapedBootReturn (gamma stopping : ℝ) :
    ℝ → List (ℝ × ℝ) → ℝ → ℝ
  | currentPotential, [], finalReward =>
      terminalCumulant finalReward stopping currentPotential
  | currentPotential, (reward, nextPotential) :: rest, finalReward =>
      shapedCumulant reward gamma nextPotential currentPotential +
        gamma * shapedBootReturn gamma stopping nextPotential rest finalReward

theorem finite_activation_bootstrap_correction
    (gamma stopping currentPotential finalReward : ℝ)
    (transitions : List (ℝ × ℝ)) :
    shapedBootReturn gamma stopping currentPotential transitions finalReward +
        currentPotential =
      rewardReturn gamma (transitions.map Prod.fst ++ [finalReward]) +
        gamma ^ transitions.length * stopping := by
  induction transitions generalizing currentPotential with
  | nil => simp [shapedBootReturn, rewardReturn, terminalCumulant]
  | cons head tail ih =>
      rcases head with ⟨reward, nextPotential⟩
      simp only [shapedBootReturn, List.map_cons, List.cons_append, rewardReturn,
        List.length_cons, shapedCumulant, pow_succ]
      linear_combination gamma * ih nextPotential

theorem subtask_returns_agree
    (gamma stopping φ φ' finalReward : ℝ)
    (transitions transitions' : List (ℝ × ℝ))
    (h : transitions.map Prod.fst = transitions'.map Prod.fst) :
    shapedBootReturn gamma stopping φ transitions finalReward + φ =
      shapedBootReturn gamma stopping φ' transitions' finalReward + φ' := by
  have hlen : transitions.length = transitions'.length := by
    simpa [List.length_map] using congrArg List.length h
  rw [finite_activation_bootstrap_correction, finite_activation_bootstrap_correction,
    h, hlen]

theorem nonterminal_bellman_correction
    (reward gamma currentPotential nextPotential futureReward : ℝ) :
    shapedCumulant reward gamma nextPotential currentPotential +
          gamma * (futureReward - nextPotential) + currentPotential =
        reward + gamma * futureReward := by
  simp only [shapedCumulant]
  ring

theorem finite_activation_correction
    (gamma currentPotential : ℝ) (transitions : List (ℝ × ℝ)) :
    shapedReturn gamma currentPotential transitions + currentPotential =
      rewardReturn gamma (transitions.map Prod.fst) := by
  induction transitions generalizing currentPotential with
  | nil => simp [shapedReturn, rewardReturn]
  | cons head tail ih =>
      rcases head with ⟨reward, nextPotential⟩
      simp only [shapedReturn, List.map_cons, rewardReturn]
      rw [← ih nextPotential]
      simp [shapedCumulant]
      ring

theorem corrected_interruption_iff
    (stopping shapedContinuing currentPotential : ℝ) :
    stopping > shapedContinuing + currentPotential ↔
      stopping - currentPotential > shapedContinuing := by
  constructor <;> intro h <;> linarith

theorem controller_discounts_match :
    ModelConstants.optionGamma = ModelConstants.metaGamma := by
  norm_num [ModelConstants.optionGamma, ModelConstants.metaGamma]

def gapAcc (γ : ℝ) (r : ℕ → ℝ) : ℕ → ℝ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
    let p := gapAcc γ r n
    (p.1 + r n * γ ^ p.2, p.2 + 1)

def gapRun (γ : ℝ) (r : ℕ → ℝ) (k : ℕ) : ℝ × ℕ :=
  let p := gapAcc γ r k
  (p.1 + r k * γ ^ p.2, p.2 + 1)

theorem gap_close_is_smdp_backup (γ : ℝ) (r : ℕ → ℝ) (k : ℕ) :
    gapRun γ r k = (∑ i ∈ Finset.range (k + 1), γ ^ i * r i, k + 1) := by
  have acc : ∀ n, gapAcc γ r n = (∑ i ∈ Finset.range n, γ ^ i * r i, n) := by
    intro n
    induction n with
    | zero =>
      simp [gapAcc]
    | succ n ih =>
      simp only [gapAcc, ih, Finset.sum_range_succ, mul_comm]
  simp only [gapRun, acc, Finset.sum_range_succ, mul_comm]

theorem interrupted_span_return (γ : ℝ) (r : ℕ → ℝ) (z : ℝ) (j n : ℕ) :
    (∑ i ∈ Finset.range j, γ ^ i * r i) +
        γ ^ j * ((∑ i ∈ Finset.range n, γ ^ i * r (j + i)) + γ ^ n * z) =
      (∑ i ∈ Finset.range (j + n), γ ^ i * r i) + γ ^ (j + n) * z := by
  rw [Finset.sum_range_add, mul_add, Finset.mul_sum, pow_add, add_assoc]
  congr 2
  · exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_assoc]
  · rw [mul_assoc]

def stompStoppingValue (agentEstimate bonus terminalPotential : ℝ) : ℝ :=
  agentEstimate + bonus * terminalPotential

theorem subtask_terminal_telescoping
    (gamma agentEstimate bonus terminalPotential currentPotential finalReward : ℝ)
    (transitions : List (ℝ × ℝ)) :
    shapedBootReturn gamma (stompStoppingValue agentEstimate bonus terminalPotential)
        currentPotential transitions finalReward + currentPotential =
      rewardReturn gamma (transitions.map Prod.fst ++ [finalReward]) +
        gamma ^ transitions.length * (agentEstimate + bonus * terminalPotential) := by
  simpa [stompStoppingValue] using
    finite_activation_bootstrap_correction gamma
      (stompStoppingValue agentEstimate bonus terminalPotential)
      currentPotential finalReward transitions

theorem subtask_potential_invariance
    (gamma stopping φ₁ φ₂ finalReward : ℝ)
    (transitions₁ transitions₂ : List (ℝ × ℝ))
    (h_rew : transitions₁.map Prod.fst = transitions₂.map Prod.fst)
    (h_len : transitions₁.length = transitions₂.length) :
    (shapedBootReturn gamma stopping φ₁ transitions₁ finalReward + φ₁) -
      (shapedBootReturn gamma stopping φ₂ transitions₂ finalReward + φ₂) = 0 := by
  rw [finite_activation_bootstrap_correction, finite_activation_bootstrap_correction]
  rw [h_rew, h_len]
  ring

theorem subtask_block_exclusivity
    {β : Type} (b₀ b₁ b₂ : β)
    (h_nodup : [b₀, b₁, b₂].Nodup) :
    b₀ ≠ b₁ ∧ b₀ ≠ b₂ ∧ b₁ ≠ b₂ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at h_nodup
  exact ⟨h_nodup.1.1, h_nodup.1.2, h_nodup.2.1⟩

theorem option_model_scalar_continuation_equiv
    {ι : Type} (s : Finset ι)
    (w x n_next n_curr : ι → ℝ) (beta gamma : ℝ) :
    (∑ i ∈ s, w i * (gamma * beta * x i + gamma * (1 - beta) * n_next i - n_curr i)) =
      gamma * beta * (∑ i ∈ s, w i * x i) +
        gamma * (1 - beta) * (∑ i ∈ s, w i * n_next i) -
        (∑ i ∈ s, w i * n_curr i) := by
  have h_term : ∀ i ∈ s,
      w i * (gamma * beta * x i + gamma * (1 - beta) * n_next i - n_curr i) =
        gamma * beta * (w i * x i) + gamma * (1 - beta) * (w i * n_next i) - w i * n_curr i := by
    intro i _
    ring
  rw [Finset.sum_congr rfl h_term]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem option_model_terminal_discount_correction
    (gamma beta terminalFeature next current : ℝ) :
    (gamma * beta * terminalFeature + gamma * (1 - beta) * next - current) -
      (beta * terminalFeature + gamma * (1 - beta) * next - current) =
        (gamma - 1) * beta * terminalFeature := by
  ring

def optionModelIntraStepError (gamma r r_next c_next r_curr c_curr : ℝ) : ℝ :=
  (r + gamma * r_next - r_curr) + (gamma * c_next - c_curr)

def optionModelTerminalStepError (gamma finalReward terminalValue r_curr c_curr : ℝ) : ℝ :=
  (finalReward - r_curr) + (gamma * terminalValue - c_curr)

def optionModelErrorFold (gamma : ℝ) :
    ℝ → ℝ → List (ℝ × ℝ × ℝ) → ℝ → ℝ → ℝ
  | r_curr, c_curr, [], finalReward, terminalValue =>
      optionModelTerminalStepError gamma finalReward terminalValue r_curr c_curr
  | r_curr, c_curr, (reward, r_next, c_next) :: rest, finalReward, terminalValue =>
      optionModelIntraStepError gamma reward r_next c_next r_curr c_curr +
        gamma * optionModelErrorFold gamma r_next c_next rest finalReward terminalValue

theorem option_model_termination_telescoping
    (gamma finalReward terminalValue r_init c_init : ℝ)
    (transitions : List (ℝ × ℝ × ℝ)) :
    optionModelErrorFold gamma r_init c_init transitions finalReward terminalValue +
        (r_init + c_init) =
      rewardReturn gamma (transitions.map (fun t => t.1) ++ [finalReward]) +
        gamma ^ (transitions.length + 1) * terminalValue := by
  induction transitions generalizing r_init c_init with
  | nil =>
      simp only [optionModelErrorFold, optionModelTerminalStepError, List.map_nil,
        List.nil_append, rewardReturn, List.length_nil, zero_add, pow_one]
      ring
  | cons head tail ih =>
      rcases head with ⟨reward, r_next, c_next⟩
      simp only [optionModelErrorFold, optionModelIntraStepError, List.map_cons,
        List.cons_append, rewardReturn, List.length_cons, pow_succ]
      have h_step := ih r_next c_next
      linear_combination gamma * h_step

theorem stomp_planning_backup_contraction
    (r gamma v₁ v₂ : ℝ) (h_gamma : 0 ≤ gamma) :
    |(r + gamma * v₁) - (r + gamma * v₂)| = gamma * |v₁ - v₂| := by
  have h_diff : (r + gamma * v₁) - (r + gamma * v₂) = gamma * (v₁ - v₂) := by ring
  rw [h_diff, abs_mul, abs_of_nonneg h_gamma]

theorem planning_weight_convex_step_bounded
    (w b alpha H : ℝ)
    (hw0 : -H ≤ w) (hwH : w ≤ H)
    (hb0 : -H ≤ b) (hbH : b ≤ H)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    -H ≤ w + alpha * (b - w) ∧ w + alpha * (b - w) ≤ H := by
  have h_eq : w + alpha * (b - w) = (1 - alpha) * w + alpha * b := by ring
  constructor
  · rw [h_eq]
    have h1 : (1 - alpha) * (-H) ≤ (1 - alpha) * w := mul_le_mul_of_nonneg_left hw0 (by linarith)
    have h2 : alpha * (-H) ≤ alpha * b := mul_le_mul_of_nonneg_left hb0 ha0
    have h3 : (1 - alpha) * (-H) + alpha * (-H) = -H := by ring
    linarith
  · rw [h_eq]
    have h1 : (1 - alpha) * w ≤ (1 - alpha) * H := mul_le_mul_of_nonneg_left hwH (by linarith)
    have h2 : alpha * b ≤ alpha * H := mul_le_mul_of_nonneg_left hbH ha0
    have h3 : (1 - alpha) * H + alpha * H = H := by ring
    linarith

namespace Refresh

def replaceOwner {A : Type*} (old replacement : A) : A × A := (replacement, old)

theorem replacement_exact {A : Type*} (old replacement : A) :
    (replaceOwner old replacement).1 = replacement := rfl

theorem closing_owner_exact {A : Type*} (old replacement : A) :
    (replaceOwner old replacement).2 = old := rfl

def continuationPair {A V : Type*} (draw : A × V) : V × A := (draw.2, draw.1)

theorem continuation_exact {A V : Type*} (draw : A × V) :
    continuationPair draw = (draw.2, draw.1) := rfl

def boundaryCredit (changed : Bool) (trace reward bootstrap oldValue : ℝ) : ℝ :=
  (if changed then 0 else trace) * (reward + bootstrap - oldValue)

theorem replaced_credit_zero (trace reward bootstrap oldValue : ℝ) :
    boundaryCredit true trace reward bootstrap oldValue = 0 := by
  simp [boundaryCredit]

theorem unchanged_credit_exact (trace reward bootstrap oldValue : ℝ) :
    boundaryCredit false trace reward bootstrap oldValue =
      trace * (reward + bootstrap - oldValue) := rfl

end Refresh

end AcornVerif
