/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import AcornVerif.ModelConstants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Option lifecycle and shaping equations

These equations model option lifecycle and reward shaping over ℝ.
An active option learns the host reward plus potential shaping. A terminated
activation bootstraps the stopping value `z` — the reward-respecting subtask
rule `δ = c + βz + γ(1−β)v′ − v` at `β = 1` — so the terminal equation
uses `reward + stopping - previousPotential` with no new action trace.

**Prior-art pin (PAR-5 / G31).** Sutton, Machado, Holland, David Szepesvari, Timbers,
Tanner & White, *Reward-Respecting Subtasks for Model-Based Reinforcement
Learning*, Artificial Intelligence 324 (2023); arXiv:2202.03466v4 opened.
Printed p. 9 eq. (5): `δ(c,z,v,v′,β) ≐ c + βz + γ(1−β)v′ − v`. At `β = 1`
this is `c + z − v`. SPS99 (AI 112, 1999) printed p. 190 eqs. (8)–(9) and
p. 195 SMDP Q-learning bootstrap `γ^k V`; eq. (14) printed p. 198 is the
interruption improvement inequality, not this terminal update.
**Status:** this file is the proof owner of the **correction of SPS99's
discounted backup toward subtask eq. (5) at β = 1**. Not a silent
improvement of SPS99. The stopping value carries no extra discount, matching
the source's `γ^{K−1} z(S_K)` return, which weights `z` with the final
cumulant.

The main theorem is not a witness trajectory: it quantifies over every finite
list of rewards and potentials. It establishes that the shaped return plus the
current potential is exactly the unshaped task-reward return. That identity is
what permits the interruption rule to compare `Q_shaped + Φ(current)` with the
unshaped meta-controller value. `controller_discounts_match` separately binds
the two sides to the rational controller constants in `AcornVerif.ModelConstants`.
-/

namespace AcornVerif

/-- The non-terminal cumulant implemented by `options::shaped_cumulant`. -/
def shapedCumulant (reward gamma nextPotential previousPotential : ℝ) : ℝ :=
  reward + gamma * nextPotential - previousPotential

/-- The terminal cumulant implemented by `options::terminal_cumulant`: the
final reward, the undiscounted stopping-value bootstrap, and the shaping
close-out. Subtask eq. (5) at `β = 1`, printed p. 9 of arXiv:2202.03466v4. -/
def terminalCumulant (reward stopping previousPotential : ℝ) : ℝ :=
  reward + stopping - previousPotential

/-- Discounted return of the host reward stream. -/
def rewardReturn (gamma : ℝ) : List ℝ → ℝ
  | [] => 0
  | reward :: rest => reward + gamma * rewardReturn gamma rest

/--
Discounted shaped return of a finite activation.

Each pair is a reward and the next state's potential. The empty suffix is the
terminal boundary and contributes `-currentPotential`, exactly the zero-next-
potential terminal equation. Thus the definition covers every finite duration
and every termination reason without selecting a scenario.
-/
def shapedReturn (gamma currentPotential : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => -currentPotential
  | (reward, nextPotential) :: rest =>
      shapedCumulant reward gamma nextPotential currentPotential +
        gamma * shapedReturn gamma nextPotential rest

/-- A terminal update transformed back to task-reward coordinates is exactly
the final reward plus the stopping value — the `c + z` of the subtask rule at
`β = 1`. -/
theorem terminal_correction (reward stopping potential : ℝ) :
    terminalCumulant reward stopping potential + potential = reward + stopping := by
  simp [terminalCumulant]

/--
The shaped fold over one whole learning
activation: the non-terminal transitions each contribute `shapedCumulant`,
and the boundary consumes the final reward through the bootstrapped terminal
cumulant. `finalReward` is threaded so the boundary lands at the same
discount step as the last cumulant, exactly as `terminate` runs after the
final action's transition.
-/
def shapedBootReturn (gamma stopping : ℝ) :
    ℝ → List (ℝ × ℝ) → ℝ → ℝ
  | currentPotential, [], finalReward =>
      terminalCumulant finalReward stopping currentPotential
  | currentPotential, (reward, nextPotential) :: rest, finalReward =>
      shapedCumulant reward gamma nextPotential currentPotential +
        gamma * shapedBootReturn gamma stopping nextPotential rest finalReward

/--
Every finite bootstrapped activation, transformed back by the initial
potential, is exactly the task-reward return of its whole reward sequence
plus the stopping value at the final cumulant's own discount — the source's
`Σ γ^{k−1} c_k + γ^{K−1} z(S_K)` with `K = transitions.length + 1`, for every
duration, reward sequence, potential sequence, and stopping value.
-/
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

/--
Two finite bootstrapped activations that share the host-reward stream
(equal reward projections), the stopping scalar `z`, the discount and the
final reward — and differ only in their potential sequence — have equal
shaped returns plus their own initial potentials. A conditional identity
over finite returns, and no more: there is no MDP, policy, expectation or
action maximisation here, and nothing links the shared `z` to the three
implemented stopping-value cases. This corollary of
`finite_activation_bootstrap_correction` establishes that shared-stopping
return identity; it does not establish common host-optimal policies for
subtasks with different attained-feature bonuses.
-/
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

/-- One non-terminal Bellman step preserves the shaping coordinate transform. -/
theorem nonterminal_bellman_correction
    (reward gamma currentPotential nextPotential futureReward : ℝ) :
    shapedCumulant reward gamma nextPotential currentPotential +
          gamma * (futureReward - nextPotential) + currentPotential =
        reward + gamma * futureReward := by
  simp only [shapedCumulant]
  ring

/--
Every finite option activation differs from its task-reward return by exactly
the negative initial potential, irrespective of duration, rewards, intermediate
potentials, or termination reason.
-/
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

/--
The shipped strict interruption rule is the same inequality expressed in the
unshaped coordinate; adding the current potential cannot change its meaning.
-/
theorem corrected_interruption_iff
    (stopping shapedContinuing currentPotential : ℝ) :
    stopping > shapedContinuing + currentPotential ↔
      stopping - currentPotential > shapedContinuing := by
  constructor <;> intro h <;> linarith

/--
The option and meta-controller discounts in the model constant table
are identical, so the corrected values have the same reward horizon as well as
the same shaping coordinate.
-/
theorem controller_discounts_match :
    ModelConstants.optionGamma = ModelConstants.metaGamma := by
  norm_num [ModelConstants.optionGamma, ModelConstants.metaGamma]

/-- Skip-accumulate state of `Gap` over exact reals: after `n` skipped
primitive steps the pair is `(∑_{i=0}^{n-1} γ^i r i, n)`. Each skip does
`reward += r * γ^steps` then `steps += 1` — the recurrence of
`Gap::accumulate` then `Gap::skip`. -/
def gapAcc (γ : ℝ) (r : ℕ → ℝ) : ℕ → ℝ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
    let p := gapAcc γ r n
    (p.1 + r n * γ ^ p.2, p.2 + 1)

/-- Closing a gap after `k` skipped primitive steps, then taking the acting
step: the recurrence of `Gap::accumulate` then `Gap::close`. -/
def gapRun (γ : ℝ) (r : ℕ → ℝ) (k : ℕ) : ℝ × ℕ :=
  let p := gapAcc γ r k
  (p.1 + r k * γ ^ p.2, p.2 + 1)

/-- **The mathematical identity**: closing a gap of `k` skipped steps yields
exactly the SMDP backup `(∑_{i=0}^{k} γ^i r i, k+1)` — the discounted sum
over the gap and its span, not the undiscounted primitive return
`(∑ r i, k+1)`.

This theorem is over exact `ℝ` and unbounded `ℕ`, and owns the closed
form of the recurrence. Rounded arithmetic, integer-power implementation and
bounded spans require separate execution correspondence. -/
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

/-- The stopping value with STOMP attainment bonus: `z(s) = \hat{V}(s) + g * Φ(s)`
(adapted from Sutton et al., AIJ 324:104001, eq. (4), where the feature attainment bonus
`(w̄_i - w_i) x_i(s)` is instantiated as `g * Φ(s)` added to the meta value estimate
`\hat{V}(s)`). -/
def stompStoppingValue (agentEstimate bonus terminalPotential : ℝ) : ℝ :=
  agentEstimate + bonus * terminalPotential

/--
The bootstrapped activation return under STOMP attainment bonus telescoping:
adding the initial potential `currentPotential` recovers the unshaped host-reward
return plus the discounted terminal stopping value `\hat{V}(S_K) + g * Φ(S_K)`
at `γ^(K-1)` for total activation duration `K = transitions.length + 1`
(Alberta Plan Step 10; PAR-12).
-/
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

/--
Finite-return equality for identical host reward lists, equal duration and one
shared stopping value, after adding each initial potential. This specializes
the telescoping form of Ng, Harada & Russell, ICML 1999, Theorem 1; it does
not equate trajectories with different attainment stopping bonuses or establish
host-optimal policy invariance of the composed learned hierarchy.
-/
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

/--
Block-Exclusivity Invariant (PAR-12): any three assigned subtasks with distinct block
identifiers satisfy pairwise block exclusivity across all three skill slots.
-/
theorem subtask_block_exclusivity
    {β : Type} (b₀ b₁ b₂ : β)
    (h_nodup : [b₀, b₁, b₂].Nodup) :
    b₀ ≠ b₁ ∧ b₀ ≠ b₂ ∧ b₁ ≠ b₂ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at h_nodup
  exact ⟨h_nodup.1.1, h_nodup.1.2, h_nodup.2.1⟩

/--
Equivalence of linear expectation model TD error vector under inner product with fixed
weights to scalar continuation GVF TD error (Wan et al., IJCAI 2019, Theorem 1;
Sutton, Machado et al., Artificial Intelligence 324 (2023) 104001,
STOMP eqs. (5), (15), (17), arXiv:2202.03466v4 pp. 9, 14; PAR-13).
The terminal feature is multiplied by gamma to target eq. (15)'s gamma^K
continuation. The source's eq. (17) passes the unscaled terminal feature to
eq. (5); `option_model_terminal_discount_correction` characterizes the
discrepancy for every input. This fixed-weight identity does not establish
equivalence for a maximum over independently learned action-value functions.
-/
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

/-- The terminal discount required by STOMP's gamma^K model definition
(Sutton, Machado et al., Artificial Intelligence 324 (2023) 104001,
arXiv:2202.03466v4 eq. (15), p. 14) differs from its eq. (17) substitution
into eq. (5) by exactly `(gamma - 1) * beta * terminalFeature`.
The identity characterizes the source discrepancy over the entire domain;
it vanishes for gamma one or a nonterminal transition. -/
theorem option_model_terminal_discount_correction
    (gamma beta terminalFeature next current : ℝ) :
    (gamma * beta * terminalFeature + gamma * (1 - beta) * next - current) -
      (beta * terminalFeature + gamma * (1 - beta) * next - current) =
        (gamma - 1) * beta * terminalFeature := by
  ring

/-- Combined 1-step TD error of the option model at an intra-option transition (STOMP eq. 17). -/
def optionModelIntraStepError (gamma r r_next c_next r_curr c_curr : ℝ) : ℝ :=
  (r + gamma * r_next - r_curr) + (gamma * c_next - c_curr)

/-- Combined 1-step TD error of the option model at a terminal transition (STOMP eq. 5 & 17). -/
def optionModelTerminalStepError (gamma finalReward terminalValue r_curr c_curr : ℝ) : ℝ :=
  (finalReward - r_curr) + (gamma * terminalValue - c_curr)

/-- Folded discounted TD error sum over an option activation trajectory. -/
def optionModelErrorFold (gamma : ℝ) :
    ℝ → ℝ → List (ℝ × ℝ × ℝ) → ℝ → ℝ → ℝ
  | r_curr, c_curr, [], finalReward, terminalValue =>
      optionModelTerminalStepError gamma finalReward terminalValue r_curr c_curr
  | r_curr, c_curr, (reward, r_next, c_next) :: rest, finalReward, terminalValue =>
      optionModelIntraStepError gamma reward r_next c_next r_curr c_curr +
        gamma * optionModelErrorFold gamma r_next c_next rest finalReward terminalValue

/--
Telescoping identity of multi-step option model TD errors
(STOMP eqs. 5, 12, 13; SPS99 eqs. 8, 9; PAR-13).
Over any finite option execution trajectory, the discounted sum of 1-step option model
TD errors collapses exactly to the cumulative discounted host reward plus discounted
terminal state value, minus the initial option model prediction. Intermediate model
predictions cancel out telescopingly.
-/
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

/--
Lipschitz scaling identity of the Bellman planning backup over option models
under fixed models (Sutton, Machado et al., AIJ 324 (2023) 104001, §5 eq. 19;
SPS99 eq. 8; Wan et al. 2019; PAR-14).
For any fixed expected option reward `r` and continuation discount `γ` with `0 ≤ γ`,
the planning backup operator `T(v) = r + γ * v` satisfies the Lipschitz scaling identity
`|T(v₁) - T(v₂)| = γ * |v₁ - v₂|`. Strict contraction additionally needs `γ < 1`.
-/
theorem stomp_planning_backup_contraction
    (r gamma v₁ v₂ : ℝ) (h_gamma : 0 ≤ gamma) :
    |(r + gamma * v₁) - (r + gamma * v₂)| = gamma * |v₁ - v₂| := by
  have h_diff : (r + gamma * v₁) - (r + gamma * v₂) = gamma * (v₁ - v₂) := by ring
  rw [h_diff, abs_mul, abs_of_nonneg h_gamma]

/--
Convex step boundedness for background planning updates (PAR-14).
For any step size `α ∈ [0, 1]`, current weight `w ∈ [-H, H]`, and backed-up option value
target `b ∈ [-H, H]`, the interpolated planning step `w + α * (b - w) = (1 - α) * w + α * b`
remains bounded within `[-H, H]`.
-/
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

/-! ## Coalesced refresh and identity boundaries

These structural contracts model dispatch and replacement ordering. A closing
owner is retained independently of its replacement slot, so the model's terminal
update uses the original objective and next policy draw. Machine request
transitions and bonus-word identity require separate execution correspondence;
these model contracts concern lifecycle semantics.
-/

namespace Refresh

/-- An idle boundary consumes all accumulated requests as one latest-state ranking. -/
def drain (pending idle : Bool) : Bool × Bool :=
  if idle then (false, pending) else (pending, false)

/-- Busy occupancy cannot consume or erase a request. -/
theorem busy_preserves (pending : Bool) : drain pending false = (pending, false) := rfl

/-- At the first free boundary, pending work is completed and cleared together. -/
theorem idle_completes (pending : Bool) : drain pending true = (false, pending) := rfl

/-- Pending work is conserved between the outstanding and completed sides. -/
theorem conservation (pending idle : Bool) :
    ((drain pending idle).1 || (drain pending idle).2) = pending := by
  cases idle <;> cases pending <;> rfl

/-- One refresh obligation cannot be both outstanding and completed. -/
theorem exclusive (pending idle : Bool) :
    ((drain pending idle).1 && (drain pending idle).2) = false := by
  cases idle <;> cases pending <;> rfl

/-- Requests are idempotent accumulation of a need to inspect current weights. -/
def request (pending event : Bool) : Bool := pending || event

/-- Repeated requests coalesce without counters that can overflow. -/
theorem coalesces (pending event : Bool) :
    request (request pending event) event = request pending event := by
  cases pending <;> cases event <;> rfl

/-- Requests alone cannot clear existing work. -/
theorem request_preserves (event : Bool) : request true event = true := rfl

/-- Arbitrarily many busy steps, with arbitrary request arrivals. -/
def busyStream (pending : Bool) : List Bool → Bool
  | [] => pending
  | event :: rest => busyStream (drain (request pending event) false).1 rest

/-- Conservation across the whole busy prefix, not a chosen duration. -/
theorem busy_stream_exact (events : List Bool) (pending : Bool) :
    busyStream pending events = (pending || events.any id) := by
  induction events generalizing pending with
  | nil => cases pending <;> rfl
  | cons event rest ih =>
    rw [busyStream, busy_preserves, ih]
    simp only [request, List.any_cons]
    exact Bool.or_assoc pending event (rest.any id)

/-- The first free boundary consumes every request from an arbitrary busy prefix. -/
theorem first_idle_exact (events : List Bool) (pending : Bool) :
    drain (busyStream pending events) true = (false, pending || events.any id) := by
  rw [busy_stream_exact, idle_completes]

/-- Slot replacement retains a separate old owner until its closing update. -/
def replaceOwner {A : Type*} (old replacement : A) : A × A := (replacement, old)

/-- The new table slot contains exactly the requested identity. -/
theorem replacement_exact {A : Type*} (old replacement : A) :
    (replaceOwner old replacement).1 = replacement := rfl

/-- Terminal credit consumes the original owner independently of replacement. -/
theorem closing_owner_exact {A : Type*} (old replacement : A) :
    (replaceOwner old replacement).2 = old := rfl

/-- A policy draw supplies both terminal continuation and the next action. -/
def continuationPair {A V : Type*} (draw : A × V) : V × A := (draw.2, draw.1)

/-- No intervening redraw can change the terminal bootstrap's sampled action. -/
theorem continuation_exact {A V : Type*} (draw : A × V) :
    continuationPair draw = (draw.2, draw.1) := rfl

/-- First-loop credit under original shared lags, masking replaced action traces.
Javed & Sutton, *Swift-Sarsa: Fast and Robust Linear Control*, arXiv preprint
2507.19539v1 (2025), Algorithm 1 and eq. (4), supplies the shared TD error.
Here bootstrap is an arbitrary scalar, including a caller's SMDP continuation.
This identity describes replacement masking, not the full meta-gradient update. -/
def boundaryCredit (changed : Bool) (trace reward bootstrap oldValue : ℝ) : ℝ :=
  (if changed then 0 else trace) * (reward + bootstrap - oldValue)

/-- Replaced identities receive none of the old trajectory's trace credit. -/
theorem replaced_credit_zero (trace reward bootstrap oldValue : ℝ) :
    boundaryCredit true trace reward bootstrap oldValue = 0 := by
  simp [boundaryCredit]

/-- Unchanged identities retain their original shared-error credit exactly. -/
theorem unchanged_credit_exact (trace reward bootstrap oldValue : ℝ) :
    boundaryCredit false trace reward bootstrap oldValue =
      trace * (reward + bootstrap - oldValue) := rfl

end Refresh

end AcornVerif
