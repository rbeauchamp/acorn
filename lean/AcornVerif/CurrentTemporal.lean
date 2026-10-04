/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.TemporalControl
import AcornVerif.CurrentControl
import AcornVerif.Options

/-!
# Contracts of the executing temporal kernel

The machine statements below concern the same Options, Exploration and
TemporalControl definitions compiled by the native consumer. The retained real
shaping theorem has shared stopping and endpoint hypotheses; it does not remove
attainment bonuses or identify independently learned critic gauges. Sources:
Ng, Harada & Russell, ICML (1999), Theorem 1 and Corollary 2; Sutton, Machado
et al., Artificial Intelligence 324 (2023), 104001, arXiv:2202.03466v4,
equations (4)–(5). No useful-abstraction or policy-improvement theorem is inferred.

The `follow_*`, `settle_*` and `step_executing` statements concern the off-policy
learning of options that are not executing: Sutton, Machado et al. (2023), §3, equation (10)
and §4, equation (17); Sutton, Precup & Singh, Artificial Intelligence 112 (1999),
§5, equations (18)–(19); Precup, Sutton & Singh, ICML (2000), §4, Algorithm 2.
They state what the executed update writes, not that it converges.
-/
namespace AcornVerif.CurrentTemporal
open Acorn Acorn.Features Acorn.Handcrafted
open CurrentFeatureConsumers CurrentLearner

variable {mode : Bool} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}

/-- Terminal reward coordinates are bit-exact over the complete Boolean reward,
stopping and potential domain. This small closed-domain exhaustion checks the
executing binary32 operations, independently of the ideal-real shaping identity.
Ng, Harada & Russell, ICML (1999), Theorem 1; Sutton, Machado et al.,
Artificial Intelligence 324 (2023), equations (4)–(5). -/
theorem terminal_coordinate_exact (reward stopping previous : Potential) :
    ((Acorn.Features.terminalCumulant reward.value stopping.value previous).add
      previous.value).bits =
      (reward.value.add stopping.value).bits := by
  cases reward <;> cases stopping <;> cases previous <;> decide

/-- The continuing target is exactly the executed machine expression, with
the hierarchy's old gain and no intervening projection of the raw cumulant. -/
theorem continuing_target (reward : Binary32) (gain : RewardRate) (next previous : Potential) :
    Features.shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next previous =
      ((criterion.center reward 1 gain).add (criterion.rule.gamma.mul next.value)).sub
        previous.value := rfl

/-- Learned terminal credit retains the complete attained objective, even on
the goal-ending branch. Machine additions keep their order; an attained feature
adds its held bonus and an unattained feature leaves the estimate word unchanged. -/
theorem learned_terminal_target (assignment : Assignment config) (estimate reward : Binary32)
    (next previous : Potential) :
    Features.terminalCumulant reward ((Interest.learned assignment).stoppingValue estimate next)
      previous =
      (reward.add (if next then estimate.add assignment.bonus else estimate)).sub
        previous.value := rfl

/-- Declared potentials cannot replace the learned assignment's actual slot membership. -/
theorem learned_potential (assignment : Assignment config) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) :
    (Interest.learned assignment).potential features declared = some (assignment.potential
      features) := rfl

/-- A mismatched declared source is refused before constructing a replacement transition. -/
theorem declared_refusal (origin : Departure) (tag : Fin Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (different : origin ≠
      declared.origin) :
    (Interest.declared (config := config) origin tag).potential features declared = none := by
  simp [Interest.potential, different]

/-- The actual continuation token admits exactly one age increment and retains
its frozen mode/coordinate, independent of every reward or model-operation word. -/
theorem option_step_clock (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let result := skill.stepTemporal models activation next reward gain rng
    result.2.1.age.val = activation.age.val + 1 ∧
    result.2.1.learning = activation.learning ∧ result.2.1.previous = next.potential := by
  dsimp only
  rw [(skill.stepTemporal_policy models activation next reward gain rng).2]
  exact ⟨skill.step_age activation next reward gain rng, rfl, rfl⟩

/-- Terminal learning clears all actual policy trajectory registers in all rows. -/
theorem terminal_clears (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate)
    (learning : ending.activation.learning = true) (action : Action primitiveCount.word.toNat) :
    (((skill.endTemporal models value features ending reward terminal gain).policy.learners.get
      action).state.transient) =
      TransientState.zero dimension := by
  simp only [Skill.endTemporal, Skill.terminateOption, learning, ↓reduceIte]
  exact CurrentControl.terminal_clears _ _ action

/-- Frozen begin retains every policy and model register, not just its observations. -/
theorem frozen_begin (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential false rate).1 = skill := rfl

/-- Frozen terminal consumption performs no policy or model write. -/
theorem frozen_terminal (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate)
    (frozen : ending.activation.learning = false) :
    skill.endTemporal models value features ending reward terminal gain = skill := by
  simp [Skill.endTemporal, Skill.terminateOption, frozen]

/-- All returned option policies retain the same managed admission and legal
knowledge, including arbitrary raw reward and transient words. -/
theorem option_step_legal (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256)
    (action : Action primitiveCount.word.toNat) (index : FeatIdx dimension) :
    let learner := (skill.stepTemporal models activation next reward gain
      rng).1.policy.learners.get action
    criterion.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    ScheduleInv learner.state learner.phase ∧ learner.state.eligibleCount ≤ dimension.capacity := by
  exact ⟨weight_legal _, Bounded32.legal _, managed_schedule _, managed_capacity _⟩

/-- Exclusive phase storage bounds both temporal occupancies on all admission/write paths. -/
theorem stored_clocks (state : TemporalControl profile config criterion dimension) :
    match state.runtime.references.phase with
    | .idle => True
    | .exploring run => run.remaining.val + 1 ≤ explorationCap
    | .option _ activation => activation.age.val ≤ Acorn.FeatureConstants.optionMaxDuration := by
  split
  · trivial
  · rename_i run _
    exact run.remaining.isLt
  · rename_i slot activation _
    have := activation.age.isLt
    omega

/-- Every stored option carries the immutable profile's mutation mode; public
construction and phase replacement cannot admit a learning activation in frozen mode. -/
theorem stored_mode (state : TemporalControl profile config criterion dimension) :
    match state.runtime.references.phase with
    | .option _ activation => activation.learning = (profile.mode != .frozen)
    | .idle | .exploring _ => True := by
  split <;> trivial

/-- The same gain clock is observed only after the one common completion boundary. -/
theorem finish_gain (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision) :
    (state.finish features obs reward decision).average =
      criterion.observe state.average state.runtime.references.pendingAction (profile.mode !=
        .frozen) reward := by
  by_cases frozen : profile.mode = .frozen
  · simp [TemporalControl.finish_eq, TemporalControl.predictionView,
      PredictionControl.advanceWith, frozen, PrimitiveControl.finish,
      TemporalControl.recordEpisodes]
  · have clock := (state.recordEpisodes decision).predictionView.control.credit_preserves_clock
      features decision.action decision.own reward
    simp only [TemporalControl.finish_eq, PredictionControl.advanceWith, beq_iff_eq,
      frozen, ↓reduceIte, PrimitiveControl.finish]
    rw [clock.1, clock.2]
    have hb : (profile.mode == .frozen) = false :=
      Bool.eq_false_iff.mpr (fun h => frozen (beq_iff_eq.mp h))
    simp [TemporalControl.predictionView, TemporalControl.recordEpisodes, bne, hb]

/-- A detached ending owner cannot overwrite any current table learner. Pure
terminal arithmetic on a discarded owner has no retained effect; native dead-code
elimination of that unused result preserves this exact state relation. -/
theorem detached_terminal (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing config criterion dimension demonLayout
      (EndingPayload (profile.mode != .frozen)))
    (owner : Skill config criterion dimension demonLayout)
    (detached : closing.oldOwner = some owner)
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1 = state := by
  simp [TemporalControl.closeOption_eq, detached]

/-- Every returned observation action is legal under either explicit planning selection. -/
theorem step_admitted (state : TemporalControl profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32) (goal :
      Bool)
    (result : TemporalControl profile config criterion dimension × TemporalDecision)
    (_executed : state.step planning features obs reward goal = some result) :
    result.2.action.val < Acorn.FeatureConstants.primitiveCount := result.2.action.isLt

/-- One admitted local input frame; caller-owned encoding correspondence remains explicit. -/
abbrev Frame (dimension : Dimension) := SwiftTd.ActiveSet dimension × Host.Observation × Binary32
    × Bool

/-- Fold the actual local transition over a finite prefix, stopping at the first refusal.
The list is a proof argument, not a retained replay buffer in the agent. -/
def runPrefix (planning : PlanningSelection)
    (state : TemporalControl profile config criterion dimension) : List (Frame dimension) →
    Option (TemporalControl profile config criterion dimension)
  | [] => some state
  | frame :: rest => do
    let result ← state.step planning frame.1 frame.2.1 frame.2.2.1 frame.2.2.2
    runPrefix planning result.1 rest

/-- Every admitted finite prefix retains the actual primary controller's managed
schedule and storage bound. -/
theorem finite_prefix_schedule (planning : PlanningSelection)
    (state result : TemporalControl profile config criterion dimension) (frames : List (Frame
      dimension))
    (_executed : runPrefix planning state frames = some result) (action : Action
      primitiveCount.word.toNat) :
    let learner := result.runtime.lifecycle.consumers.control.learners.get action
    ScheduleInv learner.state learner.phase ∧ learner.state.eligibleCount ≤ dimension.capacity :=
  ⟨managed_schedule _, managed_capacity _⟩

/-- A served primitive step preempts all hierarchy choices, including goal feedback,
for every incoming RNG state and all model/planning implementations. -/
theorem served_preempts (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary config criterion dimension demonLayout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (run : ExploratoryRun primitiveCount)
    (phase : state.runtime.references.phase = .exploring run)
    (remaining : 0 < run.remaining.val)
    (result : TemporalControl profile config criterion dimension × TemporalDecision)
    (selected : state.selectWithOperations models plan features declared reward goal =
      some result) :
    result.2.action = run.action ∧ result.2.source = .explorationContinuation ∧
    result.1.runtime.references.rng = state.runtime.references.rng := by
  have prepared :
      (state.prepareSelection models features reward).runtime.references.phase =
        state.runtime.references.phase ∧
      (state.prepareSelection models features reward).runtime.references.rng =
        state.runtime.references.rng := by
    by_cases hf : profile.mode = .frozen <;> cases hh : profile.usesHierarchy <;>
      simp [TemporalControl.prepareSelection, TemporalControl.withGap, hh, hf, bne]
  have served : ∃ output,
      (state.prepareSelection models features reward).serve features = some output := by
    simp [TemporalControl.serve, prepared.1, phase, ExploratoryRun.serve, remaining]
  obtain ⟨output, served⟩ := served
  have selectedOutput : state.selectWithOperations models plan features declared reward goal =
      some output := by
    simp [TemporalControl.selectWithOperations, served]
  have same := Option.some.inj (selectedOutput.symm.trans selected)
  subst result
  simp only [TemporalControl.serve, prepared.1, phase] at served
  simp only [ExploratoryRun.serve, remaining, ↓reduceDIte] at served
  rcases Bool.eq_false_or_eq_true (profile.mode != .frozen) with hf | hf <;>
    cases hh : profile.usesHierarchy <;>
    simp only [TemporalControl.skipMeta, TemporalControl.withGap, TemporalControl.withPhase,
      TemporalControl.withoutPlanning, hh, hf, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte] at served <;>
    cases served <;> exact ⟨rfl, rfl, prepared.2⟩

/-- Repeated service is a proof-level fold of the actual one-step operation. -/
def serveSteps (run : ExploratoryRun primitiveCount) : Nat → Option (ExploratoryRun primitiveCount)
  | 0 => some run
  | n + 1 => do
    let served ← run.serve
    serveSteps served.2 n

/-- Any successful service prefix consumes exactly its length from the clock;
therefore a run can serve no more than its stored remaining actions. -/
theorem service_prefix_exact (run finalRun : ExploratoryRun primitiveCount) (count : Nat)
    (served : serveSteps run count = some finalRun) :
    finalRun.action = run.action ∧ finalRun.remaining.val + count = run.remaining.val := by
  induction count generalizing run with
  | zero =>
    simp only [serveSteps, Option.some.injEq] at served
    subst finalRun
    exact ⟨rfl, by omega⟩
  | succ count ih =>
    cases step : run.serve with
    | none => simp [serveSteps, step] at served
    | some result =>
      have one := run.serve_exact result.2 result.1 step
      have rest := ih result.2 (by simpa [serveSteps, step] using served)
      exact ⟨rest.1.trans one.2.1, by omega⟩

section AttainedStopping

open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentPower AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder
  AcornVerif.CurrentPrediction

/-! ## Attained stopping value

Standard rounding returns a natural multiple of its target unit within half that
unit. A representable value on one side of the exact result therefore remains on
that side of the rounded result. Adding a nonnegative word never decreases a
finite binary32 estimate on the strict finite domain, so the executed attained
stopping value is at least its estimate. These theorems unfold the pinned
standard model; native arithmetic remains the declared trust boundary. -/

/-- Standard rounding returns a signed natural multiple of the input's target unit. -/
theorem model_round_grid (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int) :
    ∃ rounded : Nat, unpackedValue (round spec sign mantissa exponent) =
      signCoefficient sign * rounded *
        (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) := by
  by_cases hz : mantissa = 0
  · refine ⟨0, ?_⟩
    rw [hz, model_round_zero]
    simp [unpackedValue]
  · let target := spec.targetExponent (totalExponent mantissa exponent)
    let shift := (exponent-target).toNat
    have hp : 0 < mantissa := by omega
    have htotal : totalExponent (mantissa*2^shift) (exponent-shift) =
        totalExponent mantissa exponent := by
      simp only [totalExponent, model_log2_scaled_positive mantissa shift hp]
      omega
    have hout : exponent-shift+(target-(exponent-shift)).toNat = target := by omega
    have value := model_round_exact_value spec sign (mantissa*2^shift) (exponent-shift)
    dsimp only at value
    rw [htotal, hout] at value
    change ∃ rounded : Nat, unpackedValue (roundWithAccuracy spec sign (mantissa <<< shift)
      (exponent - shift) .exact) = signCoefficient sign * rounded * (2:ℚ)^target
    rw [Nat.shiftLeft_eq]
    exact ⟨_, value⟩

/-- A sign coefficient common to both sides leaves an absolute error unchanged. -/
theorem model_sign_error (sign : Sign) (x p y q r : ℚ)
    (bound : |signCoefficient sign * x * p - signCoefficient sign * y * q| ≤ r) :
    |x * p - y * q| ≤ r := by
  cases sign with
  | positive => simpa only [signCoefficient, one_mul] using bound
  | negative =>
    have flip : signCoefficient .negative * x * p - signCoefficient .negative * y * q =
        -(x * p - y * q) := by
      simp only [signCoefficient]
      ring
    rw [flip, abs_neg] at bound
    exact bound

/-- A representable magnitude at or below a positive exact dyadic stays at or below
its nearest-even rounding. -/
theorem model_round_core_lower (spec : Format) (mantissa k rounded : Nat) (exponent y : Int)
    (positive : 0 < mantissa) (bound : k < 2 ^ spec.mantissaBits)
    (floor : spec.minExponent ≤ y)
    (error : |(rounded : ℚ) * (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) -
      mantissa * (2 : ℚ) ^ exponent| ≤
        (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) / 2)
    (below : (k : ℚ) * (2 : ℚ) ^ y ≤ mantissa * (2 : ℚ) ^ exponent) :
    (k : ℚ) * (2 : ℚ) ^ y ≤
      rounded * (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) := by
  have window := (model_positive_dyadic_window mantissa exponent positive).1
  have mantissaBits : spec.mantissaBits = 1 + spec.mantissaBitsWithoutImplicit := rfl
  generalize ht : spec.targetExponent (totalExponent mantissa exponent) = t at error ⊢
  have hp : (0 : ℚ) < (2 : ℚ) ^ t := zpow_pos (by norm_num) _
  have grid : ∀ j : Nat, (j : ℚ) * (2 : ℚ) ^ t ≤ mantissa * (2 : ℚ) ^ exponent →
      (j : ℚ) * (2 : ℚ) ^ t ≤ rounded * (2 : ℚ) ^ t := by
    intro j hj
    have hle : j ≤ rounded := by
      by_contra h
      have hlt : (rounded : ℚ) + 1 ≤ j := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_le h)
      have scaled := mul_le_mul_of_nonneg_right hlt (le_of_lt hp)
      have lower := (abs_le.mp error).1
      linarith
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hp)
  by_cases high : t ≤ y
  · have split : (k : ℚ) * (2 : ℚ) ^ y = ((k * 2 ^ (y - t).toNat : Nat) : ℚ) * (2 : ℚ) ^ t := by
      have hy : y = ((y - t).toNat : Int) + t := by omega
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← zpow_natCast,
        ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), ← hy]
    rw [split] at below ⊢
    exact grid _ below
  · have normal : t = totalExponent mantissa exponent - spec.mantissaBits := by
      simp only [Format.targetExponent] at ht
      omega
    have leading : ((2 ^ spec.mantissaBitsWithoutImplicit : Nat) : ℚ) * (2 : ℚ) ^ t =
        (2 : ℚ) ^ (totalExponent mantissa exponent - 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      congr 1
      omega
    have reached := grid (2 ^ spec.mantissaBitsWithoutImplicit) (by rw [leading]; exact window)
    rw [leading] at reached
    have hk : (k : ℚ) + 1 ≤ ((2 ^ spec.mantissaBits : Nat) : ℚ) := by
      exact_mod_cast Nat.lt_iff_add_one_le.mp bound
    have hy : (0 : ℚ) < (2 : ℚ) ^ y := zpow_pos (by norm_num) _
    have top : ((2 ^ spec.mantissaBits : Nat) : ℚ) * (2 : ℚ) ^ y ≤
        (2 : ℚ) ^ (totalExponent mantissa exponent - 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have scaled := mul_le_mul_of_nonneg_right hk (le_of_lt hy)
    linarith

/-- A representable magnitude at or above a positive exact dyadic stays at or above
its nearest-even rounding. -/
theorem model_round_core_upper (spec : Format) (mantissa k rounded : Nat) (exponent y : Int)
    (positive : 0 < mantissa) (bound : k < 2 ^ spec.mantissaBits)
    (floor : spec.minExponent ≤ y)
    (error : |(rounded : ℚ) * (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) -
      mantissa * (2 : ℚ) ^ exponent| ≤
        (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) / 2)
    (above : (mantissa : ℚ) * (2 : ℚ) ^ exponent ≤ k * (2 : ℚ) ^ y) :
    (rounded : ℚ) * (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) ≤
      k * (2 : ℚ) ^ y := by
  have window := (model_positive_dyadic_window mantissa exponent positive).1
  generalize ht : spec.targetExponent (totalExponent mantissa exponent) = t at error ⊢
  have hp : (0 : ℚ) < (2 : ℚ) ^ t := zpow_pos (by norm_num) _
  by_cases high : t ≤ y
  · have split : (k : ℚ) * (2 : ℚ) ^ y = ((k * 2 ^ (y - t).toNat : Nat) : ℚ) * (2 : ℚ) ^ t := by
      have hy : y = ((y - t).toNat : Int) + t := by omega
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← zpow_natCast,
        ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), ← hy]
    rw [split] at above ⊢
    have hle : rounded ≤ k * 2 ^ (y - t).toNat := by
      by_contra h
      have hlt : ((k * 2 ^ (y - t).toNat : Nat) : ℚ) + 1 ≤ rounded := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_le h)
      have scaled := mul_le_mul_of_nonneg_right hlt (le_of_lt hp)
      have upper := (abs_le.mp error).2
      linarith
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hp)
  · exfalso
    have normal : t = totalExponent mantissa exponent - spec.mantissaBits := by
      simp only [Format.targetExponent] at ht
      omega
    have hk : (k : ℚ) + 1 ≤ ((2 ^ spec.mantissaBits : Nat) : ℚ) := by
      exact_mod_cast Nat.lt_iff_add_one_le.mp bound
    have hy : (0 : ℚ) < (2 : ℚ) ^ y := zpow_pos (by norm_num) _
    have top : ((2 ^ spec.mantissaBits : Nat) : ℚ) * (2 : ℚ) ^ y ≤
        (2 : ℚ) ^ (totalExponent mantissa exponent - 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have scaled := mul_le_mul_of_nonneg_right hk (le_of_lt hy)
    linarith

/-- Signed normalization never rounds below a canonical finite value that is at
or below the exact signed dyadic. -/
theorem model_normalize_lower (spec : Format) (mantissa exponent : Int) (zeroSign sign : Sign)
    (lm : Nat) (le : Int) (lp : 0 < lm) (bound : lm < 2 ^ spec.mantissaBits)
    (floor : spec.minExponent ≤ le)
    (below : unpackedValue (.finite sign lm le lp) ≤ (mantissa : ℚ) * (2 : ℚ) ^ exponent) :
    unpackedValue (.finite sign lm le lp) ≤
      unpackedValue (normalize spec mantissa exponent zeroSign) := by
  have hp : (0 : ℚ) < (2 : ℚ) ^ exponent := zpow_pos (by norm_num) _
  have hl : (0 : ℚ) ≤ (lm : ℚ) * (2 : ℚ) ^ le :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _))
  unfold normalize
  split
  · rename_i negative
    have hn : mantissa < 0 := (Int.compare_eq_lt).mp negative
    have hm : (mantissa : ℚ) < 0 := by exact_mod_cast hn
    have magnitude : ((-mantissa).toNat : ℚ) = -(mantissa : ℚ) := by
      have he : ((-mantissa).toNat : Int) = -mantissa := Int.toNat_of_nonneg (by omega)
      exact_mod_cast he
    obtain ⟨rounded, value⟩ := model_round_grid spec .negative (-mantissa).toNat exponent
    have error := model_round_error spec .negative (-mantissa).toNat exponent
    rw [value] at error
    have rounding := model_sign_error _ _ _ _ _ _ error
    rw [value]
    cases sign with
    | positive =>
      exfalso
      have lval : unpackedValue (.finite .positive lm le lp) = (lm : ℚ) * (2 : ℚ) ^ le := by
        simp only [unpackedValue, signCoefficient, one_mul]
      rw [lval] at below
      have negativeValue : (mantissa : ℚ) * (2 : ℚ) ^ exponent < 0 :=
        mul_neg_of_neg_of_pos hm hp
      linarith
    | negative =>
      have lval : unpackedValue (.finite .negative lm le lp) = -((lm : ℚ) * (2 : ℚ) ^ le) := by
        simp only [unpackedValue, signCoefficient]
        ring
      rw [lval] at below ⊢
      have above : ((-mantissa).toNat : ℚ) * (2 : ℚ) ^ exponent ≤ lm * (2 : ℚ) ^ le := by
        rw [magnitude]
        linarith
      have core := model_round_core_upper spec (-mantissa).toNat lm rounded exponent le
        (by omega) bound floor rounding above
      simp only [signCoefficient]
      linarith
  · rename_i zero
    have hn : mantissa = 0 := (Int.compare_eq_eq).mp zero
    subst hn
    change unpackedValue (.finite sign lm le lp) ≤ 0
    simpa using below
  · rename_i positive
    have hn : 0 < mantissa := (Int.compare_eq_gt).mp positive
    have magnitude : (mantissa.toNat : ℚ) = (mantissa : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ mantissa)
    obtain ⟨rounded, value⟩ := model_round_grid spec .positive mantissa.toNat exponent
    have error := model_round_error spec .positive mantissa.toNat exponent
    rw [value] at error
    have rounding := model_sign_error _ _ _ _ _ _ error
    rw [value]
    have roundedNonneg : (0 : ℚ) ≤ signCoefficient .positive * rounded *
        (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa.toNat exponent)) := by
      simp only [signCoefficient, one_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _))
    cases sign with
    | negative =>
      have lval : unpackedValue (.finite .negative lm le lp) = -((lm : ℚ) * (2 : ℚ) ^ le) := by
        simp only [unpackedValue, signCoefficient]
        ring
      rw [lval]
      linarith
    | positive =>
      have lval : unpackedValue (.finite .positive lm le lp) = (lm : ℚ) * (2 : ℚ) ^ le := by
        simp only [unpackedValue, signCoefficient, one_mul]
      rw [lval] at below ⊢
      have core := model_round_core_lower spec mantissa.toNat lm rounded exponent le
        (by omega) bound floor rounding (by rw [magnitude]; exact below)
      simp only [signCoefficient, one_mul]
      exact core

/-- Standard unpacked addition of a nonnegative canonical value never decreases
a canonical finite or zero value. -/
theorem model_add_lower (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (nonnegative : 0 ≤ unpackedValue right) :
    unpackedValue left ≤ unpackedValue (UnpackedFloat.add spec left right) := by
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right with
    | notANumber => contradiction
    | infinity s => contradiction
    | zero s => cases sign <;> cases s <;> exact le_refl (0 : ℚ)
    | finite s m e hp => exact nonnegative
  | finite leftSign lm le lp =>
    obtain ⟨bound, floor, _⟩ := leftNormal
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero rightSign => exact le_refl _
    | finite rightSign rm re rp =>
      let target := min le re
      let lmantissa := (decreaseExponent lm le target).1
      let rmantissa := (decreaseExponent rm re target).1
      let sum := leftSign.apply lmantissa + rightSign.apply rmantissa
      have hl := model_decrease_dyadic_value leftSign lm le target (Int.min_le_left _ _)
      have hr := model_decrease_dyadic_value rightSign rm re target (Int.min_le_right _ _)
      have heq : (sum:ℚ)*(2:ℚ)^target =
          unpackedValue (.finite leftSign lm le lp)+unpackedValue (.finite rightSign rm re rp) := by
        change ((leftSign.apply lmantissa + rightSign.apply rmantissa : Int):ℚ)*(2:ℚ)^target = _
        rw [Int.cast_add, add_mul, hl, hr]
        rfl
      simp only [UnpackedFloat.add]
      change _ ≤ unpackedValue (normalize spec sum target .positive)
      exact model_normalize_lower spec sum target .positive leftSign lm le lp bound floor
        (by rw [heq]; linarith)

/-- The executing binary32 addition is the standard unpacked addition throughout the
strict finite domain used by the prediction cap. -/
theorem binary32_add_decoded (left right : Binary32)
    (leftFinite : left.Finite) (rightFinite : right.Finite) (limit : Int) (range : limit ≤ 33)
    (bound : |numerical32 left + numerical32 right| < (2 : ℚ) ^ limit) :
    decoded32 (left.add right) =
      UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right) := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr leftFinite)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr rightFinite)).1
  have operation := model_add_dyadic_local_strict Format.binary32 (decoded32 left)
    (decoded32 right) ln rn limit bound
  have error : |unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 left)
      (decoded32 right))-(numerical32 left+numerical32 right)| ≤
        (2:ℚ)^(max (limit-24) (-149))/2 := operation.2
  have radiusBound : (2:ℚ)^(max (limit-24) (-149))/2 ≤ 256 := by
    have power := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2)
      (show max (limit-24) (-149) ≤ 9 by omega)
    norm_num at power
    linarith only [power]
  have sumBound : |numerical32 left+numerical32 right| ≤ 8589934592 := by
    have power := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2) range
    norm_num at power
    exact le_trans (le_of_lt bound) power
  have fits : ModelFits Format.binary32 (UnpackedFloat.add Format.binary32
      (decoded32 left) (decoded32 right)) := by
    apply model_fits_of_value_bound Format.binary32 _
      (model_normalized_finite _ _ operation.1) 34 (by decide)
    have triangle := abs_add_le
      (unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right))-
        (numerical32 left+numerical32 right)) (numerical32 left+numerical32 right)
    rw [sub_add_cancel] at triangle
    norm_num
    linarith only [triangle,error,radiusBound,sumBound]
  exact model_add32_decoded left right leftFinite rightFinite operation.1 fits

/-- Adding a nonnegative finite word never decreases a finite binary32 word whose
exact sum lies strictly inside the prediction cap's domain. -/
theorem binary32_add_nondecreasing (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (nonnegative : 0 ≤ numerical32 right)
    (bound : |numerical32 left + numerical32 right| < (2 : ℚ) ^ (33 : Int)) :
    (left.add right).Finite ∧ left.key ≤ (left.add right).key := by
  have finite := (binary32_add_finite_strict_error left right leftFinite rightFinite 33
    le_rfl bound).1
  have decoded := binary32_add_decoded left right leftFinite rightFinite 33 le_rfl bound
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr leftFinite)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr rightFinite)).1
  refine ⟨finite, (numerical32_order left (left.add right) leftFinite finite).mp ?_⟩
  change unpackedValue (decoded32 left) ≤ unpackedValue (decoded32 (left.add right))
  rw [decoded]
  exact model_add_lower Format.binary32 _ _ ln rn nonnegative

/-- Every held bonus word is finite, nonnegative and inside the Demon-0 horizon bound. -/
theorem assignment_bonus_numerical (assignment : Assignment config) :
    assignment.bonus.Finite ∧ 0 ≤ numerical32 assignment.bonus ∧
      numerical32 assignment.bonus ≤ 101 := by
  have zeroValue : numerical32 Binary32.zero = 0 := by decide
  have zeroFinite : Binary32.zero.Finite := by decide
  cases assignment with
  | neutral =>
    change Binary32.zero.Finite ∧ 0 ≤ numerical32 Binary32.zero ∧
      numerical32 Binary32.zero ≤ 101
    rw [zeroValue]
    exact ⟨zeroFinite, le_refl 0, by norm_num⟩
  | selected unit bonus =>
    change bonus.value.Finite ∧ 0 ≤ numerical32 bonus.value ∧ numerical32 bonus.value ≤ 101
    have legal := bonus.weight.legal
    let upper : Binary32 := ⟨0x42ca0000⟩
    have upperFinite : upper.Finite := by decide
    have upperValue : numerical32 upper = 101 := by
      dsimp only [upper]
      change (1:ℚ)*13238272*(2:ℚ)^(-17:Int) = _
      norm_num
    have zeroKey : Binary32.zero.key = 0 := by decide
    have hi : Discount.g99.predictionRange.upper.key ≤ upper.key := by decide
    have lowerProof := (numerical32_order Binary32.zero bonus.value zeroFinite legal.1).mpr
      (by rw [zeroKey]; exact Int.le_of_lt bonus.positive)
    have upperProof := (numerical32_order bonus.value upper legal.1 upperFinite).mpr
      (le_trans legal.2.2 hi)
    rw [zeroValue] at lowerProof
    rw [upperValue] at upperProof
    exact ⟨legal.1, lowerProof, upperProof⟩

/-- T2: attaining the assigned feature never lowers the executed stopping value below
its estimate, for every interest and every finite estimate within the prediction cap.
Together with `Bonus.finite_positive`, every selected bonus is positive and finite. -/
theorem attained_stopping (interest : Interest config) (estimate : Binary32)
    (finite : estimate.Finite) (bound : |numerical32 estimate| ≤ 4294967296) :
    (interest.stoppingValue estimate true).Finite ∧
      estimate.key ≤ (interest.stoppingValue estimate true).key := by
  cases interest with
  | declared origin tag => exact ⟨finite, le_refl _⟩
  | learned assignment =>
    have held := assignment_bonus_numerical assignment
    change (estimate.add assignment.bonus).Finite ∧
      estimate.key ≤ (estimate.add assignment.bonus).key
    apply binary32_add_nondecreasing estimate assignment.bonus finite held.1 held.2.1
    have triangle := abs_add_le (numerical32 estimate) (numerical32 assignment.bonus)
    have power : (2:ℚ)^(33:Int) = 8589934592 := by norm_num
    rw [abs_of_nonneg held.2.1] at triangle
    rw [power]
    linarith only [triangle, bound, held.2.2]

end AttainedStopping

/-- Reduction, dispatch level: the executing option keeps exactly the policy and
model its own on-policy update produced. Off-policy learning writes only the
other slots, for every state, frame and model implementation. -/
theorem follow_executing (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision)
    (slot : Fin Acorn.FeatureConstants.skillCount) (executing : state.activeSlot = some slot) :
    let next := state.followOptions models features declared reward goal decision
    next.runtime.lifecycle.consumers.skills[slot.val].policy =
        state.runtime.lifecycle.consumers.skills[slot.val].policy ∧
      next.runtime.lifecycle.consumers.skills[slot.val].model =
        state.runtime.lifecycle.consumers.skills[slot.val].model := by
  dsimp only
  rw [TemporalControl.followOptions_eq]
  split
  · simp [followSlot, executing]
  · exact ⟨rfl, rfl⟩

/-- Reduction, step level: after the complete local step the executing option's
policy and model are those its selection left, so every existing contract of the
on-policy option update describes them unchanged. -/
theorem step_executing (state : TemporalControl profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (obs : Host.Observation) (reward : Binary32) (goal : Bool)
    (result : TemporalControl profile config criterion dimension × TemporalDecision)
    (executed : state.step planning features obs reward goal = some result) :
    ∃ selected, state.select planning features (spatialPotentials obs) reward goal =
        some (selected, result.2) ∧
      ∀ slot : Fin Acorn.FeatureConstants.skillCount, selected.activeSlot = some slot →
        result.1.runtime.lifecycle.consumers.skills[slot.val].policy =
            selected.runtime.lifecycle.consumers.skills[slot.val].policy ∧
          result.1.runtime.lifecycle.consumers.skills[slot.val].model =
            selected.runtime.lifecycle.consumers.skills[slot.val].model := by
  unfold TemporalControl.step at executed
  cases selection : state.select planning features (spatialPotentials obs) reward goal with
  | none => simp [selection] at executed
  | some chosen =>
    simp only [selection, bind, Option.bind, pure, Option.some.injEq] at executed
    cases executed
    refine ⟨chosen.1, rfl, fun slot executing => ?_⟩
    have followed := follow_executing chosen.1 (modelOperations criterion dimension) features
      (spatialPotentials obs) reward goal chosen.2 slot executing
    have finished := TemporalControl.finish_skill
      (chosen.1.followOptions (modelOperations criterion dimension) features
        (spatialPotentials obs) reward goal chosen.2) features obs reward chosen.2 slot
    simp only at followed
    constructor
    · exact (congrArg (·.policy) finished).trans (by split <;> exact followed.1)
    · exact (congrArg (·.model) finished).trans (by split <;> exact followed.2)

/-- Work bound, inactive profiles: frozen and primitive-only execution performs no
off-policy option work at all. -/
theorem follow_inactive (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision)
    (inactive : (profile.usesHierarchy && profile.mode != .frozen) = false) :
    state.followOptions models features declared reward goal decision = state := by
  rw [TemporalControl.followOptions_eq]
  split
  · rename_i active
    rw [inactive] at active
    contradiction
  · rfl

/-- Off-policy option learning writes the skill table only. It consumes no random
draw and leaves occupancy, the meta span, the gain, and the primitive, meta and
prediction learners exactly as selection left them. -/
theorem follow_frame (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision) :
    let next := state.followOptions models features declared reward goal decision
    next.runtime.references = state.runtime.references ∧
      next.runtime.lifecycle.representation = state.runtime.lifecycle.representation ∧
      next.runtime.lifecycle.consumers.control = state.runtime.lifecycle.consumers.control ∧
      next.runtime.lifecycle.consumers.metaController =
        state.runtime.lifecycle.consumers.metaController ∧
      next.runtime.lifecycle.consumers.demons = state.runtime.lifecycle.consumers.demons ∧
      next.average = state.average ∧ next.credit = state.credit := by
  dsimp only
  rw [TemporalControl.followOptions_eq]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Work bound, per learner: after a followed frame every option policy learner
keeps legal knowledge, its managed schedule and an eligibility list within the
feature capacity, for arbitrary raw reward, estimate and transient words. Each
first loop of the next frame therefore visits at most `dimension.capacity` entries. -/
theorem follow_legal (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision)
    (slot : Fin Acorn.FeatureConstants.skillCount) (action : Action primitiveCount.word.toNat)
    (index : FeatIdx dimension) :
    let learner := ((state.followOptions models features declared reward goal
      decision).runtime.lifecycle.consumers.skills[slot.val]).policy.learners.get action
    criterion.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    ScheduleInv learner.state learner.phase ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  exact ⟨weight_legal _, Bounded32.legal _, managed_schedule _, managed_capacity _⟩

/-- A slot is refused, and unlinked, exactly when its declared potential source
is not the one supplied; a learned interest is never refused. -/
theorem follow_refused (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat)
    (reward : Binary32) (gain : RewardRate) (skill : Skill config criterion dimension demonLayout)
    (refused : skill.interest.potential features declared = none) :
    followSlot models value features declared goal estimate rate action behaviour reward gain
      false skill = { skill with following := none } := by
  simp [followSlot, refused]

/-- When a meta decision was drawn at the frame, the stopping estimate reads that
decision's own frozen snapshot, values and rate: no rate read after the meta
learner's update can enter it. -/
theorem stopping_estimate_frozen (state : TemporalControl profile config criterion dimension)
    (decision : TemporalDecision) (drawn : PolicyDecision metaCount)
    (frozen : decision.metaDecision = some drawn) :
    state.stoppingEstimate decision = comparisonValue criterion drawn.snapshot := by
  simp only [TemporalControl.stoppingEstimate, frozen]

/-- The trajectory age advances by exactly one on every continuing frame, never
saturating and whatever the action taken, so the stored age is the number of
actions followed since the trajectory began. -/
theorem follow_age (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).following.map (·.age.val) = some (following.age.val + 1) := by
  have room : following.age.val < Acorn.FeatureConstants.optionMaxDuration := next.room
  cases skill with
  | mk interest policy model stored questions =>
    obtain rfl : stored = some following := linked
    simp only [Skill.followTemporal, continuing]
    simp [ModelAge.advance]
    omega

/-- Duration cap: a stored trajectory that has followed the option's full duration
ends at the next frame, as the executing option does, so policy learning cannot
run past the cap. -/
theorem follow_cap (skill : Skill config criterion dimension discounts) (following : Following)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32)
    (rate : ConsumerRate)
    (full : following.age.val = Acorn.FeatureConstants.optionMaxDuration) :
    skill.decideOption following.activation features potential false estimate rate =
      .ending .duration :=
  skill.cap_ends following.activation features potential estimate rate full

/-- With no live model trajectory, a frame whose behaviour masses differ from the
option's own neither credits nor restarts its model. -/
theorem follow_idle_model (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next)
    (idle : following.live = false) (inconsistent : next.policy.consistent behaviour = false) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).model = skill.model := by
  cases skill with
  | mk interest policy model stored questions =>
    obtain rfl : stored = some following := linked
    simp [Skill.followTemporal, continuing, idle, inconsistent]

/-- Along a live run the model takes exactly the executing option's continuing
credit, at the trajectory's age and the raw reward, whatever the action taken:
Sutton, Machado et al. (2023), §4, equation (17), where the preceding frame's
importance ratio is one. -/
theorem follow_live_model (skill : Skill config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next)
    (live : following.live = true) :
    (skill.followTemporal (modelOperations criterion dimension) value features potential goal
      estimate rate action behaviour reward gain).model =
      skill.model.step features following.age reward := by
  cases skill with
  | mk interest policy model stored questions =>
    obtain rfl : stored = some following := linked
    simp [Skill.followTemporal, continuing, live, modelOperations]

/-- The model trajectory is live after a continuing frame exactly when that
frame's behaviour masses equal the option's own. -/
theorem follow_live (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).following.map (·.live) = some (next.policy.consistent behaviour) := by
  cases skill with
  | mk interest policy model stored questions =>
    obtain rfl : stored = some following := linked
    simp only [Skill.followTemporal, continuing]
    rfl

/-- On every continuing frame the policy takes tree-backup credit for the action
actually taken, with the shaped cumulant the executing option would have read. -/
theorem follow_policy (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).policy =
      skill.policy.backupStep (count := primitiveCount) features next.policy action
        (Features.shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
          following.previous) := by
  cases skill with
  | mk interest policy model stored questions =>
    obtain rfl : stored = some following := linked
    simp only [Skill.followTemporal, continuing]
    rfl

/-- An option that starts executing first credits the transition it was following,
with the tree-backup error a followed frame would have used and the model's step
along a live run; nothing of the stored trajectory is discarded uncredited. -/
theorem settle_continuing (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    let settled := skill.settleFollowing models value features potential goal estimate rate
      reward gain
    settled.policy = skill.policy.stopStep
        (skill.policy.backupError (count := primitiveCount) next.policy
          (Features.shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
            following.previous)) ∧
      settled.model =
        (if following.live then models.step skill.model features following.age reward
          else skill.model) := by
  cases skill with
  | mk interest policy model stored questions =>
    obtain rfl : stored = some following := linked
    simp only [Skill.settleFollowing, continuing, and_self]

/-- Where the stopping decision fires at an invocation start, the settled skill is
exactly the stopped one a followed frame would have produced. -/
theorem settle_ending (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate)
    (following : Following) (linked : skill.following = some following) (reason : OptionEnd)
    (ending : skill.decideOption following.activation features potential goal estimate rate =
      .ending reason) :
    skill.settleFollowing models value features potential goal estimate rate reward gain =
      skill.stopFollowing models value features following potential estimate reward gain := by
  cases skill with
  | mk interest policy model stored questions =>
    obtain rfl : stored = some following := linked
    simp only [Skill.settleFollowing, ending]

/-! ## Off-policy questions

`askQuestions_get` arms a slot's questions at a frame exactly when the option drew the
frame's action or its model trajectory is live after `followOptions`. The theorems below
show what that means for the importance ratio: on every frame that arms an option's
questions, the behaviour's reported mass of every action equals the option's own, so the
ratio of the two is one wherever it is defined, and a served exploratory frame never arms
an option that gives mass to another action. No ratio is formed or bounded beyond that. -/

/-- On a continuing followed frame, a slot's questions are armed only when the masses the
behaviour reported equal those of the option's own snapshot at the frame, action by
action. -/
theorem follow_armed_ratio (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next)
    (armed : (skill.followTemporal models value features potential goal estimate rate action
      behaviour reward gain).following.any (·.live) = true)
    (other : Action primitiveCount.word.toNat) :
    next.policy.probabilities.get other = behaviour.get other := by
  have live := follow_live skill models value features potential goal estimate rate action
    behaviour reward gain following linked next continuing
  have consistent : next.policy.consistent behaviour = true := by
    revert armed live
    cases (skill.followTemporal models value features potential goal estimate rate action
      behaviour reward gain).following with
    | none => simp
    | some stored =>
      intro armed live
      simp only [Option.any_some] at armed
      simp only [Option.map_some, Option.some.injEq] at live
      rw [← live]
      exact armed
  exact PolicySnapshot.consistent_mass _ _ other consistent

/-- A frame that starts a followed trajectory, after a stop or with no stored trajectory,
arms the questions only when the behaviour's masses equal those of the option's snapshot
at the frame, action by action. -/
theorem start_armed_ratio (skill : Skill config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (rate : ConsumerRate) (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat)
    (armed : (skill.startFollowing models features potential rate action
      behaviour).following.any (·.live) = true)
    (other : Action primitiveCount.word.toNat) :
    (skill.policy.snapshot (count := primitiveCount) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount))).probabilities.get
        other = behaviour.get other := by
  have consistent : (skill.policy.snapshot (count := primitiveCount) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount))).consistent
        behaviour = true := by
    simpa [Skill.startFollowing] using armed
  exact PolicySnapshot.consistent_mass _ _ other consistent

/-- A served frame reports a point mass on its committed action, so it never arms the
questions of an option whose snapshot gives a nonzero mass word to any other action. -/
theorem served_unarmed (snapshot : PolicySnapshot primitiveCount)
    (action other : Action primitiveCount.word.toNat) (different : other ≠ action)
    (positive : snapshot.probabilities.get other ≠ .zero) :
    snapshot.consistent (servedProbabilities action) = false := by
  by_contra consistent
  have equal := PolicySnapshot.consistent_mass snapshot _ other
    (by simpa using consistent)
  simp only [served_probability, different, ↓reduceIte] at equal
  exact positive equal

end AcornVerif.CurrentTemporal
