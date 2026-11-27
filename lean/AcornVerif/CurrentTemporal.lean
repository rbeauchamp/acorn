import Acorn.Handcrafted.TemporalControl
import AcornVerif.CurrentControl
import AcornVerif.Options

namespace AcornVerif.CurrentTemporal
open Acorn Acorn.Features Acorn.Handcrafted
open CurrentFeatureConsumers CurrentLearner

variable {mode : Bool} {interface : Interface} {actions : Word.Count} {profile : FeatureProfile}
    {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}

theorem terminal_coordinate_exact (reward stopping previous : Potential) :
    ((Acorn.Features.terminalCumulant reward.value stopping.value previous).add
      previous.value).bits =
      (reward.value.add stopping.value).bits := by
  cases reward <;> cases stopping <;> cases previous <;> decide

theorem continuing_target (reward : Binary32) (gain : RewardRate) (next previous : Potential) :
    Features.shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next previous =
      ((criterion.center reward 1 gain).add (criterion.rule.gamma.mul next.value)).sub
        previous.value := rfl

theorem learned_terminal_target (assignment : Assignment config) (estimate reward : Binary32)
    (next previous : Potential) :
    Features.terminalCumulant reward ((Interest.learned assignment).stoppingValue estimate next)
      previous =
      (reward.add (if next then estimate.add assignment.bonus else estimate)).sub
        previous.value := rfl

theorem learned_potential (assignment : Assignment config) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) :
    (Interest.learned assignment).potential features declared = some (assignment.potential
      features) := rfl

theorem declared_refusal (origin : Departure) (tag : Fin Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (different : origin ≠
      declared.origin) :
    (Interest.declared (config := config) origin tag).potential features declared = none := by
  simp [Interest.potential_def, different]

theorem option_step_clock (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let result := skill.stepTemporal models activation next reward gain rng
    result.2.1.age.val = activation.age.val + 1 ∧
    result.2.1.learning = activation.learning ∧ result.2.1.previous = next.potential := by
  dsimp only
  rw [(skill.stepTemporal_policy models activation next reward gain rng).2]
  exact ⟨skill.step_age activation next reward gain rng, rfl, rfl⟩

theorem terminal_clears (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate)
    (learning : ending.activation.learning = true) (action : Action actions.word.toNat) :
    (((skill.endTemporal models value features ending reward terminal gain).policy.learners.get
      action).state.transient) =
      TransientState.zero dimension := by
  simp only [Skill.endTemporal_def, Skill.terminateOption_def, learning, ↓reduceIte]
  exact CurrentControl.terminal_clears _ _ action

theorem frozen_begin (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential false rate).1 = skill := rfl

theorem frozen_terminal (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate)
    (frozen : ending.activation.learning = false) :
    skill.endTemporal models value features ending reward terminal gain = skill := by
  simp [Skill.endTemporal_def, Skill.terminateOption_def, frozen]

theorem option_step_legal (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256)
    (action : Action actions.word.toNat) (index : FeatIdx dimension) :
    let learner := (skill.stepTemporal models activation next reward gain
      rng).1.policy.learners.get action
    criterion.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    ScheduleInv learner.state learner.phase ∧ learner.state.eligibleCount ≤ dimension.capacity := by
  exact ⟨weight_legal _, Bounded32.legal _, managed_schedule _, managed_capacity _⟩

theorem stored_clocks (state : TemporalControl interface profile config criterion dimension) :
    match state.runtime.references.phase with
    | .idle => True
    | .exploring committed => committed.run.remaining.val + 1 ≤ explorationCap ∧
        ∀ held, committed.origin = some held →
          held.2.age.val ≤ Acorn.FeatureConstants.optionMaxDuration
    | .option _ activation => activation.age.val ≤ Acorn.FeatureConstants.optionMaxDuration := by
  split
  · trivial
  · rename_i committed _
    refine ⟨committed.run.remaining.isLt, fun held _ => ?_⟩
    have := held.2.age.isLt
    omega
  · rename_i slot activation _
    have := activation.age.isLt
    omega

theorem stored_mode (state : TemporalControl interface profile config criterion dimension) :
    match state.runtime.references.phase with
    | .option _ activation => activation.learning = (profile.mode != .frozen)
    | .exploring committed => ∀ held, committed.origin = some held →
        held.2.learning = (profile.mode != .frozen)
    | .idle => True := by
  split
  · rfl
  · intro held _
    rfl
  · trivial

theorem finish_gain (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
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

theorem detached_terminal (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))
    (owner : Skill interface.actions config criterion dimension interface.layout)
    (detached : closing.oldOwner = some owner)
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1 = state := by
  simp [TemporalControl.closeOption_eq, detached]

theorem step_admitted (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32) (goal :
      Bool)
    (result : TemporalControl interface profile config criterion dimension × TemporalDecision
      interface.actions)
    (_executed : state.step planning features obs reward goal = some result) :
    result.2.action.val < interface.actions.word.toNat := result.2.action.isLt

abbrev Input (interface : Interface) (dimension : Dimension) :=
  SwiftTd.ActiveSet dimension × Frame interface × Binary32 × Bool

def runPrefix (planning : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension) :
    List (Input interface dimension) →
    Option (TemporalControl interface profile config criterion dimension)
  | [] => some state
  | frame :: rest => do
    let result ← state.step planning frame.1 frame.2.1 frame.2.2.1 frame.2.2.2
    runPrefix planning result.1 rest

theorem finite_prefix_schedule (planning : PlanningSelection)
    (state result : TemporalControl interface profile config criterion dimension)
    (frames : List (Input interface dimension))
    (_executed : runPrefix planning state frames = some result) (action : Action
      interface.actions.word.toNat) :
    let learner := result.runtime.lifecycle.consumers.control.learners.get action
    ScheduleInv learner.state learner.phase ∧ learner.state.eligibleCount ≤ dimension.capacity :=
  ⟨managed_schedule _, managed_capacity _⟩

theorem prepare_frame (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (state.prepareSelection models features reward).runtime.references.phase =
        state.runtime.references.phase ∧
      (state.prepareSelection models features reward).runtime.references.rng =
        state.runtime.references.rng := by
  by_cases hf : profile.mode = .frozen <;> cases hh : profile.usesHierarchy <;>
    simp [TemporalControl.prepareSelection, TemporalControl.withGap, hh, hf, bne]

theorem served_preempts (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (reward : Binary32) (goal : Bool)
    (committed : CommittedRun interface.actions (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .exploring committed)
    (remaining : 0 < committed.run.remaining.val)
    (result : TemporalControl interface profile config criterion dimension × TemporalDecision
      interface.actions)
    (selected : state.selectWithOperations models plan features declared reward goal =
      some result) :
    result.2.action = committed.run.action ∧ result.2.source = .explorationContinuation ∧
    result.1.runtime.references.rng = state.runtime.references.rng := by
  have prepared := prepare_frame state models features reward
  have served : ∃ output,
      (state.prepareSelection models features reward).serve features = some output := by
    simp [TemporalControl.serve, prepared.1, phase, ExploratoryRun.serve, remaining]
  obtain ⟨output, served⟩ := served
  have selectedOutput : state.selectWithOperations models plan features declared reward goal =
      some output := by
    simp [TemporalControl.selectWithOperations, served]
  have same := Option.some.inj (selectedOutput.symm.trans selected)
  subst result
  obtain ⟨held, rest, holds, service, source, _, generator⟩ :=
    (state.prepareSelection models features reward).serve_frame output.1 features output.2 served
  obtain rfl : held = committed :=
    Occupancy.exploring.inj (holds.symm.trans (prepared.1.trans phase))
  exact ⟨(held.run.serve_exact rest _ service).1, source, generator.trans prepared.2⟩

def serveSteps (run : ExploratoryRun actions) : Nat → Option (ExploratoryRun actions)
  | 0 => some run
  | n + 1 => do
    let served ← run.serve
    serveSteps served.2 n

theorem service_prefix_exact (run finalRun : ExploratoryRun actions) (count : Nat)
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

theorem follow_executing (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions)
    (slot : Fin Acorn.FeatureConstants.skillCount) (executing : state.activeSlot = some slot) :
    let next := state.followOptions models features declared reward goal decision
    next.runtime.lifecycle.consumers.skills[slot.val].policy =
        state.runtime.lifecycle.consumers.skills[slot.val].policy ∧
      next.runtime.lifecycle.consumers.skills[slot.val].model =
        state.runtime.lifecycle.consumers.skills[slot.val].model := by
  dsimp only
  rw [TemporalControl.followOptions_eq]
  split
  · simp [followSlot_def, executing]
  · exact ⟨rfl, rfl⟩

theorem closeSpan_skills (state : TemporalControl interface profile config criterion dimension)
    (continuation : Option Binary32) :
    (state.closeSpan continuation).runtime.lifecycle.consumers.skills =
      state.runtime.lifecycle.consumers.skills := by
  cases continuation with
  | none => rfl
  | some value =>
    rw [TemporalControl.closeSpan_eq]
    rfl

theorem step_executing (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (obs : Frame interface) (reward : Binary32) (goal : Bool)
    (result : TemporalControl interface profile config criterion dimension × TemporalDecision
      interface.actions)
    (executed : state.step planning features obs reward goal = some result) :
    ∃ selected, state.select planning features obs.declared reward goal =
        some (selected, result.2) ∧
      ∀ slot : Fin Acorn.FeatureConstants.skillCount, selected.activeSlot = some slot →
        result.1.runtime.lifecycle.consumers.skills[slot.val].policy =
            selected.runtime.lifecycle.consumers.skills[slot.val].policy ∧
          result.1.runtime.lifecycle.consumers.skills[slot.val].model =
            selected.runtime.lifecycle.consumers.skills[slot.val].model := by
  unfold TemporalControl.step at executed
  cases selection : state.select planning features obs.declared reward goal with
  | none => simp [selection] at executed
  | some chosen =>
    simp only [selection, bind, Option.bind, pure, Option.some.injEq] at executed
    cases executed
    refine ⟨chosen.1, rfl, fun slot executing => ?_⟩
    have followed := follow_executing chosen.1 (modelOperations criterion dimension) features
      obs.declared reward goal chosen.2 slot executing
    have finished := TemporalControl.finish_skills
      ((chosen.1.followOptions (modelOperations criterion dimension) features
        obs.declared reward goal chosen.2).closeSpan
          (chosen.1.takeoverValue features obs.declared goal chosen.2))
      features obs reward chosen.2
    rw [closeSpan_skills] at finished
    simp only at followed
    rw [finished]
    exact ⟨followed.1, followed.2⟩

theorem follow_inactive (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions)
    (inactive : (profile.usesHierarchy && profile.mode != .frozen) = false) :
    state.followOptions models features declared reward goal decision = state := by
  rw [TemporalControl.followOptions_eq]
  split
  · rename_i active
    rw [inactive] at active
    contradiction
  · rfl

theorem follow_frame (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
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

theorem follow_legal (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions)
    (slot : Fin Acorn.FeatureConstants.skillCount) (action : Action interface.actions.word.toNat)
    (index : FeatIdx dimension) :
    let learner := ((state.followOptions models features declared reward goal
      decision).runtime.lifecycle.consumers.skills[slot.val]).policy.learners.get action
    criterion.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    ScheduleInv learner.state learner.phase ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  exact ⟨weight_legal _, Bounded32.legal _, managed_schedule _, managed_capacity _⟩

theorem follow_refused (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat)
    (reward : Binary32) (gain : RewardRate)
    (skill : Skill interface.actions config criterion dimension interface.layout)
    (refused : skill.interest.potential features declared = none) :
    followSlot models value features declared goal estimate rate action behaviour reward gain
      false skill = { skill with following := none } := by
  simp [followSlot_def, refused]

theorem stopping_estimate_frozen
    (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) (drawn : PolicyDecision metaCount)
    (frozen : decision.metaDecision = some drawn) :
    state.stoppingEstimate decision = comparisonValue criterion drawn.snapshot := by
  simp only [TemporalControl.stoppingEstimate_def, frozen]

theorem follow_age (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation actions dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).following.map (·.age.val) = some (following.age.val + 1) := by
  have room : following.age.val < Acorn.FeatureConstants.optionMaxDuration := next.room
  cases skill with
  | mk interest policy model stored =>
    obtain rfl : stored = some following := linked
    simp only [Skill.followTemporal_def, continuing]
    simp [ModelAge.advance]
    omega

theorem follow_cap (skill : Skill actions config criterion dimension discounts)
    (following : Following)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32)
    (rate : ConsumerRate)
    (full : following.age.val = Acorn.FeatureConstants.optionMaxDuration) :
    skill.decideOption following.activation features potential false estimate rate =
      .ending .duration :=
  skill.cap_ends following.activation features potential estimate rate full

theorem follow_idle_model (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation actions dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next)
    (idle : following.live = false) (inconsistent : next.policy.consistent behaviour = false) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).model = skill.model := by
  cases skill with
  | mk interest policy model stored =>
    obtain rfl : stored = some following := linked
    simp [Skill.followTemporal_def, continuing, idle, inconsistent]

theorem follow_live_model (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation actions dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next)
    (live : following.live = true) :
    (skill.followTemporal (modelOperations criterion dimension) value features potential goal
      estimate rate action behaviour reward gain).model =
      skill.model.step features following.age reward := by
  cases skill with
  | mk interest policy model stored =>
    obtain rfl : stored = some following := linked
    simp [Skill.followTemporal_def, continuing, live, modelOperations, Model.step]

theorem follow_live (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation actions dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).following.map (·.live) = some (next.policy.consistent behaviour) := by
  cases skill with
  | mk interest policy model stored =>
    obtain rfl : stored = some following := linked
    simp only [Skill.followTemporal_def, continuing]
    rfl

theorem follow_policy (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation actions dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour reward
      gain).policy =
      skill.policy.backupStep (count := actions) features next.policy action
        (Features.shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
          following.previous) := by
  cases skill with
  | mk interest policy model stored =>
    obtain rfl : stored = some following := linked
    simp only [Skill.followTemporal_def, continuing]

theorem settle_continuing (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation actions dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next) :
    let settled := skill.settleFollowing models value features potential goal estimate rate
      reward gain
    settled.policy = skill.policy.stopStep
        (skill.policy.backupError (count := actions) next.policy
          (Features.shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
            following.previous)) ∧
      settled.model =
        (if following.live then (models.step skill.model features following.age reward).val
          else skill.model) := by
  cases skill with
  | mk interest policy model stored =>
    obtain rfl : stored = some following := linked
    simp only [Skill.settleFollowing_def, continuing, and_self]

theorem settle_ending (skill : Skill actions config criterion dimension discounts)
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
  | mk interest policy model stored =>
    obtain rfl : stored = some following := linked
    simp only [Skill.settleFollowing_def, ending]

theorem follow_live_ratio (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (following : Following) (linked : skill.following = some following)
    (next : OptionContinuation actions dimension following.activation)
    (continuing : skill.decideOption following.activation features potential goal estimate rate =
      .continuing next)
    (kept : (skill.followTemporal models value features potential goal estimate rate action
      behaviour reward gain).following.any (·.live) = true)
    (other : Action actions.word.toNat) :
    next.policy.probabilities.get other = behaviour.get other := by
  have live := follow_live skill models value features potential goal estimate rate action
    behaviour reward gain following linked next continuing
  have consistent : next.policy.consistent behaviour = true := by
    revert kept live
    cases (skill.followTemporal models value features potential goal estimate rate action
      behaviour reward gain).following with
    | none => simp
    | some stored =>
      intro kept live
      simp only [Option.any_some] at kept
      simp only [Option.map_some, Option.some.injEq] at live
      rw [← live]
      exact kept
  exact PolicySnapshot.consistent_mass _ _ other consistent

theorem start_live_ratio (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat)
    (kept : (skill.startFollowing models features potential rate action
      behaviour).following.any (·.live) = true)
    (other : Action actions.word.toNat) :
    (skill.policy.snapshot (count := actions) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := actions))).probabilities.get
        other = behaviour.get other := by
  have consistent : (skill.policy.snapshot (count := actions) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := actions))).consistent
        behaviour = true := by
    simpa [Skill.startFollowing_def] using kept
  exact PolicySnapshot.consistent_mass _ _ other consistent

theorem served_inconsistent (snapshot : PolicySnapshot actions)
    (action other : Action actions.word.toNat) (different : other ≠ action)
    (positive : snapshot.probabilities.get other ≠ .zero) :
    snapshot.consistent (servedProbabilities action) = false := by
  by_contra consistent
  have equal := PolicySnapshot.consistent_mass snapshot _ other
    (by simpa using consistent)
  simp only [served_probability, different, ↓reduceIte] at equal
  exact positive equal

theorem persistent_branch {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    (snapshot.drawPersistent rng).1.explored = (snapshot.draw rng).1.explored := by
  cases branch : rng.nextF64.1.less (Conversion.widen snapshot.epsilon.value) <;>
    simp [PolicySnapshot.drawPersistent_def, beginExploration, PolicySnapshot.draw_def, branch]

theorem persistent_draw {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    ((snapshot.drawPersistent rng).1.explored = true →
        (snapshot.drawPersistent rng).1.run =
          some ⟨(uniformAction count rng.nextF64.2.nextF64.2).1,
            durationRemaining rng.nextF64.2.nextF64.1⟩ ∧
        (snapshot.drawPersistent rng).1.action =
          (uniformAction count rng.nextF64.2.nextF64.2).1) ∧
      ((snapshot.drawPersistent rng).1.explored = false →
        (snapshot.drawPersistent rng).1.run = none ∧
        (snapshot.drawPersistent rng).1.action = (snapshot.greedy rng.nextF64.2).1) ∧
      (snapshot.drawPersistent rng).1.probabilities = snapshot.probabilities := by
  cases branch : rng.nextF64.1.less (Conversion.widen snapshot.epsilon.value) <;>
    simp [PolicySnapshot.drawPersistent_def, beginExploration, branch]

theorem persistent_consistent {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    snapshot.consistent (snapshot.drawPersistent rng).1.probabilities = true :=
  (snapshot.consistent_iff _).mpr (persistent_draw snapshot rng).2.2.symm

def committedRun :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) → Option (ExploratoryRun actions)
  | .exploring committed => some committed.run
  | .option _ _ | .idle => none

def leftToServe (run : Option (ExploratoryRun actions)) :
    Option (ExploratoryRun actions) :=
  run.bind fun run => if 0 < run.remaining.val then some run else none

theorem afterPrimitive_committed (run : Option (ExploratoryRun actions)) :
    committedRun (Occupancy.afterPrimitive (mode := mode) run) = leftToServe run := by
  cases run with
  | none => rfl
  | some run =>
    by_cases left : 0 < run.remaining.val <;>
      simp [committedRun, leftToServe, Occupancy.afterPrimitive, CommittedRun.bare, left]

theorem afterOption_committed (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation mode) (run : Option (ExploratoryRun actions)) :
    committedRun (Occupancy.afterOption slot activation run) = leftToServe run := by
  cases run with
  | none => rfl
  | some run =>
    by_cases left : 0 < run.remaining.val <;>
      simp [committedRun, leftToServe, Occupancy.afterOption, left]

def Drawn (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) (snapshot : PolicySnapshot interface.actions)
    (rng : Rng.Xoshiro256) : Prop :=
  decision.action = (snapshot.drawPersistent rng).1.action ∧
    decision.explored = (snapshot.drawPersistent rng).1.explored ∧
    decision.values = snapshot.values ∧
    decision.probabilities = snapshot.probabilities ∧
    next.runtime.references.rng = (snapshot.drawPersistent rng).2 ∧
    committedRun next.runtime.references.phase = leftToServe (snapshot.drawPersistent rng).1.run

def optionSnapshot (origin : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (features : SwiftTd.ActiveSet dimension) :
    PolicySnapshot interface.actions :=
  (origin.runtime.lifecycle.consumers.skills.get slot).policy.snapshot (count := interface.actions)
    features (origin.skillRate.resolve fun _ =>
      (origin.runtime.lifecycle.consumers.skills.get slot).policy.exploreRate
        (count := interface.actions))

def Acting (features : SwiftTd.ActiveSet dimension)
    (origin next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : Prop :=
  (decision.source = (if decision.explored then .explorationStart else .primitive) ∧
    Drawn next decision
      (origin.runtime.lifecycle.consumers.control.snapshot (count := interface.actions) features
        origin.controlRate)
      origin.runtime.references.rng) ∨
  ∃ slot : Fin Acorn.FeatureConstants.skillCount,
    decision.source = .option slot ∧
      Drawn next decision (optionSnapshot origin slot features) origin.runtime.references.rng

def Handed (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) (rng : Rng.Xoshiro256) : Prop :=
  (decision.metaDecision = none ∧ rng = state.runtime.references.rng) ∨
  ∃ metaSnapshot : PolicySnapshot metaCount,
    decision.metaDecision = some (metaSnapshot.draw state.runtime.references.rng).1 ∧
      rng = (metaSnapshot.draw state.runtime.references.rng).2

def Served (state next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : Prop :=
  ∃ committed rest, state.runtime.references.phase = .exploring committed ∧
    committed.run.serve = some (decision.action, rest) ∧
    decision.source = .explorationContinuation ∧
    next.runtime.references.phase = .exploring (.bare rest) ∧
    next.runtime.references.rng = state.runtime.references.rng

theorem serve_explored (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (served : state.serve features = some (next, decision)) : decision.explored = true := by
  unfold TemporalControl.serve at served
  cases phase : state.runtime.references.phase with
  | idle => simp [phase] at served
  | option slot activation => simp [phase] at served
  | exploring committed =>
    simp only [phase] at served
    cases run : committed.run.serve with
    | none => simp [run] at served
    | some pair =>
      simp only [run, bind, Option.bind, pure, Option.some.injEq] at served
      cases served
      rfl

def Reached (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : Prop :=
  ∃ origin : TemporalControl interface profile config criterion dimension,
    Acting features origin next decision ∧
      Handed state decision origin.runtime.references.rng

theorem optionSnapshot_withSkill
    (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) :
    optionSnapshot (state.withSkill slot skill) slot features =
      skill.policy.snapshot (count := interface.actions) features
        (state.skillRate.resolve fun _ => skill.policy.exploreRate (count := interface.actions)) :=
        by
  have stored : (state.withSkill slot skill).runtime.lifecycle.consumers.skills.get slot =
      skill := by
    simp only [TemporalControl.withSkill, vector_get, Vector.getElem_set_self]
  unfold optionSnapshot
  rw [stored]
  rfl

theorem choosePrimitive_drawn (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    Drawn (state.choosePrimitive features metaValues metaDecision ended).1
      (state.choosePrimitive features metaValues metaDecision ended).2
      (state.runtime.lifecycle.consumers.control.snapshot (count := interface.actions) features
        state.controlRate)
      state.runtime.references.rng :=
  ⟨rfl, rfl, rfl, (persistent_draw _ _).2.2, rfl, afterPrimitive_committed _⟩

theorem choosePrimitive_acting
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    Acting features state (state.choosePrimitive features metaValues metaDecision ended).1
      (state.choosePrimitive features metaValues metaDecision ended).2 :=
  Or.inl ⟨rfl, choosePrimitive_drawn state features metaValues metaDecision ended⟩

theorem stepOption_drawn (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool)
    (ended : Option EndEvent) :
    Drawn (state.stepOption models slot activation next reward metaValues metaDecision started
        ended).1
      (state.stepOption models slot activation next reward metaValues metaDecision started
        ended).2
      next.policy state.runtime.references.rng := by
  have drawn : ((state.runtime.lifecycle.consumers.skills.get slot).stepTemporal models activation
      next reward state.average.rate state.runtime.references.rng).2.2 =
        next.policy.drawPersistent state.runtime.references.rng := by
    rw [((state.runtime.lifecycle.consumers.skills.get slot).stepTemporal_policy models activation
      next reward state.average.rate state.runtime.references.rng).2]
    exact Skill.step_drawn _ activation next reward state.average.rate state.runtime.references.rng
  rw [TemporalControl.stepOption_eq]
  refine ⟨congrArg (·.1.action) drawn, congrArg (·.1.explored) drawn, rfl, ?_,
    congrArg (·.2) drawn, ?_⟩
  · exact (congrArg (·.1.probabilities) drawn).trans (persistent_draw _ _).2.2
  · exact (afterOption_committed slot _ _).trans
      (congrArg (fun pair => leftToServe pair.1.run) drawn)

theorem stepOption_source (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool)
    (ended : Option EndEvent) :
    (state.stepOption models slot activation next reward metaValues metaDecision started
      ended).2.source = .option slot := by
  rw [TemporalControl.stepOption_eq]

theorem stepOption_recorded (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool)
    (ended : Option EndEvent) :
    (state.stepOption models slot activation next reward metaValues metaDecision started
      ended).2.metaDecision = metaDecision := by
  rw [TemporalControl.stepOption_eq]

theorem stepOption_acting (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool)
    (ended : Option EndEvent) (own : next.policy = optionSnapshot state slot features) :
    Acting features state
      (state.stepOption models slot activation next reward metaValues metaDecision started
        ended).1
      (state.stepOption models slot activation next reward metaValues metaDecision started
        ended).2 :=
  Or.inr ⟨slot, stepOption_source state models slot activation next reward metaValues
    metaDecision started ended, own ▸ stepOption_drawn state models slot activation next reward
      metaValues metaDecision started ended⟩

theorem learnMeta_rng (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (state.learnMeta features decision).runtime.references.rng =
      state.runtime.references.rng := by
  rw [TemporalControl.learnMeta_eq]
  split <;> rfl

theorem closeOption_rng (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1.runtime.references.rng =
      state.runtime.references.rng := by
  rw [TemporalControl.closeOption_eq]
  split <;> rfl

theorem skipMeta_frame (state : TemporalControl interface profile config criterion dimension) :
    state.skipMeta.runtime.references.rng = state.runtime.references.rng ∧
      state.skipMeta.runtime.references.phase = state.runtime.references.phase := by
  unfold TemporalControl.skipMeta
  split <;> exact ⟨rfl, rfl⟩

theorem drawn_skip {state : TemporalControl interface profile config criterion dimension}
    {decision : TemporalDecision interface.actions} {snapshot : PolicySnapshot interface.actions}
    {rng : Rng.Xoshiro256} (drawn : Drawn state decision snapshot rng) :
    Drawn state.skipMeta decision snapshot rng :=
  ⟨drawn.1, drawn.2.1, drawn.2.2.1, drawn.2.2.2.1,
    (skipMeta_frame state).1.trans drawn.2.2.2.2.1,
    (congrArg committedRun (skipMeta_frame state).2).trans drawn.2.2.2.2.2⟩

theorem acting_skip {features : SwiftTd.ActiveSet dimension}
    {origin state : TemporalControl interface profile config criterion dimension}
    {decision : TemporalDecision interface.actions} (acting : Acting features origin state decision)
    :
    Acting features origin state.skipMeta decision := by
  rcases acting with ⟨source, drawn⟩ | ⟨slot, source, drawn⟩
  · exact Or.inl ⟨source, drawn_skip drawn⟩
  · exact Or.inr ⟨slot, source, drawn_skip drawn⟩

theorem serve_source (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (served : state.serve features = some (next, decision)) :
    decision.source = .explorationContinuation := by
  unfold TemporalControl.serve at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      obtain ⟨_, rfl⟩ := served
      rfl
  · contradiction
  · contradiction

theorem dispatchMeta_acting
    (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount) (ended : Option EndEvent)
    (observed : TemporalDecision interface.actions)
    (executed : state.dispatchMeta models features declared reward goal decision ended =
      some (next, observed)) :
    observed.metaDecision = some decision ∧
      ∃ origin : TemporalControl interface profile config criterion dimension,
        Acting features origin next observed ∧
          origin.runtime.references.rng = state.runtime.references.rng := by
  rw [TemporalControl.dispatchMeta_eq] at executed
  have kept := learnMeta_rng state features decision
  generalize state.learnMeta features decision = credited at executed kept
  cases selected : skillOfMeta decision.action with
  | none =>
    simp only [selected, pure, Option.some.injEq] at executed
    cases executed
    exact ⟨rfl, credited, choosePrimitive_acting credited features _ _ _, kept⟩
  | some slot =>
    simp only [selected] at executed
    cases potential : (credited.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at executed
      generalize step : TemporalControl.stepOption _ _ _ _ _ _ _ _ _ _ = result at executed
      obtain ⟨rfl, rfl⟩ : result.1 = next ∧ result.2 = observed := by
        rw [executed]
        exact ⟨rfl, rfl⟩
      rw [← step]
      refine ⟨stepOption_recorded _ models slot _ _ reward _ _ true ended, _,
        stepOption_acting _ models slot _ _ features reward _ _ true ended ?_, kept⟩
      rw [optionSnapshot_withSkill]
      exact Skill.beginTemporal_policy _ models features value _ credited.skillRate

theorem atBoundary_reached
    (state boundary next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) (observed : TemporalDecision interface.actions)
    (incoming : boundary.runtime.references.rng = state.runtime.references.rng)
    (executed : boundary.atBoundary models plan features declared reward goal closing ended =
      some (next, observed)) : Reached state features next observed := by
  unfold TemporalControl.atBoundary at executed
  have refreshedRng : (boundary.refreshFree closing).1.runtime.references.rng =
      state.runtime.references.rng := incoming
  generalize boundary.refreshFree closing = refreshed at executed refreshedRng
  dsimp only at executed
  have plannedRng : (refreshed.1.planFree plan features).runtime.references.rng =
      state.runtime.references.rng := refreshedRng
  generalize refreshed.1.planFree plan features = planned at executed plannedRng
  have drawnFacts :
      (planned.drawMeta features).2 =
          ((planned.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
            features planned.metaRate).draw planned.runtime.references.rng).1 ∧
        (planned.drawMeta features).1.runtime.references.rng =
          ((planned.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
            features planned.metaRate).draw planned.runtime.references.rng).2 := ⟨rfl, rfl⟩
  rw [plannedRng] at drawnFacts
  generalize planned.drawMeta features = drawn at executed drawnFacts
  cases hc : refreshed.2 with
  | none =>
    simp only [hc] at executed
    obtain ⟨recorded, origin, acting, kept⟩ := dispatchMeta_acting drawn.1 next models features
      declared reward goal drawn.2 ended observed executed
    exact ⟨origin, acting, Or.inr ⟨_, recorded.trans (congrArg some drawnFacts.1),
      kept.trans drawnFacts.2⟩⟩
  | some owner =>
    simp only [hc] at executed
    obtain ⟨recorded, origin, acting, kept⟩ := dispatchMeta_acting _ next models features
      declared reward goal drawn.2 _ observed executed
    exact ⟨origin, acting, Or.inr ⟨_, recorded.trans (congrArg some drawnFacts.1),
      (kept.trans (closeOption_rng drawn.1 models features owner reward _)).trans drawnFacts.2⟩⟩

theorem select_persistent
    (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (observed : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, observed)) :
    Served state next observed ∨ Reached state features next observed := by
  unfold TemporalControl.selectWithOperations at executed
  have frame := prepare_frame state models features reward
  generalize state.prepareSelection models features reward = prepared at executed frame
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    obtain ⟨held, rest, holds, service, source, stored, generator⟩ :=
      prepared.serve_frame next features observed served
    exact Or.inl ⟨held, rest, frame.1.symm.trans holds, service, source, stored,
      generator.trans frame.2⟩
  | none =>
    simp only [served] at executed
    refine Or.inr ?_
    split at executed
    · have same : (prepared.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero)
          none none = (next, observed) := Option.some.inj executed
      have acting := choosePrimitive_acting (prepared.withPhase .idle) features
        (Vector.replicate _ .zero) none none
      have undrawn : ((prepared.withPhase .idle).choosePrimitive features
          (Vector.replicate _ .zero) none none).2.metaDecision = none := rfl
      rw [same] at acting undrawn
      exact ⟨prepared.withPhase .idle, acting, Or.inl ⟨undrawn, frame.2⟩⟩
    · cases phase : prepared.runtime.references.phase with
      | idle =>
        simp only [phase] at executed
        exact atBoundary_reached state (prepared.withPhase .idle) next models plan features
          declared reward goal none none observed frame.2 executed
      | exploring committed =>
        simp only [phase] at executed
        exact atBoundary_reached state (prepared.withPhase .idle) next models plan features
          declared reward goal none none observed frame.2 executed
      | option slot activation =>
        simp only [phase] at executed
        let free := prepared.withPhase .idle
        let skill := free.runtime.lifecycle.consumers.skills.get slot
        let metaPolicy := free.runtime.lifecycle.consumers.metaController.snapshot
          (count := metaCount) features free.metaRate
        cases potential : skill.interest.potential features declared with
        | none =>
          simp only [skill, free] at potential
          simp [potential] at executed
        | some value =>
          simp only [skill, free] at potential
          simp only [potential, bind, Option.bind] at executed
          cases choice : skill.decideOption activation features value goal
              (comparisonValue criterion metaPolicy) free.skillRate with
          | continuing continuation =>
            have policy : continuation.policy =
                optionSnapshot free.withoutPlanning slot features :=
              skill.decide_policy activation features value goal
                (comparisonValue criterion metaPolicy) free.skillRate continuation choice
            simp only [skill, free, metaPolicy] at choice
            simp only [choice, pure, Option.some.injEq] at executed
            cases executed
            exact ⟨free.withoutPlanning,
              acting_skip (stepOption_acting free.withoutPlanning models slot activation
                continuation features reward metaPolicy.values none false none policy),
              Or.inl ⟨stepOption_recorded free.withoutPlanning models slot activation continuation
                reward metaPolicy.values none false none, frame.2⟩⟩
          | ending reason =>
            simp only [skill, free, metaPolicy] at choice
            simp only [choice] at executed
            let closing : Closing interface.actions config criterion dimension interface.layout
                (EndingPayload (profile.mode != .frozen)) :=
              ⟨slot, ⟨activation, value, reason⟩, none⟩
            cases criterion with
            | differential =>
              exact atBoundary_reached state free next models plan features declared reward goal
                (some closing) none observed frame.2 executed
            | discounted =>
              let closed := free.closeOption models features closing reward
                (comparisonValue .discounted metaPolicy)
              exact atBoundary_reached state closed.1 next models plan features declared reward
                goal none (some closed.2) observed
                ((closeOption_rng free models features closing reward _).trans frame.2) executed

theorem interrupt_link (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (learning : activation.learning = true) :
    (state.interrupt (some (slot, activation))).1 =
        state.withSkill slot { state.runtime.lifecycle.consumers.skills.get slot with
          following := some activation.following } ∧
      (state.interrupt (some (slot, activation))).2 =
        some ⟨slot, activation.age, .interrupted⟩ := by
  unfold TemporalControl.interrupt
  dsimp only
  rw [ite_eq_left learning]
  exact ⟨rfl, rfl⟩

theorem interrupt_frozen (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (frozen : activation.learning = false) :
    (state.interrupt (some (slot, activation))).1 = state := by
  unfold TemporalControl.interrupt
  dsimp only
  rw [ite_eq_right (by simp [frozen])]

theorem serve_interrupts (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (committed : CommittedRun interface.actions (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .exploring committed)
    (served : state.serve features = some (next, decision)) :
    next.runtime.lifecycle = (state.interrupt committed.origin).1.runtime.lifecycle ∧
      decision.ended = (state.interrupt committed.origin).2 ∧ next.activeSlot = none ∧
      (committed.origin.isSome = true → next.gap = state.gap) := by
  unfold TemporalControl.serve at served
  simp only [phase] at served
  cases hs : committed.run.serve with
  | none => simp [hs] at served
  | some pair =>
    simp only [hs, bind, Option.bind, pure, Option.some.injEq] at served
    cases served
    refine ⟨?_, rfl, ?_, fun held => ?_⟩
    · unfold TemporalControl.skipMeta
      repeat' split
      all_goals rfl
    · unfold TemporalControl.skipMeta
      repeat' split
      all_goals rfl
    · have span : (state.interrupt committed.origin).1.gap = state.gap :=
        congrArg (fun references => (⟨references.gapSteps, references.gapReward⟩ : CreditGap))
          (state.interrupt_frame committed.origin).2.1
      simp only [held, ↓reduceIte]
      split <;> exact span

theorem serve_run (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (committed : CommittedRun interface.actions (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .exploring committed)
    (served : state.serve features = some (next, decision)) :
    ∃ rest, committed.run.serve = some (decision.action, rest) ∧
      next.runtime.references.phase = .exploring (.bare rest) := by
  obtain ⟨held, rest, holds, service, _, stored, _⟩ :=
    state.serve_frame next features decision served
  obtain rfl : held = committed := Occupancy.exploring.inj (holds.symm.trans phase)
  exact ⟨rest, service, stored⟩

theorem meta_span_fits :
    (Acorn.FeatureConstants.optionMaxDuration - 1) + (explorationCap - 1) < 255 := by decide

theorem follow_unoccupied (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions)
    (active : (profile.usesHierarchy && profile.mode != .frozen) = true)
    (unoccupied : state.activeSlot = none) (slot : Fin Acorn.FeatureConstants.skillCount) :
    (state.followOptions models features declared reward goal
        decision).runtime.lifecycle.consumers.skills[slot.val] =
      followSlot models state.valueFunction features declared goal
        (state.stoppingEstimate decision) state.skillRate decision.action decision.probabilities
        reward state.average.rate false state.runtime.lifecycle.consumers.skills[slot.val] := by
  rw [TemporalControl.followOptions_eq, ite_eq_left active]
  simp only [Vector.getElem_mapFinIdx, unoccupied]
  rfl

theorem handoff_model (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate) (rng : Rng.Xoshiro256)
    (activation : OptionActivation true) (aged : 0 < activation.age.val)
    (held : skill.following = some activation.following)
    (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal (modelOperations criterion dimension) value features potential goal
      estimate rate action behaviour reward gain).model =
      (skill.stepTemporal (modelOperations criterion dimension) activation next reward gain
        rng).1.model := by
  have frame := (skill.decide_frame activation features potential goal estimate rate next
    continuing).1
  have learning : activation.learning = true := rfl
  rw [follow_live_model skill value features potential goal estimate rate action behaviour reward
    gain activation.following held next continuing (decide_eq_true aged)]
  simp [Skill.stepTemporal_eq, Skill.optionStep_def, learning, aged, modelOperations, frame,
    OptionActivation.following, Model.step]

theorem handoff_policy (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (activation : OptionActivation true)
    (held : skill.following = some activation.following)
    (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour
      reward gain).policy =
      skill.policy.backupStep (count := actions) features next.policy action
        (Features.shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
          activation.previous) :=
  follow_policy skill models value features potential goal estimate rate action behaviour reward
    gain activation.following held next continuing

theorem handoff_stop (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (activation : OptionActivation true)
    (held : skill.following = some activation.following) (reason : OptionEnd)
    (ending : skill.decideOption activation features potential goal estimate rate =
      .ending reason) :
    skill.followTemporal models value features potential goal estimate rate action behaviour
        reward gain =
      (skill.stopFollowing models value features activation.following potential estimate reward
        gain).startFollowing models features potential rate action behaviour := by
  have stop : skill.decideOption activation.following.activation features potential goal estimate
      rate = .ending reason := ending
  cases skill with
  | mk interest policy model stored =>
    obtain rfl : stored = some activation.following := held
    simp only [Skill.followTemporal_def, stop]

theorem handoff_age (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate)
    (activation : OptionActivation true)
    (held : skill.following = some activation.following)
    (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate =
      .continuing next) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour
      reward gain).following.map (·.age.val) = some (activation.age.val + 1) :=
  follow_age skill models value features potential goal estimate rate action behaviour reward
    gain activation.following held next continuing

theorem takeover_value (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (decision : TemporalDecision interface.actions) (event : EndEvent) (following : Following)
    (potential : Potential)
    (active : (profile.usesHierarchy && profile.mode != .frozen) = true)
    (served : decision.source = .explorationContinuation)
    (ended : decision.ended = some event)
    (linked : (state.runtime.lifecycle.consumers.skills.get event.slot).following =
      some following)
    (supplied : (state.runtime.lifecycle.consumers.skills.get event.slot).interest.potential
      features declared = some potential) :
    state.takeoverValue features declared goal decision =
      some (match (state.runtime.lifecycle.consumers.skills.get event.slot).decideOption
          following.activation features potential goal (state.stoppingEstimate decision)
          state.skillRate with
        | .continuing _ => decision.metaValues.get (metaOfSkill event.slot)
        | .ending _ => state.stoppingEstimate decision) := by
  simp [TemporalControl.takeoverValue, active, served, ended, linked, supplied]
  split <;> simp [*]

theorem takeover_none (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (decision : TemporalDecision interface.actions)
    (other : decision.source ≠ .explorationContinuation ∨ decision.ended = none) :
    state.takeoverValue features declared goal decision = none := by
  rcases other with source | ended
  · simp [TemporalControl.takeoverValue, source]
  · simp [TemporalControl.takeoverValue, ended]

theorem closeSpan_controller (state : TemporalControl interface profile config criterion dimension)
    (value : Binary32) :
    (state.closeSpan (some value)).runtime.lifecycle.consumers.metaController =
        state.runtime.lifecycle.consumers.metaController.closeStep
          (criterion.center state.gap.close.1 state.gap.close.2 state.average.rate) value
          state.gap.close.2 ∧
      (state.closeSpan (some value)).gap = .closed := by
  rw [TemporalControl.closeSpan_eq]
  exact ⟨rfl, rfl⟩

end AcornVerif.CurrentTemporal
