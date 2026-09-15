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
-/
namespace AcornVerif.CurrentTemporal
open Acorn Acorn.Features Acorn.Handcrafted
open CurrentFeatureConsumers CurrentLearner

variable {mode : Bool} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}

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
the goal-ending branch. Machine additions and multiplication keep their order. -/
theorem learned_terminal_target (assignment : Assignment config) (estimate reward : Binary32)
    (next previous : Potential) :
    Features.terminalCumulant reward ((Interest.learned assignment).stoppingValue estimate next)
      previous =
      (reward.add (estimate.add (assignment.bonus.mul next.value))).sub previous.value := rfl

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
theorem option_step_clock (skill : Skill config criterion dimension) (models : OptionModelOps
    criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    let result := skill.stepTemporal models activation next reward gain rng
    result.2.1.age.val = activation.age.val + 1 ∧
    result.2.1.learning = activation.learning ∧ result.2.1.previous = next.potential := by
  dsimp only
  rw [(skill.stepTemporal_policy models activation next reward gain rng).2]
  exact ⟨skill.step_age activation next reward gain rng, rfl, rfl⟩

/-- Terminal learning clears all actual policy trajectory registers in all rows. -/
theorem terminal_clears (skill : Skill config criterion dimension) (models : OptionModelOps
    criterion dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate)
    (learning : ending.activation.learning = true) (action : Action primitiveCount.word.toNat) :
    (((skill.endTemporal models ending reward terminal gain).policy.learners.get
      action).state.transient) =
      TransientState.zero dimension := by
  simp only [Skill.endTemporal, Skill.terminateOption, learning, ↓reduceIte]
  exact CurrentControl.terminal_clears _ _ action

/-- Frozen begin retains every policy and model register, not just its observations. -/
theorem frozen_begin (skill : Skill config criterion dimension) (models : OptionModelOps criterion
    dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential false rate).1 = skill := rfl

/-- Frozen terminal consumption performs no policy or model write. -/
theorem frozen_terminal (skill : Skill config criterion dimension) (models : OptionModelOps
    criterion dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate)
    (frozen : ending.activation.learning = false) :
    skill.endTemporal models ending reward terminal gain = skill := by
  simp [Skill.endTemporal, Skill.terminateOption, frozen]

/-- All returned option policies retain the same managed admission and legal
knowledge, including arbitrary raw reward and transient words. -/
theorem option_step_legal (skill : Skill config criterion dimension) (models : OptionModelOps
    criterion dimension)
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
  · simp [TemporalControl.finish_eq, TemporalControl.predictionView, PredictionControl.advance,
      frozen, PrimitiveControl.finish, TemporalControl.recordEpisodes]
  · have clock := (state.recordEpisodes decision).predictionView.control.credit_preserves_clock
      features decision.action decision.own reward
    simp only [TemporalControl.finish_eq, PredictionControl.advance, beq_iff_eq,
      frozen, ↓reduceIte, PrimitiveControl.finish]
    rw [clock.1, clock.2]
    have hb : (profile.mode == .frozen) = false :=
      Bool.eq_false_iff.mpr (fun h => frozen (beq_iff_eq.mp h))
    simp [TemporalControl.predictionView, TemporalControl.recordEpisodes, bne, hb]

/-- A detached ending owner cannot overwrite any current table learner. Pure
terminal arithmetic on a discarded owner has no retained effect; native dead-code
elimination of that unused result preserves this exact state relation. -/
theorem detached_terminal (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (closing : Closing config criterion dimension
      (EndingPayload (profile.mode != .frozen)))
    (owner : Skill config criterion dimension) (detached : closing.oldOwner = some owner)
    (reward terminal : Binary32) : (state.closeOption models closing reward terminal).1 = state :=
      by
  simp [TemporalControl.closeOption, detached]

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
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
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

end AcornVerif.CurrentTemporal
