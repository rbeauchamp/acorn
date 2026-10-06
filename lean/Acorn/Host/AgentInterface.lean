/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.StepParts
import Acorn.Handcrafted.GridWorld
import Acorn.Host.Runner
import Acorn.Host.AgentDiagnostics

/-!
# Current agent input and observation boundary

The runner callbacks call the two parts of the actual composed transition and the
lifetime owners at the grid world's interface instance: each grid observation and
preceding raw result reaches the agent as one percept, and the chosen action index
leaves as a host action.
Snapshots retain current immutable values only. Delivered telemetry and byte IO
are separate interface owners; neither has a parameter on action selection.
-/
namespace Acorn.Handcrafted
open Features

/-- Task-family indexing is exhaustive over the host's closed family type. -/
def familyIndex : Host.GoalFamily → Fin 4
  | .reach => 0 | .collect => 1 | .craft => 2 | .survive => 3

/-- Public research selection resolves all immutable discriminants explicitly. -/
def researchProfile : Host.ResearchProfile → FeatureProfile
  | .ranked => ⟨.final, .perStep, .declared, .learned⟩
  | .primitive => ⟨.primitiveOnly, .perStep, .declared, .learned⟩
  | .boundaryCredit => ⟨.final, .smdpCatchUp, .declared, .learned⟩
  | .annealed => ⟨.final, .perStep, .annealed, .learned⟩
  | .spatial => ⟨.final, .perStep, .declared, .spatial⟩

/-- Host checkpoint admission and the actual constructed profile agree. -/
theorem researchProfile_resumable (profile : Host.ResearchProfile) :
    (researchProfile profile).checkpointSupported = profile.resumable := by
  cases profile <;> rfl

/-- Every research profile except the annealed rate comparison uses the declared D6 rate. -/
theorem researchProfile_declared (profile : Host.ResearchProfile) (ordinary : profile ≠ .annealed) :
    (researchProfile profile).rate = .declared := by
  cases profile <;> first | rfl | exact absurd rfl ordinary

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

/-- Attempt metrics read current errors, the primitive controller's resolved
rate, and the first primitive learner. These are raw diagnostic numbers,
without a convergence or finiteness assertion. -/
def Agent.metrics (state : Agent Grid.interface profile config criterion dimension planning) : Host.LearnerMetrics :=
  ⟨(Binary32.sumFrom .zero state.control.runtime.references.demonErrors.toList).div
      (Binary32.ofUInt64 demonLayout.length.toUInt64),
    state.control.controlRate.value,
    (state.control.runtime.lifecycle.consumers.control.learners.get ⟨0, by decide⟩).state.meanAlpha⟩

/-- Current one-way observation, including complete representation and assignment identities. -/
structure AgentObservation (config : Features.Config) (dimension : Dimension) where
  /-- Saturating lifetime decision clock. -/
  clock : UInt64
  /-- Receiver-owned representation history and current bank. -/
  representation : Representation Host.patchShape config
  /-- Assignment identities include the complete unit and threshold payload. -/
  interests : Vector (Interest config) Acorn.FeatureConstants.skillCount
  /-- Current feedback cache in its immutable horizon order. -/
  predictions : PredictionCache demonLayout
  /-- Current primitive decision and hierarchy diagnostics, absent on cold state. -/
  decision : Option (TemporalDecision Grid.actions)
  /-- One-way scalar observations from the current learners. -/
  metrics : Host.LearnerMetrics
  /-- Shared host-time gain observed after learning. -/
  gain : RewardRate
  /-- All current accounting, including process-local pending returns. -/
  lifetime : Lifetime.Stats demonLayout
  /-- Current per-learner step sizes and eligibility cardinalities. -/
  learners : Host.EnsembleDiagnostics demonLayout
  /-- Stored option-model cache, without refreshing or planning again. -/
  models : Vector ModelCache Acorn.FeatureConstants.skillCount
  /-- Actual accumulated process-local planning work. -/
  planningSteps : UInt64
  /-- Actual planner error cache in skill order. -/
  planningErrors : Vector Binary32 Acorn.FeatureConstants.skillCount
  /-- Number of actions served by the currently active option, or zero. -/
  optionElapsed : ModelAge
  /-- Actual immutable control criterion of the captured agent. -/
  criterion : Criterion
  /-- Actual immutable behavior profile, including declared subtask policy. -/
  featureProfile : FeatureProfile

/-- Capture reads this receiver, without encoding again or advancing any learner. -/
@[noinline] def Agent.observe (state : Agent Grid.interface profile config criterion dimension planning) :
    AgentObservation config dimension :=
  ⟨state.clock, state.control.runtime.lifecycle.representation,
    state.control.runtime.lifecycle.consumers.skills.map (·.interest),
    state.control.runtime.references.demonPredictions, state.control.runtime.references.lastDecision,
    state.metrics, state.control.average.rate, state.control.lifetime,
    Host.ensembleDiagnostics state.control.runtime.lifecycle.consumers,
    state.control.runtime.references.modelPredictions, state.control.runtime.references.planningSteps,
    state.control.runtime.references.planningErrors,
    match state.control.runtime.references.phase with
    | .option _ activation => activation.age
    | .exploring committed => (committed.origin.map (·.2.age)).getD 0
    | .idle => 0,
    criterion, profile⟩

/-- Full-agent callbacks bind every existing host protocol operation to its actual
owner, for one step order. The two parts of a step are the agent's own parts of that
order, and the order is the index of the result, so a host loop of the other order
does not take it. This is the composition over the learner state, which holds no order
of its own; a host composes `AgentConstruction.callbacks`, whose state type is of one
construction. -/
def Agent.callbacks (order : StepOrder) :
    Host.AgentCallbacks order (Agent Grid.interface profile config criterion dimension planning)
      (AgentObservation config dimension) where
  Chosen := Chosen Grid.interface profile config criterion dimension planning
  choose state observation result :=
    let chosen := state.choose order
      (Grid.percept profile.taskMode observation result.reward result.events.done)
    (Host.Action.fromIndex chosen.decision.action.val, chosen)
  learn := Chosen.learn
  recordEnvironment state family reward := state.recordEnvironment (familyIndex family) reward
  recordAttempt state family cycle steps achieved := state.recordAttempt (familyIndex family) cycle steps achieved
  capture := Agent.observe
  metrics := Agent.metrics

/-- Under the default order the host's whole step is the interface agent's step on the
grid percept: the raw preceding reward and achievement event are passed unchanged, the
host action is the chosen index of the interface's action set, and the two parts the
host calls compose to the executed `Agent.act`. -/
theorem Agent.callbacks_act (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    (Agent.callbacks .learnThenAct).act state observation result =
      (Host.Action.fromIndex (state.act (Grid.percept profile.taskMode observation result.reward
          result.events.done)).2.action.val,
        (state.act (Grid.percept profile.taskMode observation result.reward
          result.events.done)).1) := by
  rw [Agent.act_parts]
  rfl

/-- Under every order the host's whole step is the agent's whole step of that order on
the grid percept. -/
theorem Agent.callbacks_ordered (order : StepOrder)
    (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    (Agent.callbacks order).act state observation result =
      (Host.Action.fromIndex (state.actOrdered order (Grid.percept profile.taskMode observation
          result.reward result.events.done)).2.action.val,
        (state.actOrdered order (Grid.percept profile.taskMode observation result.reward
          result.events.done)).1) := rfl

/-- The words the grid agent's coder reads are the complete host word stream: the
declared channels, then the feedback of the receiver's stored predictions. -/
theorem Agent.grid_words (state : Agent Grid.interface profile config criterion dimension planning)
    (mode : TaskFeatureMode) (obs : Host.Observation) (achieved : Bool) :
    state.words (Grid.frame mode obs achieved) =
      observationWords obs
        (feedbackPredictions state.control.runtime.references.demonPredictions) mode := by
  exact congrArg (sensorWords obs mode ++ ·) (Grid.feedback_eq
    (feedbackPredictions state.control.runtime.references.demonPredictions))

/-- The grid agent's encoding of an observation is the standalone observation coder
applied to the receiver's current bank and stored predictions. -/
theorem Agent.grid_encode (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (achieved : Bool) :
    (state.frame (Grid.frame profile.taskMode obs achieved)).active =
      profile.encode dimension state.control.runtime.lifecycle.representation.bank obs
        (feedbackPredictions state.control.runtime.references.demonPredictions) := by
  change encode dimension _ (state.words (Grid.frame profile.taskMode obs achieved)) _ = _
  rw [Agent.grid_words]
  rfl

/-- Every input of one grid decision, in terms of the executed host definitions. The
percept is the frame of the observation and the reward word. Of that frame, the
coder's words and symbols, the prediction cumulants, the declared potentials and the
achievement event are the host's own. The decision is the interface agent's on
exactly these. -/
theorem Agent.grid_inputs (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (reward : Binary32) (achieved : Bool) :
    Grid.percept profile.taskMode obs reward achieved =
        ⟨Grid.frame profile.taskMode obs achieved, reward⟩ ∧
      state.words (Grid.frame profile.taskMode obs achieved) = observationWords obs
        (feedbackPredictions state.control.runtime.references.demonPredictions) profile.taskMode ∧
      (Grid.frame profile.taskMode obs achieved).symbols =
        observationPatch obs profile.taskMode ∧
      signalValues (Grid.frame profile.taskMode obs achieved) reward =
        evaluateCumulants cumulantOrder obs reward ∧
      (Grid.frame profile.taskMode obs achieved).declared = spatialPotentials obs ∧
      (Grid.frame profile.taskMode obs achieved).achieved = achieved :=
  ⟨rfl, state.grid_words profile.taskMode obs achieved, rfl,
    Grid.signalValues_eq profile.taskMode obs reward achieved, rfl, rfl⟩

/-- The frame captures the actual receiver's feedback, never a recomputed future prediction. -/
theorem Agent.observe_predictions (state : Agent Grid.interface profile config criterion dimension planning) :
    state.observe.predictions = state.control.runtime.references.demonPredictions := rfl

/-- The observer retains the exact cached model predictions of the executed transition. -/
theorem Agent.observe_models (state : Agent Grid.interface profile config criterion dimension planning) :
    state.observe.models = state.control.runtime.references.modelPredictions := rfl

/-- Learner diagnostics are a projection of current composed storage. -/
theorem Agent.observe_learners (state : Agent Grid.interface profile config criterion dimension planning) :
    state.observe.learners = Host.ensembleDiagnostics state.control.runtime.lifecycle.consumers := rfl

/-- Accounting preserves the entire action-selection owner and its pending feedback. -/
theorem Agent.environment_isolation (state : Agent Grid.interface profile config criterion dimension planning)
    (family : Fin 4) (reward : Binary32) :
    (state.recordEnvironment family reward).control.runtime = state.control.runtime ∧
    (state.recordEnvironment family reward).control.credit = state.control.credit ∧
    (state.recordEnvironment family reward).control.average = state.control.average ∧
    (state.recordEnvironment family reward).control.rate = state.control.rate := ⟨rfl, rfl, rfl, rfl⟩

/-- Attempt boundaries preserve the entire action-selection owner, including every
learner, objective and the active temporal owner, and the reward-credit state: an
attempt's outcome and its curriculum cycle reach the observations only. -/
theorem Agent.attempt_continuity (state : Agent Grid.interface profile config criterion dimension planning)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) :
    (state.recordAttempt family cycle steps achieved).control.runtime = state.control.runtime ∧
    (state.recordAttempt family cycle steps achieved).control.credit = state.control.credit ∧
    (state.recordAttempt family cycle steps achieved).control.average = state.control.average :=
  ⟨rfl, rfl, rfl⟩

end Acorn.Handcrafted
