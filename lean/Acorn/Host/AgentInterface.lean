import Acorn.Handcrafted.StepParts
import Acorn.Handcrafted.GridWorld
import Acorn.Host.Runner
import Acorn.Host.AgentDiagnostics

namespace Acorn.Handcrafted
open Features

def familyIndex : Host.GoalFamily → Fin 4
  | .reach => 0 | .collect => 1 | .craft => 2 | .survive => 3

def researchProfile : Host.ResearchProfile → FeatureProfile
  | .ranked => ⟨.final, .perStep, .declared, .learned⟩
  | .primitive => ⟨.primitiveOnly, .perStep, .declared, .learned⟩
  | .boundaryCredit => ⟨.final, .smdpCatchUp, .declared, .learned⟩
  | .annealed => ⟨.final, .perStep, .annealed, .learned⟩
  | .spatial => ⟨.final, .perStep, .declared, .spatial⟩

theorem researchProfile_resumable (profile : Host.ResearchProfile) :
    (researchProfile profile).checkpointSupported = profile.resumable := by
  cases profile <;> rfl

theorem researchProfile_declared (profile : Host.ResearchProfile) (ordinary : profile ≠ .annealed) :
    (researchProfile profile).rate = .declared := by
  cases profile <;> first | rfl | exact absurd rfl ordinary

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

def Agent.metrics (state : Agent Grid.interface profile config criterion dimension planning) : Host.LearnerMetrics :=
  ⟨(Binary32.sumFrom .zero state.control.runtime.references.demonErrors.toList).div
      (Binary32.ofUInt64 demonLayout.length.toUInt64),
    state.control.controlRate.value,
    (state.control.runtime.lifecycle.consumers.control.learners.get ⟨0, by decide⟩).state.meanAlpha⟩

structure AgentObservation (config : Features.Config) (dimension : Dimension) where
  clock : UInt64
  representation : Representation Host.patchShape config
  interests : Vector (Interest config) Acorn.FeatureConstants.skillCount
  predictions : PredictionCache demonLayout
  decision : Option (TemporalDecision Grid.actions)
  metrics : Host.LearnerMetrics
  gain : RewardRate
  lifetime : Lifetime.Stats demonLayout
  learners : Host.EnsembleDiagnostics demonLayout
  models : Vector ModelCache Acorn.FeatureConstants.skillCount
  planningSteps : UInt64
  planningErrors : Vector Binary32 Acorn.FeatureConstants.skillCount
  optionElapsed : ModelAge
  criterion : Criterion
  featureProfile : FeatureProfile

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

theorem Agent.callbacks_act (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    (Agent.callbacks .learnThenAct).act state observation result =
      (Host.Action.fromIndex (state.act (Grid.percept profile.taskMode observation result.reward
          result.events.done)).2.action.val,
        (state.act (Grid.percept profile.taskMode observation result.reward
          result.events.done)).1) := by
  rw [Agent.act_parts]
  rfl

theorem Agent.callbacks_ordered (order : StepOrder)
    (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    (Agent.callbacks order).act state observation result =
      (Host.Action.fromIndex (state.actOrdered order (Grid.percept profile.taskMode observation
          result.reward result.events.done)).2.action.val,
        (state.actOrdered order (Grid.percept profile.taskMode observation result.reward
          result.events.done)).1) := rfl

theorem Agent.grid_words (state : Agent Grid.interface profile config criterion dimension planning)
    (mode : TaskFeatureMode) (obs : Host.Observation) (achieved : Bool) :
    state.words (Grid.frame mode obs achieved) =
      observationWords obs
        (feedbackPredictions state.control.runtime.references.demonPredictions) mode := by
  exact congrArg (sensorWords obs mode ++ ·) (Grid.feedback_eq
    (feedbackPredictions state.control.runtime.references.demonPredictions))

theorem Agent.grid_encode (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (achieved : Bool) :
    (state.frame (Grid.frame profile.taskMode obs achieved)).active =
      profile.encode dimension state.control.runtime.lifecycle.representation.bank obs
        (feedbackPredictions state.control.runtime.references.demonPredictions) := by
  change encode dimension _ (state.words (Grid.frame profile.taskMode obs achieved)) _ = _
  rw [Agent.grid_words]
  rfl

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

theorem Agent.observe_predictions (state : Agent Grid.interface profile config criterion dimension planning) :
    state.observe.predictions = state.control.runtime.references.demonPredictions := rfl

theorem Agent.observe_models (state : Agent Grid.interface profile config criterion dimension planning) :
    state.observe.models = state.control.runtime.references.modelPredictions := rfl

theorem Agent.observe_learners (state : Agent Grid.interface profile config criterion dimension planning) :
    state.observe.learners = Host.ensembleDiagnostics state.control.runtime.lifecycle.consumers := rfl

theorem Agent.environment_isolation (state : Agent Grid.interface profile config criterion dimension planning)
    (family : Fin 4) (reward : Binary32) :
    (state.recordEnvironment family reward).control.runtime = state.control.runtime ∧
    (state.recordEnvironment family reward).control.credit = state.control.credit ∧
    (state.recordEnvironment family reward).control.average = state.control.average ∧
    (state.recordEnvironment family reward).control.rate = state.control.rate := ⟨rfl, rfl, rfl, rfl⟩

theorem Agent.attempt_continuity (state : Agent Grid.interface profile config criterion dimension planning)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) :
    (state.recordAttempt family cycle steps achieved).control.runtime = state.control.runtime ∧
    (state.recordAttempt family cycle steps achieved).control.credit = state.control.credit ∧
    (state.recordAttempt family cycle steps achieved).control.average = state.control.average :=
  ⟨rfl, rfl, rfl⟩

end Acorn.Handcrafted
