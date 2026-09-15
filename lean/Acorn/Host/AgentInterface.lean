/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Agent
import Acorn.Host.Runner
import Acorn.Host.AgentDiagnostics

/-!
# Current agent input and observation boundary

The runner callbacks call the actual composed transition and lifetime owners.
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
  | .ranked => ⟨.final, .perStep, .perLearner, .learned⟩
  | .primitive => ⟨.primitiveOnly, .perStep, .perLearner, .learned⟩
  | .boundaryCredit => ⟨.final, .smdpCatchUp, .perLearner, .learned⟩
  | .annealed => ⟨.final, .perStep, .annealed, .learned⟩
  | .spatial => ⟨.final, .perStep, .perLearner, .spatial⟩

/-- Host checkpoint admission and the actual constructed profile agree. -/
theorem researchProfile_resumable (profile : Host.ResearchProfile) :
    (researchProfile profile).checkpointSupported = profile.resumable := by
  cases profile <;> rfl

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

/-- Attempt metrics read current errors, the primitive rate, and the first primitive learner.
These are raw diagnostic numbers, without a convergence or finiteness assertion. -/
def Agent.metrics (state : Agent profile config criterion dimension planning) : Host.LearnerMetrics :=
  ⟨(Binary32.sumFrom .zero state.control.runtime.references.demonErrors.toList).div
      (Binary32.ofUInt64 demonLayout.length.toUInt64),
    (state.control.rate.controller (fun _ => state.control.primitiveRate)
      (fun _ => state.control.primitiveRate)).value,
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
  decision : Option TemporalDecision
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
@[noinline] def Agent.observe (state : Agent profile config criterion dimension planning) :
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
    | .idle | .exploring _ => 0,
    criterion, profile⟩

/-- Full-agent callbacks bind every existing host protocol operation to its actual owner. -/
def Agent.callbacks : Host.AgentCallbacks (Agent profile config criterion dimension planning)
    (AgentObservation config dimension) where
  act state observation result :=
    let (next, decision) := state.act observation result.reward result.events.done
    (Host.Action.fromIndex decision.action.val, next)
  recordEnvironment state family reward := state.recordEnvironment (familyIndex family) reward
  recordAttempt state family cycle steps achieved := state.recordAttempt (familyIndex family) cycle steps achieved
  capture := Agent.observe
  metrics := Agent.metrics

/-- Raw preceding reward and terminal event are passed unchanged to the composed core. -/
theorem Agent.callbacks_act (state : Agent profile config criterion dimension planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    (Agent.callbacks.act state observation result).2 =
      (state.act observation result.reward result.events.done).1 := rfl

/-- The frame captures the actual receiver's feedback, never a recomputed future prediction. -/
theorem Agent.observe_predictions (state : Agent profile config criterion dimension planning) :
    state.observe.predictions = state.control.runtime.references.demonPredictions := rfl

/-- The observer retains the exact cached model predictions of the executed transition. -/
theorem Agent.observe_models (state : Agent profile config criterion dimension planning) :
    state.observe.models = state.control.runtime.references.modelPredictions := rfl

/-- Learner diagnostics are a projection of current composed storage. -/
theorem Agent.observe_learners (state : Agent profile config criterion dimension planning) :
    state.observe.learners = Host.ensembleDiagnostics state.control.runtime.lifecycle.consumers := rfl

/-- Accounting preserves the entire action-selection owner and its pending feedback. -/
theorem Agent.environment_isolation (state : Agent profile config criterion dimension planning)
    (family : Fin 4) (reward : Binary32) :
    (state.recordEnvironment family reward).control.runtime = state.control.runtime ∧
    (state.recordEnvironment family reward).control.credit = state.control.credit ∧
    (state.recordEnvironment family reward).control.average = state.control.average ∧
    (state.recordEnvironment family reward).control.rate = state.control.rate := ⟨rfl, rfl, rfl, rfl⟩

/-- Attempt boundaries preserve the pending action, reward-credit state and active temporal owner. -/
theorem Agent.attempt_continuity (state : Agent profile config criterion dimension planning)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) :
    (state.recordAttempt family cycle steps achieved).control.runtime.references = state.control.runtime.references ∧
    (state.recordAttempt family cycle steps achieved).control.runtime.lifecycle = state.control.runtime.lifecycle ∧
    (state.recordAttempt family cycle steps achieved).control.credit = state.control.credit ∧
    (state.recordAttempt family cycle steps achieved).control.average = state.control.average :=
  ⟨rfl, rfl, rfl, rfl⟩

end Acorn.Handcrafted
