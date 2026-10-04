/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix

/-!
# The grid agent composed directly over host observations

The executed agent meets the grid world through its interface: the host turns each
observation into a percept (`Grid.percept`) and calls `Agent.act`. This module states
the same agent the other way round, as a composition that reads the host observation
itself, and proves the two equal.

The definitions under `Direct` are a frozen reference. Each is the definition of the
same name at commit `d3bc6e0`, before the agent took an interface. Its computational
body is kept word for word, apart from naming the other frozen definitions it calls,
and only its proof arguments are restated:
`TemporalControl.initial`, `TemporalControl.finish`, `TemporalControl.step`,
`TemporalControl.alignedStep`, `Agent.initial`, `Agent.frame`, `Agent.act`,
`Agent.install`, `Agent.restore`, `PredictionControl.advance` and the `act` field of
`Agent.callbacks`. Only their state types are written at the grid instance, because
the stored types now carry the interface. No executing module imports this one.

The theorems are equalities for every agent state, observation, reward word and
achievement flag: construction, the composed transition with its returned decision,
the host's action and next state, the prefix input edge, and restoration.

What the reference does not freeze is the storage below the composition. The core
types replaced the constant nine by an action-count parameter, which the grid
instance sets to that constant, and the selection, option, model and planning
definitions the reference calls are the executed ones. A reference for them would be
a second copy of the learned core.
-/
namespace AcornVerif.GridCorrespondence
open Acorn Acorn.Features Acorn.Handcrafted

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

namespace Direct

/-- Zero knowledge, no invented prior transition, and canonical action-stream seed. -/
def initialControl (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    TemporalControl Grid.interface profile config criterion dimension :=
  ⟨⟨⟨Representation.initial _ _, Ensemble.initial config criterion dimension demonLayout
      (profile.interests config)⟩,
      TemporalReferences.cold config demonLayout none⟩,
    profile.credit.initial, by cases profile.credit <;> rfl, .initial,
    RateState.initial profile.rate, Lifetime.Stats.initial _⟩

/-- Complete one selected primitive step: primitive credit, demons, every option's
questions in a learning hierarchy, then gain, and record the frame for later search
control. -/
def finish (state : TemporalControl Grid.interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision Grid.actions) :
    TemporalControl Grid.interface profile config criterion dimension :=
  let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
    credit, creditMatches, average, rate, lifetime⟩ := state
  let cumulants := evaluateCumulants cumulantOrder obs reward
  let lifetime := { lifetime with
    options := Lifetime.recordOptions lifetime.options decision.episodeEnd decision.started }
  let view : PredictionControl Grid.interface profile criterion dimension :=
    ⟨⟨control, credit, average, references.pendingAction⟩, creditMatches, demons,
      references.demonPredictions, references.demonErrors, lifetime⟩
  let predicted := view.advanceWith features cumulants reward decision.action decision.own
    representation.progress.clock
  let skills := if profile.usesHierarchy && profile.mode != .frozen then
    askQuestions skills features cumulants decision else skills
  ⟨⟨⟨representation, ⟨predicted.control.controller, metaController, skills, predicted.demons⟩⟩,
      { references with
        demonPredictions := predicted.predictions, demonErrors := predicted.errors,
        pendingAction := predicted.control.pending, lastDecision := some decision,
        recent := references.recent.record features }⟩,
    predicted.control.credit, predicted.creditMatches, predicted.control.average, rate,
    predicted.lifetime⟩

/-- One local temporal transition: selection, off-policy learning of every option
that is not executing, the closing of an interrupted option's meta span, then credit
and feedback on every selected path. -/
def step (state : TemporalControl Grid.interface profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (goal : Bool) :
    Option (TemporalControl Grid.interface profile config criterion dimension ×
      TemporalDecision Grid.actions) := do
  let (selected, decision) ← state.select planning features (spatialPotentials obs) reward goal
  let continuation := selected.takeoverValue features (spatialPotentials obs) goal decision
  let followed := selected.followOptions (modelOperations criterion dimension) features
    (spatialPotentials obs) reward goal decision
  pure (finish (followed.closeSpan continuation) features obs reward decision, decision)

/-- One already-selected primitive transition: the signal values are evaluated once
from the observation, then `advanceWith`. -/
def advance (state : PredictionControl Grid.interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (action : Action Acorn.FeatureConstants.primitiveCount) (own : Bool) (clock : UInt64 := 0) :
    PredictionControl Grid.interface profile criterion dimension :=
  state.advanceWith features (evaluateCumulants cumulantOrder obs reward) reward action own clock

end Direct

/-- Direct construction is the interface construction at the grid instance. -/
theorem initialControl_eq (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    Direct.initialControl profile config criterion dimension =
      TemporalControl.initial Grid.interface profile config criterion dimension := rfl

/-- The direct completion boundary is the interface one on the grid frame, whatever
the frame's task mode and achievement flag. -/
theorem finish_eq (state : TemporalControl Grid.interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision Grid.actions) (mode : TaskFeatureMode) (achieved : Bool) :
    Direct.finish state features obs reward decision =
      state.finish features (Grid.frame mode obs achieved) reward decision := rfl

/-- The direct local transition is the interface one on the grid frame. -/
theorem step_eq (state : TemporalControl Grid.interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (obs : Host.Observation) (reward : Binary32) (goal : Bool) (mode : TaskFeatureMode)
    (achieved : Bool) :
    Direct.step state planning features obs reward goal =
      state.step planning features (Grid.frame mode obs achieved) reward goal := rfl

/-- The direct prediction and credit transition is the interface one on the grid frame. -/
theorem advance_eq (state : PredictionControl Grid.interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (action : Action Acorn.FeatureConstants.primitiveCount) (own : Bool) (clock : UInt64)
    (mode : TaskFeatureMode) (achieved : Bool) :
    Direct.advance state features obs reward action own clock =
      state.advance features (Grid.frame mode obs achieved) reward action own clock := rfl

namespace Direct

/-- Execute the direct local transition once. Its totality proof closes the
potential-source premise; the proof and its existential witnesses are erased. -/
def alignedStep (state : TemporalControl Grid.interface profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    { result : TemporalControl Grid.interface profile config criterion dimension ×
        TemporalDecision Grid.actions //
      step state planning features observation reward goal = some result ∧ result.1.Aligned } :=
  match executed : step state planning features observation reward goal with
  | none => False.elim (by
      obtain ⟨next, decision, accepted, _⟩ := state.step_total aligned planning features
        (Grid.frame .complete observation goal) reward goal
      rw [← step_eq, executed] at accepted
      contradiction)
  | some result => ⟨result, rfl, by
      obtain ⟨next, decision, accepted, valid⟩ := state.step_total aligned planning features
        (Grid.frame .complete observation goal) reward goal
      rw [← step_eq] at accepted
      have same := Option.some.inj (executed.symm.trans accepted)
      cases same
      exact valid⟩

/-- Complete cold initialization reuses the direct component constructor. -/
def initial (profile : FeatureProfile) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (planning : PlanningSelection) :
    Agent Grid.interface profile config criterion dimension planning :=
  ⟨initialControl profile config criterion dimension,
    TemporalControl.initial_aligned Grid.interface profile config criterion dimension,
    TemporalControl.initial_episodes Grid.interface profile config criterion dimension⟩

/-- Materialize a frame from this exact receiver, old cache and complete observation. -/
def frame (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) :
    EncodingFrame dimension state.control.runtime.lifecycle.representation.bank
      (observationWords observation
        (feedbackPredictions state.control.runtime.references.demonPredictions)
        profile.taskMode) (observationPatch observation profile.taskMode) :=
  state.control.runtime.encodeCurrent
    (observationWords observation
      (feedbackPredictions state.control.runtime.references.demonPredictions)
      profile.taskMode) (observationPatch observation profile.taskMode)

/-- The actual full decision: clock, current-bank encoding, temporal learning and
observation, then the receiver-owned tester on the same frame. The returned
decision is the one credited. -/
def act (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    Agent Grid.interface profile config criterion dimension planning ×
      TemporalDecision Grid.actions :=
  let prepared := state.advanceClock
  let frame := frame prepared observation
  let result := alignedStep prepared.control prepared.aligned planning frame.active observation
    reward goal
  let next : Agent Grid.interface profile config criterion dimension planning :=
    ⟨result.1.1, result.2.2, prepared.control.step_episodes result.1.1 prepared.episodes
      planning frame.active (Grid.frame .complete observation goal) reward goal result.1.2
      result.2.1⟩
  (next.retire frame.units, result.1.2)

/-- The host's step: raw preceding reward and terminal event are passed unchanged
to the composed core, and the chosen index becomes a host action. -/
def callbackAct (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    Host.Action × Agent Grid.interface profile config criterion dimension planning :=
  let (next, decision) := act state observation result.reward result.events.done
  (Host.Action.fromIndex decision.action.val, next)

/-- Installation resets process-local references and models, retaining admitted
knowledge, assignment identities, durable gain and lifetime observations. -/
def install (state : Agent Grid.interface profile config criterion dimension planning)
    (image : AgentImage Grid.interface config criterion dimension) :
    Agent Grid.interface profile config criterion dimension planning :=
  ⟨{ state.control with
      runtime := state.control.runtime.restore image.features none
      credit := profile.credit.initial
      creditMatches := by cases profile.credit <;> rfl
      average := state.control.average.restore image.gain
      rate := RateState.initial profile.rate
      lifetime := { image.lifetime.restore with
        agreementStarted := some image.features.progress.clock
        agreementLastClock := some image.features.progress.clock } },
    ⟨fun slot => by simp [FeatureRuntime.restore, Ensemble.restore, Interest.Aligned],
      Ensemble.restore_distinct _ _ _ image.features.distinct⟩, by
    constructor
    · intro slot
      exact image.episodes slot
    · intro _; rfl⟩

/-- Profile refusal precedes installation. No partial replacement is returned. -/
def restore (state : Agent Grid.interface profile config criterion dimension planning)
    (image : AgentImage Grid.interface config criterion dimension) :
    Option (Agent Grid.interface profile config criterion dimension planning) :=
  if profile.checkpointSupported then some (install state image) else none

end Direct

/-- Direct cold initialization is the interface agent's at the grid instance. -/
theorem initial_eq (profile : FeatureProfile) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (planning : PlanningSelection) :
    Direct.initial profile config criterion dimension planning =
      Agent.initial Grid.interface profile config criterion dimension planning := rfl

/-- The direct encoding's unit outputs are the interface agent's on the grid frame. -/
theorem frame_units (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (achieved : Bool) :
    (Direct.frame state obs).units =
      (state.frame (Grid.frame profile.taskMode obs achieved)).units := rfl

/-- The direct encoding's active set is the interface agent's on the grid frame: the
coder reads the same words, with the same feedback, and the same symbols. -/
theorem frame_active (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (achieved : Bool) :
    (Direct.frame state obs).active =
      (state.frame (Grid.frame profile.taskMode obs achieved)).active := by
  rw [(state.frame (Grid.frame profile.taskMode obs achieved)).fresh, state.grid_words]
  rfl

/-- The direct decision is obtained from the direct local transition on its own
encoding. -/
theorem act_execution (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (reward : Binary32) (goal : Bool) :
    ∃ (next : TemporalControl Grid.interface profile config criterion dimension)
      (valid : next.Aligned) (episodes : next.Episodes),
      Direct.step state.advanceClock.control planning
        (Direct.frame state.advanceClock obs).active obs reward goal =
          some (next, (Direct.act state obs reward goal).2) ∧
      (Direct.act state obs reward goal).1 =
        (Agent.mk next valid episodes).retire (Direct.frame state.advanceClock obs).units := by
  let result := Direct.alignedStep state.advanceClock.control state.advanceClock.aligned planning
    (Direct.frame state.advanceClock obs).active obs reward goal
  exact ⟨result.1.1, result.2.2, state.advanceClock.control.step_episodes result.1.1
    state.advanceClock.episodes planning (Direct.frame state.advanceClock obs).active
    (Grid.frame .complete obs goal) reward goal result.1.2 result.2.1, result.2.1, rfl⟩

/-- **The composed transition.** For every grid agent state, host observation, reward
word and achievement flag, the direct decision and the interface agent's decision on
the grid percept return the same next state and the same decision. -/
theorem act_eq (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (reward : Binary32) (goal : Bool) :
    Direct.act state obs reward goal =
      state.act (Grid.percept profile.taskMode obs reward goal) := by
  obtain ⟨direct, _, _, stepped, replaced⟩ := act_execution state obs reward goal
  obtain ⟨next, _, _, executed, installed⟩ :=
    state.act_execution (Grid.percept profile.taskMode obs reward goal)
  rw [step_eq (mode := profile.taskMode) (achieved := goal),
    frame_active state.advanceClock obs goal] at stepped
  have same := Option.some.inj (stepped.symm.trans executed)
  have controls : direct = next := (Prod.mk.inj same).1
  have decisions := (Prod.mk.inj same).2
  subst controls
  refine Prod.ext ?_ decisions
  rw [replaced, installed, frame_units state.advanceClock obs goal]
  rfl

/-- **The host's step.** The action the host executes and the agent it carries forward
are the direct composition's, for every state, observation and raw result. -/
theorem callback_eq (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (result : Host.RawStepResult) :
    Agent.callbacks.act state obs result = Direct.callbackAct state obs result := by
  rw [Agent.callbacks_act]
  simp only [Direct.callbackAct, act_eq]

/-- The prefix input edge delivers the direct composition's next state. -/
theorem input_eq (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (result : Host.RawStepResult) :
    state.input (.act obs result) =
      .ok ((Direct.act state obs result.reward result.events.done).1, false) := by
  rw [act_eq]
  rfl

/-- **Restoration.** Direct restoration is the interface agent's, including refusal. -/
theorem restore_eq (state : Agent Grid.interface profile config criterion dimension planning)
    (image : AgentImage Grid.interface config criterion dimension) :
    Direct.restore state image = state.restore image := rfl

end AcornVerif.GridCorrespondence
