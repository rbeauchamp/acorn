import Acorn.Host.AgentPrefix

namespace AcornVerif.GridCorrespondence
open Acorn Acorn.Features Acorn.Handcrafted

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

namespace Direct

def initialControl (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    TemporalControl Grid.interface profile config criterion dimension :=
  ⟨⟨⟨Representation.initial _ _, Ensemble.initial config criterion dimension demonLayout
      (profile.interests config)⟩,
      TemporalReferences.cold config demonLayout none⟩,
    profile.credit.initial, by cases profile.credit <;> rfl, .initial,
    RateState.initial profile.rate, Lifetime.Stats.initial _⟩

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
  ⟨⟨⟨representation, ⟨predicted.control.controller, metaController, skills, predicted.demons⟩⟩,
      { references with
        demonPredictions := predicted.predictions, demonErrors := predicted.errors,
        pendingAction := predicted.control.pending, lastDecision := some decision,
        recent := references.recent.record features }⟩,
    predicted.control.credit, predicted.creditMatches, predicted.control.average, rate,
    predicted.lifetime⟩

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

def advance (state : PredictionControl Grid.interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (action : Action Acorn.FeatureConstants.primitiveCount) (own : Bool) (clock : UInt64 := 0) :
    PredictionControl Grid.interface profile criterion dimension :=
  state.advanceWith features (evaluateCumulants cumulantOrder obs reward) reward action own clock

end Direct

theorem initialControl_eq (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    Direct.initialControl profile config criterion dimension =
      TemporalControl.initial Grid.interface profile config criterion dimension := rfl

theorem finish_eq (state : TemporalControl Grid.interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision Grid.actions) (mode : TaskFeatureMode) (achieved : Bool) :
    Direct.finish state features obs reward decision =
      state.finish features (Grid.frame mode obs achieved) reward decision := rfl

theorem step_eq (state : TemporalControl Grid.interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (obs : Host.Observation) (reward : Binary32) (goal : Bool) (mode : TaskFeatureMode)
    (achieved : Bool) :
    Direct.step state planning features obs reward goal =
      state.step planning features (Grid.frame mode obs achieved) reward goal := rfl

theorem advance_eq (state : PredictionControl Grid.interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (action : Action Acorn.FeatureConstants.primitiveCount) (own : Bool) (clock : UInt64)
    (mode : TaskFeatureMode) (achieved : Bool) :
    Direct.advance state features obs reward action own clock =
      state.advance features (Grid.frame mode obs achieved) reward action own clock := rfl

namespace Direct

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

def initial (profile : FeatureProfile) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (planning : PlanningSelection) :
    Agent Grid.interface profile config criterion dimension planning :=
  ⟨initialControl profile config criterion dimension,
    TemporalControl.initial_aligned Grid.interface profile config criterion dimension,
    TemporalControl.initial_episodes Grid.interface profile config criterion dimension⟩

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

def callbackAct (state : Agent Grid.interface profile config criterion dimension planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    Host.Action × Agent Grid.interface profile config criterion dimension planning :=
  let (next, decision) := act state observation result.reward result.events.done
  (Host.Action.fromIndex decision.action.val, next)

end Direct

theorem initial_eq (profile : FeatureProfile) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (planning : PlanningSelection) :
    Direct.initial profile config criterion dimension planning =
      Agent.initial Grid.interface profile config criterion dimension planning := rfl

theorem frame_units (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (achieved : Bool) :
    (Direct.frame state obs).units =
      (state.frame (Grid.frame profile.taskMode obs achieved)).units := rfl

theorem frame_active (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (achieved : Bool) :
    (Direct.frame state obs).active =
      (state.frame (Grid.frame profile.taskMode obs achieved)).active := by
  rw [(state.frame (Grid.frame profile.taskMode obs achieved)).fresh, state.grid_words]
  rfl

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

theorem callback_eq (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (result : Host.RawStepResult) :
    (Agent.callbacks .learnThenAct).act state obs result = Direct.callbackAct state obs result := by
  rw [Agent.callbacks_act]
  simp only [Direct.callbackAct, act_eq]

theorem input_eq (state : Agent Grid.interface profile config criterion dimension planning)
    (obs : Host.Observation) (result : Host.RawStepResult) :
    state.input (.act obs result) =
      ((Direct.act state obs result.reward result.events.done).1, false) := by
  rw [act_eq]
  rfl

end AcornVerif.GridCorrespondence
