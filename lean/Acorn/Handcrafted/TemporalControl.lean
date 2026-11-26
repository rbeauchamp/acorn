import Acorn.Planning
import Acorn.Handcrafted.TemporalProfile
import Acorn.Handcrafted.PredictionControl

namespace Acorn.Handcrafted
open Features

structure TemporalControl (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) where
  runtime : FeatureRuntime interface.symbols interface.actions config criterion dimension interface.layout
    (OptionActivation (profile.mode != .frozen)) (CommittedRun interface.actions (profile.mode != .frozen))
    (Option (TemporalDecision interface.actions))
  credit : PrimitiveCredit
  creditMatches : creditKind credit = profile.credit
  average : AverageRewardTracker
  rate : RateState profile.rate
  lifetime : Lifetime.Stats interface.layout

def TemporalControl.initial (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) :
    TemporalControl interface profile config criterion dimension :=
  ⟨⟨⟨Representation.initial _ _, Ensemble.initial config criterion dimension interface.layout (profile.interests config)⟩,
      TemporalReferences.cold config interface.layout none⟩,
    profile.credit.initial, by cases profile.credit <;> rfl, .initial, RateState.initial profile.rate, Lifetime.Stats.initial _⟩

variable {interface : Interface} {actions : Word.Count} {profile : FeatureProfile}
  {config : Features.Config} {criterion : Criterion} {dimension : Dimension}

def TemporalControl.predictionView (state : TemporalControl interface profile config criterion dimension) :
    PredictionControl interface profile criterion dimension :=
  ⟨⟨state.runtime.lifecycle.consumers.control, state.credit, state.average, state.runtime.references.pendingAction⟩,
    state.creditMatches, state.runtime.lifecycle.consumers.demons,
    state.runtime.references.demonPredictions, state.runtime.references.demonErrors, state.lifetime⟩

def _root_.Acorn.Features.TemporalDecision.episodeEnd (decision : TemporalDecision actions) : Option Lifetime.EpisodeEnd :=
  decision.ended.map fun event =>
    let reason : Fin 3 := match event.reason with
      | .goal => 0 | .duration => 1 | .interrupted => 2
    ⟨event.slot, event.age.val.toUInt32, reason⟩

def TemporalControl.recordEpisodes (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : TemporalControl interface profile config criterion dimension :=
  { state with lifetime := { state.lifetime with
      options := Lifetime.recordOptions state.lifetime.options decision.episodeEnd decision.started } }

def TemporalControl.finish (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) : TemporalControl interface profile config criterion dimension :=
  let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
    credit, creditMatches, average, rate, lifetime⟩ := state
  let cumulants := signalValues obs reward
  let lifetime := { lifetime with
    options := Lifetime.recordOptions lifetime.options decision.episodeEnd decision.started }
  let view : PredictionControl interface profile criterion dimension :=
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

theorem TemporalControl.finish_eq (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    state.finish features obs reward decision =
    let recorded := state.recordEpisodes decision
    let cumulants := signalValues obs reward
    let predicted := recorded.predictionView.advanceWith features cumulants reward decision.action
      decision.own state.runtime.lifecycle.representation.progress.clock
    { state with
      runtime := { state.runtime with
        lifecycle := { state.runtime.lifecycle with consumers := { state.runtime.lifecycle.consumers with
          control := predicted.control.controller, demons := predicted.demons } }
        references := { state.runtime.references with
          demonPredictions := predicted.predictions, demonErrors := predicted.errors,
          pendingAction := predicted.control.pending, lastDecision := some decision,
          recent := state.runtime.references.recent.record features } }
      credit := predicted.control.credit
      creditMatches := predicted.creditMatches
      average := predicted.control.average
      lifetime := predicted.lifetime }
    := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        rfl

theorem TemporalControl.finish_skills (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.lifecycle.consumers.skills =
      state.runtime.lifecycle.consumers.skills := by
  rw [TemporalControl.finish_eq]

def TemporalControl.gap (state : TemporalControl interface profile config criterion dimension) : CreditGap :=
  ⟨state.runtime.references.gapSteps, state.runtime.references.gapReward⟩

def TemporalControl.withGap (state : TemporalControl interface profile config criterion dimension) (gap : CreditGap) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with
    gapSteps := gap.steps, gapReward := gap.reward } } }

def TemporalControl.skipMeta (state : TemporalControl interface profile config criterion dimension) :
    TemporalControl interface profile config criterion dimension :=
  if profile.usesHierarchy && profile.mode != .frozen then state.withGap state.gap.skip else state

def TemporalControl.primitiveRateCosted
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  state.runtime.lifecycle.consumers.control.exploreRateCosted (count := interface.actions)

def TemporalControl.primitiveRate (state : TemporalControl interface profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.primitiveRateCosted.val

theorem TemporalControl.primitiveRate_def
    (state : TemporalControl interface profile config criterion dimension) :
    state.primitiveRate =
      state.runtime.lifecycle.consumers.control.exploreRate (count := interface.actions) := rfl

def TemporalControl.metaRateCosted
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  state.rate.controllerCosted
    (fun _ => state.runtime.lifecycle.consumers.metaController.exploreRateCosted
      (count := metaCount))
    (fun _ => state.primitiveRateCosted)

def TemporalControl.metaRate (state : TemporalControl interface profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.metaRateCosted.val

theorem TemporalControl.metaRate_def
    (state : TemporalControl interface profile config criterion dimension) :
    state.metaRate =
      state.rate.controller
        (fun _ => state.runtime.lifecycle.consumers.metaController.exploreRate (count := metaCount))
        (fun _ => state.primitiveRate) :=
  RateState.controllerCosted_val _ _ _

def TemporalControl.controlRate (state : TemporalControl interface profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.rate.controller (fun _ => state.primitiveRate) (fun _ => state.primitiveRate)

def TemporalControl.skillRateCosted
    (state : TemporalControl interface profile config criterion dimension) :
    Costed ConsumerRate :=
  state.rate.skillCosted (fun _ => state.primitiveRateCosted)

def TemporalControl.skillRate (state : TemporalControl interface profile config criterion dimension) : ConsumerRate :=
  state.skillRateCosted.val

theorem TemporalControl.skillRate_def
    (state : TemporalControl interface profile config criterion dimension) :
    state.skillRate = state.rate.skill (fun _ => state.primitiveRate) :=
  RateState.skillCosted_val _ _

theorem TemporalControl.declared_rates (state : TemporalControl interface profile config criterion dimension)
    (declared : profile.rate = .declared) :
    state.controlRate = declaredRate ∧ state.metaRate = declaredRate ∧
      ∀ own, state.skillRate.resolve own = declaredRate := by
  refine ⟨RateState.declared_controller state.rate declared _ _,
    state.metaRate_def.trans (RateState.declared_controller state.rate declared _ _),
    fun own => ?_⟩
  simp only [TemporalControl.skillRate_def, RateState.declared_skill state.rate declared,
    ConsumerRate.resolve]

def TemporalControl.valueFunctionCosted
    (state : TemporalControl interface profile config criterion dimension) :
    Costed (ValueFunction criterion dimension) := do
  let rate ← state.metaRateCosted
  Costed.pure ⟨state.runtime.lifecycle.consumers.metaController, rate⟩

def TemporalControl.valueFunction (state : TemporalControl interface profile config criterion dimension) :
    ValueFunction criterion dimension :=
  state.valueFunctionCosted.val

theorem TemporalControl.valueFunction_def
    (state : TemporalControl interface profile config criterion dimension) :
    state.valueFunction = ⟨state.runtime.lifecycle.consumers.metaController, state.metaRate⟩ :=
  rfl

def TemporalControl.withSkill (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (skill : Skill interface.actions config criterion dimension interface.layout) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with lifecycle := { state.runtime.lifecycle with
    consumers := { state.runtime.lifecycle.consumers with
      skills := state.runtime.lifecycle.consumers.skills.set slot.val skill slot.isLt } } } }

def TemporalControl.withPhase (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen)) (CommittedRun interface.actions (profile.mode != .frozen))) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with phase } } }

def TemporalControl.withoutPlanning (state : TemporalControl interface profile config criterion dimension) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with
    planningErrors := Vector.replicate _ .zero } } }

def TemporalControl.choosePrimitive (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions :=
  let snapshot := state.runtime.lifecycle.consumers.control.snapshot (count := interface.actions) features state.controlRate
  let drawn := snapshot.drawPersistent state.runtime.references.rng
  let state := state.withPhase (Occupancy.afterPrimitive drawn.1.run)
  let state := { state with runtime := { state.runtime with references := { state.runtime.references with rng := drawn.2 } } }
  (state, ⟨if drawn.1.explored then .explorationStart else .primitive,
    drawn.1.action, snapshot.values, drawn.1.probabilities, drawn.1.explored,
    metaValues, metaDecision, none, ended⟩)

def TemporalControl.interrupt (state : TemporalControl interface profile config criterion dimension)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) :
    TemporalControl interface profile config criterion dimension × Option EndEvent :=
  match origin with
  | none => (state, none)
  | some (slot, activation) =>
    (if activation.learning then
        state.withSkill slot
          { state.runtime.lifecycle.consumers.skills.get slot with
            following := some activation.following }
      else state,
      some ⟨slot, activation.age, .interrupted⟩)

theorem TemporalControl.interrupt_frame (state : TemporalControl interface profile config criterion dimension)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) :
    (state.interrupt origin).1.lifetime = state.lifetime ∧
      (state.interrupt origin).1.runtime.references = state.runtime.references ∧
      (state.interrupt origin).2.map (·.slot) = origin.map (·.1) := by
  cases origin with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some held =>
    obtain ⟨slot, activation⟩ := held
    refine ⟨?_, ?_, rfl⟩
    all_goals
      unfold TemporalControl.interrupt
      dsimp only
      split <;> rfl

def TemporalControl.serve (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) :=
  match state.runtime.references.phase with
  | .exploring committed => do
    let (action, next) ← committed.run.serve
    let interrupted := state.interrupt committed.origin
    let state := interrupted.1.withPhase (.exploring (.bare next))
    let state := if committed.origin.isSome then state else state.skipMeta
    let state := if profile.usesHierarchy then state.withoutPlanning else state
    let values := state.runtime.lifecycle.consumers.control.predictAll features
    let metaValues := if profile.usesHierarchy then state.runtime.lifecycle.consumers.metaController.predictAll features
      else Vector.replicate _ .zero
    pure (state, ⟨.explorationContinuation, action, values, servedProbabilities action, true,
      metaValues, none, none, interrupted.2⟩)
  | .idle | .option _ _ => none

theorem TemporalControl.serve_frame (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (served : state.serve features = some (next, decision)) :
    ∃ committed rest, state.runtime.references.phase = .exploring committed ∧
      committed.run.serve = some (decision.action, rest) ∧
      decision.source = .explorationContinuation ∧
      next.runtime.references.phase = .exploring (.bare rest) ∧
      next.runtime.references.rng = state.runtime.references.rng := by
  unfold TemporalControl.serve at served
  cases phase : state.runtime.references.phase with
  | idle => simp [phase] at served
  | option slot activation => simp [phase] at served
  | exploring committed =>
    simp only [phase] at served
    cases hs : committed.run.serve with
    | none => simp [hs] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq] at served
      cases served
      refine ⟨committed, pair.2, rfl, hs, rfl, ?_, ?_⟩
      · unfold TemporalControl.skipMeta
        repeat' split
        all_goals rfl
      · unfold TemporalControl.skipMeta
        repeat' split
        all_goals exact congrArg (·.rng) (state.interrupt_frame committed.origin).2.1

def TemporalControl.stepOption (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : (OptionActivation (profile.mode != .frozen))) (next : OptionContinuation interface.actions dimension activation)
    (reward : Binary32) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool) (ended : Option EndEvent) :
    TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions :=
  let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
    credit, creditMatches, average, rate, lifetime⟩ := state
  let stepped := detachedUpdate skills slot fun skill =>
    skill.stepTemporal models activation next reward average.rate references.rng
  let decision := stepped.2.2.1
  (⟨⟨⟨representation, ⟨control, metaController, stepped.1, demons⟩⟩,
      { references with
        phase := Occupancy.afterOption slot stepped.2.1 decision.run, rng := stepped.2.2.2 }⟩,
      credit, creditMatches, average, rate, lifetime⟩,
    ⟨.option slot, decision.action, next.policy.values, decision.probabilities,
      decision.explored, metaValues, metaDecision, if started then some slot else none, ended⟩)

theorem TemporalControl.stepOption_eq (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : (OptionActivation (profile.mode != .frozen))) (next : OptionContinuation interface.actions dimension activation)
    (reward : Binary32) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool) (ended : Option EndEvent) :
    state.stepOption models slot activation next reward metaValues metaDecision started ended =
      let skill := state.runtime.lifecycle.consumers.skills.get slot
      let result := skill.stepTemporal models activation next reward state.average.rate
        state.runtime.references.rng
      let state := (state.withSkill slot result.1).withPhase
        (Occupancy.afterOption slot result.2.1 result.2.2.1.run)
      let state := { state with runtime := { state.runtime with references :=
        { state.runtime.references with rng := result.2.2.2 } } }
      let decision := result.2.2.1
      (state, ⟨.option slot, decision.action, next.policy.values, decision.probabilities,
        decision.explored, metaValues, metaDecision, if started then some slot else none, ended⟩) := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        simp only [TemporalControl.stepOption, detachedUpdate_eq]
        rfl

def TemporalControl.closeOption (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) : TemporalControl interface profile config criterion dimension × EndEvent :=
  let state := match closing.oldOwner with
    | some _ => state
    | none =>
      let value := state.valueFunction
      let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
        credit, creditMatches, average, rate, lifetime⟩ := state
      let ended := detachedUpdate skills closing.slot fun skill =>
        (skill.endTemporal models value features closing.activation reward terminal average.rate,
          ())
      ⟨⟨⟨representation, ⟨control, metaController, ended.1, demons⟩⟩, references⟩,
        credit, creditMatches, average, rate, lifetime⟩
  (state, ⟨closing.slot, closing.activation.activation.age, closing.activation.reason⟩)

theorem TemporalControl.closeOption_eq (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    state.closeOption models features closing reward terminal =
      let owner := closing.oldOwner.getD (state.runtime.lifecycle.consumers.skills.get closing.slot)
      let ended := owner.endTemporal models state.valueFunction features closing.activation reward
        terminal state.average.rate
      let state := match closing.oldOwner with
        | none => state.withSkill closing.slot ended
        | some _ => state
      (state, ⟨closing.slot, closing.activation.activation.age, closing.activation.reason⟩) := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        unfold TemporalControl.closeOption
        cases closing.oldOwner with
        | some owner => rfl
        | none =>
          simp only [detachedUpdate_eq]
          rfl

def TemporalControl.refreshFree (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    TemporalControl interface profile config criterion dimension × Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))) :=
  let free : FreeDispatch interface.symbols interface.actions config criterion dimension interface.signals (EndingPayload (profile.mode != .frozen)) :=
    ⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩
  let free := free.refreshModels profile.ranksSubtasks
  ({ state with runtime := { state.runtime with
    lifecycle := free.lifecycle
    references := { state.runtime.references with modelPredictions := free.predictions } } }, free.closing)

theorem TemporalControl.refreshFree_assigns (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).1.runtime.lifecycle =
      ((⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩ :
        FreeDispatch interface.symbols interface.actions config criterion dimension interface.signals
          (EndingPayload (profile.mode != .frozen))).refreshModels true).lifecycle := by
  simp only [TemporalControl.refreshFree, learned]

def TemporalControl.planFree (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout) (features : SwiftTd.ActiveSet dimension) :
    TemporalControl interface profile config criterion dimension :=
  let planning : PlanningResult criterion dimension := ⟨state.runtime.lifecycle.consumers.metaController,
    state.runtime.references.modelPredictions, state.runtime.references.planningSteps, state.runtime.references.planningErrors,
    state.runtime.references.recent⟩
  let planning := if profile.mode == .frozen then { planning with errors := Vector.replicate _ .zero }
    else plan planning state.runtime.lifecycle.consumers.skills features state.average.rate
      state.metaRate
  { state with runtime := { state.runtime with
    lifecycle := { state.runtime.lifecycle with consumers := { state.runtime.lifecycle.consumers with metaController := planning.controller } }
    references := { state.runtime.references with
      modelPredictions := planning.predictions
      planningSteps := planning.steps
      planningErrors := planning.errors
      recent := planning.recent } } }

def TemporalControl.drawMeta (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    TemporalControl interface profile config criterion dimension × PolicyDecision metaCount :=
  let drawn := (state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount) features state.metaRate).draw state.runtime.references.rng
  ({ state with runtime := { state.runtime with references := { state.runtime.references with rng := drawn.2 } } }, drawn.1)

def TemporalControl.learnMeta (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    TemporalControl interface profile config criterion dimension :=
  if profile.mode == .frozen then state else
    let owed := state.gap.close
    let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
      credit, creditMatches, average, rate, lifetime⟩ := state
    let controller := metaController.policyStep features decision
      (criterion.center owed.1 owed.2 average.rate) owed.2
    ⟨⟨⟨representation, ⟨control, controller, skills, demons⟩⟩,
        { references with gapSteps := CreditGap.closed.steps, gapReward := CreditGap.closed.reward }⟩,
      credit, creditMatches, average, rate, lifetime⟩

theorem TemporalControl.learnMeta_eq (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    state.learnMeta features decision =
      if profile.mode == .frozen then state else
        let owed := state.gap.close
        let controller := state.runtime.lifecycle.consumers.metaController.policyStep features
          decision (criterion.center owed.1 owed.2 state.average.rate) owed.2
        let state := state.withGap .closed
        { state with runtime := { state.runtime with lifecycle := { state.runtime.lifecycle with
          consumers := { state.runtime.lifecycle.consumers with metaController := controller } } } } := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        rfl

def skillOfMeta (action : Action metaCount.word.toNat) : Option (Fin Acorn.FeatureConstants.skillCount) :=
  if h : action.val = 0 then none else
    some ⟨action.val - 1, by have bound := action.isLt; change action.val < 4 at bound; change action.val - 1 < 3; omega⟩

def TemporalControl.dispatchMeta (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount)
    (ended : Option EndEvent) : Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) := do
  let state := state.learnMeta features decision
  match skillOfMeta decision.action with
  | none => pure (state.choosePrimitive features decision.snapshot.values (some decision) ended)
  | some slot =>
    let potential ← (state.runtime.lifecycle.consumers.skills.get slot).interest.potential
      features declared
    let value := state.valueFunction
    let skillRate := state.skillRate
    let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
      credit, creditMatches, average, rate, lifetime⟩ := state
    let begun := detachedUpdate skills slot fun skill =>
      (skill.settleTemporal models value features potential goal
        (comparisonValue criterion decision.snapshot) skillRate reward average.rate
        (profile.mode != .frozen)).beginTemporal models features potential
          (profile.mode != .frozen) skillRate
    let state : TemporalControl interface profile config criterion dimension :=
      ⟨⟨⟨representation, ⟨control, metaController, begun.1, demons⟩⟩, references⟩,
        credit, creditMatches, average, rate, lifetime⟩
    pure (state.stepOption models slot begun.2.1 begun.2.2 reward
      decision.snapshot.values (some decision) true ended)

theorem TemporalControl.dispatchMeta_eq (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    state.dispatchMeta models features declared reward goal decision ended = (do
      let state := state.learnMeta features decision
      match skillOfMeta decision.action with
      | none => pure (state.choosePrimitive features decision.snapshot.values (some decision) ended)
      | some slot =>
        let skill := state.runtime.lifecycle.consumers.skills.get slot
        let potential ← skill.interest.potential features declared
        let settled := skill.settleTemporal models state.valueFunction features potential goal
          (comparisonValue criterion decision.snapshot) state.skillRate reward state.average.rate
          (profile.mode != .frozen)
        let begun := settled.beginTemporal models features potential (profile.mode != .frozen)
          state.skillRate
        pure ((state.withSkill slot begun.1).stepOption models slot begun.2.1 begun.2.2 reward
          decision.snapshot.values (some decision) true ended)) := by
  unfold TemporalControl.dispatchMeta
  generalize state.learnMeta features decision = learned
  cases learned with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        dsimp only
        split
        · rfl
        · simp only [detachedUpdate_eq]
          rfl

def TemporalControl.atBoundary (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) (ended : Option EndEvent) :
    Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) :=
  let refreshed := state.refreshFree closing
  let drawn := (refreshed.1.planFree plan features).drawMeta features
  let decision := drawn.2
  let (state, ended) := match refreshed.2 with
    | none => (drawn.1, ended)
    | some closing =>
      let result := drawn.1.closeOption models features closing reward decision.continuation
      (result.1, some result.2)
  state.dispatchMeta models features declared reward goal decision ended

def TemporalControl.prepareSelection (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : TemporalControl interface profile config criterion dimension :=
  let state := { state with rate := state.rate.advance }
  let state := if profile.usesHierarchy && profile.mode != .frozen then
    state.withGap (state.gap.accumulate reward criterion.rule.gamma) else state
  let state := if profile.usesHierarchy then
    { state with runtime := { state.runtime with references := { state.runtime.references with
      modelPredictions := state.runtime.lifecycle.consumers.skills.map
        (fun skill => models.predict skill.model state.valueFunction features) } } }
    else state
  state

def TemporalControl.selectWithOperations (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) := do
  let state := state.prepareSelection models features reward
  if let some result := state.serve features then
    return result
  if !profile.usesHierarchy then
    return (state.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero) none none
  let phase := state.runtime.references.phase
  let state := state.withPhase .idle
  match phase with
  | .idle | .exploring _ => state.atBoundary models plan features declared reward goal none none
  | .option slot activation =>
    let skill := state.runtime.lifecycle.consumers.skills.get slot
    let potential ← skill.interest.potential features declared
    let metaPolicy := state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount) features state.metaRate
    let estimate := comparisonValue criterion metaPolicy
    match skill.decideOption activation features potential goal estimate state.skillRate with
    | .continuing next =>
      let result := state.withoutPlanning.stepOption models slot activation next reward metaPolicy.values none false none
      pure (result.1.skipMeta, result.2)
    | .ending reason =>
      let closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)) :=
        ⟨slot, ⟨activation, potential, reason⟩, none⟩
      match criterion with
      | .differential => state.atBoundary models plan features declared reward goal (some closing) none
      | .discounted =>
        let result := state.closeOption models features closing reward estimate
        result.1.atBoundary models plan features declared reward goal none (some result.2)

def TemporalControl.activeSlot (state : TemporalControl interface profile config criterion dimension) :
    Option (Fin Acorn.FeatureConstants.skillCount) :=
  state.runtime.references.phase.executing

def TemporalControl.stoppingEstimateCosted
    (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : Costed Binary32 :=
  match decision.metaDecision with
  | some drawn => comparisonValueCosted criterion drawn.snapshot
  | none => do
    let rate ← state.metaRateCosted
    comparisonValueCosted criterion (⟨decision.metaValues, rate⟩ : PolicySnapshot metaCount)

def TemporalControl.stoppingEstimate (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : Binary32 :=
  (state.stoppingEstimateCosted decision).val

theorem TemporalControl.stoppingEstimate_def
    (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) :
    state.stoppingEstimate decision =
      match decision.metaDecision with
      | some drawn => comparisonValue criterion drawn.snapshot
      | none => comparisonValue criterion
          (⟨decision.metaValues, state.metaRate⟩ : PolicySnapshot metaCount) := by
  unfold TemporalControl.stoppingEstimate TemporalControl.stoppingEstimateCosted
  cases decision.metaDecision <;> rfl

def followSlotCosted (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32) (gain : RewardRate)
    (executing : Bool) (skill : Skill interface.actions config criterion dimension interface.layout) :
    Costed (Skill interface.actions config criterion dimension interface.layout) :=
  Costed.ite (executing = true) (fun _ => Costed.op .unlinkSlot { skill with following := none })
    fun _ => do
      let potential? ← skill.interest.potentialCosted features declared
      match potential? with
      | some potential =>
        skill.followTemporalCosted models value features potential goal estimate rate action
          behaviour reward gain
      | none => Costed.op .unlinkSlot { skill with following := none }

def followSlot (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32) (gain : RewardRate)
    (executing : Bool) (skill : Skill interface.actions config criterion dimension interface.layout) :
    Skill interface.actions config criterion dimension interface.layout :=
  (followSlotCosted models value features declared goal estimate rate action behaviour reward gain
    executing skill).val

theorem followSlot_def (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32) (gain : RewardRate)
    (executing : Bool) (skill : Skill interface.actions config criterion dimension interface.layout) :
    followSlot models value features declared goal estimate rate action behaviour reward gain
        executing skill =
      if executing then { skill with following := none } else
        match skill.interest.potential features declared with
        | some potential =>
          skill.followTemporal models value features potential goal estimate rate action behaviour
            reward gain
        | none => { skill with following := none } := by
  cases executing
  · show (skill.interest.potentialCosted features declared >>= fun potential? =>
        match potential? with
        | some potential =>
          skill.followTemporalCosted models value features potential goal estimate rate action
            behaviour reward gain
        | none => Costed.op .unlinkSlot { skill with following := none }).val =
      match (skill.interest.potentialCosted features declared).val with
      | some potential =>
        skill.followTemporal models value features potential goal estimate rate action behaviour
          reward gain
      | none => { skill with following := none }
    rw [Costed.bind_val]
    cases (skill.interest.potentialCosted features declared).val <;> rfl
  · rfl

def TemporalControl.followOptionsCosted
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    Costed (TemporalControl interface profile config criterion dimension) :=
  Costed.ite ((profile.usesHierarchy && profile.mode != .frozen) = true)
    (fun _ => do
      let estimate ← state.stoppingEstimateCosted decision
      let rate ← state.skillRateCosted
      let executing := state.activeSlot
      let value ← state.valueFunctionCosted
      let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
        credit, creditMatches, average, schedule, lifetime⟩ := state
      let followed ← Costed.mapFinIdx skills fun index skill bound =>
        followSlotCosted models value features declared goal estimate rate decision.action
          decision.probabilities reward average.rate (executing == some ⟨index, bound⟩) skill
      Costed.op .followTable
        ⟨⟨⟨representation, ⟨control, metaController, followed, demons⟩⟩, references⟩,
          credit, creditMatches, average, schedule, lifetime⟩)
    fun _ => Costed.op .followTable state

def TemporalControl.followOptions (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  (state.followOptionsCosted models features declared reward goal decision).val

theorem TemporalControl.followOptions_eq (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions) :
    state.followOptions models features declared reward goal decision =
      if profile.usesHierarchy && profile.mode != .frozen then
        { state with runtime := { state.runtime with lifecycle := { state.runtime.lifecycle with
          consumers := { state.runtime.lifecycle.consumers with
            skills := state.runtime.lifecycle.consumers.skills.mapFinIdx fun index skill bound =>
              followSlot models state.valueFunction features declared goal
                (state.stoppingEstimate decision) state.skillRate decision.action
                decision.probabilities reward state.average.rate
                (state.activeSlot == some ⟨index, bound⟩) skill } } } }
      else state := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        rfl

def TemporalControl.takeoverValue (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (decision : TemporalDecision interface.actions) : Option Binary32 :=
  if profile.usesHierarchy && profile.mode != .frozen &&
      decision.source == .explorationContinuation then
    decision.ended.map fun event =>
      let skill := state.runtime.lifecycle.consumers.skills.get event.slot
      let estimate := state.stoppingEstimate decision
      match skill.following, skill.interest.potential features declared with
      | some following, some potential =>
        match skill.decideOption following.activation features potential goal estimate
          state.skillRate with
        | .continuing _ => decision.metaValues.get (metaOfSkill event.slot)
        | .ending _ => estimate
      | _, _ => estimate
  else none

def TemporalControl.closeSpan (state : TemporalControl interface profile config criterion dimension)
    (continuation : Option Binary32) : TemporalControl interface profile config criterion dimension :=
  match continuation with
  | none => state
  | some value =>
    let owed := state.gap.close
    let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
      credit, creditMatches, average, rate, lifetime⟩ := state
    let controller := metaController.closeStep
      (criterion.center owed.1 owed.2 average.rate) value owed.2
    ⟨⟨⟨representation, ⟨control, controller, skills, demons⟩⟩,
        { references with gapSteps := CreditGap.closed.steps, gapReward := CreditGap.closed.reward }⟩,
      credit, creditMatches, average, rate, lifetime⟩

theorem TemporalControl.closeSpan_eq (state : TemporalControl interface profile config criterion dimension)
    (value : Binary32) :
    state.closeSpan (some value) =
      let owed := state.gap.close
      let controller := state.runtime.lifecycle.consumers.metaController.closeStep
        (criterion.center owed.1 owed.2 state.average.rate) value owed.2
      let state := state.withGap .closed
      { state with runtime := { state.runtime with lifecycle := { state.runtime.lifecycle with
        consumers := { state.runtime.lifecycle.consumers with metaController := controller } } } } := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        rfl

def TemporalControl.select (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) :=
  state.selectWithOperations (modelOperations criterion dimension) (planningBoundary planning)
    features declared reward goal

def TemporalControl.step (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) := do
  let (selected, decision) ← state.select planning features obs.declared reward goal
  let continuation := selected.takeoverValue features obs.declared goal decision
  let followed := selected.followOptions (modelOperations criterion dimension) features
    obs.declared reward goal decision
  pure ((followed.closeSpan continuation).finish features obs reward decision, decision)

def TemporalControl.learn (selected : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  let continuation := selected.takeoverValue features obs.declared goal decision
  let followed := selected.followOptions (modelOperations criterion dimension) features
    obs.declared reward goal decision
  (followed.closeSpan continuation).finish features obs reward decision

theorem TemporalControl.step_parts (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32) (goal : Bool) :
    state.step planning features obs reward goal =
      (state.select planning features obs.declared reward goal).map fun selected =>
        (selected.1.learn features obs reward goal selected.2, selected.2) := by
  unfold TemporalControl.step
  cases state.select planning features obs.declared reward goal with
  | none => rfl
  | some selected =>
    obtain ⟨selected, decision⟩ := selected
    rfl

theorem TemporalControl.finish_credit (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.lifecycle.consumers.control =
      (state.predictionView.advance features obs reward decision.action decision.own).control.controller := by
  by_cases frozen : profile.mode = .frozen <;>
    simp [TemporalControl.finish_eq, TemporalControl.predictionView, PredictionControl.advance,
      PredictionControl.advanceWith, TemporalControl.recordEpisodes, frozen]

end Acorn.Handcrafted
