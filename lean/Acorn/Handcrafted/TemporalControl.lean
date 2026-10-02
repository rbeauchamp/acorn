/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Planning
import Acorn.Handcrafted.TemporalProfile
import Acorn.Handcrafted.PredictionControl

/-!
# Current local temporal-control composition

This dispatcher consumes one already-encoded observation and its preceding
reward. It composes persistent exploration, option policies, assignment refresh,
SMDP meta credit, off-policy option learning, primitive credit, prediction
feedback and the old-gain clock.
The full agent supplies encoding/retirement order. Model learning and the selected
planning algorithm execute the current managed owners. No attempt timeout is a termination input.

Sutton, Precup & Singh, *Between MDPs and semi-MDPs*, Artificial Intelligence
112 (1999), equations (8)–(9), p. 190 and §6, pp. 204–205, supplies the SMDP
and intra-option forms. Acorn's PAR-9 uses executed-action Sarsa, and PAR-15
centers every layer with one shared pre-observation gain. For the executing
option, nominal epsilon means are used only for interruption, and differential
terminal credit uses the next sampled meta action after refresh and planning.

After selection, every option that is not executing learns from the action
actually taken (PAR-17): Sutton, Machado et al., *Reward-respecting subtasks for
model-based reinforcement learning*, Artificial Intelligence 324 (2023), 104001,
arXiv:2202.03466v4, §3, equation (10) and §4, equation (17). The executing option
keeps its on-policy update, and an ending option's terminal credit keeps its owner.
A stop of an option that is not executing credits the nominal meta value in both
criteria, since no meta action is drawn for it. An option selected to start
executing first settles the transition it was following.
-/
namespace Acorn.Handcrafted
open Features

/-- Local temporal state uses the actual receiver-owned representation and learners. -/
structure TemporalControl (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) where
  /-- One common lifecycle storage owner and exclusive phase. -/
  runtime : FeatureRuntime Host.patchShape config criterion dimension demonLayout
    (OptionActivation (profile.mode != .frozen)) (ExploratoryRun primitiveCount) (Option TemporalDecision)
  /-- Profile-fixed primitive credit and its optional deferred span. -/
  credit : PrimitiveCredit
  /-- Credit payload cannot change the immutable policy. -/
  creditMatches : creditKind credit = profile.credit
  /-- Shared host-transition gain, read before any hierarchy update. -/
  average : AverageRewardTracker
  /-- Schedule payload belongs only to its immutable rate policy. -/
  rate : RateState profile.rate
  /-- Fixed-memory observations have no reader on the policy-selection path. -/
  lifetime : Lifetime.Stats demonLayout

/-- Zero knowledge, no invented prior transition, and canonical action-stream seed. -/
def TemporalControl.initial (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) : TemporalControl profile config criterion dimension :=
  ⟨⟨⟨Representation.initial _ _, Ensemble.initial config criterion dimension demonLayout (profile.interests config)⟩,
      Refresh.cold false, TemporalReferences.cold config demonLayout none⟩,
    profile.credit.initial, by cases profile.credit <;> rfl, .initial, RateState.initial profile.rate, Lifetime.Stats.initial _⟩

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion} {dimension : Dimension}

/-- A view transfers the same controller and demon values to the already-proved
prediction/credit operation; no second learner implementation or storage is maintained. -/
def TemporalControl.predictionView (state : TemporalControl profile config criterion dimension) :
    PredictionControl profile criterion dimension :=
  ⟨⟨state.runtime.lifecycle.consumers.control, state.credit, state.average, state.runtime.references.pendingAction⟩,
    state.creditMatches, state.runtime.lifecycle.consumers.demons,
    state.runtime.references.demonPredictions, state.runtime.references.demonErrors, state.lifetime⟩

/-- Lifetime payload derives its slot, age and reason from the actual consumed activation. -/
def _root_.Acorn.Features.TemporalDecision.episodeEnd (decision : TemporalDecision) : Option Lifetime.EpisodeEnd :=
  decision.ended.map fun event =>
    let reason : Fin 3 := match event.reason with
      | .goal => 0 | .duration => 1 | .interrupted => 2
    ⟨event.slot, event.age.val.toUInt32, reason⟩

/-- Account for actual option endings before starts at the same decision boundary. -/
def TemporalControl.recordEpisodes (state : TemporalControl profile config criterion dimension)
    (decision : TemporalDecision) : TemporalControl profile config criterion dimension :=
  { state with lifetime := { state.lifetime with
      options := Lifetime.recordOptions state.lifetime.options decision.episodeEnd decision.started } }

/-- Complete one selected primitive step: primitive credit, demons, then gain.
Every selection branch uses this single completion boundary. Retirement is the
full-agent owner's next operation, after every learner has consumed this frame. -/
def TemporalControl.finish (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision) : TemporalControl profile config criterion dimension :=
  let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, refresh, references⟩,
    credit, creditMatches, average, rate, lifetime⟩ := state
  let lifetime := { lifetime with
    options := Lifetime.recordOptions lifetime.options decision.episodeEnd decision.started }
  let view : PredictionControl profile criterion dimension :=
    ⟨⟨control, credit, average, references.pendingAction⟩, creditMatches, demons,
      references.demonPredictions, references.demonErrors, lifetime⟩
  let predicted := view.advance features obs reward decision.action decision.own
    representation.progress.clock
  ⟨⟨⟨representation, ⟨predicted.control.controller, metaController, skills, predicted.demons⟩⟩,
      refresh, { references with
        demonPredictions := predicted.predictions, demonErrors := predicted.errors,
        pendingAction := predicted.control.pending, lastDecision := some decision }⟩,
    predicted.control.credit, predicted.creditMatches, predicted.control.average, rate,
    predicted.lifetime⟩

/-- Consuming the ensemble before learner updates preserves the complete
composition for every state, observation, reward word and selected decision. -/
theorem TemporalControl.finish_eq (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision) :
    state.finish features obs reward decision =
    let recorded := state.recordEpisodes decision
    let predicted := recorded.predictionView.advance features obs reward decision.action decision.own
      state.runtime.lifecycle.representation.progress.clock
    { state with
      runtime := { state.runtime with
        lifecycle := { state.runtime.lifecycle with consumers := { state.runtime.lifecycle.consumers with
          control := predicted.control.controller, demons := predicted.demons } }
        references := { state.runtime.references with
          demonPredictions := predicted.predictions, demonErrors := predicted.errors,
          pendingAction := predicted.control.pending, lastDecision := some decision } }
      credit := predicted.control.credit
      creditMatches := predicted.creditMatches
      average := predicted.control.average
      lifetime := predicted.lifetime }
    := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle refresh references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        rfl

/-- Meta span is the existing byte-bounded credit gap, observed without copying its algorithm. -/
def TemporalControl.gap (state : TemporalControl profile config criterion dimension) : CreditGap :=
  ⟨state.runtime.references.gapSteps, state.runtime.references.gapReward⟩

/-- Write a complete span together. -/
def TemporalControl.withGap (state : TemporalControl profile config criterion dimension) (gap : CreditGap) :
    TemporalControl profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with
    gapSteps := gap.steps, gapReward := gap.reward } } }

/-- Advance the deferred meta clock only when a learning hierarchy skipped its decision. -/
def TemporalControl.skipMeta (state : TemporalControl profile config criterion dimension) :
    TemporalControl profile config criterion dimension :=
  if profile.usesHierarchy && profile.mode != .frozen then state.withGap state.gap.skip else state

/-- The primitive learner's PAR-10 rate, the sole source of the explicitly shared rate. -/
def TemporalControl.primitiveRate (state : TemporalControl profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.runtime.lifecycle.consumers.control.exploreRate (count := primitiveCount)

/-- Resolve the meta rate against its own learner or the declared common source. -/
def TemporalControl.metaRate (state : TemporalControl profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.rate.controller
    (fun _ => state.runtime.lifecycle.consumers.metaController.exploreRate (count := metaCount))
    (fun _ => state.primitiveRate)

/-- The primitive source cannot accidentally read a different controller. -/
def TemporalControl.controlRate (state : TemporalControl profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.rate.controller (fun _ => state.primitiveRate) (fun _ => state.primitiveRate)

/-- Options resolve their own rates only after a possible invocation reset. -/
def TemporalControl.skillRate (state : TemporalControl profile config criterion dimension) : ConsumerRate :=
  state.rate.skill (fun _ => state.primitiveRate)

/-- Under the declared policy the primitive controller, the meta-controller and
every option read the declared D6 word at every state, whatever any learner
would derive. These are the only rates the dispatcher's snapshots consume. -/
theorem TemporalControl.declared_rates (state : TemporalControl profile config criterion dimension)
    (declared : profile.rate = .declared) :
    state.controlRate = declaredRate ∧ state.metaRate = declaredRate ∧
      ∀ own, state.skillRate.resolve own = declaredRate := by
  refine ⟨RateState.declared_controller state.rate declared _ _,
    RateState.declared_controller state.rate declared _ _, fun own => ?_⟩
  simp only [TemporalControl.skillRate, RateState.declared_skill state.rate declared,
    ConsumerRate.resolve]

/-- Replace exactly one option's managed storage. -/
def TemporalControl.withSkill (state : TemporalControl profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (skill : Skill config criterion dimension) :
    TemporalControl profile config criterion dimension :=
  { state with runtime := { state.runtime with lifecycle := { state.runtime.lifecycle with
    consumers := { state.runtime.lifecycle.consumers with
      skills := state.runtime.lifecycle.consumers.skills.set slot.val skill slot.isLt } } } }

/-- Occupancy is written atomically, so exploration and an option cannot coexist. -/
def TemporalControl.withPhase (state : TemporalControl profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen)) (ExploratoryRun primitiveCount)) :
    TemporalControl profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with phase } } }

/-- Non-planning hierarchy branches clear only the last diagnostic errors. -/
def TemporalControl.withoutPlanning (state : TemporalControl profile config criterion dimension) :
    TemporalControl profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with
    planningErrors := Vector.replicate _ .zero } } }

/-- Fresh primitive choice consumes branch, duration/action or greedy draws in order. -/
def TemporalControl.choosePrimitive (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    TemporalControl profile config criterion dimension × TemporalDecision :=
  let snapshot := state.runtime.lifecycle.consumers.control.snapshot (count := primitiveCount) features state.controlRate
  let drawn := snapshot.drawPersistent state.runtime.references.rng
  let phase := match drawn.1.run with
    | some run => if run.remaining.val > 0 then .exploring run else .idle
    | none => .idle
  let state := state.withPhase phase
  let state := { state with runtime := { state.runtime with references := { state.runtime.references with rng := drawn.2 } } }
  (state, ⟨if drawn.1.explored then .explorationStart else .primitive,
    drawn.1.action, snapshot.values, drawn.1.probabilities, drawn.1.explored,
    metaValues, metaDecision, none, ended⟩)

/-- A continuing run bypasses every option/meta draw and preserves random state. -/
def TemporalControl.serve (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Option (TemporalControl profile config criterion dimension × TemporalDecision) :=
  match state.runtime.references.phase with
  | .exploring run => do
    let (action, next) ← run.serve
    let state := (state.withPhase (.exploring next)).skipMeta
    let state := if profile.usesHierarchy then state.withoutPlanning else state
    let values := state.runtime.lifecycle.consumers.control.predictAll features
    let metaValues := if profile.usesHierarchy then state.runtime.lifecycle.consumers.metaController.predictAll features
      else Vector.replicate _ .zero
    pure (state, ⟨.explorationContinuation, action, values, servedProbabilities action, true, metaValues, none, none, none⟩)
  | .idle | .option _ _ => none

/-- Install a drawn option action and retain the same slot/activation for the next frame.
The state is consumed and the option taken out of the table before its learners
are updated, and `TemporalControl.stepOption_eq` proves the result equal to the
listed composition. The ordering is meant to let the runtime reuse the learners'
storage when the state and the option are referenced nowhere else; that is a
performance expectation, not a proved property (see `detachedUpdate`). -/
def TemporalControl.stepOption (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : (OptionActivation (profile.mode != .frozen))) (next : OptionContinuation dimension activation)
    (reward : Binary32) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool) (ended : Option EndEvent) :
    TemporalControl profile config criterion dimension × TemporalDecision :=
  let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, refresh, references⟩,
    credit, creditMatches, average, rate, lifetime⟩ := state
  let stepped := detachedUpdate skills slot fun skill =>
    skill.stepTemporal models activation next reward average.rate references.rng
  let decision := stepped.2.2.1
  (⟨⟨⟨representation, ⟨control, metaController, stepped.1, demons⟩⟩, refresh,
      { references with phase := .option slot stepped.2.1, rng := stepped.2.2.2 }⟩,
      credit, creditMatches, average, rate, lifetime⟩,
    ⟨.option slot, decision.action, decision.snapshot.values, decision.probabilities,
      decision.explored, metaValues, metaDecision, if started then some slot else none, ended⟩)

/-- Taking the option out of the table before its update preserves the complete
composition, for every state, slot, activation and reward word: the stepped
option is written back to its slot, and the phase and random state follow it. -/
theorem TemporalControl.stepOption_eq (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : (OptionActivation (profile.mode != .frozen))) (next : OptionContinuation dimension activation)
    (reward : Binary32) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool) (ended : Option EndEvent) :
    state.stepOption models slot activation next reward metaValues metaDecision started ended =
      let skill := state.runtime.lifecycle.consumers.skills.get slot
      let result := skill.stepTemporal models activation next reward state.average.rate
        state.runtime.references.rng
      let state := (state.withSkill slot result.1).withPhase (.option slot result.2.1)
      let state := { state with runtime := { state.runtime with references :=
        { state.runtime.references with rng := result.2.2.2 } } }
      let decision := result.2.2.1
      (state, ⟨.option slot, decision.action, decision.snapshot.values, decision.probabilities,
        decision.explored, metaValues, metaDecision, if started then some slot else none, ended⟩) := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle refresh references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        simp only [TemporalControl.stepOption, detachedUpdate_eq]
        rfl

/-- Terminal credit goes to the detached old owner when identity changed.
Its result is discarded with that retired objective, never written into the replacement. -/
def TemporalControl.closeOption (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (closing : Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) : TemporalControl profile config criterion dimension × EndEvent :=
  let owner := closing.oldOwner.getD (state.runtime.lifecycle.consumers.skills.get closing.slot)
  let ended := owner.endTemporal models closing.activation reward terminal state.average.rate
  let state := match closing.oldOwner with
    | none => state.withSkill closing.slot ended
    | some _ => state
  (state, ⟨closing.slot, closing.activation.activation.age, closing.activation.reason⟩)

/-- Acknowledge ranking at a free boundary, retaining a possible original owner. -/
def TemporalControl.refreshFree (state : TemporalControl profile config criterion dimension)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))) :
    TemporalControl profile config criterion dimension × Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen))) :=
  let free : FreeDispatch Host.patchShape config criterion dimension demonLayout.tail (EndingPayload (profile.mode != .frozen)) :=
    ⟨state.runtime.lifecycle, state.runtime.refresh, state.runtime.references.modelPredictions, closing⟩
  let free := free.refreshRanked
  ({ state with runtime := { state.runtime with
    lifecycle := free.lifecycle
    refresh := free.refresh
    references := { state.runtime.references with modelPredictions := free.predictions } } }, free.closing)

/-- Plan only at a free learning boundary, using the unchanged old host gain. -/
def TemporalControl.planFree (state : TemporalControl profile config criterion dimension)
    (plan : PlanBoundary config criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    TemporalControl profile config criterion dimension :=
  let planning : PlanningResult criterion dimension := ⟨state.runtime.lifecycle.consumers.metaController,
    state.runtime.references.modelPredictions, state.runtime.references.planningSteps, state.runtime.references.planningErrors⟩
  let planning := if profile.mode == .frozen then { planning with errors := Vector.replicate _ .zero }
    else plan planning state.runtime.lifecycle.consumers.skills features state.average.rate
  { state with runtime := { state.runtime with
    lifecycle := { state.runtime.lifecycle with consumers := { state.runtime.lifecycle.consumers with metaController := planning.controller } }
    references := { state.runtime.references with
      modelPredictions := planning.predictions
      planningSteps := planning.steps
      planningErrors := planning.errors } } }

/-- Freeze and draw the next meta action before any terminal or boundary credit. -/
def TemporalControl.drawMeta (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    TemporalControl profile config criterion dimension × PolicyDecision metaCount :=
  let drawn := (state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount) features state.metaRate).draw state.runtime.references.rng
  ({ state with runtime := { state.runtime with references := { state.runtime.references with rng := drawn.2 } } }, drawn.1)

/-- Repay and close the meta span using its actual already-drawn action. The state
is consumed before the controller is credited, and `TemporalControl.learnMeta_eq`
proves the result equal to the listed composition. The ordering is meant to let
the runtime reuse the rows' storage when the state is referenced nowhere else;
that is a performance expectation, not a proved property. -/
def TemporalControl.learnMeta (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    TemporalControl profile config criterion dimension :=
  if profile.mode == .frozen then state else
    let owed := state.gap.close
    let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, refresh, references⟩,
      credit, creditMatches, average, rate, lifetime⟩ := state
    let controller := metaController.policyStep features decision
      (criterion.center owed.1 owed.2 average.rate) owed.2
    ⟨⟨⟨representation, ⟨control, controller, skills, demons⟩⟩, refresh,
        { references with gapSteps := CreditGap.closed.steps, gapReward := CreditGap.closed.reward }⟩,
      credit, creditMatches, average, rate, lifetime⟩

/-- Consuming the state before the meta-controller's update preserves the complete
composition, for every state, feature list and drawn decision: the controller is
credited the owed span and the span is closed. -/
theorem TemporalControl.learnMeta_eq (state : TemporalControl profile config criterion dimension)
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
    | mk lifecycle refresh references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        rfl

/-- Meta zero delegates to primitives; each other admitted action names exactly one skill. -/
def skillOfMeta (action : Action metaCount.word.toNat) : Option (Fin Acorn.FeatureConstants.skillCount) :=
  if h : action.val = 0 then none else
    some ⟨action.val - 1, by have bound := action.isLt; change action.val < 4 at bound; change action.val - 1 < 3; omega⟩

/-- Credit the sampled meta action, then execute its primitive or option choice.
The selected action is already fixed before either credit operation. A selected
option first settles the transition it was following off-policy, against the
frozen meta snapshot of this decision, and then starts its invocation. -/
def TemporalControl.dispatchMeta (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount)
    (ended : Option EndEvent) : Option (TemporalControl profile config criterion dimension × TemporalDecision) := do
  let state := state.learnMeta features decision
  match skillOfMeta decision.action with
  | none => pure (state.choosePrimitive features decision.snapshot.values (some decision) ended)
  | some slot =>
    let skill := state.runtime.lifecycle.consumers.skills.get slot
    let potential ← skill.interest.potential features declared
    let settled := skill.settleTemporal models features potential goal
      (comparisonValue criterion decision.snapshot) state.skillRate reward state.average.rate
      (profile.mode != .frozen)
    let begun := settled.beginTemporal models features potential (profile.mode != .frozen) state.skillRate
    pure ((state.withSkill slot begun.1).stepOption models slot begun.2.1 begun.2.2 reward
      decision.snapshot.values (some decision) true ended)

/-- Free dispatch acknowledges ranking, plans, draws meta, closes differential
terminal credit, then learns meta. It starts the newly selected option immediately. -/
def TemporalControl.atBoundary (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))) (ended : Option EndEvent) :
    Option (TemporalControl profile config criterion dimension × TemporalDecision) :=
  let refreshed := state.refreshFree closing
  let drawn := (refreshed.1.planFree plan features).drawMeta features
  let decision := drawn.2
  let (state, ended) := match refreshed.2 with
    | none => (drawn.1, ended)
    | some closing =>
      let result := drawn.1.closeOption models closing reward decision.continuation
      (result.1, some result.2)
  state.dispatchMeta models features declared reward goal decision ended

/-- Advance the rate and owed meta reward, then observe models before dispatch.
The operation preserves occupancy and the incoming random/gain state. -/
def TemporalControl.prepareSelection (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : TemporalControl profile config criterion dimension :=
  let state := { state with rate := state.rate.advance }
  let state := if profile.usesHierarchy && profile.mode != .frozen then
    state.withGap (state.gap.accumulate reward criterion.rule.gamma) else state
  let state := if profile.usesHierarchy then
    { state with runtime := { state.runtime with references := { state.runtime.references with
      modelPredictions := state.runtime.lifecycle.consumers.skills.map (fun skill => models.predict skill.model features) } } }
    else state
  state

/-- Policy selection with strict branch priority. Refusal returns no replacement
state when a declared potential is not owned by the supplied source. -/
def TemporalControl.selectWithOperations (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl profile config criterion dimension × TemporalDecision) := do
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
      let closing : Closing config criterion dimension (EndingPayload (profile.mode != .frozen)) :=
        ⟨slot, ⟨activation, potential, reason⟩, none⟩
      match criterion with
      | .differential => state.atBoundary models plan features declared reward goal (some closing) none
      | .discounted =>
        let result := state.closeOption models closing reward estimate
        result.1.atBoundary models plan features declared reward goal none (some result.2)

/-- The sole active option, derived from exclusive occupancy. -/
def TemporalControl.activeSlot (state : TemporalControl profile config criterion dimension) :
    Option (Fin Acorn.FeatureConstants.skillCount) :=
  match state.runtime.references.phase with
  | .option slot _ => some slot
  | .idle | .exploring _ => none

/-- The stopping estimate options that are not executing compare against: the
nominal value of the frame's meta snapshot. When a meta decision was drawn at this
frame it is that decision's own frozen snapshot, values and rate; otherwise no
meta learner has changed since the values were read, and the current rate is theirs. -/
def TemporalControl.stoppingEstimate (state : TemporalControl profile config criterion dimension)
    (decision : TemporalDecision) : Binary32 :=
  match decision.metaDecision with
  | some drawn => comparisonValue criterion drawn.snapshot
  | none => comparisonValue criterion
      (⟨decision.metaValues, state.metaRate⟩ : PolicySnapshot metaCount)

/-- One slot's share of a followed frame. The executing option keeps its own
on-policy update and is linked to no off-policy trajectory. A slot whose declared
potential source is not supplied learns nothing and is unlinked. -/
def followSlot (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32) (gain : RewardRate)
    (executing : Bool) (skill : Skill config criterion dimension) : Skill config criterion dimension :=
  if executing then { skill with following := none } else
    match skill.interest.potential features declared with
    | some potential =>
      skill.followTemporal models features potential goal estimate rate action behaviour reward
        gain
    | none => { skill with following := none }

/-- Every option that is not executing learns from the frame's actual action and
its reported behaviour masses, in table order, after selection and before the
common completion boundary, so each reads the same pre-observation gain as the
executing option. Frozen and primitive-only profiles do no option learning. No
random draw is consumed. -/
def TemporalControl.followOptions (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) (decision : TemporalDecision) :
    TemporalControl profile config criterion dimension :=
  if profile.usesHierarchy && profile.mode != .frozen then
    let estimate := state.stoppingEstimate decision
    let rate := state.skillRate
    let executing := state.activeSlot
    let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, refresh, references⟩,
      credit, creditMatches, average, schedule, lifetime⟩ := state
    let followed := skills.mapFinIdx fun index skill bound =>
      followSlot models features declared goal estimate rate decision.action
        decision.probabilities reward average.rate (executing == some ⟨index, bound⟩) skill
    ⟨⟨⟨representation, ⟨control, metaController, followed, demons⟩⟩, refresh, references⟩,
      credit, creditMatches, average, schedule, lifetime⟩
  else state

/-- Consuming the ensemble before the option updates preserves the complete
composition: only the skill table changes, slot by slot. -/
theorem TemporalControl.followOptions_eq (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) (decision : TemporalDecision) :
    state.followOptions models features declared reward goal decision =
      if profile.usesHierarchy && profile.mode != .frozen then
        { state with runtime := { state.runtime with lifecycle := { state.runtime.lifecycle with
          consumers := { state.runtime.lifecycle.consumers with
            skills := state.runtime.lifecycle.consumers.skills.mapFinIdx fun index skill bound =>
              followSlot models features declared goal (state.stoppingEstimate decision)
                state.skillRate decision.action decision.probabilities reward state.average.rate
                (state.activeSlot == some ⟨index, bound⟩) skill } } } }
      else state := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle refresh references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        rfl

/-- Current selection executes concrete model learning and the explicit planning choice. -/
def TemporalControl.select (state : TemporalControl profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl profile config criterion dimension × TemporalDecision) :=
  state.selectWithOperations (modelOperations criterion dimension) (planningBoundary planning)
    features declared reward goal

/-- One local temporal transition: selection, off-policy learning of every option
that is not executing, then credit and feedback on every selected path.
The input active set belongs to the caller's current encoding frame. -/
def TemporalControl.step (state : TemporalControl profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl profile config criterion dimension × TemporalDecision) := do
  let (selected, decision) ← state.select planning features (spatialPotentials obs) reward goal
  let followed := selected.followOptions (modelOperations criterion dimension) features
    (spatialPotentials obs) reward goal decision
  pure (followed.finish features obs reward decision, decision)

/-- Attempt/curriculum events request future ranking without modifying an active
option, serving a run, clearing trajectories or changing random state. -/
def TemporalControl.request (state : TemporalControl profile config criterion dimension)
    (cycle : UInt64) (achieved : Bool) : TemporalControl profile config criterion dimension :=
  { state with runtime := { state.runtime with refresh := profile.request state.runtime.refresh cycle achieved } }

/-- Timeout/attempt handling retains the entire process-local dispatch state. -/
theorem TemporalControl.request_references (state : TemporalControl profile config criterion dimension)
    (cycle : UInt64) (achieved : Bool) :
    (state.request cycle achieved).runtime.references = state.runtime.references := rfl

/-- Selection updates finish through the same prediction/credit definition and
cannot use a different executed action for primitive credit. -/
theorem TemporalControl.finish_credit (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision) :
    (state.finish features obs reward decision).runtime.lifecycle.consumers.control =
      (state.predictionView.advance features obs reward decision.action decision.own).control.controller := by
  by_cases frozen : profile.mode = .frozen <;>
    simp [TemporalControl.finish_eq, TemporalControl.predictionView, PredictionControl.advance,
      TemporalControl.recordEpisodes, frozen]

end Acorn.Handcrafted
