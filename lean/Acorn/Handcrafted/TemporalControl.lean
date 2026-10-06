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

This dispatcher consumes one already-encoded frame of any world interface and its
preceding reward. It composes persistent exploration, option policies, assignment refresh,
SMDP meta credit, off-policy option learning, primitive credit, prediction
feedback, every option's off-policy questions and the old-gain clock.
The full agent supplies encoding/retirement order. Model learning and the selected
planning algorithm execute the current managed owners. No attempt timeout is a termination input.

Persistent exploration belongs to the behaviour (PAR-8): Dabney, Ostrovski & Barreto,
*Temporally-Extended ε-Greedy Exploration*, ICLR (2021), arXiv:2006.01782v1, Algorithm 1,
PDF p. 14, starts a run with probability ε at every step with no run in progress,
whichever action is greedy. Every decision that is not served from a run makes one
persistent draw, by the layer that selects the primitive action: primitive control
(`choosePrimitive`) or the executing option (`stepOption`). The meta-controller's draw
selects that layer and stays a single-step draw over meta actions. A run an option's
draw begins interrupts the option: §4.2, PDF p. 5, makes the run an option of the
behaviour, which "takes action a for n steps and then terminates", and one occupancy
executes at a time. The option is the executing invocation of the frame it drew; the
first served step ends its execution. The run gives it no terminal credit, because the
run is not one of the option's stopping conditions, and from that step the option
learns off-policy under its own stopping decision, like every option that is not
executing (`interrupt`). The meta-controller's span for the option closes at that step
toward the option's own continuing value, and the run's rewards are credited to no meta
action (`takeoverValue`, `closeSpan`). The meta-controller decides again when the run
is spent.

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

Every model operation that needs a value reads the meta-controller as it stands at
that operation (`TemporalControl.valueFunction`): the model caches before dispatch,
planning, and the residual target at each model close. Each frame is recorded in the
bounded recent-frame store at the common completion boundary, after selection and
planning, so planning's search control backs up only at earlier frames.
-/
namespace Acorn.Handcrafted
open Features

/-- Local temporal state uses the actual receiver-owned representation and learners. -/
structure TemporalControl (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) where
  /-- One common lifecycle storage owner and exclusive phase. -/
  runtime : FeatureRuntime interface.symbols interface.actions config criterion dimension interface.layout
    (OptionActivation (profile.mode != .frozen)) (CommittedRun interface.actions (profile.mode != .frozen))
    (Option (TemporalDecision interface.actions))
  /-- Profile-fixed primitive credit and its optional deferred span. -/
  credit : PrimitiveCredit
  /-- Credit payload cannot change the immutable policy. -/
  creditMatches : creditKind credit = profile.credit
  /-- Shared host-transition gain, read before any hierarchy update. -/
  average : AverageRewardTracker
  /-- Schedule payload belongs only to its immutable rate policy. -/
  rate : RateState profile.rate
  /-- Fixed-memory observations have no reader on the policy-selection path. -/
  lifetime : Lifetime.Stats interface.layout

/-- Zero knowledge, no invented prior transition, and canonical action-stream seed. -/
def TemporalControl.initial (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) :
    TemporalControl interface profile config criterion dimension :=
  ⟨⟨⟨Representation.initial _ _, Ensemble.initial config criterion dimension interface.layout (profile.interests config)⟩,
      TemporalReferences.cold config interface.layout none⟩,
    profile.credit.initial, by cases profile.credit <;> rfl, .initial, RateState.initial profile.rate, Lifetime.Stats.initial _⟩

variable {interface : Interface} {actions : Word.Count} {profile : FeatureProfile}
  {config : Features.Config} {criterion : Criterion} {dimension : Dimension}

/-- A view transfers the same controller and demon values to the already-proved
prediction/credit operation; no second learner implementation or storage is maintained. -/
def TemporalControl.predictionView (state : TemporalControl interface profile config criterion dimension) :
    PredictionControl interface profile criterion dimension :=
  ⟨⟨state.runtime.lifecycle.consumers.control, state.credit, state.average, state.runtime.references.pendingAction⟩,
    state.creditMatches, state.runtime.lifecycle.consumers.demons,
    state.runtime.references.demonPredictions, state.runtime.references.demonErrors, state.lifetime⟩

/-- Lifetime payload derives its slot, age and reason from the actual consumed activation. -/
def _root_.Acorn.Features.TemporalDecision.episodeEnd (decision : TemporalDecision actions) : Option Lifetime.EpisodeEnd :=
  decision.ended.map fun event =>
    let reason : Fin 3 := match event.reason with
      | .goal => 0 | .duration => 1 | .interrupted => 2
    ⟨event.slot, event.age.val.toUInt32, reason⟩

/-- Account for actual option endings before starts at the same decision boundary. -/
def TemporalControl.recordEpisodes (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : TemporalControl interface profile config criterion dimension :=
  { state with lifetime := { state.lifetime with
      options := Lifetime.recordOptions state.lifetime.options decision.episodeEnd decision.started } }

/-- Whether a frame's action was selected with an option's own distribution: the option drew
it, or its model trajectory is live after `followOptions`, which holds when the masses the
behaviour reported equal the option's own. -/
def askedBy (decision : TemporalDecision actions) (index : Fin Acorn.FeatureConstants.skillCount)
    (following : Option Following) : Bool :=
  decision.source == .option index || following.any (·.live)

/-- Every option's questions about its own policy take the frame (Horde, AAMAS 2011,
§4; PAR-18): each learns from the transition into this frame when the preceding frame's
action was selected with the option's own distribution, and stores this frame when its
action was. That holds when the option drew the action, or when the masses the behaviour
reported equal the option's own, which `followOptions` has recorded as the option's live
model trajectory. No decision reads the questions. -/
def askQuestions (skills : Vector (Skill interface.actions config criterion dimension interface.layout)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (cumulants : Features.Cumulants interface.layout)
    (decision : TemporalDecision interface.actions) :
    Vector (Skill interface.actions config criterion dimension interface.layout) Acorn.FeatureConstants.skillCount :=
  skills.mapFinIdx fun index skill bound =>
    let ⟨interest, policy, model, following, questions⟩ := skill
    ⟨interest, policy, model, following,
      questions.follow features cumulants (askedBy decision ⟨index, bound⟩ following)⟩

/-- Complete one selected primitive step: primitive credit, demons, every option's
questions in a learning hierarchy, then gain, and record the frame for later search
control. The signal values are evaluated once, for the demons and the questions.
Every selection branch uses this single completion boundary. Retirement is the
full-agent owner's next operation, after every learner has consumed this frame. -/
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
  let skills := if profile.usesHierarchy && profile.mode != .frozen then
    askQuestions skills features cumulants decision else skills
  ⟨⟨⟨representation, ⟨predicted.control.controller, metaController, skills, predicted.demons⟩⟩,
      { references with
        demonPredictions := predicted.predictions, demonErrors := predicted.errors,
        pendingAction := predicted.control.pending, lastDecision := some decision,
        recent := references.recent.record features }⟩,
    predicted.control.credit, predicted.creditMatches, predicted.control.average, rate,
    predicted.lifetime⟩

/-- Consuming the ensemble before learner updates preserves the complete
composition for every state, observation, reward word and selected decision. -/
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
          control := predicted.control.controller, demons := predicted.demons,
          skills := if profile.usesHierarchy && profile.mode != .frozen then
            askQuestions state.runtime.lifecycle.consumers.skills features cumulants decision
            else state.runtime.lifecycle.consumers.skills } }
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

/-- Asking questions writes each slot's questions and nothing else, for every table,
frame, signal word and decision. A slot's questions are armed exactly when the option
drew the frame's action or its model trajectory is live. -/
theorem askQuestions_get (skills : Vector (Skill interface.actions config criterion dimension interface.layout)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (cumulants : Features.Cumulants interface.layout)
    (decision : TemporalDecision interface.actions) (index : Fin Acorn.FeatureConstants.skillCount) :
    (askQuestions skills features cumulants decision)[index.val] =
      { skills[index.val] with questions := (skills[index.val].questions.follow features cumulants
          (askedBy decision index skills[index.val].following)) } := by
  simp only [askQuestions, Vector.getElem_mapFinIdx, Fin.eta]

/-- The completion boundary writes each slot's questions in a learning hierarchy and no
other field of any slot, in every profile. -/
theorem TemporalControl.finish_skill (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) (index : Fin Acorn.FeatureConstants.skillCount) :
    (state.finish features obs reward decision).runtime.lifecycle.consumers.skills[index.val] =
      if profile.usesHierarchy && profile.mode != .frozen then
        let skill := state.runtime.lifecycle.consumers.skills[index.val]
        { skill with questions := (skill.questions.follow features
            (signalValues obs reward) (askedBy decision index skill.following)) }
      else state.runtime.lifecycle.consumers.skills[index.val] := by
  rw [TemporalControl.finish_eq]
  dsimp only
  split
  · exact askQuestions_get _ _ _ _ index
  · rfl

/-- Meta span is the existing byte-bounded credit gap, observed without copying its algorithm. -/
def TemporalControl.gap (state : TemporalControl interface profile config criterion dimension) : CreditGap :=
  ⟨state.runtime.references.gapSteps, state.runtime.references.gapReward⟩

/-- Write a complete span together. -/
def TemporalControl.withGap (state : TemporalControl interface profile config criterion dimension) (gap : CreditGap) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with
    gapSteps := gap.steps, gapReward := gap.reward } } }

/-- Advance the deferred meta clock only when a learning hierarchy skipped its decision. -/
def TemporalControl.skipMeta (state : TemporalControl interface profile config criterion dimension) :
    TemporalControl interface profile config criterion dimension :=
  if profile.usesHierarchy && profile.mode != .frozen then state.withGap state.gap.skip else state

/-- The primitive learner's PAR-10 rate, the sole source of the explicitly shared rate. -/
def TemporalControl.primitiveRate (state : TemporalControl interface profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.runtime.lifecycle.consumers.control.exploreRate (count := interface.actions)

/-- Resolve the meta rate against its own learner or the declared common source. -/
def TemporalControl.metaRate (state : TemporalControl interface profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.rate.controller
    (fun _ => state.runtime.lifecycle.consumers.metaController.exploreRate (count := metaCount))
    (fun _ => state.primitiveRate)

/-- The primitive source cannot accidentally read a different controller. -/
def TemporalControl.controlRate (state : TemporalControl interface profile config criterion dimension) : SwiftTd.ExploreRate :=
  state.rate.controller (fun _ => state.primitiveRate) (fun _ => state.primitiveRate)

/-- Options resolve their own rates only after a possible invocation reset. -/
def TemporalControl.skillRate (state : TemporalControl interface profile config criterion dimension) : ConsumerRate :=
  state.rate.skill (fun _ => state.primitiveRate)

/-- Under the declared policy the primitive controller, the meta-controller and
every option read the declared D6 word at every state, whatever any learner
would derive. These are the only rates the dispatcher's snapshots consume. -/
theorem TemporalControl.declared_rates (state : TemporalControl interface profile config criterion dimension)
    (declared : profile.rate = .declared) :
    state.controlRate = declaredRate ∧ state.metaRate = declaredRate ∧
      ∀ own, state.skillRate.resolve own = declaredRate := by
  refine ⟨RateState.declared_controller state.rate declared _ _,
    RateState.declared_controller state.rate declared _ _, fun own => ?_⟩
  simp only [TemporalControl.skillRate, RateState.declared_skill state.rate declared,
    ConsumerRate.resolve]

/-- The current value function: the meta-controller as it stands, with the rate its
nominal policy resolves to now. Model targets and model caches read it. -/
def TemporalControl.valueFunction (state : TemporalControl interface profile config criterion dimension) :
    ValueFunction criterion dimension :=
  ⟨state.runtime.lifecycle.consumers.metaController, state.metaRate⟩

/-- Replace exactly one option's managed storage. -/
def TemporalControl.withSkill (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (skill : Skill interface.actions config criterion dimension interface.layout) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with lifecycle := { state.runtime.lifecycle with
    consumers := { state.runtime.lifecycle.consumers with
      skills := state.runtime.lifecycle.consumers.skills.set slot.val skill slot.isLt } } } }

/-- Occupancy is written atomically: one of free, a committed run or a live option.
A committed run holds the option whose draw began it only until its first served step. -/
def TemporalControl.withPhase (state : TemporalControl interface profile config criterion dimension)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen)) (CommittedRun interface.actions (profile.mode != .frozen))) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with phase } } }

/-- Non-planning hierarchy branches clear only the last diagnostic errors. -/
def TemporalControl.withoutPlanning (state : TemporalControl interface profile config criterion dimension) :
    TemporalControl interface profile config criterion dimension :=
  { state with runtime := { state.runtime with references := { state.runtime.references with
    planningErrors := Vector.replicate _ .zero } } }

/-- Fresh primitive choice consumes branch, duration/action or greedy draws in order. -/
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

/-- End the execution of the option a committed run holds, at the run's first served
step. The run gives the option no terminal credit: an exploratory run is not one of its
stopping conditions. A learning option is linked to the trajectory it was executing
(`OptionActivation.following`), so this frame's off-policy learning (`followOptions`)
credits the transition into the frame as it does for every option that is not
executing, under the option's own stopping decision. A frozen option is written
nowhere. The event records the interruption. -/
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

/-- Interrupting a held option writes the skill table only and reports the held slot: the
lifetime record, occupancy, random state and every other reference are untouched. -/
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

/-- A continuing run bypasses every option/meta draw and preserves random state. Its
first served step interrupts the option whose draw began the run and leaves the
deferred meta span as that option's own actions made it, for `closeSpan`; every later
served step advances the deferred clock. -/
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

/-- A served step, for every state: occupancy held a committed run, the decision repeats
its action, the returned state holds the run `ExploratoryRun.serve` returns and no
option, and the generator state is untouched. -/
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

/-- Install a drawn option action. The option keeps occupancy for the next frame unless
its draw began a run with a step left to serve, which takes occupancy and holds the
option until that step (`Occupancy.afterOption`).
The state is consumed and the option taken out of the table before its learners
are updated, and `TemporalControl.stepOption_eq` proves the result equal to the
listed composition. The ordering is meant to let the runtime reuse the learners'
storage when the state and the option are referenced nowhere else; that is a
performance expectation, not a proved property (see `detachedUpdate`). -/
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

/-- Taking the option out of the table before its update preserves the complete
composition, for every state, slot, activation and reward word: the stepped
option is written back to its slot, and the phase and random state follow its draw. -/
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

/-- Terminal credit of an option whose identity changed belongs to the detached old owner
and is discarded with that retired objective: it is not computed, and nothing is written
into the replacement. Otherwise the current owner is credited and its model closes at the
terminal frame under the current value function. The state is
consumed and the option taken out of the table before its learners are updated, and
`TemporalControl.closeOption_eq` proves the result equal to the listed composition. The
ordering is meant to let the runtime reuse the learners' storage when the state and the
option are referenced nowhere else; that is a performance expectation, not a proved
property (see `detachedUpdate`). -/
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

/-- Taking the option out of the table before its terminal credit preserves the complete
composition, for every state, closing record and reward word: the current owner's ended
option is written back to its slot, and a detached old owner's result is discarded. -/
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

/-- Refresh the ranked assignments of learned subtasks and every model's ranking at a
free boundary, retaining a possible original owner. -/
def TemporalControl.refreshFree (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    TemporalControl interface profile config criterion dimension × Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))) :=
  let free : FreeDispatch interface.symbols interface.actions config criterion dimension interface.signals (EndingPayload (profile.mode != .frozen)) :=
    ⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩
  let free := free.refreshModels profile.ranksSubtasks
  ({ state with runtime := { state.runtime with
    lifecycle := free.lifecycle
    references := { state.runtime.references with modelPredictions := free.predictions } } }, free.closing)

/-- With learned subtasks, the learner state after a free-boundary refresh is the
assigning refresh's. `TemporalControl.select_assigns` carries it to the state each
free dispatch returns. -/
theorem TemporalControl.refreshFree_assigns (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).1.runtime.lifecycle =
      ((⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩ :
        FreeDispatch interface.symbols interface.actions config criterion dimension interface.signals
          (EndingPayload (profile.mode != .frozen))).refreshModels true).lifecycle := by
  simp only [TemporalControl.refreshFree, learned]

/-- Plan only at a free learning boundary, using the unchanged old host gain and
the meta-controller's current rate. Search control reads and advances the stored
recent frames. -/
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

/-- Freeze and draw the next meta action before any terminal or boundary credit. -/
def TemporalControl.drawMeta (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    TemporalControl interface profile config criterion dimension × PolicyDecision metaCount :=
  let drawn := (state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount) features state.metaRate).draw state.runtime.references.rng
  ({ state with runtime := { state.runtime with references := { state.runtime.references with rng := drawn.2 } } }, drawn.1)

/-- Repay and close the meta span using its actual already-drawn action. The state
is consumed before the controller is credited, and `TemporalControl.learnMeta_eq`
proves the result equal to the listed composition. The ordering is meant to let
the runtime reuse the rows' storage when the state is referenced nowhere else;
that is a performance expectation, not a proved property. -/
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

/-- Consuming the state before the meta-controller's update preserves the complete
composition, for every state, feature list and drawn decision: the controller is
credited the owed span and the span is closed. -/
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

/-- Meta zero delegates to primitives; each other admitted action names exactly one skill. -/
def skillOfMeta (action : Action metaCount.word.toNat) : Option (Fin Acorn.FeatureConstants.skillCount) :=
  if h : action.val = 0 then none else
    some ⟨action.val - 1, by have bound := action.isLt; change action.val < 4 at bound; change action.val - 1 < 3; omega⟩

/-- Credit the sampled meta action, then execute its primitive or option choice.
The selected action is already fixed before either credit operation. A selected
option first settles the transition it was following off-policy, against the
frozen meta snapshot of this decision, and then starts its invocation. The state is
consumed and the option taken out of the table before it settles and begins, and
`TemporalControl.dispatchMeta_eq` proves the result equal to the listed composition.
The ordering is meant to let the runtime reuse the learners' storage when the state and
the option are referenced nowhere else; that is a performance expectation, not a proved
property (see `detachedUpdate`). -/
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

/-- Taking the selected option out of the table before it settles and begins preserves
the complete composition, for every state, frame, reward word and drawn decision. -/
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

/-- Free dispatch refreshes the ranked assignments and models, plans, draws meta, closes
differential terminal credit, then learns meta. It starts the newly selected option immediately. -/
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

/-- Advance the rate and owed meta reward, then observe models before dispatch under
the current value function.
The operation preserves occupancy and the incoming random/gain state. -/
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

/-- Policy selection with strict branch priority. Refusal returns no replacement
state when a declared potential is not owned by the supplied source. -/
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

/-- The sole executing option, derived from exclusive occupancy: a live option, or the
option a committed run holds until its first served step. -/
def TemporalControl.activeSlot (state : TemporalControl interface profile config criterion dimension) :
    Option (Fin Acorn.FeatureConstants.skillCount) :=
  state.runtime.references.phase.executing

/-- The stopping estimate options that are not executing compare against: the
nominal value of the frame's meta snapshot. When a meta decision was drawn at this
frame it is that decision's own frozen snapshot, values and rate; otherwise no
meta learner has changed since the values were read, and the current rate is theirs. -/
def TemporalControl.stoppingEstimate (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) : Binary32 :=
  match decision.metaDecision with
  | some drawn => comparisonValue criterion drawn.snapshot
  | none => comparisonValue criterion
      (⟨decision.metaValues, state.metaRate⟩ : PolicySnapshot metaCount)

/-- One slot's share of a followed frame. The executing option keeps its own
on-policy update and is linked to no off-policy trajectory. A slot whose declared
potential source is not supplied learns nothing and is unlinked. -/
def followSlot (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32) (gain : RewardRate)
    (executing : Bool) (skill : Skill interface.actions config criterion dimension interface.layout) :
    Skill interface.actions config criterion dimension interface.layout :=
  if executing then { skill with following := none } else
    match skill.interest.potential features declared with
    | some potential =>
      skill.followTemporal models value features potential goal estimate rate action behaviour
        reward gain
    | none => { skill with following := none }

/-- Every option that is not executing learns from the frame's actual action and
its reported behaviour masses, in table order, after selection and before the
common completion boundary, so each reads the same pre-observation gain as the
executing option. Frozen and primitive-only profiles do no option learning. No
random draw is consumed. -/
def TemporalControl.followOptions (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  if profile.usesHierarchy && profile.mode != .frozen then
    let estimate := state.stoppingEstimate decision
    let rate := state.skillRate
    let executing := state.activeSlot
    let value := state.valueFunction
    let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
      credit, creditMatches, average, schedule, lifetime⟩ := state
    let followed := skills.mapFinIdx fun index skill bound =>
      followSlot models value features declared goal estimate rate decision.action
        decision.probabilities reward average.rate (executing == some ⟨index, bound⟩) skill
    ⟨⟨⟨representation, ⟨control, metaController, followed, demons⟩⟩, references⟩,
      credit, creditMatches, average, schedule, lifetime⟩
  else state

/-- Consuming the ensemble before the option updates preserves the complete
composition: only the skill table changes, slot by slot. -/
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

/-- The value an interrupted option's meta span closes toward, on the first served step
of the run that held it; `none` on every other frame. The run censors the option
without stopping it, so the span is credited toward the option's own continuing return:
its own meta value at this frame while its stopping decision continues, and the frame's
nominal meta value where that decision ends. The decision is the one `followOptions`
takes for the option's learners at this frame, read from the same skill, estimate and
rate. A slot whose potential source is not supplied learns nothing and closes as
stopped. -/
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

/-- Close the meta-controller's span at an interruption. The owed span covers the
interrupted option's own actions and nothing of the run: selection accumulated this
frame's reward, which the option's last action earned, and the first served step did
not advance the deferred clock. The span is credited toward the supplied continuation
with the error `learnMeta` forms, and every meta trace is then released, so the rewards
of the served steps are credited to no meta action when the next decision is learned.
The state is consumed before the controller is credited, and `closeSpan_eq` proves the
result equal to the listed composition; storage reuse is a performance expectation,
not a proved property. -/
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

/-- Consuming the state before the meta-controller's closing credit preserves the
composition: the controller takes the closing credit for the owed span and the span is
closed; nothing else is written. -/
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

/-- Current selection executes concrete model learning and the explicit planning choice. -/
def TemporalControl.select (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) :=
  state.selectWithOperations (modelOperations criterion dimension) (planningBoundary planning)
    features declared reward goal

/-- One local temporal transition: selection, off-policy learning of every option
that is not executing, the closing of an interrupted option's meta span, then credit
and feedback on every selected path. The span's continuation value is read before the
options learn, from the state and decision selection returned.
The input active set belongs to the caller's current encoding frame. Selection, with
its assignment refresh, reads the Demon-0 weights as the previous step left them: the
reward delivered here is learned by `finish`, after selection, so a subtask candidate
that reward creates is installed at the next free dispatch, not at this decision. -/
def TemporalControl.step (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32) (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions) := do
  let (selected, decision) ← state.select planning features obs.declared reward goal
  let continuation := selected.takeoverValue features obs.declared goal decision
  let followed := selected.followOptions (modelOperations criterion dimension) features
    obs.declared reward goal decision
  pure ((followed.closeSpan continuation).finish features obs reward decision, decision)

/-- The part of one local transition that follows selection: off-policy learning of
every option that is not executing, the closing of an interrupted option's meta span,
then credit and feedback. Its inputs are the state and decision selection returned and
the frame and reward selection read. The decision is an input; it draws no action. -/
def TemporalControl.learn (selected : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  let continuation := selected.takeoverValue features obs.declared goal decision
  let followed := selected.followOptions (modelOperations criterion dimension) features
    obs.declared reward goal decision
  (followed.closeSpan continuation).finish features obs reward decision

/-- One local transition is selection, then the learning part on the state and decision
selection returned, for every state, frame and reward word. A refused selection is a
refused transition. -/
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

/-- Selection updates finish through the same prediction/credit definition and
cannot use a different executed action for primitive credit. -/
theorem TemporalControl.finish_credit (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.lifecycle.consumers.control =
      (state.predictionView.advance features obs reward decision.action decision.own).control.controller := by
  by_cases frozen : profile.mode = .frozen <;>
    simp [TemporalControl.finish_eq, TemporalControl.predictionView, PredictionControl.advance,
      PredictionControl.advanceWith, TemporalControl.recordEpisodes, frozen]

end Acorn.Handcrafted
