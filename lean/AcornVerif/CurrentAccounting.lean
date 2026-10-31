/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix
import AcornVerif.CurrentGridWorld
import AcornVerif.Oak

/-!
# Host accounting does not reach a learner

Between decisions a host reports the reward of a task family, the outcome of an attempt
and process exit to the agent, through `Agent.recordEnvironment`, `Agent.recordAttempt`
and `Agent.censorObservations`. Each writes the agent's lifetime observations and
nothing else (`recordEnvironment_learners`, `recordAttempt_learners`,
`censor_learners`), in every world interface.

That is half of the claim that such a report reaches no learner. The other half is that
no decision reads the lifetime observations. `learners` is everything of a local state
but those observations: the composed storage of representation, learners and
references, the primitive credit, the reward rate and the rate schedule.
`step_learners` shows that the executed local transition, from two states with the same
learners, returns the same decision and next states with the same learners, and
`act_learners` shows the same of the full decision `Agent.act`, encoding and tester
included. `actOrdered_learners` shows it of the whole step under each of the three step
orders. `act_accounting` concludes that a host operation that keeps the learners
changes neither the next decision nor the learners after it.

The proof follows the executed step. Every operation of selection commutes with a change
of the lifetime observations (`select_relabel` and the lemmas before it); the completion
boundary `TemporalControl.finish` is the one operation that reads them, and it reads
them only to write them (`finish_learners`). The orders other than the default place the
deferred planning, the draw-first selection and the owed writes around it, and each of those
commutes with a change of the observations as well (`deferred_relabel`, `drawFirst_relabel`,
`settle_relabel`).

The achievement event of a frame does reach a learner. It is departure D8.
`AcornVerif.CurrentOak` states, for seven operations that take it, that the operation's
results agree under two events where the outcomes of the stopping decisions it consults
agree: `Skill.settleFollowing`, `Skill.settleTemporal`, `Skill.followTemporal`,
`followSlot`, `TemporalControl.followOptions`, `TemporalControl.takeoverValue` and
`TemporalControl.dispatchMeta`. Selection (`TemporalControl.selectWithOperations`) also
takes the event: it consults the executing option's stopping decision and hands the
event to `TemporalControl.atBoundary`. No such theorem covers those two.

`executed_actions` carries the result to the closed loop of the kernel: from two agent
states with the same learners, the executed agent takes the same action at every time,
in every world over its interface. The other theorems concern single decisions. No
theorem here composes them along a run of the host: the kernel instance of
`AcornVerif.CurrentGridWorld` does not model the host's reports between decisions.
`AcornVerif.CurrentVisits` composes them along a run of visits.
-/

namespace AcornVerif.CurrentAccounting
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-! ## The learners of a state -/

/-- Everything of a local state but its lifetime observations: the composed storage of
representation, learners and references, the primitive credit, the reward rate and the
rate schedule. -/
def learners (state : TemporalControl interface profile config criterion dimension) :=
  (state.runtime, state.credit, state.average, state.rate)

/-- A local state with its lifetime observations replaced. -/
def relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    TemporalControl interface profile config criterion dimension :=
  { state with lifetime := lifetime }

/-- A selected state and decision, with the state's lifetime observations replaced. -/
def relabelResult (lifetime : Lifetime.Stats interface.layout)
    (result : TemporalControl interface profile config criterion dimension ×
      TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension ×
      TemporalDecision interface.actions :=
  (relabel result.1 lifetime, result.2)

/-- What a transition returns apart from the lifetime observations: the learners of the
next state, and the decision. -/
def outcome (result : TemporalControl interface profile config criterion dimension ×
    TemporalDecision interface.actions) :=
  (learners result.1, result.2)

/-- Two local states with the same learners differ in their lifetime observations
only. -/
theorem relabel_of_learners
    (first second : TemporalControl interface profile config criterion dimension)
    (same : learners first = learners second) : second = relabel first second.lifetime := by
  cases first with
  | mk runtime credit creditMatches average rate lifetime =>
    cases second with
    | mk otherRuntime otherCredit otherMatches otherAverage otherRate otherLifetime =>
      simp only [learners, Prod.mk.injEq] at same
      obtain ⟨sameRuntime, sameCredit, sameAverage, sameRate⟩ := same
      subst sameRuntime sameCredit sameAverage sameRate
      rfl

/-- Replacing the lifetime observations keeps the learners. -/
theorem learners_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    learners (relabel state lifetime) = learners state :=
  rfl

/-- The composed storage does not hold the lifetime observations. -/
theorem relabel_runtime (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    (relabel state lifetime).runtime = state.runtime :=
  rfl

/-- The meta-controller's rate does not read the lifetime observations. -/
theorem relabel_metaRate (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    (relabel state lifetime).metaRate = state.metaRate :=
  rfl

/-- The options' rate source does not read the lifetime observations. -/
theorem relabel_skillRate (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    (relabel state lifetime).skillRate = state.skillRate :=
  rfl

/-- The current value function does not read the lifetime observations. -/
theorem relabel_valueFunction
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    (relabel state lifetime).valueFunction = state.valueFunction :=
  rfl

/-- The reward rate does not read the lifetime observations. -/
theorem relabel_average (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    (relabel state lifetime).average = state.average :=
  rfl

/-! ## The operations of selection -/

/-- Writing the occupancy commutes with a change of the lifetime observations. -/
theorem withPhase_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen))) :
    (relabel state lifetime).withPhase phase = relabel (state.withPhase phase) lifetime :=
  rfl

/-- Replacing an option commutes with a change of the lifetime observations. -/
theorem withSkill_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (relabel state lifetime).withSkill slot skill =
      relabel (state.withSkill slot skill) lifetime :=
  rfl

/-- Clearing the planning errors commutes with a change of the lifetime observations. -/
theorem withoutPlanning_relabel
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    (relabel state lifetime).withoutPlanning = relabel state.withoutPlanning lifetime :=
  rfl

/-- Advancing the deferred meta clock commutes with a change of the lifetime
observations. -/
theorem skipMeta_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) :
    (relabel state lifetime).skipMeta = relabel state.skipMeta lifetime := by
  unfold TemporalControl.skipMeta
  split <;> rfl

/-- Preparation commutes with a change of the lifetime observations. -/
theorem prepare_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (relabel state lifetime).prepareSelection models features reward =
      relabel (state.prepareSelection models features reward) lifetime := by
  unfold TemporalControl.prepareSelection
  split <;> split <;> rfl

/-- A primitive choice commutes with a change of the lifetime observations. -/
theorem choosePrimitive_relabel
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    (relabel state lifetime).choosePrimitive features metaValues metaDecision ended =
      relabelResult lifetime (state.choosePrimitive features metaValues metaDecision ended) :=
  rfl

/-- Interrupting a held option commutes with a change of the lifetime observations. -/
theorem interrupt_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) :
    (relabel state lifetime).interrupt origin =
      (relabel (state.interrupt origin).1 lifetime, (state.interrupt origin).2) := by
  cases origin with
  | none => rfl
  | some held =>
    unfold TemporalControl.interrupt
    dsimp only
    split <;> rfl

/-- A served step of a committed run commutes with a change of the lifetime
observations. -/
theorem serve_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension) :
    (relabel state lifetime).serve features =
      (state.serve features).map (relabelResult lifetime) := by
  unfold TemporalControl.serve
  dsimp only [relabel_runtime]
  cases state.runtime.references.phase with
  | idle => rfl
  | option slot activation => rfl
  | exploring committed =>
    dsimp only
    cases committed.run.serve with
    | none => rfl
    | some pair =>
      simp only [bind, Option.bind, pure, Option.map_some, interrupt_relabel, withPhase_relabel]
      split <;> split <;>
        simp only [skipMeta_relabel, withoutPlanning_relabel, relabel_runtime, relabelResult]

/-- An option step commutes with a change of the lifetime observations. -/
theorem stepOption_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (started : Bool)
    (ended : Option EndEvent) :
    (relabel state lifetime).stepOption models slot activation next reward metaValues
        metaDecision started ended =
      relabelResult lifetime (state.stepOption models slot activation next reward metaValues
        metaDecision started ended) := by
  rw [TemporalControl.stepOption_eq, TemporalControl.stepOption_eq]
  rfl

/-- Terminal credit of an option commutes with a change of the lifetime observations. -/
theorem closeOption_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (relabel state lifetime).closeOption models features closing reward terminal =
      (relabel (state.closeOption models features closing reward terminal).1 lifetime,
        (state.closeOption models features closing reward terminal).2) := by
  rw [TemporalControl.closeOption_eq, TemporalControl.closeOption_eq]
  dsimp only
  split <;> rfl

/-- The free-boundary refresh commutes with a change of the lifetime observations. -/
theorem refreshFree_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) :
    (relabel state lifetime).refreshFree closing =
      (relabel (state.refreshFree closing).1 lifetime, (state.refreshFree closing).2) :=
  rfl

/-- A planning boundary commutes with a change of the lifetime observations. -/
theorem planFree_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) :
    (relabel state lifetime).planFree plan features =
      relabel (state.planFree plan features) lifetime :=
  rfl

/-- The meta draw commutes with a change of the lifetime observations. -/
theorem drawMeta_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension) :
    (relabel state lifetime).drawMeta features =
      (relabel (state.drawMeta features).1 lifetime, (state.drawMeta features).2) :=
  rfl

/-- Meta credit commutes with a change of the lifetime observations. -/
theorem learnMeta_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (decision : PolicyDecision metaCount) :
    (relabel state lifetime).learnMeta features decision =
      relabel (state.learnMeta features decision) lifetime := by
  rw [TemporalControl.learnMeta_eq, TemporalControl.learnMeta_eq]
  split <;> rfl

/-- Dispatch of a drawn meta action commutes with a change of the lifetime
observations. -/
theorem dispatchMeta_relabel
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    (relabel state lifetime).dispatchMeta models features declared reward goal decision ended =
      (state.dispatchMeta models features declared reward goal decision ended).map
        (relabelResult lifetime) := by
  rw [TemporalControl.dispatchMeta_eq, TemporalControl.dispatchMeta_eq, learnMeta_relabel]
  generalize state.learnMeta features decision = learned
  cases skillOfMeta decision.action with
  | none => rfl
  | some slot =>
    dsimp only [relabel_runtime, relabel_valueFunction, relabel_skillRate, relabel_average]
    cases (learned.runtime.lifecycle.consumers.skills.get slot).interest.potential features
        declared with
    | none => rfl
    | some potential =>
      simp only [bind, Option.bind, pure, Option.map_some, withSkill_relabel,
        stepOption_relabel]

/-- A free dispatch commutes with a change of the lifetime observations. -/
theorem atBoundary_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) :
    (relabel state lifetime).atBoundary models plan features declared reward goal closing
        ended =
      (state.atBoundary models plan features declared reward goal closing ended).map
        (relabelResult lifetime) := by
  unfold TemporalControl.atBoundary
  simp only [refreshFree_relabel, planFree_relabel, drawMeta_relabel]
  generalize state.refreshFree closing = refreshed
  obtain ⟨free, owner⟩ := refreshed
  generalize (free.planFree plan features).drawMeta features = drawn
  cases owner with
  | none =>
    exact dispatchMeta_relabel drawn.1 lifetime models features declared reward goal drawn.2
      ended
  | some held =>
    simp only [closeOption_relabel]
    exact dispatchMeta_relabel _ lifetime models features declared reward goal drawn.2 _

/-- Selection commutes with a change of the lifetime observations: it neither reads nor
writes them, for every model operation and planning boundary. -/
theorem select_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) :
    (relabel state lifetime).selectWithOperations models plan features declared reward goal =
      (state.selectWithOperations models plan features declared reward goal).map
        (relabelResult lifetime) := by
  unfold TemporalControl.selectWithOperations
  rw [prepare_relabel]
  generalize state.prepareSelection models features reward = prepared
  dsimp only
  rw [serve_relabel]
  cases prepared.serve features with
  | some result => rfl
  | none =>
    simp only [Option.map_none]
    split
    · rfl
    · simp only [withPhase_relabel, relabel_runtime]
      cases prepared.runtime.references.phase with
      | idle =>
        exact atBoundary_relabel (prepared.withPhase .idle) lifetime models plan features
          declared reward goal none none
      | exploring committed =>
        exact atBoundary_relabel (prepared.withPhase .idle) lifetime models plan features
          declared reward goal none none
      | option slot activation =>
        generalize prepared.withPhase .idle = free
        dsimp only [relabel_runtime, relabel_metaRate, relabel_skillRate]
        cases (free.runtime.lifecycle.consumers.skills.get slot).interest.potential features
            declared with
        | none => rfl
        | some potential =>
          simp only [bind, Option.bind]
          cases (free.runtime.lifecycle.consumers.skills.get slot).decideOption activation
              features potential goal
              (comparisonValue criterion
                (free.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
                  features free.metaRate))
              free.skillRate with
          | continuing next =>
            simp only [withoutPlanning_relabel, stepOption_relabel, relabelResult,
              skipMeta_relabel, pure, Option.map_some]
          | ending reason =>
            cases criterion with
            | differential =>
              exact atBoundary_relabel free lifetime models plan features declared reward goal
                _ none
            | discounted =>
              simp only [closeOption_relabel]
              exact atBoundary_relabel _ lifetime models plan features declared reward goal
                none _

/-! ## The operations after selection -/

/-- The value an interrupted option's span closes toward does not read the lifetime
observations. -/
theorem takeoverValue_relabel
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (relabel state lifetime).takeoverValue features declared goal decision =
      state.takeoverValue features declared goal decision :=
  rfl

/-- Off-policy option learning commutes with a change of the lifetime observations. -/
theorem followOptions_relabel
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    (relabel state lifetime).followOptions models features declared reward goal decision =
      relabel (state.followOptions models features declared reward goal decision) lifetime := by
  rw [TemporalControl.followOptions_eq, TemporalControl.followOptions_eq]
  split <;> rfl

/-- Closing an interrupted option's span commutes with a change of the lifetime
observations. -/
theorem closeSpan_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (continuation : Option Binary32) :
    (relabel state lifetime).closeSpan continuation =
      relabel (state.closeSpan continuation) lifetime := by
  cases continuation with
  | none => rfl
  | some value =>
    rw [TemporalControl.closeSpan_eq, TemporalControl.closeSpan_eq]
    rfl

/-- The completion boundary reads the lifetime observations only to write them: its
learners are the same whatever they are. -/
theorem finish_learners (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    learners ((relabel state lifetime).finish features observation reward decision) =
      learners (state.finish features observation reward decision) := by
  by_cases frozen : profile.mode = .frozen <;>
    simp [learners, relabel, TemporalControl.finish_eq, TemporalControl.recordEpisodes,
      TemporalControl.predictionView, PredictionControl.advanceWith, frozen]

/-! ## The local transition and the full decision -/

/-- The local transition does not read the lifetime observations: from two states with
the same learners it returns the same decision and next states with the same learners,
and it refuses both or neither. -/
theorem step_learners
    (first second : TemporalControl interface profile config criterion dimension)
    (same : learners first = learners second) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
    (reward : Binary32) (goal : Bool) :
    (first.step planning features observation reward goal).map outcome =
      (second.step planning features observation reward goal).map outcome := by
  obtain ⟨lifetime, rfl⟩ : ∃ lifetime, second = relabel first lifetime :=
    ⟨second.lifetime, relabel_of_learners first second same⟩
  unfold TemporalControl.step TemporalControl.select
  rw [select_relabel]
  cases first.selectWithOperations (modelOperations criterion dimension)
      (planningBoundary planning) features observation.declared reward goal with
  | none => rfl
  | some result =>
    simp only [Option.map_some, bind, Option.bind, pure, relabelResult, takeoverValue_relabel,
      followOptions_relabel, closeSpan_relabel, outcome, finish_learners]

/-- The tester keeps the relation: from two agents with the same learners it returns
agents with the same learners, on the same unit outputs. -/
theorem retire_learners
    (first second : Agent interface profile config criterion dimension planning)
    (same : learners first.control = learners second.control)
    (units : Vector Bool config.units.count) :
    learners (first.retire units).control = learners (second.retire units).control := by
  unfold Agent.retire
  split
  · exact same
  · simp only [learners, Prod.mk.injEq] at same ⊢
    obtain ⟨runtime, credit, average, rate⟩ := same
    exact ⟨by rw [runtime], credit, average, rate⟩

/-- The clock advance keeps the relation. -/
theorem advance_learners
    (first second : Agent interface profile config criterion dimension planning)
    (same : learners first.control = learners second.control) :
    learners first.advanceClock.control = learners second.advanceClock.control := by
  simp only [learners, Agent.advanceClock, Prod.mk.injEq] at same ⊢
  obtain ⟨runtime, credit, average, rate⟩ := same
  exact ⟨by rw [runtime], credit, average, rate⟩

/-- The encoding of a frame does not read the lifetime observations: two agents with the
same learners give the same features and unit outputs. -/
theorem frame_learners
    (first second : Agent interface profile config criterion dimension planning)
    (same : learners first.control = learners second.control) (observation : Frame interface) :
    (first.frame observation).active = (second.frame observation).active ∧
      (first.frame observation).units = (second.frame observation).units := by
  have runtime : first.control.runtime = second.control.runtime := congrArg Prod.fst same
  refine ⟨?_, ?_⟩
  · rw [(first.frame observation).fresh, (second.frame observation).fresh]
    simp only [Agent.words_def]
    rw [runtime]
  · rw [(first.frame observation).freshUnits, (second.frame observation).freshUnits, runtime]

/-- The full decision does not read the lifetime observations. Two agents with the same
learners return the same decision on every percept, and agents with the same learners
after it, in every world interface, profile, criterion and planning selection. -/
theorem act_learners
    (first second : Agent interface profile config criterion dimension planning)
    (same : learners first.control = learners second.control) (percept : Percept interface) :
    (first.act percept).2 = (second.act percept).2 ∧
      learners (first.act percept).1.control = learners (second.act percept).1.control := by
  obtain ⟨firstNext, firstValid, firstEpisodes, firstStep, firstState⟩ :=
    first.act_execution percept
  obtain ⟨secondNext, secondValid, secondEpisodes, secondStep, secondState⟩ :=
    second.act_execution percept
  have advanced := advance_learners first second same
  have encoded := frame_learners first.advanceClock second.advanceClock advanced percept.frame
  have stepped := step_learners first.advanceClock.control second.advanceClock.control advanced
    planning (first.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved
  rw [← encoded.1] at secondStep
  rw [firstStep, secondStep] at stepped
  simp only [Option.map_some, Option.some.injEq, outcome, Prod.mk.injEq] at stepped
  refine ⟨stepped.2, ?_⟩
  rw [firstState, secondState, ← encoded.2]
  exact retire_learners ⟨firstNext, firstValid, firstEpisodes⟩
    ⟨secondNext, secondValid, secondEpisodes⟩ stepped.1 _

/-! ## Every step order -/

/-- The learning part reads the lifetime observations only to write them: its learners are the
same whatever they are. -/
theorem learn_learners (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    learners ((relabel state lifetime).learn features observation reward goal decision) =
      learners (state.learn features observation reward goal decision) := by
  unfold TemporalControl.learn
  simp only [takeoverValue_relabel, followOptions_relabel, closeSpan_relabel, finish_learners]

/-- The reward-free preparation commutes with a change of the lifetime observations. -/
theorem prepareDraw_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (relabel state lifetime).prepareDraw models features =
      relabel (state.prepareDraw models features) lifetime := by
  unfold TemporalControl.prepareDraw
  dsimp only
  split <;> rfl

/-- A served step that draws first commutes with a change of the lifetime observations. -/
theorem serveDraw_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension) :
    (relabel state lifetime).serveDraw features =
      (state.serveDraw features).map fun result => (relabel result.1 lifetime, result.2) := by
  unfold TemporalControl.serveDraw
  dsimp only [relabel_runtime]
  cases state.runtime.references.phase with
  | idle => rfl
  | option slot activation => rfl
  | exploring committed =>
    dsimp only
    cases committed.run.serve with
    | none => rfl
    | some pair =>
      simp only [bind, Option.bind, pure, Option.map_some, interrupt_relabel, withPhase_relabel]
      split <;> simp only [withoutPlanning_relabel, relabel_runtime]

/-- What `TemporalControl.drawBoundary` does after its refresh, planning and meta draw: draw the
primitive action or the first action of the selected option. -/
def drawDispatch (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (owed : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)) × Binary32))
    (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    Option (TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions) :=
  match skillOfMeta decision.action with
  | none =>
    let result := state.choosePrimitive features decision.snapshot.values (some decision) ended
    some (result.1, .boundary owed decision none, result.2)
  | some slot => do
    let skill := state.runtime.lifecycle.consumers.skills.get slot
    let potential ← skill.interest.potential features declared
    let policy := skill.frozenPolicy features state.skillRate
    let first := policy.drawPersistent state.runtime.references.rng
    let state := state.withPhase
      (Occupancy.afterOption slot (OptionActivation.first _ potential) first.1.run)
    let state := { state with runtime := { state.runtime with references :=
      { state.runtime.references with rng := first.2 } } }
    pure (state, .boundary owed decision (some ⟨slot, potential, first.1⟩),
      ⟨.option slot, first.1.action, policy.values, first.1.probabilities, first.1.explored,
        decision.snapshot.values, some decision, some slot, ended⟩)

set_option maxRecDepth 4096 in
/-- `TemporalControl.drawBoundary` is its refresh, planning and meta draw, then `drawDispatch`. -/
theorem drawBoundary_dispatch
    (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32) :
    state.drawBoundary plan features declared closing estimate =
      drawDispatch (((state.refreshFree closing).1.planFree plan features).drawMeta features).1
        features declared
        ((state.refreshFree closing).2.map fun held => (held, terminalValue criterion
          (((state.refreshFree closing).1.planFree plan features).drawMeta features).2 estimate))
        (((state.refreshFree closing).1.planFree plan features).drawMeta features).2
        ((state.refreshFree closing).2.map closingEvent) :=
  rfl

/-- `drawDispatch` commutes with a change of the lifetime observations. -/
theorem drawDispatch_relabel
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials)
    (owed : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)) × Binary32))
    (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    drawDispatch (relabel state lifetime) features declared owed decision ended =
      (drawDispatch state features declared owed decision ended).map
        fun result => (relabel result.1 lifetime, result.2) := by
  unfold drawDispatch
  cases skillOfMeta decision.action with
  | none => rfl
  | some slot =>
    dsimp only [relabel_runtime]
    cases (state.runtime.lifecycle.consumers.skills.get slot).interest.potential features
        declared with
    | none => rfl
    | some potential => rfl

/-- A free dispatch that draws first commutes with a change of the lifetime observations. -/
theorem drawBoundary_relabel
    (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32) :
    (relabel state lifetime).drawBoundary plan features declared closing estimate =
      (state.drawBoundary plan features declared closing estimate).map
        fun result => (relabel result.1 lifetime, result.2) := by
  rw [drawBoundary_dispatch, drawBoundary_dispatch]
  simp only [refreshFree_relabel, planFree_relabel, drawMeta_relabel]
  exact drawDispatch_relabel _ lifetime features declared _ _ _

/-- What `TemporalControl.drawFirst` does at a live option, from the state with its occupancy
cleared: the option continues and draws, or it ends at a free dispatch. -/
def drawOption (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen)) :
    Option (TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions) := do
  let skill := state.runtime.lifecycle.consumers.skills.get slot
  let potential ← skill.interest.potential features declared
  let metaPolicy := state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
    features state.metaRate
  let estimate := comparisonValue criterion metaPolicy
  match skill.decideOption activation features potential goal estimate state.skillRate with
  | .continuing next =>
    let drawn := next.policy.drawPersistent state.runtime.references.rng
    let state := state.withoutPlanning.withPhase
      (Occupancy.afterOption slot (activation.advance next) drawn.1.run)
    let state := { state with runtime := { state.runtime with references :=
      { state.runtime.references with rng := drawn.2 } } }
    pure (state, .continuing slot activation next drawn.1,
      ⟨.option slot, drawn.1.action, next.policy.values, drawn.1.probabilities,
        drawn.1.explored, metaPolicy.values, none, none, none⟩)
  | .ending reason =>
    state.drawBoundary plan features declared (some ⟨slot, ⟨activation, potential, reason⟩, none⟩)
      estimate

/-- `drawOption` commutes with a change of the lifetime observations. -/
theorem drawOption_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen)) :
    drawOption (relabel state lifetime) plan features declared goal slot activation =
      (drawOption state plan features declared goal slot activation).map
        fun result => (relabel result.1 lifetime, result.2) := by
  unfold drawOption
  dsimp only [relabel_runtime, relabel_metaRate, relabel_skillRate]
  cases (state.runtime.lifecycle.consumers.skills.get slot).interest.potential features
      declared with
  | none => rfl
  | some potential =>
    simp only [bind, Option.bind]
    cases (state.runtime.lifecycle.consumers.skills.get slot).decideOption activation
        features potential goal
        (comparisonValue criterion
          (state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
            features state.metaRate))
        state.skillRate with
    | continuing next => rfl
    | ending reason => exact drawBoundary_relabel state lifetime plan features declared _ _

/-- What `TemporalControl.drawFirst` does after its preparation at a step that serves no
committed run. -/
def drawFree (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions) :=
  if !profile.usesHierarchy then
    let result := (state.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero)
      none none
    some (result.1, .settled, result.2)
  else
    match state.runtime.references.phase with
    | .idle | .exploring _ => (state.withPhase .idle).drawBoundary plan features declared none .zero
    | .option slot activation =>
      drawOption (state.withPhase .idle) plan features declared goal slot activation

/-- `drawFree` commutes with a change of the lifetime observations. -/
theorem drawFree_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool) :
    drawFree (relabel state lifetime) plan features declared goal =
      (drawFree state plan features declared goal).map
        fun result => (relabel result.1 lifetime, result.2) := by
  unfold drawFree
  split
  · rfl
  · dsimp only [relabel_runtime]
    cases state.runtime.references.phase with
    | idle =>
      exact drawBoundary_relabel (state.withPhase .idle) lifetime plan features declared none .zero
    | exploring committed =>
      exact drawBoundary_relabel (state.withPhase .idle) lifetime plan features declared none .zero
    | option slot activation =>
      exact drawOption_relabel (state.withPhase .idle) lifetime plan features declared goal slot
        activation

/-- `TemporalControl.drawFirst` is its preparation, then a served step or `drawFree`. -/
theorem drawFirst_dispatch (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool) :
    state.drawFirst models plan features declared goal =
      match (state.prepareDraw models features).serveDraw features with
      | some result => some (result.1, .served result.2.1, result.2.2)
      | none => drawFree (state.prepareDraw models features) plan features declared goal := by
  unfold TemporalControl.drawFirst
  dsimp only
  cases (state.prepareDraw models features).serveDraw features <;> rfl

/-- Selection that draws before it credits commutes with a change of the lifetime
observations: it neither reads nor writes them, for every model operation and planning
boundary. -/
theorem drawFirst_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool) :
    (relabel state lifetime).drawFirst models plan features declared goal =
      (state.drawFirst models plan features declared goal).map
        fun result => (relabel result.1 lifetime, result.2) := by
  rw [drawFirst_dispatch, drawFirst_dispatch, prepareDraw_relabel, serveDraw_relabel]
  cases (state.prepareDraw models features).serveDraw features with
  | some result => rfl
  | none => exact drawFree_relabel _ lifetime plan features declared goal

/-- The owed reward commutes with a change of the lifetime observations. -/
theorem oweReward_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (reward : Binary32) :
    (relabel state lifetime).oweReward reward = relabel (state.oweReward reward) lifetime := by
  unfold TemporalControl.oweReward
  split <;> rfl

/-- The owed writes commute with a change of the lifetime observations. -/
theorem settle_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout)
    (owed : Owed interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) :
    (relabel state lifetime).settle owed models features reward goal =
      relabel (state.settle owed models features reward goal) lifetime := by
  have credit : ∀ (held : TemporalControl interface profile config criterion dimension)
      (slot : Fin Acorn.FeatureConstants.skillCount)
      (activation : OptionActivation (profile.mode != .frozen))
      (next : OptionContinuation interface.actions dimension activation)
      (drawn : PersistentDecision interface.actions),
      (relabel held lifetime).creditOption models slot activation next drawn reward =
        relabel (held.creditOption models slot activation next drawn reward) lifetime := by
    intro held slot activation next drawn
    rw [TemporalControl.creditOption_eq, TemporalControl.creditOption_eq]
    rfl
  have start : ∀ (held : TemporalControl interface profile config criterion dimension)
      (started : StartDraw interface) (estimate : Binary32),
      (relabel held lifetime).startOption models features started goal estimate reward =
        relabel (held.startOption models features started goal estimate reward) lifetime := by
    intro held started estimate
    rw [TemporalControl.startOption_eq, TemporalControl.startOption_eq]
    rfl
  cases owed with
  | settled => rfl
  | served skip =>
    cases skip <;> simp only [TemporalControl.settle, oweReward_relabel, skipMeta_relabel,
      Bool.false_eq_true, ↓reduceIte]
  | continuing slot activation next drawn =>
    simp only [TemporalControl.settle, oweReward_relabel, credit, skipMeta_relabel]
  | boundary closing decision started =>
    simp only [TemporalControl.settle, oweReward_relabel]
    cases closing <;> cases started <;>
      simp only [closeOption_relabel, learnMeta_relabel, start]

/-- The deferred work of a step order commutes with a change of the lifetime observations. -/
theorem deferred_relabel (state : TemporalControl interface profile config criterion dimension)
    (lifetime : Lifetime.Stats interface.layout) (order : StepOrder)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (owed : Owed interface profile config criterion dimension) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (relabel state lifetime).deferred order planning features owed reward goal decision =
      relabel (state.deferred order planning features owed reward goal decision) lifetime := by
  have after : ∀ held : TemporalControl interface profile config criterion dimension,
      (relabel held lifetime).planAfter planning features decision =
        relabel (held.planAfter planning features decision) lifetime := by
    intro held
    unfold TemporalControl.planAfter
    split <;> rfl
  cases order
  · rfl
  · exact after state
  · simp only [TemporalControl.deferred, settle_relabel, after]

/-- Two chosen values with one order, percept, encoding, decision and owed record, whose
temporal states differ in their lifetime observations, reach the same learners. -/
theorem chosen_learners
    (left right : Chosen interface profile config criterion dimension planning)
    (lifetime : Lifetime.Stats interface.layout) (order : left.order = right.order)
    (percept : left.percept = right.percept) (features : left.features = right.features)
    (decision : left.decision = right.decision) (owed : left.owed = right.owed)
    (control : right.control = relabel left.control lifetime) :
    learners left.learned.control = learners right.learned.control := by
  change learners ((left.control.deferred left.order planning left.features left.owed
      left.percept.reward left.percept.frame.achieved left.decision).learn left.features
      left.percept.frame left.percept.reward left.percept.frame.achieved left.decision) =
    learners ((right.control.deferred right.order planning right.features right.owed
      right.percept.reward right.percept.frame.achieved right.decision).learn right.features
      right.percept.frame right.percept.reward right.percept.frame.achieved right.decision)
  rw [← order, ← percept, ← features, ← decision, ← owed, control, deferred_relabel, learn_learners]

/-- **At every step order the agent's step reads its lifetime observations only to write
them.** Two agents with the same learners return the same decision on every percept, and agents
with the same learners after it, under each of the three orders, in every world interface,
profile, criterion and planning selection. Under `learnThenAct` this is `act_learners`
(`Agent.act_parts`). -/
theorem actOrdered_learners
    (first second : Agent interface profile config criterion dimension planning)
    (same : learners first.control = learners second.control) (order : StepOrder)
    (percept : Percept interface) :
    (first.actOrdered order percept).2 = (second.actOrdered order percept).2 ∧
      learners (first.actOrdered order percept).1.control =
        learners (second.actOrdered order percept).1.control := by
  have advanced := advance_learners first second same
  have encoded := frame_learners first.advanceClock second.advanceClock advanced percept.frame
  obtain ⟨lifetime, relabeled⟩ : ∃ lifetime, second.advanceClock.control =
      relabel first.advanceClock.control lifetime :=
    ⟨second.advanceClock.control.lifetime, relabel_of_learners _ _ advanced⟩
  have finished : ∀ decision : (first.choose order percept).decision =
        (second.choose order percept).decision,
      (first.choose order percept).units = (second.choose order percept).units →
      learners (first.choose order percept).learned.control =
        learners (second.choose order percept).learned.control →
      (first.actOrdered order percept).2 = (second.actOrdered order percept).2 ∧
        learners (first.actOrdered order percept).1.control =
          learners (second.actOrdered order percept).1.control := by
    intro decision units learned
    refine ⟨decision, ?_⟩
    change learners ((first.choose order percept).learned.retire
        (first.choose order percept).units).control =
      learners ((second.choose order percept).learned.retire
        (second.choose order percept).units).control
    rw [units]
    exact retire_learners _ _ learned _
  have selected : ∀ selects : order ≠ .actThenLearn,
      (first.actOrdered order percept).2 = (second.actOrdered order percept).2 ∧
        learners (first.actOrdered order percept).1.control =
          learners (second.actOrdered order percept).1.control := by
    intro selects
    obtain ⟨leftChosen, leftOrder, leftPercept, leftFeatures, leftUnits, leftOwed⟩ :=
      first.choose_selected order selects percept
    obtain ⟨rightChosen, rightOrder, rightPercept, rightFeatures, rightUnits, rightOwed⟩ :=
      second.choose_selected order selects percept
    have moved := select_relabel first.advanceClock.control lifetime
      (modelOperations criterion dimension) (planningBoundary (firstPlanning order planning))
      (first.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
      percept.frame.achieved
    have leftSelected : first.advanceClock.control.selectWithOperations
        (modelOperations criterion dimension) (planningBoundary (firstPlanning order planning))
        (first.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
        percept.frame.achieved = some ((first.choose order percept).control,
          (first.choose order percept).decision) := leftChosen
    have rightSelected : (relabel first.advanceClock.control lifetime).selectWithOperations
        (modelOperations criterion dimension) (planningBoundary (firstPlanning order planning))
        (first.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
        percept.frame.achieved = some ((second.choose order percept).control,
          (second.choose order percept).decision) := by
      rw [← relabeled, encoded.1]
      exact rightChosen
    rw [leftSelected, rightSelected, Option.map_some, Option.some.injEq] at moved
    have control := congrArg Prod.fst moved
    have decision := (congrArg Prod.snd moved).symm
    exact finished decision (leftUnits.trans (encoded.2.trans rightUnits.symm))
      (chosen_learners _ _ lifetime (leftOrder.trans rightOrder.symm)
        (leftPercept.trans rightPercept.symm)
        (leftFeatures.trans (encoded.1.trans rightFeatures.symm)) decision
        (leftOwed.trans rightOwed.symm) control)
  cases order with
  | learnThenAct => exact selected (by decide)
  | planAfterAct => exact selected (by decide)
  | actThenLearn =>
    obtain ⟨leftChosen, leftOrder, leftPercept, leftFeatures, leftUnits⟩ :=
      first.choose_drawn percept
    obtain ⟨rightChosen, rightOrder, rightPercept, rightFeatures, rightUnits⟩ :=
      second.choose_drawn percept
    have moved := drawFirst_relabel first.advanceClock.control lifetime
      (modelOperations criterion dimension) (planningBoundary .none)
      (first.advanceClock.frame percept.frame).active percept.frame.declared percept.frame.achieved
    rw [leftChosen, ← relabeled, encoded.1, rightChosen, Option.map_some, Option.some.injEq]
      at moved
    have control := congrArg Prod.fst moved
    have rest := (congrArg Prod.snd moved).symm
    have owed := congrArg Prod.fst rest
    have decision := congrArg Prod.snd rest
    exact finished decision (leftUnits.trans (encoded.2.trans rightUnits.symm))
      (chosen_learners _ _ lifetime (leftOrder.trans rightOrder.symm)
        (leftPercept.trans rightPercept.symm)
        (leftFeatures.trans (encoded.1.trans rightFeatures.symm)) decision owed control)

/-! ## Host accounting -/

/-- Environment accounting keeps every learner, in every world interface. -/
theorem recordEnvironment_learners
    (state : Agent interface profile config criterion dimension planning) (family : Fin 4)
    (reward : Binary32) :
    learners (state.recordEnvironment family reward).control = learners state.control :=
  rfl

/-- Attempt accounting keeps every learner, in every world interface. -/
theorem recordAttempt_learners
    (state : Agent interface profile config criterion dimension planning) (family : Fin 4)
    (cycle steps : UInt64) (achieved : Bool) :
    learners (state.recordAttempt family cycle steps achieved).control =
      learners state.control :=
  rfl

/-- Censoring the pending observations at process exit keeps every learner. -/
theorem censor_learners (state : Agent interface profile config criterion dimension planning) :
    learners state.censorObservations.control = learners state.control :=
  rfl

/-- A host operation that keeps the learners changes neither the next decision nor the
learners after it. Environment accounting, attempt accounting and censoring are such
operations. -/
theorem act_accounting (state : Agent interface profile config criterion dimension planning)
    (account : Agent interface profile config criterion dimension planning →
      Agent interface profile config criterion dimension planning)
    (isolated : ∀ current, learners (account current).control = learners current.control)
    (percept : Percept interface) :
    ((account state).act percept).2 = (state.act percept).2 ∧
      learners ((account state).act percept).1.control =
        learners (state.act percept).1.control :=
  act_learners (account state) state (isolated state) percept

/-! ## The closed loop -/

/-- The executed agent's actions are a function of its learners: from two agent states
with the same learners, the executed agent takes the same action at every time, in every
world over its interface and from every start state. -/
theorem executed_actions
    (first second : Agent interface profile config criterion dimension planning)
    (same : learners first.control = learners second.control)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    Kernel.actionAt world (CurrentGridWorld.executedAgent first) start time =
      Kernel.actionAt world (CurrentGridWorld.executedAgent second) start time :=
  related_actions (first := CurrentGridWorld.executedAgent first)
    (second := CurrentGridWorld.executedAgent second)
    (fun (left right : Agent interface profile config criterion dimension planning) =>
      learners left.control = learners right.control)
    same
    (fun left right percept held =>
      ⟨congrArg TemporalDecision.action (act_learners left right held percept).1,
        (act_learners left right held percept).2⟩)
    world start time

end AcornVerif.CurrentAccounting
