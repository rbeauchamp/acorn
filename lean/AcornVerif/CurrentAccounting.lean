/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix
import AcornVerif.CurrentGridWorld

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
included. `act_accounting` concludes that a host operation that keeps the learners
changes neither the next decision nor the learners after it.

The proof follows the executed step. Every operation of selection commutes with a change
of the lifetime observations (`select_relabel` and the lemmas before it); the completion
boundary `TemporalControl.finish` is the one operation that reads them, and it reads
them only to write them (`finish_learners`).

The achievement event of a frame does reach a learner. It is departure D8, and
`AcornVerif.CurrentOak` states, for each operation that takes it, that the operation
reads it through stopping decisions only.

`executed_actions` carries the result to the closed loop of the kernel: from two agent
states with the same learners, the executed agent takes the same action at every time,
in every world over its interface. The other theorems concern single decisions. No
theorem here composes them along a run of the host: the kernel instance of
`AcornVerif.CurrentGridWorld` does not model the host's reports between decisions.
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
    unfold Agent.words
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

/-- Two agents of the kernel take the same actions in every world when a relation of
their memories holds at the start and every decision keeps it and gives one action. -/
theorem related_actions {first second : Kernel.Agent interface}
    (related : first.Memory → second.Memory → Prop)
    (initial : related first.initial second.initial)
    (kept : ∀ left right percept, related left right →
      (first.act left percept).1 = (second.act right percept).1 ∧
        related (first.act left percept).2 (second.act right percept).2)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    Kernel.actionAt world first start time = Kernel.actionAt world second start time := by
  have held : ∀ count,
      (Kernel.loop world first start count).1 = (Kernel.loop world second start count).1 ∧
        related (Kernel.loop world first start count).2
          (Kernel.loop world second start count).2 := by
    intro count
    induction count with
    | zero => exact ⟨rfl, initial⟩
    | succ count ih =>
      have decided := kept _ _ (world.percept (Kernel.loop world first start count).1) ih.2
      change world.step (Kernel.loop world first start count).1
            (first.act (Kernel.loop world first start count).2
              (world.percept (Kernel.loop world first start count).1)).1 =
          world.step (Kernel.loop world second start count).1
            (second.act (Kernel.loop world second start count).2
              (world.percept (Kernel.loop world second start count).1)).1 ∧
        related
          (first.act (Kernel.loop world first start count).2
            (world.percept (Kernel.loop world first start count).1)).2
          (second.act (Kernel.loop world second start count).2
            (world.percept (Kernel.loop world second start count).1)).2
      rw [← ih.1]
      exact ⟨congrArg _ decided.1, decided.2⟩
  have decided := kept _ _ (world.percept (Kernel.loop world first start time).1) (held time).2
  change (first.act (Kernel.loop world first start time).2
      (world.percept (Kernel.loop world first start time).1)).1 =
    (second.act (Kernel.loop world second start time).2
      (world.percept (Kernel.loop world second start time).1)).1
  rw [← (held time).1]
  exact decided.1

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
