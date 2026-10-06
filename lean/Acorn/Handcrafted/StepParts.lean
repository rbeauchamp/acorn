/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Agent

/-!
# The two parts of the agent's step

`Agent.act` is one function from a percept to the next agent and a decision. This
module states it as two functions. `Agent.choose` runs the step up to the point where
the decision is known: the clock, the encoding of the percept's frame, and selection.
`Chosen.learn` runs everything after that point: off-policy learning of the options
that are not executing, the closing of an interrupted option's meta span, primitive
credit, the prediction demons, every option's questions, and the tester.
`Agent.act_parts` proves that the two compose to `Agent.act`, for every agent state
and percept, in every world.

A host can release the action between the two parts (`Acorn.StepOrder.actThenLearn`)
or after both (`Acorn.StepOrder.learnThenAct`); PAR-19, with the source cited in
`Acorn.Timing`. Neither order reorders any computation of the agent: both run the same
first part and then the same second part on its result. Only the world's transition
moves, and it is no input of the second part. The decision of the first part is the
decision of the whole step (`Agent.choose_decision`).

Selection is not a pure read. It contains the assignment refresh and planning of a
free boundary, a closing option's terminal credit, the settlement of a newly selected
option, and the on-policy credit of the meta-controller and of the executing option.
All of that is in the first part. `Agent.choose_keeps` states what the first part does
not write: the primitive controller and the prediction demons. The reward of a percept
reaches those two in the second part only.

The second part draws nothing from the action generator (`Chosen.learn_rng`). Its
tester draws from the feature generator's own stream when it replaces a unit.
-/
namespace Acorn.Handcrafted
open Features

variable {interface : Interface} {actions : Word.Count} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {planning : PlanningSelection} {discounts : List Discount} {shape : PatchShape}
    {payload : Type}

/-! ## What selection does not write -/

/-- The actual installation fold never writes the primitive controller. -/
theorem _root_.Acorn.Features.FreeDispatch.fold_control
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    (slots.foldl (fun current slot => current.install slot targets[slot.val])
      state).lifecycle.consumers.control = state.lifecycle.consumers.control := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    exact (ih (state.install slot targets[slot.val])).trans
      (state.install_preserves slot targets[slot.val]).2

/-- The complete free-boundary refresh, assigning or not, writes neither the primitive
controller nor a prediction demon. -/
theorem _root_.Acorn.Features.FreeDispatch.refreshModels_critics
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (assign : Bool) :
    (state.refreshModels assign).lifecycle.consumers.control =
        state.lifecycle.consumers.control ∧
      (state.refreshModels assign).lifecycle.consumers.demons =
        state.lifecycle.consumers.demons := by
  cases assign with
  | false =>
    rw [FreeDispatch.refreshModels_keep]
    exact ⟨state.rerankModels_preserves.2.2.2.2.1, state.rerankModels_preserves.2.2.2.2.2⟩
  | true =>
    rw [FreeDispatch.refreshModels_assign]
    refine ⟨state.refreshRanked.rerankModels_preserves.2.2.2.2.1.trans ?_,
      state.refreshRanked.rerankModels_preserves.2.2.2.2.2.trans state.refresh_demons⟩
    unfold FreeDispatch.refreshRanked
    exact FreeDispatch.fold_control _ _ _

/-- One temporal state holds the primitive controller and the prediction demons of
another: no operation between the two wrote either. -/
abbrev TemporalControl.Keeps
    (next origin : TemporalControl interface profile config criterion dimension) : Prop :=
  next.runtime.lifecycle.consumers.control = origin.runtime.lifecycle.consumers.control ∧
    next.runtime.lifecycle.consumers.demons = origin.runtime.lifecycle.consumers.demons

/-- A skipped meta decision advances the deferred meta clock only. -/
theorem TemporalControl.skipMeta_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) : state.skipMeta.Keeps origin := by
  unfold TemporalControl.skipMeta
  split <;> exact kept

/-- Selection preparation writes clocks, the owed meta reward and the model caches. -/
theorem TemporalControl.prepare_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).Keeps origin := by
  unfold TemporalControl.prepareSelection
  dsimp only
  split <;> split <;> exact kept

/-- A fresh primitive choice reads the primitive controller and writes occupancy and
the generator state. -/
theorem TemporalControl.primitive_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (ended : Option EndEvent) :
    (state.choosePrimitive features values decision ended).1.Keeps origin :=
  kept

/-- Replacing one option writes the option table only. -/
theorem TemporalControl.withSkill_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (state.withSkill slot skill).Keeps origin :=
  kept

/-- Interrupting a held option writes that option's trajectory link only. -/
theorem TemporalControl.interrupt_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin)
    (held : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) : (state.interrupt held).1.Keeps origin := by
  cases held with
  | none => exact kept
  | some held =>
    obtain ⟨slot, activation⟩ := held
    unfold TemporalControl.interrupt
    dsimp only
    split <;> exact kept

/-- A served run writes occupancy, diagnostics and an interrupted option's trajectory
link. -/
theorem TemporalControl.serve_keeps
    (state next origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension)
    (decision : TemporalDecision interface.actions)
    (served : state.serve features = some (next, decision)) : next.Keeps origin := by
  unfold TemporalControl.serve at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      rw [← served.1]
      have base := state.interrupt_keeps origin kept committed.origin
      repeat' split
      all_goals first
        | exact base
        | exact TemporalControl.skipMeta_keeps ((state.interrupt committed.origin).1.withPhase
            (.exploring (.bare pair.2))) origin base
  · contradiction
  · contradiction

/-- A stepped option writes its own policy and model, occupancy and the generator state. -/
theorem TemporalControl.stepOption_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (started : Bool) (ended : Option EndEvent) :
    (state.stepOption models slot activation next reward values decision started
      ended).1.Keeps origin := by
  rw [TemporalControl.stepOption_eq]
  exact kept

/-- Terminal credit writes the closing option, or nothing for a detached owner. -/
theorem TemporalControl.closeOption_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1.Keeps origin := by
  rw [TemporalControl.closeOption_eq]
  dsimp only
  cases closing.oldOwner with
  | none => exact kept
  | some owner => exact kept

/-- The free-boundary refresh writes objectives, option storage, the meta-controller's
reset rows and the model caches. -/
theorem TemporalControl.refreshFree_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).1.Keeps origin := by
  have critics := FreeDispatch.refreshModels_critics
    (⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩ :
      FreeDispatch interface.symbols interface.actions config criterion dimension interface.signals
        (EndingPayload (profile.mode != .frozen))) profile.ranksSubtasks
  exact ⟨critics.1.trans kept.1, critics.2.trans kept.2⟩

/-- Planning writes the meta-controller and the planning references. -/
theorem TemporalControl.planFree_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) : (state.planFree plan features).Keeps origin :=
  kept

/-- The meta draw writes the generator state. -/
theorem TemporalControl.drawMeta_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension) :
    (state.drawMeta features).1.Keeps origin :=
  kept

/-- Meta credit writes the meta-controller and the meta span. -/
theorem TemporalControl.learnMeta_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension)
    (decision : PolicyDecision metaCount) : (state.learnMeta features decision).Keeps origin := by
  rw [TemporalControl.learnMeta_eq]
  split <;> exact kept

/-- The dispatch of a drawn meta decision writes the meta-controller, the selected
option, occupancy and the generator state. -/
theorem TemporalControl.dispatchMeta_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : PolicyDecision metaCount) (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension)
    (selected : TemporalDecision interface.actions)
    (executed : state.dispatchMeta models features declared reward goal decision ended =
      some (next, selected)) : next.Keeps origin := by
  rw [TemporalControl.dispatchMeta_eq] at executed
  have learnedKept := state.learnMeta_keeps origin kept features decision
  generalize state.learnMeta features decision = learned at executed learnedKept
  dsimp only at executed
  split at executed
  · cases executed
    exact learnedKept
  · rename_i slot _
    cases potential : (learned.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at executed
      generalize step : TemporalControl.stepOption _ _ _ _ _ _ _ _ _ _ = result at executed
      obtain ⟨rfl, rfl⟩ : result.1 = next ∧ result.2 = selected := by
        rw [executed]
        exact ⟨rfl, rfl⟩
      rw [← step]
      exact TemporalControl.stepOption_keeps _ origin
        (learned.withSkill_keeps origin learnedKept slot _) _ _ _ _ _ _ _ _ _

/-- A free dispatch writes neither the primitive controller nor a prediction demon. -/
theorem TemporalControl.atBoundary_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.atBoundary models plan features declared reward goal closing ended =
      some (next, decision)) : next.Keeps origin := by
  unfold TemporalControl.atBoundary at executed
  have refreshedKept := state.refreshFree_keeps origin kept closing
  generalize state.refreshFree closing = refreshed at executed refreshedKept
  dsimp only at executed
  have drawnKept : ((refreshed.1.planFree plan features).drawMeta features).1.Keeps origin :=
    refreshedKept
  generalize (refreshed.1.planFree plan features).drawMeta features = drawn at executed drawnKept
  revert executed
  cases refreshed.2 with
  | none =>
    intro executed
    exact drawn.1.dispatchMeta_keeps origin drawnKept models features declared reward goal
      drawn.2 ended next decision executed
  | some owner =>
    intro executed
    exact TemporalControl.dispatchMeta_keeps _ origin
      (drawn.1.closeOption_keeps origin drawnKept models features owner reward _)
      models features declared reward goal drawn.2 _ next decision executed

/-- **What selection does not write.** For every state, frame, reward word and
selection branch, the state selection returns holds the primitive controller and the
prediction demons of the state it started from. Selection reads the primitive
controller for its primitive draw and the Demon-0 weights for its assignment refresh;
it writes neither. -/
theorem TemporalControl.select_keeps
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision)) : next.Keeps state := by
  unfold TemporalControl.selectWithOperations at executed
  have preparedKept := state.prepare_keeps state ⟨rfl, rfl⟩ models features reward
  generalize state.prepareSelection models features reward = prepared at executed preparedKept
  dsimp only at executed
  revert executed
  cases served : prepared.serve features with
  | some result =>
    intro executed
    obtain ⟨rfl, _⟩ := selected_eq executed
    exact prepared.serve_keeps result.1 state preparedKept features result.2 served
  | none =>
    intro executed
    simp only at executed
    split at executed
    · obtain ⟨rfl, _⟩ := selected_eq executed
      exact preparedKept
    · split at executed
      · exact (prepared.withPhase .idle).atBoundary_keeps state preparedKept models plan features
          declared reward goal none none next decision executed
      · exact (prepared.withPhase .idle).atBoundary_keeps state preparedKept models plan features
          declared reward goal none none next decision executed
      · rename_i slot activation phase
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          split at executed
          · obtain ⟨rfl, _⟩ := selected_eq executed
            exact TemporalControl.skipMeta_keeps _ state
              (TemporalControl.stepOption_keeps (prepared.withPhase .idle).withoutPlanning state
                preparedKept _ _ _ _ _ _ _ _ _)
          · split at executed
            · exact (prepared.withPhase .idle).atBoundary_keeps state preparedKept models plan
                features declared reward goal _ none next decision executed
            · generalize closedEq : (prepared.withPhase .idle).closeOption models features _ reward
                _ = closed at executed
              have closedKept : closed.1.Keeps state :=
                closedEq ▸ (prepared.withPhase .idle).closeOption_keeps state preparedKept models
                  features _ reward _
              exact closed.1.atBoundary_keeps state closedKept models plan features declared
                reward goal none _ next decision executed

/-! ## The two parts -/

/-- Selection with its totality proof. The proof closes the potential-source premise
and is erased. -/
def TemporalControl.alignedSelect
    (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (goal : Bool) :
    { result : TemporalControl interface profile config criterion dimension ×
        TemporalDecision interface.actions //
      state.select planning features observation.declared reward goal = some result } :=
  match executed : state.select planning features observation.declared reward goal with
  | none => False.elim (by
      obtain ⟨next, decision, accepted, _⟩ := state.select_total aligned
        (modelOperations criterion dimension) (planningBoundary planning) features observation
        reward goal
      have refused : state.selectWithOperations (modelOperations criterion dimension)
          (planningBoundary planning) features observation.declared reward goal = none := executed
      rw [refused] at accepted
      contradiction)
  | some result => ⟨result, rfl⟩

/-- A completed local transition from an aligned state is aligned. -/
theorem TemporalControl.step_aligned
    (state next : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.step planning features observation reward goal = some (next, decision)) :
    next.Aligned := by
  obtain ⟨other, chosen, accepted, valid⟩ :=
    state.step_total aligned planning features observation reward goal
  have same := Option.some.inj (executed.symm.trans accepted)
  cases same
  exact valid

/-- A selected state and decision determine the completed local transition: the
learning part on them. -/
theorem TemporalControl.step_selected
    (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool)
    (selected : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.select planning features observation.declared reward goal =
      some (selected, decision)) :
    state.step planning features observation reward goal =
      some (selected.learn features observation reward goal decision, decision) :=
  (state.step_parts planning features observation reward goal).trans
    (congrArg (Option.map fun chosen : TemporalControl interface profile config criterion dimension ×
        TemporalDecision interface.actions =>
      (chosen.1.learn features observation reward goal chosen.2, chosen.2)) executed)

/-- What the agent holds between the two parts of one step: the percept, its encoding,
the temporal state selection returned, and the decision. The decision's action is the
action of the step. The two proofs state that the learning part of this value is a
legal agent; they are erased. The planning selection is carried as an index, so a
chosen value returns to an agent of the type it came from. -/
structure Chosen (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) where
  /-- The percept both parts read. -/
  percept : Percept interface
  /-- Active features of the percept's frame, under the bank selection read. -/
  features : SwiftTd.ActiveSet dimension
  /-- Outputs of the generated units on the same frame, for the tester. -/
  units : Vector Bool config.units.count
  /-- Temporal state after selection. -/
  control : TemporalControl interface profile config criterion dimension
  /-- The decision selection made. -/
  decision : TemporalDecision interface.actions
  /-- The learning part keeps every declared option source matched. -/
  aligned : (control.learn features percept.frame percept.reward percept.frame.achieved
    decision).Aligned
  /-- The learning part keeps the episode accounting. -/
  episodes : (control.learn features percept.frame percept.reward percept.frame.achieved
    decision).Episodes

/-- The first part of the step, from one percept: advance the clock, encode the frame
under the current bank and the stored predictions, and select. The result holds
everything the second part reads. -/
def Agent.choose (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) : Chosen interface profile config criterion dimension planning :=
  let prepared := state.advanceClock
  let frame := prepared.frame percept.frame
  let selected := prepared.control.alignedSelect prepared.aligned planning frame.active
    percept.frame percept.reward percept.frame.achieved
  have stepped : prepared.control.step planning frame.active percept.frame percept.reward
      percept.frame.achieved = some (selected.1.1.learn frame.active percept.frame percept.reward
        percept.frame.achieved selected.1.2, selected.1.2) :=
    prepared.control.step_selected planning frame.active percept.frame percept.reward
      percept.frame.achieved selected.1.1 selected.1.2 selected.2
  ⟨percept, frame.active, frame.units, selected.1.1, selected.1.2,
    prepared.control.step_aligned _ prepared.aligned planning frame.active percept.frame
      percept.reward percept.frame.achieved selected.1.2 stepped,
    prepared.control.step_episodes _ prepared.episodes planning frame.active percept.frame
      percept.reward percept.frame.achieved selected.1.2 stepped⟩

/-- The agent of a chosen value after every update that follows selection, before the
tester. -/
def Chosen.learned (chosen : Chosen interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨chosen.control.learn chosen.features chosen.percept.frame chosen.percept.reward
    chosen.percept.frame.achieved chosen.decision, chosen.aligned, chosen.episodes⟩

/-- The second part of the step: every update that follows selection, then the
receiver-owned tester on the same frame's unit outputs. It reads the chosen value
only. -/
def Chosen.learn (chosen : Chosen interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  chosen.learned.retire chosen.units

/-- Two agents with the same temporal state are the same agent. -/
theorem Agent.ext_control {left right : Agent interface profile config criterion dimension planning}
    (same : left.control = right.control) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- The tester applied to two agents with one temporal state returns one agent. -/
theorem Agent.retire_control
    (left right : Agent interface profile config criterion dimension planning)
    (same : left.control = right.control) (active : Vector Bool config.units.count) :
    left.retire active = right.retire active :=
  congrArg (fun agent : Agent interface profile config criterion dimension planning =>
    agent.retire active) (Agent.ext_control same)

/-- The first part selects with the executed selection, on the once-advanced clock and
the encoding of the percept's frame; a chosen value holds exactly that result. -/
theorem Agent.choose_selected (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.advanceClock.control.select planning (state.advanceClock.frame percept.frame).active
        percept.frame.declared percept.reward percept.frame.achieved =
      some ((state.choose percept).control, (state.choose percept).decision) ∧
    (state.choose percept).percept = percept ∧
    (state.choose percept).features = (state.advanceClock.frame percept.frame).active ∧
    (state.choose percept).units = (state.advanceClock.frame percept.frame).units :=
  ⟨(state.advanceClock.control.alignedSelect state.advanceClock.aligned planning
    (state.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved).2, rfl, rfl, rfl⟩

/-- **The two parts compose to the step.** For every agent state and percept, in every
world, the executed step returns the agent the learning part returns on the chosen
value, and the chosen decision. -/
theorem Agent.act_parts (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.act percept = ((state.choose percept).learn, (state.choose percept).decision) := by
  have stepped := state.advanceClock.control.step_selected planning
    (state.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved _ _ (state.choose_selected percept).1
  let result := state.advanceClock.control.alignedStep state.advanceClock.aligned planning
    (state.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved
  have same := Option.some.inj (result.2.1.symm.trans stepped)
  have controls := congrArg Prod.fst same
  have decisions := congrArg Prod.snd same
  refine Prod.ext ?_ decisions
  exact Agent.retire_control
    (Agent.mk result.1.1 result.2.2 (state.advanceClock.control.step_episodes result.1.1
      state.advanceClock.episodes planning (state.advanceClock.frame percept.frame).active
      percept.frame percept.reward percept.frame.achieved result.1.2 result.2.1))
    (state.choose percept).learned controls (state.advanceClock.frame percept.frame).units

/-- The decision is known after the first part: it is the decision of the whole step. -/
theorem Agent.choose_decision (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.choose percept).decision = (state.act percept).2 :=
  (congrArg Prod.snd (state.act_parts percept)).symm

/-- **What the first part does not write.** For every agent state and percept, the
chosen value holds the primitive controller and the prediction demons the agent held
before the percept. The decision is therefore made while the reward of this percept
has reached neither, whether a host releases the action before the second part or
after it. The first part does write the meta-controller and the options. -/
theorem Agent.choose_keeps (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.choose percept).control.Keeps state.control :=
  TemporalControl.select_keeps state.advanceClock.control (modelOperations criterion dimension)
    (planningBoundary planning) (state.advanceClock.frame percept.frame).active
    percept.frame.declared percept.reward percept.frame.achieved _ _
    (state.choose_selected percept).1

/-! ## The second part and the action generator -/

/-- Off-policy option learning consumes no draw of the action generator. -/
theorem TemporalControl.followOptions_rng
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (state.followOptions models features declared reward goal decision).runtime.references.rng =
      state.runtime.references.rng := by
  rw [TemporalControl.followOptions_eq]
  split <;> rfl

/-- Closing an interrupted option's meta span consumes no draw of the action generator. -/
theorem TemporalControl.closeSpan_rng
    (state : TemporalControl interface profile config criterion dimension)
    (continuation : Option Binary32) :
    (state.closeSpan continuation).runtime.references.rng = state.runtime.references.rng := by
  cases continuation with
  | none => rfl
  | some value =>
    exact (congrArg (fun next : TemporalControl interface profile config criterion dimension =>
      next.runtime.references.rng) (state.closeSpan_eq value)).trans rfl

/-- The completion boundary consumes no draw of the action generator. -/
theorem TemporalControl.finish_rng
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.references.rng =
      state.runtime.references.rng :=
  (congrArg (fun next : TemporalControl interface profile config criterion dimension =>
    next.runtime.references.rng) (state.finish_eq features obs reward decision)).trans rfl

/-- The learning part of a local transition leaves the action generator as selection
left it, for every selected state, frame, reward word and decision. -/
theorem TemporalControl.learn_rng
    (selected : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    (selected.learn features obs reward goal decision).runtime.references.rng =
      selected.runtime.references.rng :=
  ((TemporalControl.finish_rng _ features obs reward decision).trans
    (TemporalControl.closeSpan_rng _ _)).trans
    (selected.followOptions_rng (modelOperations criterion dimension) features obs.declared
      reward goal decision)

/-- The tester leaves the action generator untouched. -/
theorem Agent.retire_rng (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (state.retire active).control.runtime.references.rng =
      state.control.runtime.references.rng := by
  unfold Agent.retire
  split
  · rfl
  · exact congrArg (·.rng) (state.control.runtime.retire_references active)

/-- **The second part makes no action draw.** For every chosen value, the agent the
second part returns holds the action generator the first part left. Every draw of an
action, of a meta action and of an exploration run is in the first part. The tester's
replacement draws are from the feature generator's own stream. -/
theorem Chosen.learn_rng (chosen : Chosen interface profile config criterion dimension planning) :
    chosen.learn.control.runtime.references.rng = chosen.control.runtime.references.rng :=
  (chosen.learned.retire_rng chosen.units).trans
    (chosen.control.learn_rng chosen.features chosen.percept.frame chosen.percept.reward
      chosen.percept.frame.achieved chosen.decision)

end Acorn.Handcrafted
