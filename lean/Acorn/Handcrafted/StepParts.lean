/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Agent
import Acorn.Timing

/-!
# The two parts of the agent's step

`Agent.act` is one function from a percept to the next agent and a decision. This
module states the step as two functions under a declared `Acorn.StepOrder`.
`Agent.choose` runs the step up to the point where the decision is known: the clock,
the encoding of the percept's frame, and selection. `Chosen.learn` runs everything
after that point: off-policy learning of the options that are not executing, the
closing of an interrupted option's meta span, primitive credit, the prediction demons,
every option's questions, and the tester.

Under `learnThenAct` the two parts compose to `Agent.act`, for every agent state and
percept, in every world (`Agent.act_parts`). Under `planAfterAct` selection runs with
no planning, and the planning of a free boundary is the first work of the second part
(`TemporalControl.planAfter`). The two orders differ at a free dispatch only: a step
whose decision records no meta decision is the executed step under both
(`Agent.actOrdered_undrawn`, from `TemporalControl.select_unplanned`). This is PAR-19;
the source of the reordering is cited in `Acorn.Timing`.

What each draw of the first part reads, in both orders unless an order is named. Each
statement is about the operation that makes the draw; which operation a step calls is
the definition of selection.

- A served exploration step repeats the action of its run and consumes no draw
  (`TemporalControl.serve_frame`). The values its decision reports are read from the
  controllers.
- A primitive draw is the persistent draw from the primitive controller of the state it
  is made in (`TemporalControl.choosePrimitive_snapshot`). Its weights are those the
  step started from: selection writes neither that controller nor a prediction demon
  (`TemporalControl.select_keeps`). Its exploration rate is the one this step's rate
  schedule has advanced to.
- A continuing option draws from its own policy, frozen at the decision's frame
  (`Skill.decide_policy`, `Skill.step_drawn`). Before that decision selection writes the
  rate schedule, the owed meta reward and the model caches, and no learner or objective
  (`TemporalControl.prepare_lifecycle`).
- The meta draw of a free dispatch reads the meta-controller after the assignment
  refresh and after the planning selection runs (`TemporalControl.atBoundary_meta`).
  Under `planAfterAct` selection runs no planning, so the draw reads the refreshed
  meta-controller before this frame's planning (`TemporalControl.atBoundary_unplanned`).
  It is the one draw that reads the meta-controller.
- An option that starts draws its first action from its own policy after the terminal
  credit and the settlement that this percept causes (`Skill.beginTemporal_policy`), in
  both orders. The settlement, and under the differential criterion the terminal credit,
  are computed from the frozen snapshot of the drawn meta decision, so this draw can
  read different weights under the two orders as well. Moving those two writes after
  the draw needs a draw and a credit that are separate functions of the option learner;
  it is not built.

The decision keeps the frozen snapshot of the drawn meta decision, and the order changes
every later read of it, because it changes the snapshot. The first part has three. The
settlement of an option that starts takes its stopping estimate from the snapshot
(`TemporalControl.dispatchMeta`, `Skill.settleTemporal`). Under the differential
criterion the terminal credit of the option that closes takes the snapshot's value of
the drawn meta action (`TemporalControl.atBoundary`, `TemporalControl.closeOption`). The
on-policy credit of the meta decision forms its error and stores its lag from that same
value (`TemporalControl.learnMeta`, `Controller.valuesStep_lag`). The second part has
one: the off-policy learning of every option that is not executing compares against a
stopping estimate that is read from the snapshot (`TemporalControl.stoppingEstimate`,
`TemporalControl.followOptions`, `Skill.followTemporal`), so the stopping decision of
such an option's stored trajectory and the stopping value that a stop credits to its
policy (`Skill.stopFollowing`) can differ under the two orders at a frame that records a
meta decision. The decision also reports the snapshot's values and probabilities to an
observer. Two closings in the first part read the meta-controller itself, as the current
value function, which under `planAfterAct` holds no planning of this frame: the model of
the option that closes under the differential criterion (`Skill.endTemporal`) and the
model of a stored trajectory that the settlement stops (`Skill.stopFollowing`).
`TemporalControl.takeoverValue` uses the same stopping estimate on a served step only.
That step records no meta decision (`TemporalControl.serve_undrawn`), so the estimate is
read from the decision's own meta values and the current rate, and the two orders are
one step there (`Agent.actOrdered_undrawn`). No theorem states the difference of one of
these reads: each follows from the definitions named, with
`TemporalControl.atBoundary_meta` and `TemporalControl.atBoundary_unplanned`.

The assignment refresh precedes the draws in both orders. It reads no part of the
percept: it is a function of the Demon-0 weights and the objectives the step started
from (`TemporalControl.select_assigns`).

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

/-! ## What the meta draw and the primitive draw read -/

/-- A fresh primitive choice is the persistent draw from the frozen primitive controller
of the state it is made in, at the supplied features and that state's control rate. The
action, the masses and the exploration flag of the decision are that draw's, and the
reported values are the snapshot's. -/
theorem TemporalControl.choosePrimitive_snapshot
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (metaValues : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    let snapshot := state.runtime.lifecycle.consumers.control.snapshot
      (count := interface.actions) features state.controlRate
    let drawn := snapshot.drawPersistent state.runtime.references.rng
    let decision := (state.choosePrimitive features metaValues metaDecision ended).2
    decision.action = drawn.1.action ∧ decision.values = snapshot.values ∧
      decision.probabilities = drawn.1.probabilities ∧ decision.explored = drawn.1.explored :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **What the meta draw reads.** For every free dispatch and every planning parameter,
the meta decision the dispatch records is the draw from the meta-controller of the
state after the assignment refresh and after that planning, at the supplied features
and that state's meta rate. No later write of the dispatch precedes it. -/
theorem TemporalControl.atBoundary_meta
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.atBoundary models plan features declared reward goal closing ended =
      some (next, decision)) :
    decision.metaDecision =
      some (((state.refreshFree closing).1.planFree plan features).drawMeta features).2 := by
  unfold TemporalControl.atBoundary at executed
  generalize state.refreshFree closing = refreshed at executed ⊢
  dsimp only at executed
  generalize (refreshed.1.planFree plan features).drawMeta features = drawn at executed ⊢
  revert executed
  cases refreshed.2 with
  | none =>
    intro executed
    exact (drawn.1.dispatchMeta_interest models features declared reward goal drawn.2 ended
      next decision executed).1
  | some owner =>
    intro executed
    exact (TemporalControl.dispatchMeta_interest _ models features declared reward goal drawn.2
      _ next decision executed).1

/-- The meta draw freezes the meta-controller of the state it is made in. -/
theorem TemporalControl.drawMeta_snapshot
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (state.drawMeta features).2.snapshot =
      state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount) features
        state.metaRate :=
  rfl

/-- With no planning selected, the free boundary's planning step writes no learner and
no rate source: the meta-controller and the meta rate are those before it. -/
theorem TemporalControl.planFree_none
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (state.planFree (planningBoundary .none) features).runtime.lifecycle.consumers.metaController =
        state.runtime.lifecycle.consumers.metaController ∧
      (state.planFree (planningBoundary .none) features).metaRate = state.metaRate := by
  unfold TemporalControl.planFree
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- **The meta draw before planning.** For every free dispatch that runs no planning,
the meta decision is drawn from the frozen meta-controller of the refreshed state: the
values that controller holds before this frame's planning, at that state's meta rate. -/
theorem TemporalControl.atBoundary_unplanned
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.atBoundary models (planningBoundary .none) features declared reward goal
      closing ended = some (next, decision)) :
    ∃ drawn : PolicyDecision metaCount, decision.metaDecision = some drawn ∧
      drawn.snapshot = (state.refreshFree closing).1.runtime.lifecycle.consumers.metaController.snapshot
        (count := metaCount) features (state.refreshFree closing).1.metaRate := by
  refine ⟨_, state.atBoundary_meta models (planningBoundary .none) features declared reward goal
    closing ended next decision executed, ?_⟩
  have kept := (state.refreshFree closing).1.planFree_none features
  rw [TemporalControl.drawMeta_snapshot, kept.1, kept.2]

/-- **A decision with no meta decision ran no planning.** For every executed selection
whose decision records no meta decision, selection with every other planning function
returns the same state and the same decision. Selection calls its planning function at
a free dispatch only, and every free dispatch records a meta decision
(`TemporalControl.atBoundary_meta`). -/
theorem TemporalControl.select_unplanned
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan other : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision))
    (undrawn : decision.metaDecision = none) :
    state.selectWithOperations models other features declared reward goal =
      some (next, decision) := by
  have drawn : ∀ (origin : TemporalControl interface profile config criterion dimension)
      (closing : Option (Closing interface.actions config criterion dimension interface.layout
        (EndingPayload (profile.mode != .frozen)))) (ended : Option EndEvent),
      origin.atBoundary models plan features declared reward goal closing ended =
        some (next, decision) → False := by
    intro origin closing ended boundary
    have recorded := origin.atBoundary_meta models plan features declared reward goal closing
      ended next decision boundary
    rw [undrawn] at recorded
    cases recorded
  unfold TemporalControl.selectWithOperations at executed ⊢
  generalize state.prepareSelection models features reward = prepared at executed ⊢
  dsimp only at executed ⊢
  revert executed
  cases served : prepared.serve features with
  | some result => exact id
  | none =>
    simp only
    split
    · exact id
    · split
      · exact fun executed => (drawn _ _ _ executed).elim
      · exact fun executed => (drawn _ _ _ executed).elim
      · rename_i slot activation phase
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [bind, Option.bind]
        | some value =>
          simp only [bind, Option.bind]
          split
          · exact id
          · intro executed
            split at executed
            · exact (drawn _ _ _ executed).elim
            · exact (drawn _ _ _ executed).elim

/-! ## Planning after the action -/

/-- The planning selection the first part runs under a step order: the configured one
when both parts precede the action, none when planning follows the action. -/
def firstPlanning (order : StepOrder) (planning : PlanningSelection) : PlanningSelection :=
  match order with
  | .learnThenAct => planning
  | .planAfterAct => .none

/-- Planning after the action: at a decision that drew a meta decision, which is a free
dispatch, the boundary's configured planning on the selected state. Every other
decision plans nothing, as selection plans nothing there. The planning function is
the one selection calls under the default order; only its position differs, so it
reads the meta-controller after that decision's on-policy credit. That credit has
stored the decision's value before planning as the controller's lag
(`Controller.valuesStep_lag`), and planning keeps the lag, so the next meta credit
forms its error from a value that this planning has since changed at the same feature
vector. -/
def TemporalControl.planAfter
    (selected : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  if decision.metaDecision.isSome then selected.planFree (planningBoundary planning) features
  else selected

/-- The state the second part starts from under a step order: the selected state, with
the deferred planning when planning follows the action. -/
def TemporalControl.deferred
    (selected : TemporalControl interface profile config criterion dimension)
    (order : StepOrder) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  match order with
  | .learnThenAct => selected
  | .planAfterAct => selected.planAfter planning features decision

/-- Deferred planning writes the meta-controller and the planning references only: the
lifetime record, the executing option and the action generator are the selected
state's, under both orders. -/
theorem TemporalControl.deferred_frame
    (selected : TemporalControl interface profile config criterion dimension)
    (order : StepOrder) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (decision : TemporalDecision interface.actions) :
    (selected.deferred order planning features decision).lifetime = selected.lifetime ∧
      (selected.deferred order planning features decision).activeSlot = selected.activeSlot ∧
      (selected.deferred order planning features decision).runtime.references.rng =
        selected.runtime.references.rng := by
  cases order
  · exact ⟨rfl, rfl, rfl⟩
  · unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact ⟨rfl, rfl, rfl⟩

/-- Deferred planning keeps every declared option source matched. -/
theorem TemporalControl.deferred_aligned
    (selected : TemporalControl interface profile config criterion dimension)
    (aligned : selected.Aligned) (order : StepOrder) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions) :
    (selected.deferred order planning features decision).Aligned := by
  cases order
  · exact aligned
  · unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact aligned

/-- Deferred planning writes neither the primitive controller nor a prediction demon. -/
theorem TemporalControl.deferred_keeps
    (selected origin : TemporalControl interface profile config criterion dimension)
    (kept : selected.Keeps origin) (order : StepOrder) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions) :
    (selected.deferred order planning features decision).Keeps origin := by
  cases order
  · exact kept
  · unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact kept

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

/-- A selected state of an aligned state is aligned, for every planning selection. -/
theorem TemporalControl.select_aligned
    (state next : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.select planning features observation.declared reward goal =
      some (next, decision)) : next.Aligned := by
  obtain ⟨other, chosen, accepted, valid⟩ := state.select_total aligned
    (modelOperations criterion dimension) (planningBoundary planning) features observation
    reward goal
  have selected : state.selectWithOperations (modelOperations criterion dimension)
      (planningBoundary planning) features observation.declared reward goal =
        some (next, decision) := executed
  have same := Option.some.inj (selected.symm.trans accepted)
  cases same
  exact valid

/-- The learning part keeps every declared option source matched, from any aligned
state. -/
theorem TemporalControl.learn_aligned
    (middle : TemporalControl interface profile config criterion dimension)
    (aligned : middle.Aligned) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (middle.learn features observation reward goal decision).Aligned :=
  TemporalControl.finish_aligned _ (TemporalControl.closeSpan_aligned _
    (middle.followOptions_aligned aligned (modelOperations criterion dimension) features
      observation.declared reward goal decision) _) features observation reward decision

/-- The learning part keeps the episode accounting, from any state that holds the
lifetime record and the executing option that selection returned. The planning
parameter of that selection is arbitrary. -/
theorem TemporalControl.learn_episodes
    (state selected middle : TemporalControl interface profile config criterion dimension)
    (valid : state.Episodes) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features observation.declared reward goal =
      some (selected, decision))
    (lifetime : middle.lifetime = selected.lifetime)
    (active : middle.activeSlot = selected.activeSlot) :
    (middle.learn features observation reward goal decision).Episodes := by
  have trace := state.select_episodes selected models plan features observation.declared reward
    goal decision valid.2 executed
  have follow := middle.follow_episodes (modelOperations criterion dimension) features
    observation.declared reward goal decision
  unfold TemporalControl.learn
  dsimp only
  generalize middle.followOptions (modelOperations criterion dimension) features
    observation.declared reward goal decision = followed at follow ⊢
  have closed := followed.closeSpan_episodes
    (middle.takeoverValue features observation.declared goal decision)
  generalize followed.closeSpan
    (middle.takeoverValue features observation.declared goal decision) = spanned at closed ⊢
  constructor
  · change Lifetime.OptionsValid
      (spanned.finish features observation reward decision).lifetime.options spanned.activeSlot
    rw [TemporalControl.finish_options, closed.1, closed.2, follow.1, follow.2, lifetime, active,
      trace.1]
    apply trace.2.record_valid _ decision.episodeEnd _ valid.1
    simp [TemporalDecision.episodeEnd, Option.map_map, Function.comp_def]
  · intro primitive
    change spanned.activeSlot = none
    rw [closed.2, follow.2, active]
    exact state.select_primitive selected models plan features observation.declared reward goal
      decision primitive executed

/-- A selected state and decision determine the completed local transition of the
default order: the learning part on them. -/
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

/-- What the agent holds between the two parts of one step: the step order, the
percept, its encoding, the temporal state selection returned, and the decision. The
decision's action is the action of the step. The two proofs state that the second part
of this value is a legal agent; they are erased. The planning selection is carried as
an index, so a chosen value returns to an agent of the type it came from. In this
module `Agent.choose` is the one use of the constructor, so the order a chosen value
holds is the order its selection ran under. The constructor is private, which stops the
constructor notation and the constructor name outside this module and does not stop a
tactic; no check stops a module of this project from making a chosen value. -/
structure Chosen (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) where
  private mk ::
  /-- The order the first part ran under; the second part completes the same order. -/
  order : StepOrder
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
  /-- The second part keeps every declared option source matched. -/
  aligned : ((control.deferred order planning features decision).learn features percept.frame
    percept.reward percept.frame.achieved decision).Aligned
  /-- The second part keeps the episode accounting. -/
  episodes : ((control.deferred order planning features decision).learn features percept.frame
    percept.reward percept.frame.achieved decision).Episodes

/-- The first part of the step under a step order, from one percept: advance the clock,
encode the frame under the current bank and the stored predictions, and select with
the planning that order places before the action. The result holds everything the
second part reads. -/
def Agent.choose (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    Chosen interface profile config criterion dimension planning :=
  let prepared := state.advanceClock
  let frame := prepared.frame percept.frame
  let selected := prepared.control.alignedSelect prepared.aligned (firstPlanning order planning)
    frame.active percept.frame percept.reward percept.frame.achieved
  have kept := selected.1.1.deferred_frame order planning frame.active selected.1.2
  ⟨order, percept, frame.active, frame.units, selected.1.1, selected.1.2,
    TemporalControl.learn_aligned _
      (selected.1.1.deferred_aligned
        (prepared.control.select_aligned selected.1.1 prepared.aligned
          (firstPlanning order planning) frame.active percept.frame percept.reward
          percept.frame.achieved selected.1.2 selected.2)
        order planning frame.active selected.1.2)
      frame.active percept.frame percept.reward percept.frame.achieved selected.1.2,
    prepared.control.learn_episodes selected.1.1 _ prepared.episodes
      (modelOperations criterion dimension) (planningBoundary (firstPlanning order planning))
      frame.active percept.frame percept.reward percept.frame.achieved selected.1.2 selected.2
      kept.1 kept.2.1⟩

/-- The agent of a chosen value after every update that follows selection, before the
tester: the deferred planning of its order, then the learning part. -/
def Chosen.learned (chosen : Chosen interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨(chosen.control.deferred chosen.order planning chosen.features chosen.decision).learn
    chosen.features chosen.percept.frame chosen.percept.reward chosen.percept.frame.achieved
    chosen.decision, chosen.aligned, chosen.episodes⟩

/-- The second part of the step: the planning its order places after the action, every
update that follows selection, then the receiver-owned tester on the same frame's unit
outputs. It reads the chosen value only. -/
def Chosen.learn (chosen : Chosen interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  chosen.learned.retire chosen.units

/-- The whole step under a step order: the first part, then the second on its result. -/
def Agent.actOrdered (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    Agent interface profile config criterion dimension planning ×
      TemporalDecision interface.actions :=
  ((state.choose order percept).learn, (state.choose order percept).decision)

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

/-- The first part selects with the executed selection, on the once-advanced clock, the
encoding of the percept's frame and the planning its order places before the action; a
chosen value holds exactly that result. -/
theorem Agent.choose_selected (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    state.advanceClock.control.select (firstPlanning order planning)
        (state.advanceClock.frame percept.frame).active
        percept.frame.declared percept.reward percept.frame.achieved =
      some ((state.choose order percept).control, (state.choose order percept).decision) ∧
    (state.choose order percept).order = order ∧
    (state.choose order percept).percept = percept ∧
    (state.choose order percept).features = (state.advanceClock.frame percept.frame).active ∧
    (state.choose order percept).units = (state.advanceClock.frame percept.frame).units :=
  ⟨(state.advanceClock.control.alignedSelect state.advanceClock.aligned
    (firstPlanning order planning) (state.advanceClock.frame percept.frame).active percept.frame
    percept.reward percept.frame.achieved).2, rfl, rfl, rfl, rfl⟩

/-- **Under the default order the two parts compose to the step.** For every agent state
and percept, in every world, the executed step returns the agent the second part
returns on the chosen value, and the chosen decision. -/
theorem Agent.act_parts (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.act percept = state.actOrdered .learnThenAct percept := by
  have stepped := state.advanceClock.control.step_selected planning
    (state.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved _ _ (state.choose_selected .learnThenAct percept).1
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
    (state.choose .learnThenAct percept).learned controls
    (state.advanceClock.frame percept.frame).units

/-- Under the default order the decision of the first part is the decision of the whole
step. -/
theorem Agent.choose_decision (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.choose .learnThenAct percept).decision = (state.act percept).2 :=
  (congrArg Prod.snd (state.act_parts percept)).symm

/-- **What the first part does not write.** Under both orders, for every agent state and
percept, the chosen value holds the primitive controller and the prediction demons the
agent held before the percept. The decision is therefore made while the reward of
this percept has reached neither. The first part does write the meta-controller and
the options. -/
theorem Agent.choose_keeps (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    (state.choose order percept).control.Keeps state.control :=
  TemporalControl.select_keeps state.advanceClock.control (modelOperations criterion dimension)
    (planningBoundary (firstPlanning order planning))
    (state.advanceClock.frame percept.frame).active
    percept.frame.declared percept.reward percept.frame.achieved _ _
    (state.choose_selected order percept).1

/-- **The two orders differ at a free dispatch only.** For every agent state and percept
whose decision under planning after the action records no meta decision, the whole
step of that order is the executed step: the same next agent and the same decision.
Every free dispatch records a meta decision (`TemporalControl.atBoundary_meta`), so the
steps on which the orders can differ are those with a free dispatch. -/
theorem Agent.actOrdered_undrawn
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface)
    (undrawn : (state.choose .planAfterAct percept).decision.metaDecision = none) :
    state.actOrdered .planAfterAct percept = state.act percept := by
  rw [Agent.act_parts]
  have before : state.advanceClock.control.selectWithOperations
      (modelOperations criterion dimension) (planningBoundary planning)
      (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
      percept.frame.achieved = some ((state.choose .learnThenAct percept).control,
        (state.choose .learnThenAct percept).decision) :=
    (state.choose_selected .learnThenAct percept).1
  have moved := state.advanceClock.control.select_unplanned
    (modelOperations criterion dimension) (planningBoundary .none) (planningBoundary planning)
    (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
    percept.frame.achieved _ _ (state.choose_selected .planAfterAct percept).1 undrawn
  have same := Option.some.inj (moved.symm.trans before)
  have controls := congrArg Prod.fst same
  have decisions := congrArg Prod.snd same
  dsimp only at controls decisions
  refine Prod.ext ?_ decisions
  refine Agent.retire_control (state.choose .planAfterAct percept).learned
    (state.choose .learnThenAct percept).learned ?_
    (state.advanceClock.frame percept.frame).units
  change ((state.choose .planAfterAct percept).control.planAfter planning
        (state.advanceClock.frame percept.frame).active
        (state.choose .planAfterAct percept).decision).learn
      (state.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved (state.choose .planAfterAct percept).decision =
    (state.choose .learnThenAct percept).control.learn
      (state.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved (state.choose .learnThenAct percept).decision
  rw [← controls, ← decisions]
  unfold TemporalControl.planAfter
  simp only [undrawn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

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

/-- The learning part of a local transition leaves the action generator as it received
it, for every state, frame, reward word and decision. -/
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

/-- **The second part makes no action draw.** Under both orders, for every chosen value,
the agent the second part returns holds the action generator the first part left.
Every draw of an action, of a meta action and of an exploration run is in the first
part. The tester's replacement draws are from the feature generator's own stream. -/
theorem Chosen.learn_rng (chosen : Chosen interface profile config criterion dimension planning) :
    chosen.learn.control.runtime.references.rng = chosen.control.runtime.references.rng :=
  ((chosen.learned.retire_rng chosen.units).trans
    ((chosen.control.deferred chosen.order planning chosen.features chosen.decision).learn_rng
      chosen.features chosen.percept.frame chosen.percept.reward chosen.percept.frame.achieved
      chosen.decision)).trans
    (chosen.control.deferred_frame chosen.order planning chosen.features chosen.decision).2.2

end Acorn.Handcrafted
