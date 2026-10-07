/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Agent
import Acorn.Handcrafted.DrawFirst
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
(`TemporalControl.planAfter`). These two orders can differ at a free dispatch only: a step
whose decision records no meta decision is the executed step under both
(`Agent.actOrdered_undrawn`, from `TemporalControl.select_unplanned`). This is PAR-19;
the source of the reordering is cited in `Acorn.Timing`.

Under `actThenLearn` the first part is not selection. It is the draw-first dispatch of
`Acorn.Handcrafted.DrawFirst`, which makes every draw of the step and takes no reward
word (`Agent.chooseDrawn`, `Agent.choose_reward`), and the chosen value holds the record of
the writes that dispatch owes. The second part makes those writes from the reward
(`TemporalControl.settle`), then plans as under `planAfterAct`, then learns. This is
PAR-20. `AcornVerif.DrawFirst` states where this step is the step of `planAfterAct` and
where it can differ.

What each draw of the first part reads, under `learnThenAct` and `planAfterAct` unless
an order is named. Each statement is about the operation that makes the draw; which
operation a step calls is the definition of selection. Under `actThenLearn` the first
four draws are made by the same operations, before the writes that selection makes
after them, and the last is drawn from another policy, as its item says.

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
  credit and the settlement that this percept causes (`Skill.beginTemporal_policy`),
  under `learnThenAct` and `planAfterAct`. The settlement, and under the differential
  criterion the terminal credit, are computed from the frozen snapshot of the drawn meta
  decision, so this draw can read different weights under those two orders as well.
  Under `actThenLearn` it draws from its frozen policy as the preceding step left it,
  after the assignment refresh (`Skill.frozenPolicy`, `TemporalControl.drawBoundary`),
  and those two writes follow the action.

The next paragraph compares `learnThenAct` with `planAfterAct`. Under `actThenLearn` the
meta draw reads what it reads under `planAfterAct`
(`AcornVerif.DrawFirst.drawBoundary_unplanned`), and each write the paragraph places in
the first part is in the second part, after the action.

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

The assignment refresh precedes the draws in every order. It reads no part of the
percept: it is a function of the Demon-0 weights and the objectives the step started
from (`TemporalControl.select_assigns` for selection; `AcornVerif.DrawFirst.drawFirst_assigns`
for the draw-first dispatch).

The second part draws nothing from the action generator in any order
(`Chosen.learn_rng`). Its tester draws from the feature generator's own stream when it
replaces a unit.
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
  | .planAfterAct | .actThenLearn => .none

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
the deferred planning when planning follows the action. Under `actThenLearn` the first
part made no write that reads the reward, so the second part first makes the owed
writes of the record the first part returned (`TemporalControl.settle`), and then the
deferred planning. The other orders owe nothing and read neither the record nor the
reward here. -/
def TemporalControl.deferred
    (selected : TemporalControl interface profile config criterion dimension)
    (order : StepOrder) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (owed : Owed interface profile config criterion dimension) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  match order with
  | .learnThenAct => selected
  | .planAfterAct => selected.planAfter planning features decision
  | .actThenLearn =>
    (selected.settle owed (modelOperations criterion dimension) features reward goal).planAfter
      planning features decision

/-- The owed writes and deferred planning record no episode, move no activation and draw
nothing: the lifetime record, the executing option and the action generator are the
selected state's, under every order. -/
theorem TemporalControl.deferred_frame
    (selected : TemporalControl interface profile config criterion dimension)
    (order : StepOrder) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (owed : Owed interface profile config criterion dimension) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (selected.deferred order planning features owed reward goal decision).lifetime =
        selected.lifetime ∧
      (selected.deferred order planning features owed reward goal decision).activeSlot =
        selected.activeSlot ∧
      (selected.deferred order planning features owed reward goal
        decision).runtime.references.rng = selected.runtime.references.rng := by
  cases order
  · exact ⟨rfl, rfl, rfl⟩
  · unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact ⟨rfl, rfl, rfl⟩
  · have settled := selected.settle_framed owed (modelOperations criterion dimension) features
      reward goal
    unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact ⟨settled.1, congrArg Occupancy.executing settled.2.1, settled.2.2⟩

/-- The owed writes and deferred planning keep every declared option source matched. -/
theorem TemporalControl.deferred_aligned
    (selected : TemporalControl interface profile config criterion dimension)
    (aligned : selected.Aligned) (order : StepOrder) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension)
    (owed : Owed interface profile config criterion dimension) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (selected.deferred order planning features owed reward goal decision).Aligned := by
  cases order
  · exact aligned
  · unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact aligned
  · have settled := selected.settle_aligned aligned owed (modelOperations criterion dimension)
      features reward goal
    unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact settled

/-- The owed reward writes the meta span only. -/
theorem TemporalControl.oweReward_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (reward : Binary32) : (state.oweReward reward).Keeps origin := by
  unfold TemporalControl.oweReward
  split <;> exact kept

/-- The credit of a drawn decision writes the option table only. -/
theorem TemporalControl.creditOption_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (drawn : PersistentDecision interface.actions) (reward : Binary32) :
    (state.creditOption models slot activation next drawn reward).Keeps origin := by
  rw [TemporalControl.creditOption_eq]
  exact kept

/-- The start of a selected option writes the option table only. -/
theorem TemporalControl.startOption_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (start : StartDraw interface) (goal : Bool)
    (estimate reward : Binary32) :
    (state.startOption models features start goal estimate reward).Keeps origin := by
  rw [TemporalControl.startOption_eq]
  exact kept

/-- **What the owed writes do not write.** For every state, record, frame and reward
word, the settled state holds the primitive controller and the prediction demons it
was given. -/
theorem TemporalControl.settle_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (owed : Owed interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) :
    (state.settle owed models features reward goal).Keeps origin := by
  have owedKept := state.oweReward_keeps origin kept reward
  cases owed with
  | settled => exact kept
  | served skip =>
    cases skip
    · exact owedKept
    · exact TemporalControl.skipMeta_keeps _ origin owedKept
  | continuing slot activation next drawn =>
    exact TemporalControl.skipMeta_keeps _ origin
      ((state.oweReward reward).creditOption_keeps origin owedKept models slot activation next
        drawn reward)
  | boundary closing decision start =>
    have closedKept : (match closing with
        | none => state.oweReward reward
        | some closing => ((state.oweReward reward).closeOption models features closing.1 reward
            closing.2).1).Keeps origin := by
      cases closing with
      | none => exact owedKept
      | some closing =>
        exact (state.oweReward reward).closeOption_keeps origin owedKept models features
          closing.1 reward closing.2
    have learnedKept := TemporalControl.learnMeta_keeps _ origin closedKept features decision
    cases start with
    | none => exact learnedKept
    | some start =>
      exact TemporalControl.startOption_keeps _ origin learnedKept models features start goal _
        reward

/-- The owed writes and deferred planning write neither the primitive controller nor a
prediction demon. -/
theorem TemporalControl.deferred_keeps
    (selected origin : TemporalControl interface profile config criterion dimension)
    (kept : selected.Keeps origin) (order : StepOrder) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension)
    (owed : Owed interface profile config criterion dimension) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (selected.deferred order planning features owed reward goal decision).Keeps origin := by
  cases order
  · exact kept
  · unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact kept
  · have settled := selected.settle_keeps origin kept owed (modelOperations criterion dimension)
      features reward goal
    unfold TemporalControl.deferred TemporalControl.planAfter
    dsimp only
    split <;> exact settled

/-! ## What a draw-first selection does not write -/

/-- The reward-free preparation writes the rate schedule and the model caches. -/
theorem TemporalControl.prepareDraw_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : (state.prepareDraw models features).Keeps origin := by
  unfold TemporalControl.prepareDraw
  dsimp only
  split <;> exact kept

/-- A served step that draws first writes occupancy, diagnostics and an interrupted
option's trajectory link. -/
theorem TemporalControl.serveDraw_keeps
    (state next origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension) (skip : Bool)
    (decision : TemporalDecision interface.actions)
    (served : state.serveDraw features = some (next, skip, decision)) : next.Keeps origin := by
  unfold TemporalControl.serveDraw at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      rw [← served.1]
      have base := state.interrupt_keeps origin kept committed.origin
      split <;> exact base
  · contradiction
  · contradiction

/-- A free dispatch that draws first writes neither the primitive controller nor a
prediction demon. -/
theorem TemporalControl.drawBoundary_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.drawBoundary plan features declared closing estimate =
      some (next, owed, decision)) : next.Keeps origin := by
  unfold TemporalControl.drawBoundary at executed
  have refreshedKept := state.refreshFree_keeps origin kept closing
  generalize state.refreshFree closing = refreshed at executed refreshedKept
  dsimp only at executed
  have drawnKept : ((refreshed.1.planFree plan features).drawMeta features).1.Keeps origin :=
    refreshedKept
  generalize (refreshed.1.planFree plan features).drawMeta features = drawn at executed drawnKept
  split at executed
  · cases executed
    exact drawnKept
  · rename_i slot selected
    cases potential : (drawn.1.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at executed
      cases executed
      exact drawnKept

/-- **What a draw-first selection does not write.** For every state, frame and
selection branch, the state it returns holds the primitive controller and the
prediction demons of the state it started from. -/
theorem TemporalControl.drawFirst_keeps
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.drawFirst models plan features declared goal = some (next, owed, decision)) :
    next.Keeps state := by
  unfold TemporalControl.drawFirst at executed
  have preparedKept := state.prepareDraw_keeps state ⟨rfl, rfl⟩ models features
  generalize state.prepareDraw models features = prepared at executed preparedKept
  dsimp only at executed
  revert executed
  cases served : prepared.serveDraw features with
  | some result =>
    intro executed
    cases executed
    exact prepared.serveDraw_keeps result.1 state preparedKept features result.2.1 result.2.2 served
  | none =>
    intro executed
    simp only at executed
    split at executed
    · cases executed
      exact preparedKept
    · split at executed
      · exact (prepared.withPhase .idle).drawBoundary_keeps state preparedKept plan features
          declared none .zero next owed decision executed
      · exact (prepared.withPhase .idle).drawBoundary_keeps state preparedKept plan features
          declared none .zero next owed decision executed
      · rename_i slot activation phase
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          split at executed
          · simp only [pure, Option.some.injEq] at executed
            cases executed
            exact preparedKept
          · exact (prepared.withPhase .idle).drawBoundary_keeps state preparedKept plan features
              declared _ _ next owed decision executed

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
lifetime record and the executing option of a selected state whose decision records the
complete start and end transition of the step. Selection and the draw-first selection
both return such a state (`TemporalControl.select_episodes`,
`TemporalControl.drawFirst_episodes`). -/
theorem TemporalControl.learn_traced
    (state selected middle : TemporalControl interface profile config criterion dimension)
    (valid : state.Episodes) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions)
    (trace : selected.lifetime = state.lifetime ∧
      EpisodeTrace state.activeSlot (decision.ended.map (·.slot)) decision.started
        selected.activeSlot)
    (primitive : profile.usesHierarchy = false → selected.activeSlot = none)
    (lifetime : middle.lifetime = selected.lifetime)
    (active : middle.activeSlot = selected.activeSlot) :
    (middle.learn features observation reward goal decision).Episodes := by
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
  · intro hierarchy
    change spanned.activeSlot = none
    rw [closed.2, follow.2, active]
    exact primitive hierarchy

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
    (middle.learn features observation reward goal decision).Episodes :=
  state.learn_traced selected middle valid features observation reward goal decision
    (state.select_episodes selected models plan features observation.declared reward goal decision
      valid.2 executed)
    (fun primitive => state.select_primitive selected models plan features observation.declared
      reward goal decision primitive executed)
    lifetime active

/-- Draw-first selection with its totality proof. The proof closes the potential-source
premise and is erased. It runs the no-planning boundary: planning follows the action. -/
def TemporalControl.alignedDraw
    (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (goal : Bool) :
    { result : TemporalControl interface profile config criterion dimension ×
        Owed interface profile config criterion dimension × TemporalDecision interface.actions //
      state.drawFirst (modelOperations criterion dimension) (planningBoundary .none) features
        observation.declared goal = some result } :=
  match executed : state.drawFirst (modelOperations criterion dimension) (planningBoundary .none)
      features observation.declared goal with
  | none => False.elim (by
      obtain ⟨next, owed, decision, accepted, _⟩ := state.drawFirst_total aligned
        (modelOperations criterion dimension) (planningBoundary .none) features observation goal
      rw [executed] at accepted
      contradiction)
  | some result => ⟨result, rfl⟩

/-- The state a draw-first selection returns from an aligned state is aligned. -/
theorem TemporalControl.drawFirst_aligned
    (state next : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (goal : Bool)
    (owed : Owed interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.drawFirst (modelOperations criterion dimension) (planningBoundary .none)
      features observation.declared goal = some (next, owed, decision)) : next.Aligned := by
  obtain ⟨other, due, chosen, accepted, valid⟩ := state.drawFirst_total aligned
    (modelOperations criterion dimension) (planningBoundary .none) features observation goal
  have same := Option.some.inj (executed.symm.trans accepted)
  cases same
  exact valid

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
percept, its encoding, the temporal state the first part returned, the decision, and
the writes the first part owes. The decision's action is the action of the step. The
two proofs state that the second part of this value is a legal agent; they are erased.
The planning selection is carried as an index, so a chosen value returns to an agent of
the type it came from. In this module `Agent.chooseSelected` and `Agent.chooseDrawn` are
the two uses of the constructor, and `Agent.choose` calls each for its own orders, so
the order a chosen value holds is the order its first part ran under. The constructor is
private, which stops the constructor notation and the constructor name outside this
module and does not stop a tactic; no check stops a module of this project from making a
chosen value. -/
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
  /-- Temporal state after the first part. -/
  control : TemporalControl interface profile config criterion dimension
  /-- The decision the first part made. -/
  decision : TemporalDecision interface.actions
  /-- The writes the first part owes; nothing, when the first part is selection. -/
  owed : Owed interface profile config criterion dimension
  /-- The second part keeps every declared option source matched. -/
  aligned : ((control.deferred order planning features owed percept.reward percept.frame.achieved
    decision).learn features percept.frame percept.reward percept.frame.achieved decision).Aligned
  /-- The second part keeps the episode accounting. -/
  episodes : ((control.deferred order planning features owed percept.reward
    percept.frame.achieved decision).learn features percept.frame percept.reward
    percept.frame.achieved decision).Episodes

/-- The first part of the step of an order whose first part is selection, from one
percept: advance the clock, encode the frame under the current bank and the stored
predictions, and select with the planning that order places before the action. The
result holds everything the second part reads, and owes nothing. The hypothesis is
erased: it keeps selection from making a chosen value of `actThenLearn`, whose first
part is the draw-first dispatch. -/
def Agent.chooseSelected (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (_selects : order ≠ .actThenLearn) (percept : Percept interface) :
    Chosen interface profile config criterion dimension planning :=
  let prepared := state.advanceClock
  let frame := prepared.frame percept.frame
  let selected := prepared.control.alignedSelect prepared.aligned (firstPlanning order planning)
    frame.active percept.frame percept.reward percept.frame.achieved
  have kept := selected.1.1.deferred_frame order planning frame.active .settled percept.reward
    percept.frame.achieved selected.1.2
  ⟨order, percept, frame.active, frame.units, selected.1.1, selected.1.2, .settled,
    TemporalControl.learn_aligned _
      (selected.1.1.deferred_aligned
        (prepared.control.select_aligned selected.1.1 prepared.aligned
          (firstPlanning order planning) frame.active percept.frame percept.reward
          percept.frame.achieved selected.1.2 selected.2)
        order planning frame.active .settled percept.reward percept.frame.achieved selected.1.2)
      frame.active percept.frame percept.reward percept.frame.achieved selected.1.2,
    prepared.control.learn_episodes selected.1.1 _ prepared.episodes
      (modelOperations criterion dimension) (planningBoundary (firstPlanning order planning))
      frame.active percept.frame percept.reward percept.frame.achieved selected.1.2 selected.2
      kept.1 kept.2.1⟩

/-- The first part of the step under `actThenLearn`, from one percept: advance the
clock, encode the frame, and make every draw of the step with
`TemporalControl.drawFirst`, which takes the frame and no reward. The result holds the
record of the writes that the second part makes from the reward. -/
def Agent.chooseDrawn (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    Chosen interface profile config criterion dimension planning :=
  let prepared := state.advanceClock
  let frame := prepared.frame percept.frame
  let drawn := prepared.control.alignedDraw prepared.aligned frame.active percept.frame
    percept.frame.achieved
  have kept := drawn.1.1.deferred_frame .actThenLearn planning frame.active drawn.1.2.1
    percept.reward percept.frame.achieved drawn.1.2.2
  ⟨.actThenLearn, percept, frame.active, frame.units, drawn.1.1, drawn.1.2.2, drawn.1.2.1,
    TemporalControl.learn_aligned _
      (drawn.1.1.deferred_aligned
        (prepared.control.drawFirst_aligned drawn.1.1 prepared.aligned frame.active percept.frame
          percept.frame.achieved drawn.1.2.1 drawn.1.2.2 drawn.2)
        .actThenLearn planning frame.active drawn.1.2.1 percept.reward percept.frame.achieved
        drawn.1.2.2)
      frame.active percept.frame percept.reward percept.frame.achieved drawn.1.2.2,
    prepared.control.learn_traced drawn.1.1 _ prepared.episodes frame.active percept.frame
      percept.reward percept.frame.achieved drawn.1.2.2
      (prepared.control.drawFirst_episodes drawn.1.1 (modelOperations criterion dimension)
        (planningBoundary .none) frame.active percept.frame.declared percept.frame.achieved
        drawn.1.2.1 drawn.1.2.2 prepared.episodes.2 drawn.2)
      (fun primitive => prepared.control.drawFirst_primitive drawn.1.1
        (modelOperations criterion dimension) (planningBoundary .none) frame.active
        percept.frame.declared percept.frame.achieved drawn.1.2.1 drawn.1.2.2 primitive drawn.2)
      kept.1 kept.2.1⟩

/-- The first part of the step under a step order. Under `actThenLearn` it makes the
draws and owes the writes that read the reward; under the other orders it is selection
with the planning that order places before the action. -/
def Agent.choose (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    Chosen interface profile config criterion dimension planning :=
  match order with
  | .actThenLearn => state.chooseDrawn percept
  | .learnThenAct => state.chooseSelected .learnThenAct (by decide) percept
  | .planAfterAct => state.chooseSelected .planAfterAct (by decide) percept

/-- The agent of a chosen value after every update that follows the first part, before
the tester: the owed writes and the deferred planning of its order, then the learning
part. -/
def Chosen.learned (chosen : Chosen interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨(chosen.control.deferred chosen.order planning chosen.features chosen.owed
    chosen.percept.reward chosen.percept.frame.achieved chosen.decision).learn
    chosen.features chosen.percept.frame chosen.percept.reward chosen.percept.frame.achieved
    chosen.decision, chosen.aligned, chosen.episodes⟩

/-- The second part of the step: the writes its order owes, the planning its order
places after the action, every update that follows selection, then the receiver-owned
tester on the same frame's unit outputs. It reads the chosen value only. -/
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

/-- The first part of an order whose first part is selection selects with the executed
selection, on the once-advanced clock, the encoding of the percept's frame and the
planning its order places before the action; a chosen value holds exactly that result
and owes nothing. -/
theorem Agent.choose_selected (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (selects : order ≠ .actThenLearn) (percept : Percept interface) :
    state.advanceClock.control.select (firstPlanning order planning)
        (state.advanceClock.frame percept.frame).active
        percept.frame.declared percept.reward percept.frame.achieved =
      some ((state.choose order percept).control, (state.choose order percept).decision) ∧
    (state.choose order percept).order = order ∧
    (state.choose order percept).percept = percept ∧
    (state.choose order percept).features = (state.advanceClock.frame percept.frame).active ∧
    (state.choose order percept).units = (state.advanceClock.frame percept.frame).units ∧
    (state.choose order percept).owed = .settled := by
  cases order with
  | actThenLearn => exact absurd rfl selects
  | learnThenAct =>
    exact ⟨(state.advanceClock.control.alignedSelect state.advanceClock.aligned
      (firstPlanning .learnThenAct planning) (state.advanceClock.frame percept.frame).active
      percept.frame percept.reward percept.frame.achieved).2, rfl, rfl, rfl, rfl, rfl⟩
  | planAfterAct =>
    exact ⟨(state.advanceClock.control.alignedSelect state.advanceClock.aligned
      (firstPlanning .planAfterAct planning) (state.advanceClock.frame percept.frame).active
      percept.frame percept.reward percept.frame.achieved).2, rfl, rfl, rfl, rfl, rfl⟩

/-- The first part under `actThenLearn` is the executed draw-first selection, on the
once-advanced clock and the encoding of the percept's frame, with the no-planning
boundary; a chosen value holds exactly that result. The draw-first selection takes the
frame's declared potentials and its achievement event, and no reward. -/
theorem Agent.choose_drawn (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.advanceClock.control.drawFirst (modelOperations criterion dimension)
        (planningBoundary .none) (state.advanceClock.frame percept.frame).active
        percept.frame.declared percept.frame.achieved =
      some ((state.choose .actThenLearn percept).control,
        (state.choose .actThenLearn percept).owed,
        (state.choose .actThenLearn percept).decision) ∧
    (state.choose .actThenLearn percept).order = .actThenLearn ∧
    (state.choose .actThenLearn percept).percept = percept ∧
    (state.choose .actThenLearn percept).features =
      (state.advanceClock.frame percept.frame).active ∧
    (state.choose .actThenLearn percept).units = (state.advanceClock.frame percept.frame).units :=
  ⟨(state.advanceClock.control.alignedDraw state.advanceClock.aligned
    (state.advanceClock.frame percept.frame).active percept.frame percept.frame.achieved).2,
    rfl, rfl, rfl, rfl⟩

/-- **Under the default order the two parts compose to the step.** For every agent state
and percept, in every world, the executed step returns the agent the second part
returns on the chosen value, and the chosen decision. -/
theorem Agent.act_parts (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.act percept = state.actOrdered .learnThenAct percept := by
  have stepped := state.advanceClock.control.step_selected planning
    (state.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved _ _ (state.choose_selected .learnThenAct (by decide) percept).1
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

/-- **What the first part does not write.** Under every order, for every agent state and
percept, the chosen value holds the primitive controller and the prediction demons the
agent held before the percept. The decision is therefore made while the reward of
this percept has reached neither. Under `learnThenAct` and `planAfterAct` the first part
does write the meta-controller and the options; under `actThenLearn` it takes no reward
word (`Agent.choose_reward`). -/
theorem Agent.choose_keeps (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    (state.choose order percept).control.Keeps state.control := by
  cases order with
  | actThenLearn =>
    exact TemporalControl.drawFirst_keeps state.advanceClock.control
      (modelOperations criterion dimension) (planningBoundary .none)
      (state.advanceClock.frame percept.frame).active percept.frame.declared
      percept.frame.achieved _ _ _ (state.choose_drawn percept).1
  | learnThenAct =>
    exact TemporalControl.select_keeps state.advanceClock.control
      (modelOperations criterion dimension) (planningBoundary (firstPlanning .learnThenAct planning))
      (state.advanceClock.frame percept.frame).active
      percept.frame.declared percept.reward percept.frame.achieved _ _
      (state.choose_selected .learnThenAct (by decide) percept).1
  | planAfterAct =>
    exact TemporalControl.select_keeps state.advanceClock.control
      (modelOperations criterion dimension) (planningBoundary (firstPlanning .planAfterAct planning))
      (state.advanceClock.frame percept.frame).active
      percept.frame.declared percept.reward percept.frame.achieved _ _
      (state.choose_selected .planAfterAct (by decide) percept).1

/-- **Under `actThenLearn` the first part does not read the reward word.** For every
agent state, frame and two reward words, the first part returns the same temporal state,
the same decision and the same owed record. Each is a result of
`TemporalControl.drawFirst`, which has no reward parameter. The statement varies the
reward word and fixes the frame, and the frame carries the achievement event (D8), which
the first part reads. In the grid world the reward word is a function of that event
(`Host.StepResult.reward_completion`), so two percepts that world produces with one
frame have one reward word: there the statement says that no learner write of the reward
precedes a draw, and it does not say that the action is independent of the event. -/
theorem Agent.choose_reward (state : Agent interface profile config criterion dimension planning)
    (frame : Frame interface) (first second : Binary32) :
    (state.choose .actThenLearn ⟨frame, first⟩).control =
        (state.choose .actThenLearn ⟨frame, second⟩).control ∧
      (state.choose .actThenLearn ⟨frame, first⟩).decision =
        (state.choose .actThenLearn ⟨frame, second⟩).decision ∧
      (state.choose .actThenLearn ⟨frame, first⟩).owed =
        (state.choose .actThenLearn ⟨frame, second⟩).owed :=
  ⟨rfl, rfl, rfl⟩

/-- **`planAfterAct` can differ from the default order at a free dispatch only.** For every
agent state and percept whose decision under planning after the action records no meta
decision, the whole step of that order is the executed step: the same next agent and the
same decision. Every free dispatch records a meta decision
(`TemporalControl.atBoundary_meta`), so the steps on which those two orders can differ are
those with a free dispatch. -/
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
    (state.choose_selected .learnThenAct (by decide) percept).1
  have moved := state.advanceClock.control.select_unplanned
    (modelOperations criterion dimension) (planningBoundary .none) (planningBoundary planning)
    (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
    percept.frame.achieved _ _ (state.choose_selected .planAfterAct (by decide) percept).1 undrawn
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

/-- **The second part makes no action draw.** Under every order, for every chosen value,
the agent the second part returns holds the action generator the first part left.
Every draw of an action, of a meta action and of an exploration run is in the first
part. The tester's replacement draws are from the feature generator's own stream. -/
theorem Chosen.learn_rng (chosen : Chosen interface profile config criterion dimension planning) :
    chosen.learn.control.runtime.references.rng = chosen.control.runtime.references.rng :=
  ((chosen.learned.retire_rng chosen.units).trans
    ((chosen.control.deferred chosen.order planning chosen.features chosen.owed
      chosen.percept.reward chosen.percept.frame.achieved chosen.decision).learn_rng
      chosen.features chosen.percept.frame chosen.percept.reward chosen.percept.frame.achieved
      chosen.decision)).trans
    (chosen.control.deferred_frame chosen.order planning chosen.features chosen.owed
      chosen.percept.reward chosen.percept.frame.achieved chosen.decision).2.2

end Acorn.Handcrafted
