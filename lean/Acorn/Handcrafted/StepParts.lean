import Acorn.Handcrafted.Agent
import Acorn.Handcrafted.DrawFirst
import Acorn.Timing

namespace Acorn.Handcrafted
open Features

variable {interface : Interface} {actions : Word.Count} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {planning : PlanningSelection} {discounts : List Discount} {shape : PatchShape}
    {payload : Type}

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

abbrev TemporalControl.Keeps
    (next origin : TemporalControl interface profile config criterion dimension) : Prop :=
  next.runtime.lifecycle.consumers.control = origin.runtime.lifecycle.consumers.control ∧
    next.runtime.lifecycle.consumers.demons = origin.runtime.lifecycle.consumers.demons

theorem TemporalControl.skipMeta_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) : state.skipMeta.Keeps origin := by
  unfold TemporalControl.skipMeta
  split <;> exact kept

theorem TemporalControl.prepare_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).Keeps origin := by
  unfold TemporalControl.prepareSelection
  dsimp only
  split <;> split <;> exact kept

theorem TemporalControl.primitive_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (ended : Option EndEvent) :
    (state.choosePrimitive features values decision ended).1.Keeps origin :=
  kept

theorem TemporalControl.withSkill_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (state.withSkill slot skill).Keeps origin :=
  kept

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

theorem TemporalControl.planFree_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) : (state.planFree plan features).Keeps origin :=
  kept

theorem TemporalControl.drawMeta_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension) :
    (state.drawMeta features).1.Keeps origin :=
  kept

theorem TemporalControl.learnMeta_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (features : SwiftTd.ActiveSet dimension)
    (decision : PolicyDecision metaCount) : (state.learnMeta features decision).Keeps origin := by
  rw [TemporalControl.learnMeta_eq]
  split <;> exact kept

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

theorem TemporalControl.drawMeta_snapshot
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (state.drawMeta features).2.snapshot =
      state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount) features
        state.metaRate :=
  rfl

theorem TemporalControl.planFree_none
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (state.planFree (planningBoundary .none) features).runtime.lifecycle.consumers.metaController =
        state.runtime.lifecycle.consumers.metaController ∧
      (state.planFree (planningBoundary .none) features).metaRate = state.metaRate := by
  unfold TemporalControl.planFree
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

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

theorem TemporalControl.planFree_cleared
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    state.planFree (planningBoundary .none) features = state.withoutPlanning := by
  unfold TemporalControl.planFree
  dsimp only
  split <;> rfl

theorem TemporalControl.withoutPlanning_cleared
    (state : TemporalControl interface profile config criterion dimension)
    (cleared : state.runtime.references.planningErrors = Vector.replicate _ .zero) :
    state.withoutPlanning = state := by
  unfold TemporalControl.withoutPlanning
  rw [← cleared]

theorem TemporalControl.learnMeta_errors
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (state.learnMeta features decision).runtime.references.planningErrors =
      state.runtime.references.planningErrors := by
  rw [TemporalControl.learnMeta_eq]
  split <;> rfl

theorem TemporalControl.closeOption_errors
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1.runtime.references.planningErrors =
      state.runtime.references.planningErrors := by
  rw [TemporalControl.closeOption_eq]
  dsimp only
  cases closing.oldOwner <;> rfl

theorem TemporalControl.dispatchMeta_errors
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : PolicyDecision metaCount) (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension)
    (selected : TemporalDecision interface.actions)
    (executed : state.dispatchMeta models features declared reward goal decision ended =
      some (next, selected)) :
    next.runtime.references.planningErrors = state.runtime.references.planningErrors := by
  rw [TemporalControl.dispatchMeta_eq] at executed
  have kept := state.learnMeta_errors features decision
  generalize state.learnMeta features decision = learned at executed kept
  dsimp only at executed
  split at executed
  · cases executed
    exact kept
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
      rw [← step, TemporalControl.stepOption_eq]
      exact kept

theorem TemporalControl.atBoundary_cleared
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
    next.runtime.references.planningErrors = Vector.replicate _ .zero := by
  unfold TemporalControl.atBoundary at executed
  generalize state.refreshFree closing = refreshed at executed
  dsimp only at executed
  have drawnCleared : ((refreshed.1.planFree (planningBoundary .none) features).drawMeta
      features).1.runtime.references.planningErrors = Vector.replicate _ .zero := by
    rw [TemporalControl.planFree_cleared]
    rfl
  generalize (refreshed.1.planFree (planningBoundary .none) features).drawMeta features = drawn
    at executed drawnCleared
  revert executed
  cases refreshed.2 with
  | none =>
    intro executed
    exact (drawn.1.dispatchMeta_errors models features declared reward goal drawn.2 ended next
      decision executed).trans drawnCleared
  | some owner =>
    intro executed
    exact (TemporalControl.dispatchMeta_errors _ models features declared reward goal drawn.2 _
      next decision executed).trans
      ((drawn.1.closeOption_errors models features owner reward _).trans drawnCleared)

theorem TemporalControl.select_cleared
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models (planningBoundary .none) features declared
      reward goal = some (next, decision))
    (drawn : decision.metaDecision.isSome = true) :
    next.runtime.references.planningErrors = Vector.replicate _ .zero := by
  unfold TemporalControl.selectWithOperations at executed
  generalize state.prepareSelection models features reward = prepared at executed
  dsimp only at executed
  revert executed
  cases served : prepared.serve features with
  | some result =>
    intro executed
    obtain ⟨_, rfl⟩ := selected_eq executed
    rw [prepared.serve_undrawn result.1 features result.2 served] at drawn
    contradiction
  | none =>
    intro executed
    simp only at executed
    split at executed
    · obtain ⟨_, rfl⟩ := selected_eq executed
      rw [TemporalControl.choosePrimitive_meta] at drawn
      contradiction
    · split at executed
      · exact (prepared.withPhase .idle).atBoundary_cleared models features declared reward goal
          none none next decision executed
      · exact (prepared.withPhase .idle).atBoundary_cleared models features declared reward goal
          none none next decision executed
      · rename_i slot activation phase
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          split at executed
          · obtain ⟨_, rfl⟩ := selected_eq executed
            rw [TemporalControl.stepOption_meta] at drawn
            contradiction
          · split at executed
            · exact (prepared.withPhase .idle).atBoundary_cleared models features declared
                reward goal _ none next decision executed
            · exact TemporalControl.atBoundary_cleared _ models features declared reward goal
                none _ next decision executed

def firstPlanning (order : StepOrder) (planning : PlanningSelection) : PlanningSelection :=
  match order with
  | .learnThenAct => planning
  | .planAfterAct | .actThenLearn => .none

def TemporalControl.planAfter
    (selected : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (decision : TemporalDecision interface.actions) :
    TemporalControl interface profile config criterion dimension :=
  if decision.metaDecision.isSome then selected.planFree (planningBoundary planning) features
  else selected

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

theorem TemporalControl.oweReward_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (reward : Binary32) : (state.oweReward reward).Keeps origin := by
  unfold TemporalControl.oweReward
  split <;> exact kept

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

theorem TemporalControl.startOption_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (start : StartDraw interface) (goal : Bool)
    (estimate reward : Binary32) :
    (state.startOption models features start goal estimate reward).Keeps origin := by
  rw [TemporalControl.startOption_eq]
  exact kept

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

theorem TemporalControl.prepareDraw_keeps
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Keeps origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : (state.prepareDraw models features).Keeps origin := by
  unfold TemporalControl.prepareDraw
  dsimp only
  split <;> exact kept

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

theorem TemporalControl.learn_aligned
    (middle : TemporalControl interface profile config criterion dimension)
    (aligned : middle.Aligned) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (middle.learn features observation reward goal decision).Aligned :=
  TemporalControl.finish_aligned _ (TemporalControl.closeSpan_aligned _
    (middle.followOptions_aligned aligned (modelOperations criterion dimension) features
      observation.declared reward goal decision) _) features observation reward decision

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

structure Chosen (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) where
  private mk ::
  order : StepOrder
  percept : Percept interface
  features : SwiftTd.ActiveSet dimension
  units : Vector Bool config.units.count
  control : TemporalControl interface profile config criterion dimension
  decision : TemporalDecision interface.actions
  owed : Owed interface profile config criterion dimension
  aligned : ((control.deferred order planning features owed percept.reward percept.frame.achieved
    decision).learn features percept.frame percept.reward percept.frame.achieved decision).Aligned
  episodes : ((control.deferred order planning features owed percept.reward
    percept.frame.achieved decision).learn features percept.frame percept.reward
    percept.frame.achieved decision).Episodes

def Agent.chooseSelected (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (_selects : order ≠ .actThenLearn) (percept : Percept interface) :
    Chosen interface profile config criterion dimension planning :=
  let prepared := state.advanceClock
  let frame := (prepared.frameCosted percept.frame).val
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

def Agent.chooseDrawn (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    Chosen interface profile config criterion dimension planning :=
  let prepared := state.advanceClock
  let frame := (prepared.frameCosted percept.frame).val
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

def Agent.choose (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    Chosen interface profile config criterion dimension planning :=
  match order with
  | .actThenLearn => state.chooseDrawn percept
  | .learnThenAct => state.chooseSelected .learnThenAct (by decide) percept
  | .planAfterAct => state.chooseSelected .planAfterAct (by decide) percept

def Chosen.learned (chosen : Chosen interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  ⟨(chosen.control.deferred chosen.order planning chosen.features chosen.owed
    chosen.percept.reward chosen.percept.frame.achieved chosen.decision).learn
    chosen.features chosen.percept.frame chosen.percept.reward chosen.percept.frame.achieved
    chosen.decision, chosen.aligned, chosen.episodes⟩

def Chosen.learn (chosen : Chosen interface profile config criterion dimension planning) :
    Agent interface profile config criterion dimension planning :=
  chosen.learned.retire chosen.units

def Agent.actOrdered (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) :
    Agent interface profile config criterion dimension planning ×
      TemporalDecision interface.actions :=
  ((state.choose order percept).learn, (state.choose order percept).decision)

theorem Agent.ext_control {left right : Agent interface profile config criterion dimension planning}
    (same : left.control = right.control) : left = right := by
  cases left
  cases right
  cases same
  rfl

theorem Agent.retire_control
    (left right : Agent interface profile config criterion dimension planning)
    (same : left.control = right.control) (active : Vector Bool config.units.count) :
    left.retire active = right.retire active :=
  congrArg (fun agent : Agent interface profile config criterion dimension planning =>
    agent.retire active) (Agent.ext_control same)

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

theorem Agent.choose_decision (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.choose .learnThenAct percept).decision = (state.act percept).2 :=
  (congrArg Prod.snd (state.act_parts percept)).symm

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

theorem Agent.choose_reward (state : Agent interface profile config criterion dimension planning)
    (frame : Frame interface) (first second : Binary32) :
    (state.choose .actThenLearn ⟨frame, first⟩).control =
        (state.choose .actThenLearn ⟨frame, second⟩).control ∧
      (state.choose .actThenLearn ⟨frame, first⟩).decision =
        (state.choose .actThenLearn ⟨frame, second⟩).decision ∧
      (state.choose .actThenLearn ⟨frame, first⟩).owed =
        (state.choose .actThenLearn ⟨frame, second⟩).owed :=
  ⟨rfl, rfl, rfl⟩

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

theorem Agent.choose_unplanned
    (state : Agent interface profile config criterion dimension .none)
    (percept : Percept interface) :
    (state.choose .planAfterAct percept).control = (state.choose .learnThenAct percept).control ∧
      (state.choose .planAfterAct percept).decision =
        (state.choose .learnThenAct percept).decision ∧
      (state.choose .planAfterAct percept).features =
        (state.choose .learnThenAct percept).features ∧
      (state.choose .planAfterAct percept).units = (state.choose .learnThenAct percept).units ∧
      (state.choose .planAfterAct percept).owed = (state.choose .learnThenAct percept).owed :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Agent.actOrdered_unplanned
    (state : Agent interface profile config criterion dimension .none)
    (percept : Percept interface) :
    state.actOrdered .planAfterAct percept = state.actOrdered .learnThenAct percept := by
  have chosen := state.choose_unplanned percept
  refine Prod.ext ?_ chosen.2.1
  refine Agent.retire_control (state.choose .planAfterAct percept).learned
    (state.choose .learnThenAct percept).learned ?_
    (state.advanceClock.frame percept.frame).units
  change ((state.choose .planAfterAct percept).control.planAfter .none
        (state.advanceClock.frame percept.frame).active
        (state.choose .planAfterAct percept).decision).learn
      (state.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved (state.choose .planAfterAct percept).decision =
    (state.choose .learnThenAct percept).control.learn
      (state.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved (state.choose .learnThenAct percept).decision
  rw [← chosen.1, ← chosen.2.1]
  congr 1
  unfold TemporalControl.planAfter
  split
  · rename_i drawn
    rw [TemporalControl.planFree_cleared]
    exact TemporalControl.withoutPlanning_cleared _
      (TemporalControl.select_cleared _ (modelOperations criterion dimension) _ _ _ _ _ _
        (state.choose_selected .planAfterAct (by decide) percept).1 drawn)
  · rfl

theorem TemporalControl.followOptions_rng
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : TemporalDecision interface.actions) :
    (state.followOptions models features declared reward goal decision).runtime.references.rng =
      state.runtime.references.rng := by
  rw [TemporalControl.followOptions_eq]
  split <;> rfl

theorem TemporalControl.closeSpan_rng
    (state : TemporalControl interface profile config criterion dimension)
    (continuation : Option Binary32) :
    (state.closeSpan continuation).runtime.references.rng = state.runtime.references.rng := by
  cases continuation with
  | none => rfl
  | some value =>
    exact (congrArg (fun next : TemporalControl interface profile config criterion dimension =>
      next.runtime.references.rng) (state.closeSpan_eq value)).trans rfl

theorem TemporalControl.finish_rng
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.references.rng =
      state.runtime.references.rng :=
  (congrArg (fun next : TemporalControl interface profile config criterion dimension =>
    next.runtime.references.rng) (state.finish_eq features obs reward decision)).trans rfl

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

theorem Agent.retire_rng (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (state.retire active).control.runtime.references.rng =
      state.control.runtime.references.rng := by
  unfold Agent.retire
  split
  · rfl
  · exact congrArg (·.rng) (state.control.runtime.retire_references active)

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
