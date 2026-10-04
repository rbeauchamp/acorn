/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.TemporalControl

/-!
# Full-agent potential-source alignment

The local option interface permits arbitrary declared sources and refuses a
mismatch. The complete agent admits only learned interests and its actual D2
producer, and no two of its slots hold the same learned unit. These structural
proofs close both across every learning, refresh and retirement write, including
the off-policy learning of options that are not executing; they do not assume a
successful dispatch.

The last section states the timing of the assignment refresh over the executed
selection: with learned subtasks, every decision that draws a meta decision is taken
with the slot-stable ranking of the Demon-0 weights it started from installed
(`TemporalControl.select_assigns`).
-/
namespace Acorn.Handcrafted
open Features

variable {interface : Interface} {actions : Word.Count} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {profile : FeatureProfile}
    {discounts : List Discount} {shape : PatchShape} {payload : Type}

/-- Exactly the interests the current complete agent can supply. -/
def _root_.Acorn.Features.Interest.Aligned (interest : Interest config) : Prop :=
  match interest with
  | .learned _ => True
  | .declared origin _ => origin = .spatialPotentials

/-- A complete receiving table has no unresolved declared source. -/
def _root_.Acorn.Features.Ensemble.Aligned (state : Ensemble actions config criterion dimension discounts) : Prop :=
  ∀ slot : Fin Acorn.FeatureConstants.skillCount, state.skills[slot.val].interest.Aligned

/-- The complete temporal state carries that same table, rather than a copied assignment list,
with every source admitted and distinct held units. -/
abbrev TemporalControl.Aligned (state : TemporalControl interface profile config criterion dimension) : Prop :=
  state.runtime.lifecycle.consumers.Aligned ∧ state.runtime.lifecycle.consumers.Distinct

/-- Each admitted interest receives a potential from every frame. -/
theorem _root_.Acorn.Features.Interest.aligned_potential (interest : Interest config) (aligned : interest.Aligned)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) :
    ∃ potential, interest.potential features observation.declared = some potential := by
  cases interest with
  | learned assignment => exact ⟨_, rfl⟩
  | declared origin slot =>
    change origin = .spatialPotentials at aligned
    subst origin
    exact ⟨_, spatial_admitted slot features observation⟩

/-- Every initial profile installs only its own admitted interest family. -/
theorem TemporalControl.initial_aligned (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) :
    (TemporalControl.initial interface profile config criterion dimension).Aligned := by
  rcases profile with ⟨mode, credit, rate, subtasks⟩
  constructor
  · cases subtasks <;> intro slot <;>
      simp [TemporalControl.initial, Ensemble.initial, FeatureProfile.interests,
        Skill.initial, Interest.Aligned]
  · intro left right unit named _
    cases subtasks <;>
      simp [TemporalControl.initial, Ensemble.initial, FeatureProfile.interests,
        Skill.initial, Interest.held, Assignment.identity] at named

/-- Slot retirement retains the full source identity for all hashed aliases. -/
theorem _root_.Acorn.Features.Ensemble.retire_aligned (state : Ensemble actions config criterion dimension discounts)
    (aligned : state.Aligned) (feature : FeatIdx dimension) : (state.retire feature).Aligned := by
  intro slot
  simpa [Ensemble.retire, Skill.retire] using aligned slot

/-- Releasing slots installs only the learned neutral objective. -/
theorem _root_.Acorn.Features.Ensemble.release_aligned (state : Ensemble actions config criterion dimension discounts)
    (aligned : state.Aligned) (unit : Fin config.units.count) : (state.release unit).Aligned := by
  intro slot
  simp only [Ensemble.release, Vector.getElem_map]
  split
  · trivial
  · exact aligned slot

/-- Every installed assignment is learned; other slots retain their admitted source. -/
theorem _root_.Acorn.Features.FreeDispatch.install_aligned (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (aligned : state.lifecycle.consumers.Aligned)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (state.install slot target).lifecycle.consumers.Aligned := by
  unfold FreeDispatch.install
  dsimp only
  split
  all_goals
    intro index
    simp only [Vector.getElem_set]
    split
    · trivial
    · exact aligned index

/-- The complete ordered refresh fold preserves source alignment at each write. -/
theorem _root_.Acorn.Features.FreeDispatch.refresh_aligned (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (aligned : state.lifecycle.consumers.Aligned) :
    state.refreshRanked.lifecycle.consumers.Aligned := by
  simp only [FreeDispatch.refreshRanked]
  generalize rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
    (state.lifecycle.consumers.skills.map (·.interest.held)) = targets
  have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
      (current : FreeDispatch shape actions config criterion dimension discounts payload)
      (valid : current.lifecycle.consumers.Aligned) :
      (slots.foldl (fun next slot => next.install slot targets[slot.val]) current).lifecycle.consumers.Aligned := by
    induction slots generalizing current with
    | nil => exact valid
    | cons slot tail ih => exact ih _ (current.install_aligned valid slot _)
  exact fold _ _ aligned

/-- The complete refresh, which also reranks every model, preserves source alignment,
assigning or not. -/
theorem _root_.Acorn.Features.FreeDispatch.refreshModels_aligned (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (assign : Bool) (aligned : state.lifecycle.consumers.Aligned) :
    (state.refreshModels assign).lifecycle.consumers.Aligned := by
  intro slot
  cases assign with
  | false =>
    rw [FreeDispatch.refreshModels_keep, FreeDispatch.rerankModels_skill]
    exact aligned slot
  | true =>
    rw [FreeDispatch.refreshModels_assign, FreeDispatch.rerankModels_skill]
    exact FreeDispatch.refresh_aligned state aligned slot

/-- The policy/model operations never replace the skill's interest. -/
theorem _root_.Acorn.Features.Skill.beginTemporal_interest (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential learning rate).1.interest = skill.interest := by
  cases learning <;> rfl

/-- Every continuing write retains the interest whose potential was supplied. -/
theorem _root_.Acorn.Features.Skill.stepTemporal_interest {mode : Bool} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    (skill.stepTemporal models activation next reward gain rng).1.interest = skill.interest := by
  simp only [Skill.stepTemporal_eq]
  split <;> simp only [Skill.optionStep] <;> split <;> rfl

/-- Terminal policy/model credit retains its original objective. -/
theorem _root_.Acorn.Features.Skill.endTemporal_interest {mode : Bool} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate) :
    (skill.endTemporal models value features ending reward terminal gain).interest =
      skill.interest := by
  unfold Skill.endTemporal
  split <;> exact (skill.terminal_owners ending.activation ending.potential reward terminal gain).1

/-- Replacing one skill by learners for the same objective keeps the table aligned. -/
theorem TemporalControl.withSkill_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout)
    (same : skill.interest = state.runtime.lifecycle.consumers.skills[slot.val].interest) :
    (state.withSkill slot skill).Aligned := by
  have table (index : Fin Acorn.FeatureConstants.skillCount) :
      (state.withSkill slot skill).runtime.lifecycle.consumers.skills[index.val].interest =
        state.runtime.lifecycle.consumers.skills[index.val].interest := by
    simp only [TemporalControl.withSkill, Vector.getElem_set]
    split
    · rename_i equal
      have index_eq : slot = index := Fin.ext equal
      subst index_eq
      exact same
    · rfl
  refine ⟨fun index => ?_, Assignment.Distinct.mono aligned.2 fun index unit named => ?_⟩
  · rw [table index]
    exact aligned.1 index
  · rw [Vector.getElem_map] at named ⊢
    rw [table index] at named
    exact named

/-- The optional meta-gap write does not touch the receiving skill table. -/
theorem TemporalControl.skipMeta_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) : state.skipMeta.Aligned := by
  unfold TemporalControl.skipMeta
  split <;> exact aligned

/-- Selection preparation changes clocks, meta reward and model caches only. -/
theorem TemporalControl.prepare_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).Aligned := by
  unfold TemporalControl.prepareSelection
  dsimp only
  split <;> split <;> exact aligned

/-- A fresh primitive choice preserves all option interests. -/
theorem TemporalControl.primitive_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (ended : Option EndEvent) : (state.choosePrimitive features values decision ended).1.Aligned :=
  aligned

/-- Interrupting a held option writes its trajectory link and keeps its interest. -/
theorem TemporalControl.interrupt_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) : (state.interrupt origin).1.Aligned := by
  cases origin with
  | none => exact aligned
  | some held =>
    obtain ⟨slot, activation⟩ := held
    unfold TemporalControl.interrupt
    dsimp only
    split
    · exact state.withSkill_aligned aligned slot _ rfl
    · exact aligned

/-- A served run changes occupancy, diagnostics and an interrupted option's trajectory link,
retaining admitted interests. -/
theorem TemporalControl.serve_aligned (state next : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (served : state.serve features = some (next, decision)) : next.Aligned := by
  unfold TemporalControl.serve at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      rw [← served.1]
      have base := state.interrupt_aligned aligned committed.origin
      repeat' split
      all_goals first
        | exact base
        | exact TemporalControl.skipMeta_aligned ((state.interrupt committed.origin).1.withPhase
            (.exploring (.bare pair.2))) base
  · contradiction
  · contradiction

/-- Concrete option learning preserves the source of the current table owner. -/
theorem TemporalControl.stepOption_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (started : Bool) (ended : Option EndEvent) :
    (state.stepOption models slot activation next reward values decision started ended).1.Aligned := by
  rw [TemporalControl.stepOption_eq]
  apply state.withSkill_aligned aligned slot
  rw [Skill.stepTemporal_interest]
  rfl

/-- Terminal credit updates the matching current owner or discards the detached one. -/
theorem TemporalControl.closeOption_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1.Aligned := by
  rw [TemporalControl.closeOption_eq]
  dsimp only
  cases old : closing.oldOwner with
  | none =>
    simp only [Option.getD_none]
    apply state.withSkill_aligned aligned
    rw [Skill.endTemporal_interest]
    rfl
  | some owner => exact aligned

/-- Free-boundary refresh closes the potential-source premise for the next dispatch. -/
theorem TemporalControl.refreshFree_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).1.Aligned :=
  ⟨FreeDispatch.refreshModels_aligned _ _ aligned.1, FreeDispatch.refreshModels_distinct _ _ aligned.2⟩

/-- Repaying meta credit cannot replace an option's source declaration. -/
theorem TemporalControl.learnMeta_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (state.learnMeta features decision).Aligned := by
  rw [TemporalControl.learnMeta_eq]
  split <;> exact aligned

/-- Closing an interrupted option's meta span writes the meta-controller and the span. -/
theorem TemporalControl.closeSpan_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (continuation : Option Binary32) :
    (state.closeSpan continuation).Aligned := by
  cases continuation with
  | none => exact aligned
  | some value =>
    rw [TemporalControl.closeSpan_eq]
    exact aligned

/-- A followed slot keeps its interest whether it is executing, linked or refused. -/
theorem followSlot_interest (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat)
    (reward : Binary32) (gain : RewardRate) (executing : Bool)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (followSlot models value features declared goal estimate rate action behaviour reward gain
      executing skill).interest = skill.interest := by
  unfold followSlot
  split
  · rfl
  · split
    · exact skill.followTemporal_interest models value features _ goal estimate rate action
        behaviour reward gain
    · rfl

/-- A table with the same interest in every slot stays aligned and distinct. -/
theorem TemporalControl.sameInterests_aligned (state next : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned)
    (same : ∀ index : Fin Acorn.FeatureConstants.skillCount,
      next.runtime.lifecycle.consumers.skills[index.val].interest =
        state.runtime.lifecycle.consumers.skills[index.val].interest) : next.Aligned := by
  refine ⟨fun index => ?_, Assignment.Distinct.mono aligned.2 fun index unit named => ?_⟩
  · rw [same index]
    exact aligned.1 index
  · rw [Vector.getElem_map] at named ⊢
    rw [same index] at named
    exact named

/-- The common finish changes primitive credit, demons, every option's questions and
gain, retaining every option source. -/
theorem TemporalControl.finish_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
    (reward : Binary32) (decision : TemporalDecision interface.actions) :
    (state.finish features observation reward decision).Aligned := by
  apply state.sameInterests_aligned _ aligned
  intro index
  rw [TemporalControl.finish_skill]
  split <;> rfl

/-- Off-policy option learning writes policies, models and trajectory links only;
every slot keeps the interest whose potential it read. -/
theorem TemporalControl.followOptions_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    (state.followOptions models features declared reward goal decision).Aligned := by
  apply state.sameInterests_aligned _ aligned
  intro index
  rw [TemporalControl.followOptions_eq]
  split
  · simp only [Vector.getElem_mapFinIdx]
    exact followSlot_interest ..
  · rfl

/-- The drawn meta decision has a potential for its receiving option, when selected. -/
theorem TemporalControl.dispatchMeta_total (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    ∃ next selected, state.dispatchMeta models features observation.declared reward goal
        decision ended = some (next, selected) ∧ next.Aligned := by
  rw [TemporalControl.dispatchMeta_eq]
  generalize hl : state.learnMeta features decision = learned
  have learnedAligned : learned.Aligned := by
    rw [← hl]
    exact state.learnMeta_aligned aligned features decision
  dsimp only
  split
  · exact ⟨_, _, rfl, learned.primitive_aligned learnedAligned features decision.snapshot.values (some decision) ended⟩
  · rename_i slot selected
    have hs := learnedAligned.1 slot
    obtain ⟨potential, hp⟩ := Interest.aligned_potential
      (learned.runtime.lifecycle.consumers.skills.get slot).interest hs features observation
    simp only [hp, bind, Option.bind]
    have total : ∀ result : TemporalControl interface profile config criterion dimension × TemporalDecision interface.actions,
        result.1.Aligned → ∃ next selected, some result = some (next, selected) ∧ next.Aligned :=
      fun result resultAligned => ⟨result.1, result.2, rfl, resultAligned⟩
    apply total
    apply TemporalControl.stepOption_aligned (values := decision.snapshot.values)
      (decision := some decision) (started := true) (ended := ended)
    apply learned.withSkill_aligned learnedAligned
    rw [Skill.beginTemporal_interest, Skill.settleTemporal_interest]
    rfl

/-- A free boundary always has a potential for the selected receiving skill;
planning and detached terminal credit preserve that source alignment. -/
theorem TemporalControl.boundary_total (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) :
    ∃ next decision, state.atBoundary models plan features observation.declared reward goal
        closing ended = some (next, decision) ∧ next.Aligned := by
  unfold TemporalControl.atBoundary
  generalize hr : state.refreshFree closing = refreshed
  have refreshedAligned : refreshed.1.Aligned := by
    rw [← hr]
    exact state.refreshFree_aligned aligned closing
  dsimp only
  generalize hd : (refreshed.1.planFree plan features).drawMeta features = drawn
  have drawnAligned : drawn.1.Aligned := by rw [← hd]; exact refreshedAligned
  cases hc : refreshed.2 with
  | none =>
    exact drawn.1.dispatchMeta_total drawnAligned models features observation reward goal drawn.2 ended
  | some owner =>
    apply TemporalControl.dispatchMeta_total
    exact drawn.1.closeOption_aligned drawnAligned models features owner reward _

/-- Every aligned local state selects a real action, with the same priority
dispatcher and matching potential producer, and retains source alignment. -/
theorem TemporalControl.select_total (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool) :
    ∃ next decision, state.selectWithOperations models plan features observation.declared reward goal =
      some (next, decision) ∧ next.Aligned := by
  unfold TemporalControl.selectWithOperations
  generalize hp : state.prepareSelection models features reward = prepared
  have preparedAligned : prepared.Aligned := by
    rw [← hp]
    exact state.prepare_aligned aligned models features reward
  dsimp only
  cases hs : prepared.serve features with
  | some result =>
    simp only
    exact ⟨_, _, rfl, prepared.serve_aligned result.1 preparedAligned features result.2 hs⟩
  | none =>
    simp only
    split
    · exact ⟨_, _, rfl, (prepared.withPhase .idle).primitive_aligned preparedAligned features (Vector.replicate _ .zero) none none⟩
    · split
      · exact (prepared.withPhase .idle).boundary_total preparedAligned models plan features observation reward goal none none
      · exact (prepared.withPhase .idle).boundary_total preparedAligned models plan features observation reward goal none none
      · rename_i slot activation phase
        obtain ⟨potential, hpotential⟩ := Interest.aligned_potential
          ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get slot).interest
          (preparedAligned.1 slot) features observation
        simp only [hpotential, bind, Option.bind]
        split
        · rename_i continuation continuing
          refine ⟨_, _, rfl, ?_⟩
          apply TemporalControl.skipMeta_aligned
          exact (prepared.withPhase .idle).withoutPlanning.stepOption_aligned preparedAligned models
            slot activation continuation reward
              ((prepared.withPhase .idle).runtime.lifecycle.consumers.metaController.snapshot features
                (prepared.withPhase .idle).metaRate).values none false none
        · rename_i reason ending
          cases criterion with
          | discounted =>
            apply TemporalControl.boundary_total
            exact (prepared.withPhase .idle).closeOption_aligned preparedAligned models features _
              reward _
          | differential =>
            exact (prepared.withPhase .idle).boundary_total preparedAligned models plan features observation reward goal _ none

/-- Actual model/planning execution and common completion have no missing
application-internal potential oracle at the full-agent boundary. -/
theorem TemporalControl.step_total (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool) :
    ∃ next decision, state.step planning features observation reward goal = some (next, decision) ∧ next.Aligned := by
  obtain ⟨selected, decision, selectedEq, selectedAligned⟩ := state.select_total aligned
    (modelOperations criterion dimension) (planningBoundary planning) features observation reward goal
  refine ⟨((selected.followOptions (modelOperations criterion dimension) features
      observation.declared reward goal decision).closeSpan
        (selected.takeoverValue features observation.declared goal decision)).finish
      features observation reward decision, decision, ?_,
    TemporalControl.finish_aligned _ (TemporalControl.closeSpan_aligned _
      (selected.followOptions_aligned selectedAligned
        (modelOperations criterion dimension) features observation.declared reward goal
        decision) _) features observation reward decision⟩
  simp [TemporalControl.step, TemporalControl.select, selectedEq]

/-! ## Objectives at a free dispatch

The same selection path carries each slot's objective from the assignment refresh to
the state the decision returns. A decision that draws a meta decision is a free
dispatch; a served exploration step, a continuing option and a primitive-only profile
draw none. -/

/-- Replacing one skill by one with the same interest changes no slot's interest. -/
theorem TemporalControl.withSkill_interest (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill interface.actions config criterion dimension interface.layout)
    (same : skill.interest = state.runtime.lifecycle.consumers.skills[slot.val].interest)
    (index : Fin Acorn.FeatureConstants.skillCount) :
    (state.withSkill slot skill).runtime.lifecycle.consumers.skills[index.val].interest =
      state.runtime.lifecycle.consumers.skills[index.val].interest := by
  simp only [TemporalControl.withSkill, Vector.getElem_set]
  split
  · rename_i equal
    have index_eq : slot = index := Fin.ext equal
    subst index_eq
    exact same
  · rfl

/-- A stepped option keeps every slot's interest. -/
theorem TemporalControl.stepOption_interest (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (started : Bool) (ended : Option EndEvent) (index : Fin Acorn.FeatureConstants.skillCount) :
    (state.stepOption models slot activation next reward values decision started
      ended).1.runtime.lifecycle.consumers.skills[index.val].interest =
        state.runtime.lifecycle.consumers.skills[index.val].interest := by
  rw [TemporalControl.stepOption_eq]
  exact state.withSkill_interest slot _ (by rw [Skill.stepTemporal_interest]; rfl) index

/-- Terminal credit keeps every slot's interest and writes no demon. -/
theorem TemporalControl.closeOption_interest (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) (index : Fin Acorn.FeatureConstants.skillCount) :
    (state.closeOption models features closing reward
      terminal).1.runtime.lifecycle.consumers.skills[index.val].interest =
        state.runtime.lifecycle.consumers.skills[index.val].interest ∧
      (state.closeOption models features closing reward
        terminal).1.runtime.lifecycle.consumers.demons = state.runtime.lifecycle.consumers.demons := by
  rw [TemporalControl.closeOption_eq]
  dsimp only
  cases old : closing.oldOwner with
  | none =>
    simp only [Option.getD_none]
    exact ⟨state.withSkill_interest closing.slot _ (by rw [Skill.endTemporal_interest]; rfl) index,
      rfl⟩
  | some owner => exact ⟨rfl, rfl⟩

/-- Meta credit keeps every slot's interest. -/
theorem TemporalControl.learnMeta_interest (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount)
    (index : Fin Acorn.FeatureConstants.skillCount) :
    (state.learnMeta features decision).runtime.lifecycle.consumers.skills[index.val].interest =
      state.runtime.lifecycle.consumers.skills[index.val].interest := by
  rw [TemporalControl.learnMeta_eq]
  split <;> rfl

/-- The dispatch of a drawn meta decision keeps every slot's interest and records that
decision. -/
theorem TemporalControl.dispatchMeta_interest (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount) (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension) (selected : TemporalDecision interface.actions)
    (executed : state.dispatchMeta models features declared reward goal decision ended =
      some (next, selected)) :
    selected.metaDecision = some decision ∧
      ∀ index : Fin Acorn.FeatureConstants.skillCount,
        next.runtime.lifecycle.consumers.skills[index.val].interest =
          state.runtime.lifecycle.consumers.skills[index.val].interest := by
  rw [TemporalControl.dispatchMeta_eq] at executed
  have kept := state.learnMeta_interest features decision
  generalize state.learnMeta features decision = learned at executed kept
  dsimp only at executed
  split at executed
  · cases executed
    exact ⟨rfl, kept⟩
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
      refine ⟨?_, fun index => ?_⟩
      · rw [TemporalControl.stepOption_eq]
      · rw [TemporalControl.stepOption_interest,
          TemporalControl.withSkill_interest _ _ _ ?_ index]
        · exact kept index
        · rw [Skill.beginTemporal_interest, Skill.settleTemporal_interest]
          rfl

/-- Every free dispatch records the meta decision it drew and leaves each slot the
objective its refresh installed. -/
theorem TemporalControl.atBoundary_interest (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.atBoundary models plan features declared reward goal closing ended =
      some (next, decision)) :
    decision.metaDecision.isSome = true ∧
      ∀ index : Fin Acorn.FeatureConstants.skillCount,
        next.runtime.lifecycle.consumers.skills[index.val].interest =
          (state.refreshFree closing).1.runtime.lifecycle.consumers.skills[index.val].interest := by
  unfold TemporalControl.atBoundary at executed
  generalize state.refreshFree closing = refreshed at executed ⊢
  dsimp only at executed
  have drawnKept : ∀ index : Fin Acorn.FeatureConstants.skillCount,
      ((refreshed.1.planFree plan features).drawMeta features).1.runtime.lifecycle.consumers.skills[index.val].interest =
        refreshed.1.runtime.lifecycle.consumers.skills[index.val].interest := fun _ => rfl
  generalize (refreshed.1.planFree plan features).drawMeta features = drawn at executed drawnKept
  revert executed
  cases refreshed.2 with
  | none =>
    intro executed
    obtain ⟨recorded, kept⟩ := drawn.1.dispatchMeta_interest models features declared reward goal
      drawn.2 ended next decision executed
    exact ⟨by rw [recorded]; rfl, fun index => (kept index).trans (drawnKept index)⟩
  | some owner =>
    intro executed
    obtain ⟨recorded, kept⟩ := TemporalControl.dispatchMeta_interest _ models features declared
      reward goal drawn.2 _ next decision executed
    exact ⟨by rw [recorded]; rfl, fun index => ((kept index).trans
      (drawn.1.closeOption_interest models features owner reward _ index).1).trans (drawnKept index)⟩

/-- With learned subtasks, every free dispatch leaves each slot the ranking's assignment
for the Demon-0 weights and the objectives it started from. -/
theorem TemporalControl.atBoundary_assigns (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.atBoundary models plan features declared reward goal closing ended =
      some (next, decision))
    (index : Fin Acorn.FeatureConstants.skillCount) :
    next.runtime.lifecycle.consumers.skills[index.val].interest =
      .learned (rankAssignments dimension config
        (DemonBank.rankingWeights (discounts := interface.signals)
          state.runtime.lifecycle.consumers.demons)
        (state.runtime.lifecycle.consumers.skills.map (·.interest.held)))[index.val] := by
  rw [(state.atBoundary_interest models plan features declared reward goal closing ended next
    decision executed).2 index, state.refreshFree_assigns learned closing]
  exact (FreeDispatch.refreshModels_interest _ index).trans (FreeDispatch.refresh_targets _ index)

/-- Selection preparation writes no learner, objective or representation. -/
theorem TemporalControl.prepare_lifecycle (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (state.prepareSelection models features reward).runtime.lifecycle = state.runtime.lifecycle := by
  unfold TemporalControl.prepareSelection
  dsimp only
  split <;> split <;> rfl

/-- A served exploration step draws no meta decision. -/
theorem TemporalControl.serve_undrawn (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (served : state.serve features = some (next, decision)) : decision.metaDecision = none := by
  unfold TemporalControl.serve at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      obtain ⟨_, rfl⟩ := served
      rfl
  · contradiction
  · contradiction

/-- A fresh primitive choice records the meta decision it was given. -/
theorem TemporalControl.choosePrimitive_meta (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 metaCount.word.toNat)
    (decision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    (state.choosePrimitive features values decision ended).2.metaDecision = decision := rfl

/-- A stepped option records the meta decision it was given. -/
theorem TemporalControl.stepOption_meta (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (started : Bool) (ended : Option EndEvent) :
    (state.stepOption models slot activation next reward values decision started
      ended).2.metaDecision = decision := by
  rw [TemporalControl.stepOption_eq]

/-- A returned selection is its two components. -/
theorem selected_eq {α β : Type} {result : α × β} {first : α} {second : β}
    (executed : some result = some (first, second)) : result.1 = first ∧ result.2 = second := by
  cases executed
  exact ⟨rfl, rfl⟩

/-- Timing over the executed selection: with learned subtasks, every decision that draws
a meta decision is taken with the slot-stable ranking installed. Each slot's objective is
the ranking's assignment for the Demon-0 weights and the objectives the decision started
from; the reward delivered with the decision is learned afterwards, by `finish`. A served
exploration step, a continuing option and a primitive-only profile draw no meta decision. -/
theorem TemporalControl.select_assigns (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision))
    (drawn : decision.metaDecision.isSome = true)
    (index : Fin Acorn.FeatureConstants.skillCount) :
    next.runtime.lifecycle.consumers.skills[index.val].interest =
      .learned (rankAssignments dimension config
        (DemonBank.rankingWeights (discounts := interface.signals)
          state.runtime.lifecycle.consumers.demons)
        (state.runtime.lifecycle.consumers.skills.map (·.interest.held)))[index.val] := by
  unfold TemporalControl.selectWithOperations at executed
  rw [← state.prepare_lifecycle models features reward]
  generalize state.prepareSelection models features reward = prepared at executed ⊢
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
      · exact (prepared.withPhase .idle).atBoundary_assigns learned models plan features declared
          reward goal none none next decision executed index
      · exact (prepared.withPhase .idle).atBoundary_assigns learned models plan features declared
          reward goal none none next decision executed index
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
            · exact (prepared.withPhase .idle).atBoundary_assigns learned models plan features
                declared reward goal _ none next decision executed index
            · generalize closedEq : (prepared.withPhase .idle).closeOption models features _ reward
                _ = closed at executed
              have kept (slot : Fin Acorn.FeatureConstants.skillCount) :=
                closedEq ▸ (prepared.withPhase .idle).closeOption_interest models features _ reward
                  _ slot
              have assigned := closed.1.atBoundary_assigns learned models plan features declared
                reward goal none _ next decision executed index
              have held : closed.1.runtime.lifecycle.consumers.skills.map (·.interest.held) =
                  prepared.runtime.lifecycle.consumers.skills.map (·.interest.held) := by
                apply Vector.ext
                intro position bound
                simp only [Vector.getElem_map]
                exact congrArg Interest.held (kept ⟨position, bound⟩).1
              rw [(kept index).2, held] at assigned
              exact assigned

/-- Timing over the executed selection, coverage: a decision that draws a meta decision
is taken with every candidate of the ranking installed in some slot. -/
theorem TemporalControl.select_covers (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision))
    (drawn : decision.metaDecision.isSome = true)
    (candidate : Candidate config)
    (member : candidate ∈ rankedCandidates dimension config
      (DemonBank.rankingWeights (discounts := interface.signals)
        state.runtime.lifecycle.consumers.demons)) :
    ∃ slot : Fin Acorn.FeatureConstants.skillCount,
      next.runtime.lifecycle.consumers.skills[slot.val].interest.held.identity =
        some candidate.unit := by
  obtain ⟨slot, named⟩ := rankAssignments_covers dimension config _
    (state.runtime.lifecycle.consumers.skills.map (·.interest.held)) candidate member
  exact ⟨slot, by
    rw [state.select_assigns learned models plan features declared reward goal next decision
      executed drawn slot]
    exact named⟩

/-- Timing over the executed selection, the count: a decision that draws a meta decision
is taken with as many slots holding a unit as the ranking has candidates, which is the
number of positive score blocks up to the number of slots. -/
theorem TemporalControl.select_occupancy (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision))
    (drawn : decision.metaDecision.isSome = true) :
    ((List.finRange Acorn.FeatureConstants.skillCount).filter fun slot =>
      next.runtime.lifecycle.consumers.skills[slot.val].interest.held.identity.isSome).length =
        (rankedCandidates dimension config
          (DemonBank.rankingWeights (discounts := interface.signals)
            state.runtime.lifecycle.consumers.demons)).length := by
  rw [← rankAssignments_count dimension config _
    (state.runtime.lifecycle.consumers.skills.map (·.interest.held))]
  congr 1
  apply List.filter_congr
  intro slot _
  rw [state.select_assigns learned models plan features declared reward goal next decision
    executed drawn slot]
  rfl

/-- Timing over the executed selection, the full table: a decision that draws a meta
decision when the ranking has a candidate for every slot is taken with a unit in every
slot. -/
theorem TemporalControl.select_full (state : TemporalControl interface profile config criterion dimension)
    (learned : profile.ranksSubtasks = true)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision))
    (drawn : decision.metaDecision.isSome = true)
    (full : (rankedCandidates dimension config
      (DemonBank.rankingWeights (discounts := interface.signals)
        state.runtime.lifecycle.consumers.demons)).length = Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    ∃ unit bonus, next.runtime.lifecycle.consumers.skills[slot.val].interest =
      .learned (.selected unit bonus) := by
  obtain ⟨unit, bonus, target⟩ := rankAssignments_full dimension config _
    (state.runtime.lifecycle.consumers.skills.map (·.interest.held)) full slot
  exact ⟨unit, bonus, by
    rw [state.select_assigns learned models plan features declared reward goal next decision
      executed drawn slot, target]⟩

/-- A hierarchical agent draws a meta decision at every decision that serves no
exploration run and finds no option active, so the timing theorems apply there. -/
theorem TemporalControl.select_drawn (state : TemporalControl interface profile config criterion dimension)
    (hierarchy : profile.usesHierarchy = true)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision))
    (unserved : (state.prepareSelection models features reward).serve features = none)
    (free : ∀ slot activation,
      (state.prepareSelection models features reward).runtime.references.phase ≠
        .option slot activation) :
    decision.metaDecision.isSome = true := by
  unfold TemporalControl.selectWithOperations at executed
  generalize state.prepareSelection models features reward = prepared at executed unserved free
  dsimp only at executed
  rw [unserved] at executed
  simp only [hierarchy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at executed
  split at executed
  · exact ((prepared.withPhase .idle).atBoundary_interest models plan features declared reward
      goal none none next decision executed).1
  · exact ((prepared.withPhase .idle).atBoundary_interest models plan features declared reward
      goal none none next decision executed).1
  · rename_i slot activation phase
    exact absurd phase (free slot activation)

/-- A primitive-only profile draws no meta decision. -/
theorem TemporalControl.primitive_undrawn (state : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (next : TemporalControl interface profile config criterion dimension) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features declared reward goal =
      some (next, decision)) :
    decision.metaDecision = none := by
  unfold TemporalControl.selectWithOperations at executed
  generalize state.prepareSelection models features reward = prepared at executed
  dsimp only at executed
  revert executed
  cases served : prepared.serve features with
  | some result =>
    intro executed
    obtain ⟨_, rfl⟩ := selected_eq executed
    exact prepared.serve_undrawn result.1 features result.2 served
  | none =>
    intro executed
    simp only [primitive, Bool.not_false, ↓reduceIte] at executed
    obtain ⟨_, rfl⟩ := selected_eq executed
    rfl

end Acorn.Handcrafted
