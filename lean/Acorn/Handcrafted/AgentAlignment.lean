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
-/
namespace Acorn.Handcrafted
open Features

variable {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {profile : FeatureProfile} {discounts : List Discount} {shape : PatchShape} {payload : Type}

/-- Exactly the interests the current complete agent can supply. -/
def _root_.Acorn.Features.Interest.Aligned (interest : Interest config) : Prop :=
  match interest with
  | .learned _ => True
  | .declared origin _ => origin = .spatialPotentials

/-- A complete receiving table has no unresolved declared source. -/
def _root_.Acorn.Features.Ensemble.Aligned (state : Ensemble config criterion dimension discounts) : Prop :=
  ∀ slot : Fin Acorn.FeatureConstants.skillCount, state.skills[slot.val].interest.Aligned

/-- The complete temporal state carries that same table, rather than a copied assignment list,
with every source admitted and distinct held units. -/
abbrev TemporalControl.Aligned (state : TemporalControl profile config criterion dimension) : Prop :=
  state.runtime.lifecycle.consumers.Aligned ∧ state.runtime.lifecycle.consumers.Distinct

/-- Each admitted interest receives a potential from the actual observation adapter. -/
theorem _root_.Acorn.Features.Interest.aligned_potential (interest : Interest config) (aligned : interest.Aligned)
    (features : SwiftTd.ActiveSet dimension) (observation : Host.Observation) :
    ∃ potential, interest.potential features (spatialPotentials observation) = some potential := by
  cases interest with
  | learned assignment => exact ⟨_, rfl⟩
  | declared origin slot =>
    change origin = .spatialPotentials at aligned
    subst origin
    exact ⟨_, spatial_admitted slot features observation⟩

/-- Every initial profile installs only its own admitted interest family. -/
theorem TemporalControl.initial_aligned (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    (TemporalControl.initial profile config criterion dimension).Aligned := by
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
theorem _root_.Acorn.Features.Ensemble.retire_aligned (state : Ensemble config criterion dimension discounts)
    (aligned : state.Aligned) (feature : FeatIdx dimension) : (state.retire feature).Aligned := by
  intro slot
  simpa [Ensemble.retire, Skill.retire] using aligned slot

/-- Releasing slots installs only the learned neutral objective. -/
theorem _root_.Acorn.Features.Ensemble.release_aligned (state : Ensemble config criterion dimension discounts)
    (aligned : state.Aligned) (unit : Fin config.units.count) : (state.release unit).Aligned := by
  intro slot
  simp only [Ensemble.release, Vector.getElem_map]
  split
  · trivial
  · exact aligned slot

/-- Every installed assignment is learned; other slots retain their admitted source. -/
theorem _root_.Acorn.Features.FreeDispatch.install_aligned (state : FreeDispatch shape config criterion dimension discounts payload)
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
theorem _root_.Acorn.Features.FreeDispatch.refresh_aligned (state : FreeDispatch shape config criterion dimension discounts payload)
    (aligned : state.lifecycle.consumers.Aligned) :
    state.refreshRanked.lifecycle.consumers.Aligned := by
  unfold FreeDispatch.refreshRanked
  dsimp only [Refresh.take]
  split
  · generalize rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
      (state.lifecycle.consumers.skills.map (·.interest.held)) = targets
    have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (current : FreeDispatch shape config criterion dimension discounts payload)
        (valid : current.lifecycle.consumers.Aligned) :
        (slots.foldl (fun next slot => next.install slot targets[slot.val]) current).lifecycle.consumers.Aligned := by
      induction slots generalizing current with
      | nil => exact valid
      | cons slot tail ih => exact ih _ (current.install_aligned valid slot _)
    exact fold _ _ aligned
  · exact aligned

/-- The complete refresh, which also reranks every model, preserves source alignment. -/
theorem _root_.Acorn.Features.FreeDispatch.refreshModels_aligned (state : FreeDispatch shape config criterion dimension discounts payload)
    (aligned : state.lifecycle.consumers.Aligned) :
    state.refreshModels.lifecycle.consumers.Aligned := by
  unfold FreeDispatch.refreshModels
  intro slot
  rw [FreeDispatch.rerankModels_skill]
  exact FreeDispatch.refresh_aligned state aligned slot

/-- The policy/model operations never replace the skill's interest. -/
theorem _root_.Acorn.Features.Skill.beginTemporal_interest (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential learning rate).1.interest = skill.interest := by
  cases learning <;> rfl

/-- Every continuing write retains the interest whose potential was supplied. -/
theorem _root_.Acorn.Features.Skill.stepTemporal_interest {mode : Bool} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (activation : OptionActivation mode)
    (next : OptionContinuation dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    (skill.stepTemporal models activation next reward gain rng).1.interest = skill.interest := by
  simp only [Skill.stepTemporal_eq]
  split <;> simp only [Skill.optionStep] <;> split <;> rfl

/-- Terminal policy/model credit retains its original objective. -/
theorem _root_.Acorn.Features.Skill.endTemporal_interest {mode : Bool} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate) :
    (skill.endTemporal models value features ending reward terminal gain).interest =
      skill.interest := by
  unfold Skill.endTemporal
  split <;> exact (skill.terminal_owners ending.activation ending.potential reward terminal gain).1

/-- Replacing one skill by learners for the same objective keeps the table aligned. -/
theorem TemporalControl.withSkill_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill config criterion dimension)
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
theorem TemporalControl.skipMeta_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) : state.skipMeta.Aligned := by
  unfold TemporalControl.skipMeta
  split <;> exact aligned

/-- Selection preparation changes clocks, meta reward and model caches only. -/
theorem TemporalControl.prepare_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).Aligned := by
  unfold TemporalControl.prepareSelection
  dsimp only
  split <;> split <;> exact aligned

/-- A fresh primitive choice preserves all option interests. -/
theorem TemporalControl.primitive_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (ended : Option EndEvent) : (state.choosePrimitive features values decision ended).1.Aligned :=
  aligned

/-- A served run changes occupancy and diagnostics, retaining admitted interests. -/
theorem TemporalControl.serve_aligned (state next : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision)
    (served : state.serve features = some (next, decision)) : next.Aligned := by
  unfold TemporalControl.serve at served
  split at served
  · rename_i run phase
    cases hs : run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      rw [← served.1]
      split <;> exact (state.withPhase (.exploring pair.2)).skipMeta_aligned aligned
  · contradiction
  · contradiction

/-- Concrete option learning preserves the source of the current table owner. -/
theorem TemporalControl.stepOption_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount) (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation dimension activation) (reward : Binary32)
    (values : Vector Binary32 metaCount.word.toNat) (decision : Option (PolicyDecision metaCount))
    (started : Bool) (ended : Option EndEvent) :
    (state.stepOption models slot activation next reward values decision started ended).1.Aligned := by
  rw [TemporalControl.stepOption_eq]
  apply state.withSkill_aligned aligned slot
  rw [Skill.stepTemporal_interest]
  rfl

/-- Terminal credit updates the matching current owner or discards the detached one. -/
theorem TemporalControl.closeOption_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1.Aligned := by
  unfold TemporalControl.closeOption
  dsimp only
  cases old : closing.oldOwner with
  | none =>
    simp only [Option.getD_none]
    apply state.withSkill_aligned aligned
    rw [Skill.endTemporal_interest]
    rfl
  | some owner => exact aligned

/-- Free-boundary refresh closes the potential-source premise for the next dispatch. -/
theorem TemporalControl.refreshFree_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).1.Aligned :=
  ⟨FreeDispatch.refreshModels_aligned _ aligned.1, FreeDispatch.refreshModels_distinct _ aligned.2⟩

/-- Repaying meta credit cannot replace an option's source declaration. -/
theorem TemporalControl.learnMeta_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (state.learnMeta features decision).Aligned := by
  rw [TemporalControl.learnMeta_eq]
  split <;> exact aligned

/-- The common finish changes primitive credit, demons and gain, retaining every option source. -/
theorem TemporalControl.finish_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (observation : Host.Observation)
    (reward : Binary32) (decision : TemporalDecision) :
    (state.finish features observation reward decision).Aligned := aligned

/-- A followed slot keeps its interest whether it is executing, linked or refused. -/
theorem followSlot_interest (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat)
    (reward : Binary32) (gain : RewardRate) (executing : Bool)
    (skill : Skill config criterion dimension) :
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
theorem TemporalControl.sameInterests_aligned (state next : TemporalControl profile config criterion dimension)
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

/-- Off-policy option learning writes policies, models and trajectory links only;
every slot keeps the interest whose potential it read. -/
theorem TemporalControl.followOptions_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision) :
    (state.followOptions models features declared reward goal decision).Aligned := by
  apply state.sameInterests_aligned _ aligned
  intro index
  rw [TemporalControl.followOptions_eq]
  split
  · simp only [Vector.getElem_mapFinIdx]
    exact followSlot_interest ..
  · rfl

/-- The drawn meta decision has a potential for its receiving option, when selected. -/
theorem TemporalControl.dispatchMeta_total (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Host.Observation) (reward : Binary32)
    (goal : Bool) (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    ∃ next selected, state.dispatchMeta models features (spatialPotentials observation) reward goal
        decision ended = some (next, selected) ∧ next.Aligned := by
  unfold TemporalControl.dispatchMeta
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
    have total : ∀ result : TemporalControl profile config criterion dimension × TemporalDecision,
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
theorem TemporalControl.boundary_total (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary config criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) :
    ∃ next decision, state.atBoundary models plan features (spatialPotentials observation) reward goal
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
theorem TemporalControl.select_total (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary config criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    ∃ next decision, state.selectWithOperations models plan features (spatialPotentials observation) reward goal =
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
theorem TemporalControl.step_total (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    ∃ next decision, state.step planning features observation reward goal = some (next, decision) ∧ next.Aligned := by
  obtain ⟨selected, decision, selectedEq, selectedAligned⟩ := state.select_total aligned
    (modelOperations criterion dimension) (planningBoundary planning) features observation reward goal
  refine ⟨(selected.followOptions (modelOperations criterion dimension) features
      (spatialPotentials observation) reward goal decision).finish features observation reward
      decision, decision, ?_,
    TemporalControl.finish_aligned _ (selected.followOptions_aligned selectedAligned
      (modelOperations criterion dimension) features (spatialPotentials observation) reward goal
      decision) features observation reward decision⟩
  simp [TemporalControl.step, TemporalControl.select, selectedEq]

end Acorn.Handcrafted
