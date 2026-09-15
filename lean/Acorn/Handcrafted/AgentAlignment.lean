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
producer. These structural proofs close that local hypothesis across every
learning, refresh and retirement write; they do not assume a successful dispatch.
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

/-- The complete temporal state carries that same table, rather than a copied assignment list. -/
def TemporalControl.Aligned (state : TemporalControl profile config criterion dimension) : Prop :=
  state.runtime.lifecycle.consumers.Aligned

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
  cases subtasks <;> intro slot <;>
    simp [TemporalControl.initial, Ensemble.initial, FeatureProfile.interests,
      Skill.initial, Interest.Aligned]

/-- Slot retirement retains the full source identity for all hashed aliases. -/
theorem _root_.Acorn.Features.Ensemble.retire_aligned (state : Ensemble config criterion dimension discounts)
    (aligned : state.Aligned) (feature : FeatIdx dimension) : (state.retire feature).Aligned := by
  intro slot
  simpa [Ensemble.retire, Skill.retire] using aligned slot

/-- A changed assignment is learned; an unchanged assignment retains its admitted source. -/
theorem _root_.Acorn.Features.FreeDispatch.install_aligned (state : FreeDispatch shape config criterion dimension discounts payload)
    (aligned : state.lifecycle.consumers.Aligned)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (state.install slot target).lifecycle.consumers.Aligned := by
  unfold FreeDispatch.install
  dsimp only
  split
  · exact aligned
  · intro index
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
  · generalize rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights = targets
    have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (current : FreeDispatch shape config criterion dimension discounts payload)
        (valid : current.lifecycle.consumers.Aligned) :
        (slots.foldl (fun next slot => next.install slot targets[slot.val]) current).lifecycle.consumers.Aligned := by
      induction slots generalizing current with
      | nil => exact valid
      | cons slot tail ih => exact ih _ (current.install_aligned valid slot _)
    exact fold _ _ aligned
  · exact aligned

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
  simp only [Skill.stepTemporal]
  split <;> simp only [Skill.optionStep] <;> split <;> rfl

/-- Terminal policy/model credit retains its original objective. -/
theorem _root_.Acorn.Features.Skill.endTemporal_interest {mode : Bool} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (ending : EndingPayload mode)
    (reward terminal : Binary32) (gain : RewardRate) :
    (skill.endTemporal models ending reward terminal gain).interest = skill.interest := by
  unfold Skill.endTemporal
  split <;> exact (skill.terminal_owners ending.activation ending.potential reward terminal gain).1

/-- Replacing one skill requires alignment of that exact receiving value. -/
theorem TemporalControl.withSkill_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (slot : Fin Acorn.FeatureConstants.skillCount)
    (skill : Skill config criterion dimension) (valid : skill.interest.Aligned) :
    (state.withSkill slot skill).Aligned := by
  intro index
  simp only [TemporalControl.withSkill, Vector.getElem_set]
  split
  · exact valid
  · exact aligned index

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
  apply state.withSkill_aligned aligned slot
  rw [Skill.stepTemporal_interest]
  exact aligned slot

/-- Terminal credit updates the matching current owner or discards the detached one. -/
theorem TemporalControl.closeOption_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (closing : Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) : (state.closeOption models closing reward terminal).1.Aligned := by
  unfold TemporalControl.closeOption
  dsimp only
  cases old : closing.oldOwner with
  | none =>
    simp only [Option.getD_none]
    apply state.withSkill_aligned aligned
    rw [Skill.endTemporal_interest]
    exact aligned closing.slot
  | some owner => exact aligned

/-- Free-boundary refresh closes the potential-source premise for the next dispatch. -/
theorem TemporalControl.refreshFree_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).1.Aligned :=
  FreeDispatch.refresh_aligned _ aligned

/-- Repaying meta credit cannot replace an option's source declaration. -/
theorem TemporalControl.learnMeta_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (state.learnMeta features decision).Aligned := by
  unfold TemporalControl.learnMeta
  split <;> exact aligned

/-- The common finish changes primitive credit, demons and gain, retaining every option source. -/
theorem TemporalControl.finish_aligned (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (observation : Host.Observation)
    (reward : Binary32) (decision : TemporalDecision) :
    (state.finish features observation reward decision).Aligned := aligned

/-- The drawn meta decision has a potential for its receiving option, when selected. -/
theorem TemporalControl.dispatchMeta_total (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Host.Observation) (reward : Binary32)
    (decision : PolicyDecision metaCount) (ended : Option EndEvent) :
    ∃ next selected, state.dispatchMeta models features (spatialPotentials observation) reward decision ended =
      some (next, selected) ∧ next.Aligned := by
  unfold TemporalControl.dispatchMeta
  generalize hl : state.learnMeta features decision = learned
  have learnedAligned : learned.Aligned := by
    rw [← hl]
    exact state.learnMeta_aligned aligned features decision
  dsimp only
  split
  · exact ⟨_, _, rfl, learned.primitive_aligned learnedAligned features decision.snapshot.values (some decision) ended⟩
  · rename_i slot selected
    have hs := learnedAligned slot
    obtain ⟨potential, hp⟩ := Interest.aligned_potential
      (learned.runtime.lifecycle.consumers.skills.get slot).interest hs features observation
    simp only [hp, bind, Option.bind]
    refine ⟨_, _, rfl, ?_⟩
    apply TemporalControl.stepOption_aligned (values := decision.snapshot.values)
      (decision := some decision) (started := true) (ended := ended)
    apply learned.withSkill_aligned learnedAligned
    rw [Skill.beginTemporal_interest]
    exact hs

/-- A free boundary always has a potential for the selected receiving skill;
planning and detached terminal credit preserve that source alignment. -/
theorem TemporalControl.boundary_total (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary config criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) :
    ∃ next decision, state.atBoundary models plan features (spatialPotentials observation) reward closing ended =
      some (next, decision) ∧ next.Aligned := by
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
    exact drawn.1.dispatchMeta_total drawnAligned models features observation reward drawn.2 ended
  | some owner =>
    apply TemporalControl.dispatchMeta_total
    exact drawn.1.closeOption_aligned drawnAligned models owner reward _

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
      · exact (prepared.withPhase .idle).boundary_total preparedAligned models plan features observation reward none none
      · exact (prepared.withPhase .idle).boundary_total preparedAligned models plan features observation reward none none
      · rename_i slot activation phase
        obtain ⟨potential, hpotential⟩ := Interest.aligned_potential
          ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get slot).interest
          (preparedAligned slot) features observation
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
            exact (prepared.withPhase .idle).closeOption_aligned preparedAligned models _ reward _
          | differential =>
            exact (prepared.withPhase .idle).boundary_total preparedAligned models plan features observation reward _ none

/-- Actual model/planning execution and common completion have no missing
application-internal potential oracle at the full-agent boundary. -/
theorem TemporalControl.step_total (state : TemporalControl profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) :
    ∃ next decision, state.step planning features observation reward goal = some (next, decision) ∧ next.Aligned := by
  obtain ⟨selected, decision, selectedEq, selectedAligned⟩ := state.select_total aligned
    (modelOperations criterion dimension) (planningBoundary planning) features observation reward goal
  refine ⟨selected.finish features observation reward decision, decision, ?_,
    selected.finish_aligned selectedAligned features observation reward decision⟩
  simp [TemporalControl.step, TemporalControl.select, selectedEq]

end Acorn.Handcrafted
