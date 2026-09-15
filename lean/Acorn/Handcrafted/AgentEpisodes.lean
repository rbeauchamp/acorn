/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.AgentAlignment

/-!
# Option-episode ownership at composition

Episode records follow actual activation creation and consumption. The proof
protocol distinguishes continuation, free dispatch and replacement, including
ending and starting the same slot at one boundary. Saturating counters retain
that relation without storing an experience or proof history at runtime.
-/
namespace Acorn.Handcrafted
open Features

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension}

/-- The sole active option, derived from exclusive occupancy. -/
def TemporalControl.activeSlot (state : TemporalControl profile config criterion dimension) :
    Option (Fin Acorn.FeatureConstants.skillCount) :=
  match state.runtime.references.phase with
  | .option slot _ => some slot
  | .idle | .exploring _ => none

/-- Complete activation event protocol. Endings consume an old activation and
starts reserve a new one; neither operation is inferred from diagnostic counts. -/
inductive EpisodeTrace : Option (Fin Acorn.FeatureConstants.skillCount) →
    Option (Fin Acorn.FeatureConstants.skillCount) → Option (Fin Acorn.FeatureConstants.skillCount) →
      Option (Fin Acorn.FeatureConstants.skillCount) → Prop where
  /-- No lifecycle event retains the same outstanding invocation. -/
  | continuing (slot : Option (Fin Acorn.FeatureConstants.skillCount)) : EpisodeTrace slot none none slot
  /-- A free boundary may start one invocation. -/
  | free (started : Option (Fin Acorn.FeatureConstants.skillCount)) : EpisodeTrace none none started started
  /-- Consuming an old invocation may immediately start another, including the same slot. -/
  | ending (old : Fin Acorn.FeatureConstants.skillCount)
      (started : Option (Fin Acorn.FeatureConstants.skillCount)) :
      EpisodeTrace (some old) (some old) started started

/-- A closing refresh can detach a learner, but cannot change which activation ends. -/
theorem _root_.Acorn.Features.FreeDispatch.install_closing_slot
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (state.install slot target).closing.map (·.slot) = state.closing.map (·.slot) := by
  unfold FreeDispatch.install
  dsimp only
  split
  · rfl
  · simp only [Option.map_map]
    congr 1
    funext closing
    dsimp only [Function.comp_apply]
    split <;> rfl

/-- All assignment refreshes preserve the closing activation's slot. -/
theorem _root_.Acorn.Features.FreeDispatch.refresh_closing_slot
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload) :
    state.refreshRanked.closing.map (·.slot) = state.closing.map (·.slot) := by
  unfold FreeDispatch.refreshRanked
  dsimp only [Refresh.take]
  split
  · generalize rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights = targets
    have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (current : FreeDispatch shape config criterion dimension discounts payload) :
        (slots.foldl (fun next slot => next.install slot targets[slot.val]) current).closing.map (·.slot) =
          current.closing.map (·.slot) := by
      induction slots generalizing current with
      | nil => rfl
      | cons slot tail ih =>
        exact (ih (current.install slot targets[slot.val])).trans (current.install_closing_slot slot _)
    exact fold _ _
  · rfl

/-- Primitive selection creates no active option and preserves the supplied closing event. -/
theorem TemporalControl.primitive_episodes (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    let result := state.choosePrimitive features values metaDecision ended
    result.1.lifetime = state.lifetime ∧ result.1.activeSlot = none ∧
      result.2.started = none ∧ result.2.ended = ended := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  cases hr : ((state.runtime.lifecycle.consumers.control.snapshot (count := primitiveCount)
      features state.controlRate).drawPersistent state.runtime.references.rng).1.run with
  | none => simp [TemporalControl.choosePrimitive, TemporalControl.activeSlot, TemporalControl.withPhase, hr]
  | some run =>
    by_cases remaining : 0 < run.remaining.val <;>
      simp [TemporalControl.choosePrimitive, TemporalControl.activeSlot, TemporalControl.withPhase, hr, remaining]

/-- Option stepping retains exactly its slot and the caller's actual lifecycle events. -/
theorem TemporalControl.option_episodes (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation dimension activation) (reward : Binary32)
    (values : Vector Binary32 metaCount.word.toNat) (metaDecision : Option (PolicyDecision metaCount))
    (started : Bool) (ended : Option EndEvent) :
    let result := state.stepOption models slot activation next reward values metaDecision started ended
    result.1.lifetime = state.lifetime ∧ result.1.activeSlot = some slot ∧
      result.2.started = (if started then some slot else none) ∧ result.2.ended = ended :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Boundary metaDecision dispatch has a new active slot exactly when its observation records a start. -/
theorem TemporalControl.dispatch_episodes (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (decision : PolicyDecision metaCount)
    (ended : Option EndEvent) (observed : TemporalDecision)
    (executed : state.dispatchMeta models features declared reward decision ended = some (next, observed)) :
    next.lifetime = state.lifetime ∧ next.activeSlot = observed.started ∧ observed.ended = ended := by
  unfold TemporalControl.dispatchMeta at executed
  generalize prepared : state.learnMeta features decision = credited at executed
  have lifetime : credited.lifetime = state.lifetime := by
    rw [← prepared]
    unfold TemporalControl.learnMeta
    split <;> rfl
  cases selected : skillOfMeta decision.action with
  | none =>
    simp only [selected, pure, Option.some.injEq] at executed
    cases executed
    have proof := credited.primitive_episodes features decision.snapshot.values (some decision) ended
    exact ⟨proof.1.trans lifetime, proof.2.1.trans proof.2.2.1.symm, proof.2.2.2⟩
  | some slot =>
    simp only [selected] at executed
    cases potential : (credited.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at executed
      cases executed
      exact ⟨lifetime, rfl, rfl⟩

/-- Refresh alters feature knowledge and detached ownership, leaving episode observations intact. -/
theorem TemporalControl.refresh_episode_slot (state : TemporalControl profile config criterion dimension)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).2.map (·.slot) = closing.map (·.slot) := by
  exact (FreeDispatch.refresh_closing_slot
    (⟨state.runtime.lifecycle, state.runtime.refresh, state.runtime.references.modelPredictions, closing⟩ :
      FreeDispatch Host.patchShape config criterion dimension demonLayout.tail
        (EndingPayload (profile.mode != .frozen))))

/-- Terminal credit does not itself record an episode; the common finish boundary records it once. -/
theorem TemporalControl.close_lifetime (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (closing : Closing config criterion dimension (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) : (state.closeOption models closing reward terminal).1.lifetime = state.lifetime := by
  unfold TemporalControl.closeOption
  split <;> rfl

/-- Free dispatch preserves episode ownership through refresh, planning and sampled terminal credit. -/
theorem TemporalControl.boundary_episodes (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (closing : Option (Closing config criterion dimension (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) (observed : TemporalDecision)
    (executed : state.atBoundary models plan features declared reward closing ended = some (next, observed)) :
    next.lifetime = state.lifetime ∧ next.activeSlot = observed.started ∧
      observed.ended.map (·.slot) = (closing.map (·.slot)).orElse (fun _ => ended.map (·.slot)) := by
  unfold TemporalControl.atBoundary at executed
  generalize hr : state.refreshFree closing = refreshed at executed
  have refreshedLifetime : refreshed.1.lifetime = state.lifetime := by rw [← hr]; rfl
  have closingSlot : refreshed.2.map (·.slot) = closing.map (·.slot) := by
    rw [← hr]
    exact state.refresh_episode_slot closing
  dsimp only at executed
  generalize hd : (refreshed.1.planFree plan features).drawMeta features = drawn at executed
  have drawnLifetime : drawn.1.lifetime = state.lifetime := by rw [← hd]; exact refreshedLifetime
  cases hc : refreshed.2 with
  | none =>
    simp only [hc] at executed
    have proof := drawn.1.dispatch_episodes next models features declared reward drawn.2 ended observed executed
    refine ⟨proof.1.trans drawnLifetime, proof.2.1, ?_⟩
    rw [proof.2.2, ← closingSlot, hc]
    rfl
  | some owner =>
    simp only [hc] at executed
    have proof := (drawn.1.closeOption models owner reward drawn.2.continuation).1.dispatch_episodes next models
      features declared reward drawn.2 (some (drawn.1.closeOption models owner reward drawn.2.continuation).2)
      observed executed
    refine ⟨proof.1.trans ((drawn.1.close_lifetime models owner reward _).trans drawnLifetime), proof.2.1, ?_⟩
    rw [proof.2.2, ← closingSlot, hc]
    rfl

/-- Preparation updates neither the active invocation nor any episode observation. -/
theorem TemporalControl.prepare_episodes (state : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).lifetime = state.lifetime ∧
      (state.prepareSelection models features reward).activeSlot = state.activeSlot := by
  unfold TemporalControl.prepareSelection
  split <;> split <;> exact ⟨rfl, rfl⟩

/-- A deferred meta clock changes no episode ownership or accounting. -/
theorem TemporalControl.skip_episodes (state : TemporalControl profile config criterion dimension) :
    state.skipMeta.lifetime = state.lifetime ∧ state.skipMeta.activeSlot = state.activeSlot := by
  unfold TemporalControl.skipMeta
  split <;> exact ⟨rfl, rfl⟩

/-- Serving persistent exploration is always an episode-free continuation. -/
theorem TemporalControl.serve_episodes (state next : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observed : TemporalDecision)
    (executed : state.serve features = some (next, observed)) :
    next.lifetime = state.lifetime ∧ state.activeSlot = none ∧ next.activeSlot = none ∧
      observed.started = none ∧ observed.ended = none := by
  unfold TemporalControl.serve at executed
  cases phase : state.runtime.references.phase with
  | idle => simp [phase] at executed
  | option slot activation => simp [phase] at executed
  | exploring run =>
    simp only [phase] at executed
    cases served : run.serve with
    | none => simp [served] at executed
    | some result =>
      simp only [served, bind, Option.bind, pure, Option.some.injEq] at executed
      cases executed
      have noActive : state.activeSlot = none := by simp [TemporalControl.activeSlot, phase]
      refine ⟨?_, noActive, ?_, rfl, rfl⟩
      all_goals
        split
        all_goals unfold TemporalControl.skipMeta; split <;> rfl

/-- Source-exclusive selection exposes the complete start/end transition for each activation. -/
theorem TemporalControl.select_episodes (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (observed : TemporalDecision)
    (primitive : profile.usesHierarchy = false → state.activeSlot = none)
    (executed : state.selectWithOperations models plan features declared reward goal = some (next, observed)) :
    next.lifetime = state.lifetime ∧
      EpisodeTrace state.activeSlot (observed.ended.map (·.slot)) observed.started next.activeSlot := by
  unfold TemporalControl.selectWithOperations at executed
  generalize hp : state.prepareSelection models features reward = prepared at executed
  have preparedLifetime : prepared.lifetime = state.lifetime := by
    rw [← hp]; exact (state.prepare_episodes models features reward).1
  have preparedActive : prepared.activeSlot = state.activeSlot := by
    rw [← hp]; exact (state.prepare_episodes models features reward).2
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    have proof := prepared.serve_episodes next features observed served
    refine ⟨proof.1.trans preparedLifetime, ?_⟩
    rw [← preparedActive, proof.2.1, proof.2.2.1, proof.2.2.2.1, proof.2.2.2.2]
    exact .continuing none
  | none =>
    simp only [served] at executed
    split at executed
    · rename_i noHierarchy
      have noHierarchy' : profile.usesHierarchy = false := by simpa using noHierarchy
      have same : (prepared.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero) none none =
          (next, observed) := Option.some.inj executed
      have proof := (prepared.withPhase .idle).primitive_episodes features (Vector.replicate _ .zero) none none
      rw [same] at proof
      refine ⟨proof.1.trans preparedLifetime, ?_⟩
      rw [primitive noHierarchy', proof.2.1, proof.2.2.1, proof.2.2.2]
      exact .free none
    · cases phase : prepared.runtime.references.phase with
      | idle =>
        simp only [phase] at executed
        have proof := (prepared.withPhase .idle).boundary_episodes next models plan features declared reward
          none none observed executed
        refine ⟨proof.1.trans preparedLifetime, ?_⟩
        have empty : state.activeSlot = none := by
          rw [← preparedActive]; simp [TemporalControl.activeSlot, phase]
        rw [empty, proof.2.1, proof.2.2]
        exact .free observed.started
      | exploring run =>
        simp only [phase] at executed
        have proof := (prepared.withPhase .idle).boundary_episodes next models plan features declared reward
          none none observed executed
        refine ⟨proof.1.trans preparedLifetime, ?_⟩
        have empty : state.activeSlot = none := by
          rw [← preparedActive]; simp [TemporalControl.activeSlot, phase]
        rw [empty, proof.2.1, proof.2.2]
        exact .free observed.started
      | option slot activation =>
        simp only [phase] at executed
        let free := prepared.withPhase .idle
        let skill := free.runtime.lifecycle.consumers.skills.get slot
        let metaPolicy := free.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
          features free.metaRate
        have active : state.activeSlot = some slot := by
          rw [← preparedActive]; simp [TemporalControl.activeSlot, phase]
        cases potential : skill.interest.potential features declared with
        | none =>
          simp only [skill, free] at potential
          simp [potential] at executed
        | some value =>
          simp only [skill, free] at potential
          simp only [potential, bind, Option.bind] at executed
          cases choice : skill.decideOption activation features value goal
              (comparisonValue criterion metaPolicy) free.skillRate with
          | continuing continuation =>
            simp only [skill, free, metaPolicy] at choice
            simp only [choice, pure, Option.some.injEq] at executed
            cases executed
            have proof := free.withoutPlanning.option_episodes models slot activation continuation reward
              metaPolicy.values none false none
            have skip := (free.withoutPlanning.stepOption models slot activation continuation reward
              metaPolicy.values none false none).1.skip_episodes
            refine ⟨skip.1.trans (proof.1.trans preparedLifetime), ?_⟩
            rw [active, skip.2, proof.2.1, proof.2.2.1, proof.2.2.2]
            exact .continuing (some slot)
          | ending reason =>
            simp only [skill, free, metaPolicy] at choice
            simp only [choice] at executed
            let closing : Closing config criterion dimension (EndingPayload (profile.mode != .frozen)) :=
              ⟨slot, ⟨activation, value, reason⟩, none⟩
            cases criterion with
            | differential =>
              have proof := free.boundary_episodes next models plan features declared reward
                (some closing) none observed executed
              refine ⟨proof.1.trans preparedLifetime, ?_⟩
              rw [active, proof.2.1, proof.2.2]
              exact .ending slot observed.started
            | discounted =>
              let closed := free.closeOption models closing reward (comparisonValue .discounted metaPolicy)
              have proof := closed.1.boundary_episodes next models plan features declared reward
                none (some closed.2) observed executed
              refine ⟨proof.1.trans ((free.close_lifetime models closing reward _).trans preparedLifetime), ?_⟩
              rw [active, proof.2.1, proof.2.2]
              exact .ending slot observed.started

/-- The protocol preserves the whole episode vector, including same-slot end/start boundaries. -/
theorem EpisodeTrace.record_valid
    {before ending started after : Option (Fin Acorn.FeatureConstants.skillCount)}
    (trace : EpisodeTrace before ending started after)
    (options : Vector Lifetime.OptionEpisodes Acorn.FeatureConstants.skillCount)
    (ended : Option Lifetime.EpisodeEnd) (slot : ended.map (·.slot) = ending)
    (valid : Lifetime.OptionsValid options before) :
    Lifetime.OptionsValid (Lifetime.recordOptions options ended started) after := by
  cases trace with
  | continuing old =>
    have none : ended = none := Option.map_eq_none_iff.mp slot
    subst ended
    exact valid
  | free started =>
    have none : ended = none := Option.map_eq_none_iff.mp slot
    subst ended
    cases started with
    | none => exact valid
    | some started => exact Lifetime.options_start_valid options started valid
  | ending old started =>
    cases ended with
    | none => contradiction
    | some event =>
      have same : event.slot = old := Option.some.inj slot
      subst old
      have finished := Lifetime.options_finish_valid options event valid
      cases started with
      | none => exact finished
      | some started => exact Lifetime.options_start_valid _ started finished

/-- Primitive-only selection cannot leave an option active, regardless of prior raw occupancy. -/
theorem TemporalControl.select_primitive (state next : TemporalControl profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (observed : TemporalDecision) (primitive : profile.usesHierarchy = false)
    (executed : state.selectWithOperations models plan features declared reward goal = some (next, observed)) :
    next.activeSlot = none := by
  unfold TemporalControl.selectWithOperations at executed
  generalize hp : state.prepareSelection models features reward = prepared at executed
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    exact (prepared.serve_episodes next features observed served).2.2.1
  | none =>
    simp only [served, primitive, Bool.not_false, ↓reduceIte] at executed
    have same : (prepared.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero) none none =
        (next, observed) := Option.some.inj executed
    have proof := (prepared.withPhase .idle).primitive_episodes features (Vector.replicate _ .zero) none none
    rw [same] at proof
    exact proof.2.1

/-- Stored episode counts agree with the outstanding invocation and immutable hierarchy mode. -/
def TemporalControl.Episodes (state : TemporalControl profile config criterion dimension) : Prop :=
  Lifetime.OptionsValid state.lifetime.options state.activeSlot ∧
    (profile.usesHierarchy = false → state.activeSlot = none)

/-- All cold profiles have empty counts and no active invocation. -/
theorem TemporalControl.initial_episodes (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) :
    (TemporalControl.initial profile config criterion dimension).Episodes := by
  constructor
  · intro slot
    simpa [TemporalControl.initial, TemporalControl.activeSlot, TemporalReferences.cold,
      Lifetime.Stats.initial] using Lifetime.OptionEpisodes.initial_valid
  · intro _; rfl

/-- The common finish changes options only through its actual event record. -/
theorem TemporalControl.finish_options (state : TemporalControl profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Host.Observation) (reward : Binary32)
    (decision : TemporalDecision) :
    (state.finish features observation reward decision).lifetime.options =
      Lifetime.recordOptions state.lifetime.options decision.episodeEnd decision.started := by
  by_cases frozen : profile.mode = .frozen <;>
    simp [TemporalControl.finish_eq, TemporalControl.recordEpisodes, TemporalControl.predictionView,
      PredictionControl.advance, frozen]
  exact Lifetime.Stats.recordDemons_options _ _ _ _

/-- Actual local steps preserve the episode invariant at every write boundary. -/
theorem TemporalControl.step_episodes (state next : TemporalControl profile config criterion dimension)
    (valid : state.Episodes) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Host.Observation) (reward : Binary32) (goal : Bool) (decision : TemporalDecision)
    (executed : state.step planning features observation reward goal = some (next, decision)) :
    next.Episodes := by
  unfold TemporalControl.step at executed
  cases selected : state.select planning features (spatialPotentials observation) reward goal with
  | none => simp [selected] at executed
  | some result =>
    simp only [selected, bind, Option.bind, pure, Option.some.injEq] at executed
    cases executed
    have trace := state.select_episodes result.1 (modelOperations criterion dimension)
      (planningBoundary planning) features (spatialPotentials observation) reward goal result.2 valid.2 selected
    constructor
    · change Lifetime.OptionsValid
        (result.1.finish features observation reward result.2).lifetime.options result.1.activeSlot
      rw [TemporalControl.finish_options, trace.1]
      apply trace.2.record_valid _ result.2.episodeEnd _ valid.1
      simp [TemporalDecision.episodeEnd, Option.map_map, Function.comp_def]
    · intro primitive
      exact state.select_primitive result.1 (modelOperations criterion dimension) (planningBoundary planning)
        features (spatialPotentials observation) reward goal result.2 primitive selected

end Acorn.Handcrafted
