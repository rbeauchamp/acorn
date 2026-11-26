import Acorn.Handcrafted.AgentAlignment

namespace Acorn.Handcrafted
open Features

variable {interface : Interface} {actions : Word.Count} {profile : FeatureProfile}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}

inductive EpisodeTrace : Option (Fin Acorn.FeatureConstants.skillCount) →
    Option (Fin Acorn.FeatureConstants.skillCount) → Option (Fin Acorn.FeatureConstants.skillCount) →
      Option (Fin Acorn.FeatureConstants.skillCount) → Prop where
  | continuing (slot : Option (Fin Acorn.FeatureConstants.skillCount)) : EpisodeTrace slot none none slot
  | free (started : Option (Fin Acorn.FeatureConstants.skillCount)) : EpisodeTrace none none started started
  | ending (old : Fin Acorn.FeatureConstants.skillCount)
      (started : Option (Fin Acorn.FeatureConstants.skillCount)) :
      EpisodeTrace (some old) (some old) started started

theorem _root_.Acorn.Features.FreeDispatch.install_closing_slot
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
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

theorem _root_.Acorn.Features.FreeDispatch.refresh_closing_slot
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    state.refreshRanked.closing.map (·.slot) = state.closing.map (·.slot) := by
  simp only [FreeDispatch.refreshRanked]
  generalize rankAssignments dimension config state.lifecycle.consumers.demons.rankingWeights
    (state.lifecycle.consumers.skills.map (·.interest.held)) = targets
  have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
      (current : FreeDispatch shape actions config criterion dimension discounts payload) :
      (slots.foldl (fun next slot => next.install slot targets[slot.val]) current).closing.map (·.slot) =
        current.closing.map (·.slot) := by
    induction slots generalizing current with
    | nil => rfl
    | cons slot tail ih =>
      exact (ih (current.install slot targets[slot.val])).trans (current.install_closing_slot slot _)
  exact fold _ _

theorem _root_.Acorn.Features.FreeDispatch.refreshModels_closing_slot
    {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape actions config criterion dimension discounts payload) (assign : Bool) :
    (state.refreshModels assign).closing.map (·.slot) = state.closing.map (·.slot) := by
  cases assign with
  | false => rfl
  | true =>
    rw [FreeDispatch.refreshModels_assign, state.refreshRanked.rerankModels_preserves.2.1]
    exact state.refresh_closing_slot

theorem TemporalControl.primitive_episodes (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 metaCount.word.toNat)
    (metaDecision : Option (PolicyDecision metaCount)) (ended : Option EndEvent) :
    let result := state.choosePrimitive features values metaDecision ended
    result.1.lifetime = state.lifetime ∧ result.1.activeSlot = none ∧
      result.2.started = none ∧ result.2.ended = ended := by
  exact ⟨rfl, Occupancy.afterPrimitive_executing _, rfl, rfl⟩

theorem TemporalControl.option_episodes (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32)
    (values : Vector Binary32 metaCount.word.toNat) (metaDecision : Option (PolicyDecision metaCount))
    (started : Bool) (ended : Option EndEvent) :
    let result := state.stepOption models slot activation next reward values metaDecision started ended
    result.1.lifetime = state.lifetime ∧ result.1.activeSlot = some slot ∧
      result.2.started = (if started then some slot else none) ∧ result.2.ended = ended := by
  rw [TemporalControl.stepOption_eq]
  exact ⟨rfl, Occupancy.afterOption_executing _ _ _, rfl, rfl⟩

theorem TemporalControl.dispatch_episodes (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (decision : PolicyDecision metaCount)
    (ended : Option EndEvent) (observed : TemporalDecision interface.actions)
    (executed : state.dispatchMeta models features declared reward goal decision ended =
      some (next, observed)) :
    next.lifetime = state.lifetime ∧ next.activeSlot = observed.started ∧ observed.ended = ended := by
  rw [TemporalControl.dispatchMeta_eq] at executed
  generalize prepared : state.learnMeta features decision = credited at executed
  have lifetime : credited.lifetime = state.lifetime := by
    rw [← prepared, TemporalControl.learnMeta_eq]
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
      rw [TemporalControl.stepOption_eq] at executed
      cases executed
      exact ⟨lifetime, Occupancy.afterOption_executing _ _ _, rfl⟩

theorem TemporalControl.refresh_episode_slot (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))) :
    (state.refreshFree closing).2.map (·.slot) = closing.map (·.slot) := by
  exact (FreeDispatch.refreshModels_closing_slot
    (⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩ :
      FreeDispatch interface.symbols interface.actions config criterion dimension interface.signals
        (EndingPayload (profile.mode != .frozen))) profile.ranksSubtasks)

theorem TemporalControl.close_lifetime (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1.lifetime = state.lifetime := by
  rw [TemporalControl.closeOption_eq]
  split <;> rfl

theorem TemporalControl.boundary_episodes (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (ended : Option EndEvent) (observed : TemporalDecision interface.actions)
    (executed : state.atBoundary models plan features declared reward goal closing ended =
      some (next, observed)) :
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
    have proof := drawn.1.dispatch_episodes next models features declared reward goal drawn.2 ended observed
      executed
    refine ⟨proof.1.trans drawnLifetime, proof.2.1, ?_⟩
    rw [proof.2.2, ← closingSlot, hc]
    rfl
  | some owner =>
    simp only [hc] at executed
    have proof := (drawn.1.closeOption models features owner reward
      drawn.2.continuation).1.dispatch_episodes next models features declared reward goal drawn.2
      (some (drawn.1.closeOption models features owner reward drawn.2.continuation).2) observed
      executed
    refine ⟨proof.1.trans ((drawn.1.close_lifetime models features owner reward _).trans
      drawnLifetime), proof.2.1, ?_⟩
    rw [proof.2.2, ← closingSlot, hc]
    rfl

theorem TemporalControl.prepare_episodes (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (state.prepareSelection models features reward).lifetime = state.lifetime ∧
      (state.prepareSelection models features reward).activeSlot = state.activeSlot := by
  unfold TemporalControl.prepareSelection
  split <;> split <;> exact ⟨rfl, rfl⟩

theorem TemporalControl.skip_episodes (state : TemporalControl interface profile config criterion dimension) :
    state.skipMeta.lifetime = state.lifetime ∧ state.skipMeta.activeSlot = state.activeSlot := by
  unfold TemporalControl.skipMeta
  split <;> exact ⟨rfl, rfl⟩

theorem TemporalControl.serve_episodes (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observed : TemporalDecision interface.actions)
    (executed : state.serve features = some (next, observed)) :
    next.lifetime = state.lifetime ∧ next.activeSlot = none ∧
      observed.started = none ∧ observed.ended.map (·.slot) = state.activeSlot := by
  unfold TemporalControl.serve at executed
  cases phase : state.runtime.references.phase with
  | idle => simp [phase] at executed
  | option slot activation => simp [phase] at executed
  | exploring committed =>
    simp only [phase] at executed
    cases served : committed.run.serve with
    | none => simp [served] at executed
    | some result =>
      simp only [served, bind, Option.bind, pure, Option.some.injEq] at executed
      cases executed
      have interrupted := state.interrupt_frame committed.origin
      have active : state.activeSlot = committed.origin.map (·.1) := by
        simp [TemporalControl.activeSlot, phase, Occupancy.executing]
      refine ⟨?_, ?_, rfl, ?_⟩
      · unfold TemporalControl.skipMeta
        repeat' split
        all_goals exact interrupted.1
      · unfold TemporalControl.skipMeta
        repeat' split
        all_goals rfl
      · rw [active]
        exact interrupted.2.2

theorem TemporalControl.unserved_free (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (committed : CommittedRun interface.actions (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .exploring committed)
    (unserved : state.serve features = none) : state.activeSlot = none := by
  have spent : committed.run.serve = none := by
    cases served : committed.run.serve with
    | none => rfl
    | some result => simp [TemporalControl.serve, phase, served] at unserved
  have zero := committed.run.spent.mp spent
  cases held : committed.origin with
  | none => simp [TemporalControl.activeSlot, phase, Occupancy.executing, held]
  | some origin =>
    have positive := committed.pending (by simp [held])
    exact absurd positive (by omega)

theorem TemporalControl.select_episodes (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (observed : TemporalDecision interface.actions)
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
    rw [proof.2.1, proof.2.2.1, proof.2.2.2, preparedActive]
    cases state.activeSlot with
    | none => exact .continuing none
    | some old => exact .ending old none
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
          goal none none observed executed
        refine ⟨proof.1.trans preparedLifetime, ?_⟩
        have empty : state.activeSlot = none := by
          rw [← preparedActive]; simp [TemporalControl.activeSlot, phase, Occupancy.executing]
        rw [empty, proof.2.1, proof.2.2]
        exact .free observed.started
      | exploring committed =>
        simp only [phase] at executed
        have proof := (prepared.withPhase .idle).boundary_episodes next models plan features declared reward
          goal none none observed executed
        refine ⟨proof.1.trans preparedLifetime, ?_⟩
        have empty : state.activeSlot = none := by
          rw [← preparedActive]; exact prepared.unserved_free features committed phase served
        rw [empty, proof.2.1, proof.2.2]
        exact .free observed.started
      | option slot activation =>
        simp only [phase] at executed
        let free := prepared.withPhase .idle
        let skill := free.runtime.lifecycle.consumers.skills.get slot
        let metaPolicy := free.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount)
          features free.metaRate
        have active : state.activeSlot = some slot := by
          rw [← preparedActive]; simp [TemporalControl.activeSlot, phase, Occupancy.executing]
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
            let closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)) :=
              ⟨slot, ⟨activation, value, reason⟩, none⟩
            cases criterion with
            | differential =>
              have proof := free.boundary_episodes next models plan features declared reward goal
                (some closing) none observed executed
              refine ⟨proof.1.trans preparedLifetime, ?_⟩
              rw [active, proof.2.1, proof.2.2]
              exact .ending slot observed.started
            | discounted =>
              let closed := free.closeOption models features closing reward
                (comparisonValue .discounted metaPolicy)
              have proof := closed.1.boundary_episodes next models plan features declared reward goal
                none (some closed.2) observed executed
              refine ⟨proof.1.trans ((free.close_lifetime models features closing reward _).trans
                preparedLifetime), ?_⟩
              rw [active, proof.2.1, proof.2.2]
              exact .ending slot observed.started

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

theorem TemporalControl.select_primitive (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool)
    (observed : TemporalDecision interface.actions) (primitive : profile.usesHierarchy = false)
    (executed : state.selectWithOperations models plan features declared reward goal = some (next, observed)) :
    next.activeSlot = none := by
  unfold TemporalControl.selectWithOperations at executed
  generalize hp : state.prepareSelection models features reward = prepared at executed
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    exact (prepared.serve_episodes next features observed served).2.1
  | none =>
    simp only [served, primitive, Bool.not_false, ↓reduceIte] at executed
    have same : (prepared.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero) none none =
        (next, observed) := Option.some.inj executed
    have proof := (prepared.withPhase .idle).primitive_episodes features (Vector.replicate _ .zero) none none
    rw [same] at proof
    exact proof.2.1

theorem TemporalControl.follow_episodes (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions) :
    (state.followOptions models features declared reward goal decision).lifetime = state.lifetime ∧
      (state.followOptions models features declared reward goal decision).activeSlot =
        state.activeSlot := by
  rw [TemporalControl.followOptions_eq]
  split <;> exact ⟨rfl, rfl⟩

theorem TemporalControl.closeSpan_episodes (state : TemporalControl interface profile config criterion dimension)
    (continuation : Option Binary32) :
    (state.closeSpan continuation).lifetime = state.lifetime ∧
      (state.closeSpan continuation).activeSlot = state.activeSlot := by
  cases continuation with
  | none => exact ⟨rfl, rfl⟩
  | some value =>
    rw [TemporalControl.closeSpan_eq]
    exact ⟨rfl, rfl⟩

def TemporalControl.Episodes (state : TemporalControl interface profile config criterion dimension) : Prop :=
  Lifetime.OptionsValid state.lifetime.options state.activeSlot ∧
    (profile.usesHierarchy = false → state.activeSlot = none)

theorem TemporalControl.initial_episodes (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension) :
    (TemporalControl.initial interface profile config criterion dimension).Episodes := by
  constructor
  · intro slot
    simpa [TemporalControl.initial, TemporalControl.activeSlot, TemporalReferences.cold,
      Lifetime.Stats.initial, Occupancy.executing] using Lifetime.OptionEpisodes.initial_valid
  · intro _; rfl

theorem TemporalControl.finish_options (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features observation reward decision).lifetime.options =
      Lifetime.recordOptions state.lifetime.options decision.episodeEnd decision.started := by
  by_cases frozen : profile.mode = .frozen <;>
    simp [TemporalControl.finish_eq, TemporalControl.recordEpisodes, TemporalControl.predictionView,
      PredictionControl.advanceWith, frozen]
  exact Lifetime.Stats.recordDemons_options _ _ _ _

theorem TemporalControl.step_episodes (state next : TemporalControl interface profile config criterion dimension)
    (valid : state.Episodes) (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.step planning features observation reward goal = some (next, decision)) :
    next.Episodes := by
  unfold TemporalControl.step at executed
  cases selected : state.select planning features observation.declared reward goal with
  | none => simp [selected] at executed
  | some result =>
    simp only [selected, bind, Option.bind, pure, Option.some.injEq] at executed
    cases executed
    have trace := state.select_episodes result.1 (modelOperations criterion dimension)
      (planningBoundary planning) features observation.declared reward goal result.2 valid.2 selected
    have follow := result.1.follow_episodes (modelOperations criterion dimension) features
      observation.declared reward goal result.2
    generalize result.1.followOptions (modelOperations criterion dimension) features
      observation.declared reward goal result.2 = followed at follow ⊢
    have closed := followed.closeSpan_episodes
      (result.1.takeoverValue features observation.declared goal result.2)
    generalize followed.closeSpan
      (result.1.takeoverValue features observation.declared goal result.2) =
        spanned at closed ⊢
    constructor
    · change Lifetime.OptionsValid
        (spanned.finish features observation reward result.2).lifetime.options spanned.activeSlot
      rw [TemporalControl.finish_options, closed.1, closed.2, follow.1, follow.2, trace.1]
      apply trace.2.record_valid _ result.2.episodeEnd _ valid.1
      simp [TemporalDecision.episodeEnd, Option.map_map, Function.comp_def]
    · intro primitive
      change spanned.activeSlot = none
      rw [closed.2, follow.2]
      exact state.select_primitive result.1 (modelOperations criterion dimension) (planningBoundary planning)
        features observation.declared reward goal result.2 primitive selected

end Acorn.Handcrafted
