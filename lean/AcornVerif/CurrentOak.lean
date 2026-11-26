import Acorn.Host.AgentPrefix
import AcornVerif.Oak

namespace AcornVerif.CurrentOak
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
  {actions : Word.Count} {discounts : List Discount} {mode : Bool}

theorem lookAhead_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (same : (first.get slot).model = (second.get slot).model) :
    state.lookAhead first features gain rate slot =
      state.lookAhead second features gain rate slot := by
  simp only [PlanningResult.lookAhead, same]

theorem backup_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (same : (first.get slot).model = (second.get slot).model) :
    state.backup first features gain rate slot = state.backup second features gain rate slot := by
  simp only [PlanningResult.backup,
    lookAhead_models state first second features gain rate slot same]

theorem sweep_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (same : (first.get slot).model = (second.get slot).model) :
    state.sweep first features gain rate slot = state.sweep second features gain rate slot := by
  simp only [PlanningResult.sweep,
    lookAhead_models state first second features gain rate slot same]

theorem backupAll_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (same : ∀ slot, (first.get slot).model = (second.get slot).model) :
    state.backupAll first features gain rate = state.backupAll second features gain rate := by
  have step : (fun (current : PlanningResult criterion dimension) slot =>
      current.backup first features gain rate slot) =
      fun current slot => current.backup second features gain rate slot :=
    funext fun current => funext fun slot =>
      backup_models current first second features gain rate slot (same slot)
  exact congrArg (fun update => planningSlots.foldl update state) step

theorem sweepAll_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (same : ∀ slot, (first.get slot).model = (second.get slot).model) :
    state.sweepAll first features gain rate = state.sweepAll second features gain rate := by
  have step : (fun (current : PlanningResult criterion dimension) slot =>
      current.sweep first features gain rate slot) =
      fun current slot => current.sweep second features gain rate slot :=
    funext fun current => funext fun slot =>
      sweep_models current first second features gain rate slot (same slot)
  exact congrArg (fun update => planningSlots.foldl update state) step

theorem planningBoundary_models (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (same : ∀ slot, (first.get slot).model = (second.get slot).model) :
    planningBoundary selection state first features gain rate =
      planningBoundary selection state second features gain rate := by
  cases selection with
  | none => rfl
  | expectation =>
    have backed := backupAll_models state first second features gain rate same
    have swept := sweepAll_models (state.backupAll second features gain rate) first second
      (state.backupAll second features gain rate).recent.selected gain rate same
    simp only [planningBoundary, backed, swept]

theorem lookAhead_values (first second : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (controller : first.controller = second.controller) (recent : first.recent = second.recent) :
    (first.lookAhead skills features gain rate slot).1.controller =
        (second.lookAhead skills features gain rate slot).1.controller ∧
      (first.lookAhead skills features gain rate slot).1.recent =
        (second.lookAhead skills features gain rate slot).1.recent ∧
      (first.lookAhead skills features gain rate slot).2 =
        (second.lookAhead skills features gain rate slot).2 := by
  simp only [PlanningResult.lookAhead, controller, recent, and_self]

theorem backup_values (first second : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (controller : first.controller = second.controller) (recent : first.recent = second.recent) :
    (first.backup skills features gain rate slot).controller =
        (second.backup skills features gain rate slot).controller ∧
      (first.backup skills features gain rate slot).recent =
        (second.backup skills features gain rate slot).recent :=
  ⟨(lookAhead_values first second skills features gain rate slot controller recent).1,
    (lookAhead_values first second skills features gain rate slot controller recent).2.1⟩

theorem sweep_values (first second : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (controller : first.controller = second.controller) (recent : first.recent = second.recent) :
    (first.sweep skills features gain rate slot).controller =
        (second.sweep skills features gain rate slot).controller ∧
      (first.sweep skills features gain rate slot).recent =
        (second.sweep skills features gain rate slot).recent :=
  ⟨(lookAhead_values first second skills features gain rate slot controller recent).1,
    (lookAhead_values first second skills features gain rate slot controller recent).2.1⟩

theorem foldl_values
    (update : PlanningResult criterion dimension → Fin Acorn.FeatureConstants.skillCount →
      PlanningResult criterion dimension)
    (kept : ∀ left right slot, left.controller = right.controller → left.recent = right.recent →
      (update left slot).controller = (update right slot).controller ∧
        (update left slot).recent = (update right slot).recent)
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (first second : PlanningResult criterion dimension)
    (controller : first.controller = second.controller) (recent : first.recent = second.recent) :
    (slots.foldl update first).controller = (slots.foldl update second).controller ∧
      (slots.foldl update first).recent = (slots.foldl update second).recent := by
  induction slots generalizing first second with
  | nil => exact ⟨controller, recent⟩
  | cons slot rest ih =>
    exact ih (update first slot) (update second slot)
      (kept first second slot controller recent).1 (kept first second slot controller recent).2

theorem planningBoundary_values (selection : PlanningSelection)
    (first second : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (controller : first.controller = second.controller) (recent : first.recent = second.recent) :
    (planningBoundary selection first skills features gain rate).controller =
        (planningBoundary selection second skills features gain rate).controller ∧
      (planningBoundary selection first skills features gain rate).recent =
        (planningBoundary selection second skills features gain rate).recent := by
  cases selection with
  | none => exact ⟨controller, recent⟩
  | expectation =>
    have backed := foldl_values
      (fun current slot => current.backup skills features gain rate slot)
      (fun left right slot => backup_values left right skills features gain rate slot)
      planningSlots first second controller recent
    have chosen : (first.backupAll skills features gain rate).recent.selected =
        (second.backupAll skills features gain rate).recent.selected :=
      congrArg RecentFeatures.selected backed.2
    have swept := foldl_values
      (fun current slot => current.sweep skills
        (second.backupAll skills features gain rate).recent.selected gain rate slot)
      (fun left right slot => sweep_values left right skills _ gain rate slot)
      planningSlots (first.backupAll skills features gain rate)
      (second.backupAll skills features gain rate) backed.1 backed.2
    rw [planning_expectation, planning_expectation, chosen]
    exact ⟨swept.1, congrArg RecentFeatures.advance swept.2⟩

theorem get_map {source target : Type} {count : Nat} (map : source → target)
    (values : Vector source count) (index : Fin count) :
    (values.map map).get index = map (values.get index) := by
  simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray, Vector.getElem_map]

def hold (model : Model dimension criterion) :
    Skill actions config criterion dimension discounts :=
  { Skill.initial (discounts := discounts) config criterion dimension (.learned .neutral) with
    model := model }

structure PlanInput (criterion : Criterion) (dimension : Dimension) where
  models : Vector (Model dimension criterion) Acorn.FeatureConstants.skillCount
  values : PlanningResult criterion dimension
  gain : RewardRate
  rate : SwiftTd.ExploreRate

def planningView : Oak.View (TemporalControl interface profile config criterion dimension)
    (PlanningResult criterion dimension) where
  get state := ⟨state.runtime.lifecycle.consumers.metaController,
    state.runtime.references.modelPredictions, state.runtime.references.planningSteps,
    state.runtime.references.planningErrors, state.runtime.references.recent⟩
  put state planned := { state with runtime := { state.runtime with
    lifecycle := { state.runtime.lifecycle with consumers :=
      { state.runtime.lifecycle.consumers with metaController := planned.controller } }
    references := { state.runtime.references with
      modelPredictions := planned.predictions
      planningSteps := planned.steps
      planningErrors := planned.errors
      recent := planned.recent } } }
  restore _ := rfl
  replace _ _ _ := rfl
  written _ _ := rfl

def planInput (state : TemporalControl interface profile config criterion dimension) :
    PlanInput criterion dimension :=
  ⟨state.runtime.lifecycle.consumers.skills.map (·.model), planningView.get state,
    state.average.rate, state.metaRate⟩

def planArrow (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (input : PlanInput criterion dimension) : PlanningResult criterion dimension :=
  if profile.mode == .frozen then
    { input.values with errors := Vector.replicate _ Binary32.zero }
  else
    planningBoundary (actions := interface.actions) (config := config)
      (discounts := interface.layout) selection input.values (input.models.map hold) features
      input.gain input.rate

theorem planFree_realizes (selection : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) :
    Oak.Realizes
      (fun state : TemporalControl interface profile config criterion dimension =>
        state.planFree (planningBoundary selection) features)
      planInput (planArrow interface profile config selection features) planningView := by
  intro state
  have models := planningBoundary_models selection (planningView.get state)
    state.runtime.lifecycle.consumers.skills
    ((state.runtime.lifecycle.consumers.skills.map (·.model)).map hold) features
    state.average.rate state.metaRate
    (fun slot => by rw [get_map, get_map]; rfl)
  change planningView.put state
      (if profile.mode == .frozen then
        { planningView.get state with errors := Vector.replicate _ Binary32.zero }
      else planningBoundary selection (planningView.get state)
        state.runtime.lifecycle.consumers.skills features state.average.rate
        state.metaRate) = _
  rw [models]
  rfl

theorem planFree_reads (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (first second : TemporalControl interface profile config criterion dimension)
    (same : planInput first = planInput second) :
    planningView.get (first.planFree (planningBoundary selection) features) =
      planningView.get (second.planFree (planningBoundary selection) features) :=
  (planFree_realizes selection features).reads first second same

theorem planFree_planned (selection : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension)
    (state : TemporalControl interface profile config criterion dimension) :
    planningView.get (state.planFree (planningBoundary selection) features) =
      planArrow interface profile config selection features (planInput state) :=
  (planFree_realizes selection features).writes state

theorem planFree_writes (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) :
    planningView.put (state.planFree plan features) (planningView.get state) = state :=
  rfl

theorem planFree_keeps (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) :
    (state.planFree plan features).runtime.lifecycle.consumers.skills =
        state.runtime.lifecycle.consumers.skills ∧
      (state.planFree plan features).runtime.lifecycle.consumers.control =
        state.runtime.lifecycle.consumers.control ∧
      (state.planFree plan features).runtime.lifecycle.consumers.demons =
        state.runtime.lifecycle.consumers.demons ∧
      (state.planFree plan features).runtime.lifecycle.representation =
        state.runtime.lifecycle.representation :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem features_eq (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frame observation).active =
      encode dimension state.control.runtime.lifecycle.representation.bank
        (observation.words ++ feedbackWords interface.feedback interface.layout
          state.control.runtime.references.demonPredictions.words 0)
        observation.symbols :=
  (state.frame observation).fresh

theorem units_eq (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frame observation).units =
      state.control.runtime.lifecycle.representation.bank.activations observation.symbols :=
  (state.frame observation).freshUnits

theorem frame_congr (state : Agent interface profile config criterion dimension planning)
    (first second : Frame interface) (words : first.words = second.words)
    (symbols : first.symbols = second.symbols) :
    (state.frame first).active = (state.frame second).active ∧
      (state.frame first).units = (state.frame second).units := by
  rw [features_eq, features_eq, units_eq, units_eq, words, symbols]
  exact ⟨rfl, rfl⟩

def potentials (interface : Interface) : Oak.Extra interface where
  Carrier := DeclaredPotentials
  departure := .spatialPotentials
  read percept := percept.frame.declared

def signals (interface : Interface) : Oak.Extra interface where
  Carrier := Cumulants interface.layout
  departure := .cumulants
  read percept := signalValues percept.frame percept.reward

def achievement (interface : Interface) : Oak.Extra interface where
  Carrier := Bool
  departure := .achievementEvent
  read percept := percept.frame.achieved

def extras (interface : Interface) : List (Oak.Extra interface) :=
  [potentials interface, signals interface, achievement interface]

theorem extras_departures (interface : Interface) :
    (extras interface).map (·.departure) =
      [.spatialPotentials, .cumulants, .achievementEvent] :=
  rfl

theorem potentials_origin (percept : Percept interface) :
    ((potentials interface).read percept).origin = (potentials interface).departure :=
  rfl

theorem signals_origin (percept : Percept interface) :
    (signals interface).read percept =
      .cons (some (signals interface).departure) (rewardSignal percept.reward)
        percept.frame.signals :=
  rfl

theorem finish_signals (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (first second : Frame interface)
    (reward : Binary32) (decision : TemporalDecision interface.actions)
    (same : signalValues first reward = signalValues second reward) :
    state.finish features first reward decision =
      state.finish features second reward decision := by
  simp only [TemporalControl.finish_eq, same]

theorem step_frame (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (first second : Frame interface) (reward : Binary32) (goal : Bool)
    (declared : first.declared = second.declared)
    (signals : signalValues first reward = signalValues second reward) :
    state.step planning features first reward goal =
      state.step planning features second reward goal := by
  have finished := fun (current : TemporalControl interface profile config criterion dimension)
      (decision : TemporalDecision interface.actions) =>
    finish_signals current features first second reward decision signals
  simp only [TemporalControl.step, declared, finished]

theorem act_extras (state : Agent interface profile config criterion dimension planning)
    (first second : Percept interface)
    (active : (state.advanceClock.frame first.frame).active =
      (state.advanceClock.frame second.frame).active)
    (units : (state.advanceClock.frame first.frame).units =
      (state.advanceClock.frame second.frame).units)
    (reward : first.reward = second.reward)
    (extra : Oak.Extra.readAll (extras interface) first =
      Oak.Extra.readAll (extras interface) second) :
    state.act first = state.act second := by
  have unfolded : (first.frame.declared, signalValues first.frame first.reward,
      first.frame.achieved, ()) =
      (second.frame.declared, signalValues second.frame second.reward,
        second.frame.achieved, ()) := extra
  simp only [Prod.mk.injEq, and_true] at unfolded
  obtain ⟨declared, signals, achieved⟩ := unfolded
  obtain ⟨firstNext, firstValid, firstEpisodes, firstStep, firstState⟩ :=
    state.act_execution first
  obtain ⟨secondNext, secondValid, secondEpisodes, secondStep, secondState⟩ :=
    state.act_execution second
  rw [← reward] at signals secondStep
  rw [← active, ← achieved] at secondStep
  have same := step_frame state.advanceClock.control planning
    (state.advanceClock.frame first.frame).active first.frame second.frame first.reward
    first.frame.achieved declared signals
  rw [firstStep, secondStep] at same
  simp only [Option.some.injEq, Prod.mk.injEq] at same
  obtain ⟨sameNext, sameDecision⟩ := same
  subst sameNext
  apply Prod.ext
  · rw [firstState, secondState, units]
  · exact sameDecision

def continuation {activation : OptionActivation mode}
    (decision : OptionDecision actions dimension activation) :
    Option (OptionContinuation actions dimension activation) :=
  match decision with
  | .continuing next => some next
  | .ending _ => none

theorem continuation_eq {activation : OptionActivation mode}
    (first second : OptionDecision actions dimension activation)
    (same : continuation first = continuation second) :
    (∃ next, first = .continuing next ∧ second = .continuing next) ∨
      ∃ firstReason secondReason, first = .ending firstReason ∧ second = .ending secondReason := by
  cases first with
  | continuing firstNext =>
    cases second with
    | continuing secondNext =>
      simp only [continuation, Option.some.injEq] at same
      exact .inl ⟨firstNext, rfl, by rw [same]⟩
    | ending reason => simp [continuation] at same
  | ending firstReason =>
    cases second with
    | continuing secondNext => simp [continuation] at same
    | ending secondReason => exact .inr ⟨firstReason, secondReason, rfl, rfl⟩

theorem decideOption_event (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    skill.decideOption activation features potential goal estimate rate =
      if goal then .ending .goal
      else skill.decideOption activation features potential false estimate rate := by
  cases goal <;> rfl

theorem continuation_event (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (estimate : Binary32) (rate : ConsumerRate) :
    continuation (skill.decideOption activation features potential true estimate rate) = none :=
  rfl

theorem continuation_cap (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (capped : ¬ activation.age.val < Acorn.FeatureConstants.optionMaxDuration) :
    continuation (skill.decideOption activation features potential goal estimate rate) =
      none := by
  cases goal with
  | true => rfl
  | false => simp [Skill.decideOption_def, continuation, capped]

theorem settleFollowing_event (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (first second : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (same : ∀ following, skill.following = some following →
      continuation
          (skill.decideOption following.activation features potential first estimate rate) =
        continuation
          (skill.decideOption following.activation features potential second estimate rate)) :
    skill.settleFollowing models value features potential first estimate rate reward gain =
      skill.settleFollowing models value features potential second estimate rate reward
        gain := by
  rw [Skill.settleFollowing_def, Skill.settleFollowing_def]
  cases held : skill.following with
  | none => rfl
  | some following =>
    dsimp only
    rcases continuation_eq _ _ (same following held) with
      ⟨next, left, right⟩ | ⟨leftReason, rightReason, left, right⟩ <;>
      simp only [left, right]

theorem settleTemporal_event (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (first second : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool)
    (same : ∀ following, skill.following = some following →
      continuation
          (skill.decideOption following.activation features potential first estimate rate) =
        continuation
          (skill.decideOption following.activation features potential second estimate rate)) :
    skill.settleTemporal models value features potential first estimate rate reward gain
        learning =
      skill.settleTemporal models value features potential second estimate rate reward gain
        learning := by
  rw [Skill.settleTemporal_def, Skill.settleTemporal_def]
  split
  · exact settleFollowing_event skill models value features potential first second estimate
      rate reward gain same
  · rfl

theorem followTemporal_event (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (first second : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32) (gain : RewardRate)
    (same : ∀ following, skill.following = some following →
      continuation
          (skill.decideOption following.activation features potential first estimate rate) =
        continuation
          (skill.decideOption following.activation features potential second estimate rate)) :
    skill.followTemporal models value features potential first estimate rate action behaviour
        reward gain =
      skill.followTemporal models value features potential second estimate rate action
        behaviour reward gain := by
  simp only [Skill.followTemporal_def]
  cases held : skill.following with
  | none => rfl
  | some following =>
    dsimp only
    rcases continuation_eq _ _ (same following held) with
      ⟨next, left, right⟩ | ⟨leftReason, rightReason, left, right⟩ <;>
      simp only [left, right]

theorem followSlot_event (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (first second : Bool) (estimate : Binary32)
    (rate : ConsumerRate) (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32)
    (gain : RewardRate) (executing : Bool)
    (skill : Skill interface.actions config criterion dimension interface.layout)
    (same : ∀ potential following, executing = false →
      skill.interest.potential features declared = some potential →
      skill.following = some following →
      continuation
          (skill.decideOption following.activation features potential first estimate rate) =
        continuation
          (skill.decideOption following.activation features potential second estimate rate)) :
    followSlot models value features declared first estimate rate action behaviour reward gain
        executing skill =
      followSlot models value features declared second estimate rate action behaviour reward
        gain executing skill := by
  rw [followSlot_def, followSlot_def]
  cases executing with
  | true => rfl
  | false =>
    cases found : skill.interest.potential features declared with
    | none => rfl
    | some potential =>
      exact followTemporal_event skill models value features potential first second estimate
        rate action behaviour reward gain (fun following held => same potential following rfl
          found held)

theorem followOptions_event
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (first second : Bool)
    (decision : TemporalDecision interface.actions)
    (same : ∀ (index : Nat) (bound : index < Acorn.FeatureConstants.skillCount) potential
        following,
      (state.activeSlot == some ⟨index, bound⟩) = false →
      (state.runtime.lifecycle.consumers.skills[index]).interest.potential features declared =
        some potential →
      (state.runtime.lifecycle.consumers.skills[index]).following = some following →
      continuation ((state.runtime.lifecycle.consumers.skills[index]).decideOption
          following.activation features potential first (state.stoppingEstimate decision)
          state.skillRate) =
        continuation ((state.runtime.lifecycle.consumers.skills[index]).decideOption
          following.activation features potential second (state.stoppingEstimate decision)
          state.skillRate)) :
    state.followOptions models features declared reward first decision =
      state.followOptions models features declared reward second decision := by
  have tables : (state.runtime.lifecycle.consumers.skills.mapFinIdx fun index skill bound =>
        followSlot models state.valueFunction features declared first
          (state.stoppingEstimate decision) state.skillRate decision.action
          decision.probabilities reward state.average.rate
          (state.activeSlot == some ⟨index, bound⟩) skill) =
      state.runtime.lifecycle.consumers.skills.mapFinIdx fun index skill bound =>
        followSlot models state.valueFunction features declared second
          (state.stoppingEstimate decision) state.skillRate decision.action
          decision.probabilities reward state.average.rate
          (state.activeSlot == some ⟨index, bound⟩) skill := by
    apply Vector.ext
    intro index bound
    rw [Vector.getElem_mapFinIdx, Vector.getElem_mapFinIdx]
    exact followSlot_event models state.valueFunction features declared first second
      (state.stoppingEstimate decision) state.skillRate decision.action decision.probabilities
      reward state.average.rate _ _
      (fun potential following idle found held =>
        same index bound potential following idle found held)
  rw [TemporalControl.followOptions_eq, TemporalControl.followOptions_eq, tables]

theorem takeoverValue_event
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (first second : Bool) (decision : TemporalDecision interface.actions)
    (same : ∀ event following potential, decision.ended = some event →
      (state.runtime.lifecycle.consumers.skills.get event.slot).following = some following →
      (state.runtime.lifecycle.consumers.skills.get event.slot).interest.potential features
        declared = some potential →
      continuation ((state.runtime.lifecycle.consumers.skills.get event.slot).decideOption
          following.activation features potential first (state.stoppingEstimate decision)
          state.skillRate) =
        continuation ((state.runtime.lifecycle.consumers.skills.get event.slot).decideOption
          following.activation features potential second (state.stoppingEstimate decision)
          state.skillRate)) :
    state.takeoverValue features declared first decision =
      state.takeoverValue features declared second decision := by
  unfold TemporalControl.takeoverValue
  split
  · cases ended : decision.ended with
    | none => rfl
    | some event =>
      simp only [Option.map_some, Option.some.injEq]
      cases held : (state.runtime.lifecycle.consumers.skills.get event.slot).following with
      | none => rfl
      | some following =>
        cases found : (state.runtime.lifecycle.consumers.skills.get event.slot).interest.potential
            features declared with
        | none => rfl
        | some potential =>
          dsimp only
          rcases continuation_eq _ _ (same event following potential ended held found) with
            ⟨next, left, right⟩ | ⟨leftReason, rightReason, left, right⟩ <;>
            simp only [left, right]
  · rfl

theorem dispatchMeta_event
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) (reward : Binary32) (first second : Bool)
    (decision : PolicyDecision metaCount) (ended : Option EndEvent)
    (same : ∀ slot potential following, skillOfMeta decision.action = some slot →
      ((state.learnMeta features decision).runtime.lifecycle.consumers.skills.get
        slot).interest.potential features declared = some potential →
      ((state.learnMeta features decision).runtime.lifecycle.consumers.skills.get
        slot).following = some following →
      continuation (((state.learnMeta features decision).runtime.lifecycle.consumers.skills.get
          slot).decideOption following.activation features potential first
          (comparisonValue criterion decision.snapshot)
          (state.learnMeta features decision).skillRate) =
        continuation (((state.learnMeta features decision).runtime.lifecycle.consumers.skills.get
          slot).decideOption following.activation features potential second
          (comparisonValue criterion decision.snapshot)
          (state.learnMeta features decision).skillRate)) :
    state.dispatchMeta models features declared reward first decision ended =
      state.dispatchMeta models features declared reward second decision ended := by
  rw [TemporalControl.dispatchMeta_eq, TemporalControl.dispatchMeta_eq]
  cases chosen : skillOfMeta decision.action with
  | none => rfl
  | some slot =>
    dsimp only
    cases found : ((state.learnMeta features decision).runtime.lifecycle.consumers.skills.get
        slot).interest.potential features declared with
    | none => simp only [bind, Option.bind]
    | some potential =>
      have settled := settleTemporal_event
        ((state.learnMeta features decision).runtime.lifecycle.consumers.skills.get slot) models
        (state.learnMeta features decision).valueFunction
        features potential first second (comparisonValue criterion decision.snapshot)
        (state.learnMeta features decision).skillRate reward
        (state.learnMeta features decision).average.rate (profile.mode != .frozen)
        (fun following held => same slot potential following chosen found held)
      simp only [bind, Option.bind]
      rw [settled]

theorem startTemporal_event (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (first second : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) (drawn : PersistentDecision actions)
    (same : ∀ following, skill.following = some following →
      continuation
          (skill.decideOption following.activation features potential first estimate rate) =
        continuation
          (skill.decideOption following.activation features potential second estimate rate)) :
    skill.startTemporal models value features potential first estimate rate reward gain learning
        drawn =
      skill.startTemporal models value features potential second estimate rate reward gain
        learning drawn := by
  rw [Skill.startTemporal_def, Skill.startTemporal_def]
  dsimp only
  rw [settleTemporal_event skill models value features potential first second estimate rate
    reward gain learning same]

theorem startOption_event
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (start : StartDraw interface) (first second : Bool) (estimate reward : Binary32)
    (same : ∀ following,
      (state.runtime.lifecycle.consumers.skills.get start.slot).following = some following →
      continuation ((state.runtime.lifecycle.consumers.skills.get start.slot).decideOption
          following.activation features start.potential first estimate state.skillRate) =
        continuation ((state.runtime.lifecycle.consumers.skills.get start.slot).decideOption
          following.activation features start.potential second estimate state.skillRate)) :
    state.startOption models features start first estimate reward =
      state.startOption models features start second estimate reward := by
  rw [TemporalControl.startOption_eq, TemporalControl.startOption_eq,
    startTemporal_event _ models state.valueFunction features start.potential first second
      estimate state.skillRate reward state.average.rate (profile.mode != .frozen) start.drawn
      same]

theorem settle_unstarted
    (state : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (first second : Bool)
    (unstarted : ∀ closing decision start, owed ≠ .boundary closing decision (some start)) :
    state.settle owed models features reward first =
      state.settle owed models features reward second := by
  cases owed with
  | settled => rfl
  | served skip => rfl
  | continuing slot activation next drawn => rfl
  | boundary closing decision start =>
    cases start with
    | none => rfl
    | some start => exact absurd rfl (unstarted closing decision start)

theorem step_event (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (first second : Bool)
    (selected : state.select planning features observation.declared reward first =
      state.select planning features observation.declared reward second)
    (after : ∀ next decision,
      state.select planning features observation.declared reward second =
        some (next, decision) →
      next.takeoverValue features observation.declared first decision =
          next.takeoverValue features observation.declared second decision ∧
        next.followOptions (modelOperations criterion dimension) features observation.declared
            reward first decision =
          next.followOptions (modelOperations criterion dimension) features
            observation.declared reward second decision) :
    state.step planning features observation reward first =
      state.step planning features observation reward second := by
  unfold TemporalControl.step
  rw [selected]
  cases chosen : state.select planning features observation.declared reward second with
  | none => simp only [bind, Option.bind]
  | some result =>
    have agreed := after result.1 result.2 chosen
    simp only [bind, Option.bind, agreed.1, agreed.2]

theorem endTemporal_reason (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (activation : OptionActivation mode)
    (potential : Potential) (first second : OptionEnd) (reward terminal : Binary32)
    (gain : RewardRate) :
    skill.endTemporal models value features ⟨activation, potential, first⟩ reward terminal
        gain =
      skill.endTemporal models value features ⟨activation, potential, second⟩ reward terminal
        gain :=
  rfl

theorem closeOption_reason
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen)) (potential : Potential)
    (first second : OptionEnd)
    (owner : Option (Skill interface.actions config criterion dimension interface.layout))
    (reward terminal : Binary32) :
    (state.closeOption models features ⟨slot, ⟨activation, potential, first⟩, owner⟩ reward
        terminal).1 =
      (state.closeOption models features ⟨slot, ⟨activation, potential, second⟩, owner⟩ reward
        terminal).1 := by
  rw [TemporalControl.closeOption_eq, TemporalControl.closeOption_eq]
  rfl

theorem step_event_primitive
    (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (first second : Bool)
    (primitive : profile.usesHierarchy = false) :
    state.step planning features observation reward first =
      state.step planning features observation reward second := by
  unfold TemporalControl.step TemporalControl.select TemporalControl.selectWithOperations
    TemporalControl.takeoverValue
  simp only [TemporalControl.followOptions_eq, primitive, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

end AcornVerif.CurrentOak
