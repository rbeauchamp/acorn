/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix
import AcornVerif.Oak

/-!
# The executed arrows against the OaK picture

`AcornVerif.Oak` states the picture as a signature. This module states which of its
arrows the executed definitions realize, and lists the arrows outside the picture that
the executed step reads. It restates no executed definition: each theorem concerns the
function the agent executes.

## Planning

The executed planning boundary is `planningBoundary`, and the composed step calls it in
one place, `TemporalControl.planFree`. Its type takes no frame, no reward word and no
host event. Of the option table it is handed, it reads the models only:
`planningBoundary_models` shows that two tables with the same models give the same
result. `planningBoundary_values` shows that the option values and the search-control
state it returns read the planning state through the meta-controller and the stored
feature vectors only. `planArrow` is that same executed function at the picture's type,
from the option models, the option values and a feature vector to the option values,
and `planFree_realizes` shows that the executed boundary call is that arrow: it reads
the local state through `planInput`, and it writes the arrow's value into
`planningView`.

`planningView` holds the meta-controller's values over the options, the stored feature
vectors with the search-control position, and three observers of the boundary itself:
the model caches, the last planning errors and a count of the work done. `planInput`
adds the option models and two learned scalars. The exploration rate of the
meta-controller's nominal policy completes the value function of
`TemporalControl.valueFunction`. The reward rate is no part of that value function: it
enters the backed-up target (`ModelPrediction.target`). It is the rate learned from
earlier rewards, and the boundary takes no reward word.

`planFree_writes` shows that every planning boundary, whatever function it calls, writes
the planning view only, and `planFree_keeps` names what that leaves alone: the option
policies, the option models, the primitive action values, the prediction learners and
the representation.

A frozen profile runs no boundary function: `planArrow` then clears the last errors, as
`planFree` does.

## Perception

`features_eq` and `units_eq` show that the features of a frame and the outputs of the
generated units are functions of the receiver's bank, the frame's words, the stored
prediction feedback and the frame's symbols. `frame_congr` concludes that the coder reads
a frame through its words and symbols only: no signal, no declared potential and not the
achievement event. The reward word is no argument of the coder.

## Arrows outside the picture

`extras` lists what the executed decision reads from a percept beside the features and
the reward, each with the departure it names: the declared subtask potentials (D2), the
signal values of the prediction questions (D5) and the host's achievement event (D8).
`step_frame` shows that `TemporalControl.step` reads the frame through the first two
only; the achievement event and the reward are separate arguments. `act_extras` ties the
list to the full decision: `Agent.act` returns the same decision and next state on two
percepts whose frames encode to the same features and unit outputs and that have the
same reward and the same values of the three arrows. Each arrow's departure is a
declaration. `potentials_origin` and `signals_origin` show that the potentials and the
agent's reward question carry that departure in the executed values; the achievement
event is a bare flag of the frame, and `achievement` wraps it.

The achievement event reaches one decision. `Skill.goal_ends` shows that, with the event
set, an option's stopping decision ends with the reason `goal`. `settleFollowing_event`
and `followTemporal_event` show that an option that learns off-policy reads the event
through that stopping decision only. `TemporalControl.finish`, which credits the
primitive action values, the prediction learners and the options' questions, is handed
the frame and reads it through its signal values only (`finish_signals`), so it does not
read the event. The tester takes no frame. A profile without a hierarchy has no option
to end, and `step_event_primitive` shows that its local transition does not read the
event.

## What is not shown

No instance of `Oak` is built for the executed agent, and the executed agent is not
shown to conform to one. Four arrows are not separated from the composed step: `pose`
(the refresh of the ranked assignments), `solve` (the credit of the options, the
meta-controller and the primitive controller), `model` (the option models, whose
terminal target reads the current value function) and `act` (selection). Of `perceive`,
the coder is separated here; the prediction learners, whose outputs return as feedback
words, and the tester are not. In a profile with a hierarchy, no theorem here follows the
achievement event through the composed step: `TemporalControl.select`,
`TemporalControl.takeoverValue` and `TemporalControl.followOptions` take it as an
argument, and that each passes it to stopping decisions only is read from their
definitions.
-/

namespace AcornVerif.CurrentOak
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
  {actions : Word.Count} {discounts : List Discount}

/-! ## Planning reads the option models, the option values and feature vectors -/

/-- One look-ahead reads the option table through the model of its slot only. -/
theorem lookAhead_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (same : (first.get slot).model = (second.get slot).model) :
    state.lookAhead first features gain rate slot =
      state.lookAhead second features gain rate slot := by
  simp only [PlanningResult.lookAhead, same]

/-- One backup at the current feature vector reads the option table through the model of
its slot only. -/
theorem backup_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (same : (first.get slot).model = (second.get slot).model) :
    state.backup first features gain rate slot = state.backup second features gain rate slot := by
  simp only [PlanningResult.backup,
    lookAhead_models state first second features gain rate slot same]

/-- One backup at a stored feature vector reads the option table through the model of its
slot only. -/
theorem sweep_models (state : PlanningResult criterion dimension)
    (first second : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (same : (first.get slot).model = (second.get slot).model) :
    state.sweep first features gain rate slot = state.sweep second features gain rate slot := by
  simp only [PlanningResult.sweep,
    lookAhead_models state first second features gain rate slot same]

/-- The backups of every option at the current feature vector read the option table
through its models only. -/
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

/-- The backups of every option at a stored feature vector read the option table through
its models only. -/
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

/-- The executed planning boundary reads the option table through its models only: two
tables with the same models give the same result, for every selection, planning state,
feature vector, reward rate and exploration rate. Its type takes no frame, no reward
word and no host event. -/
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

/-- One look-ahead's option values and returned observations read the planning state
through the meta-controller only, and it keeps the stored feature vectors. -/
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

/-- One backup at the current feature vector: the option values it writes read the
planning state through the meta-controller only, and it keeps the stored vectors. -/
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

/-- One backup at a stored feature vector: the option values it writes read the planning
state through the meta-controller only, and it keeps the stored vectors. -/
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

/-- A fold of backups keeps agreement of the option values and of the stored feature
vectors. -/
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

/-- The option values and the search-control state that the executed planning boundary
returns read the planning state through the meta-controller and the stored feature
vectors only. The model caches, the last errors and the work count of the planning
state, which the boundary writes, reach neither. -/
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

/-- The value of a mapped table at a slot is the map of the table's value there. -/
theorem get_map {source target : Type} {count : Nat} (map : source → target)
    (values : Vector source count) (index : Fin count) :
    (values.map map).get index = map (values.get index) := by
  simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray, Vector.getElem_map]

/-- A fresh option that holds a given model. Planning reads an option through its model
only (`planningBoundary_models`), so the other parts of this option reach no result. -/
def hold (model : Model dimension criterion) :
    Skill actions config criterion dimension discounts :=
  { Skill.initial config criterion dimension (.learned .neutral) with model := model }

/-- What planning reads of a local state: the option models, the planning view, the
reward rate and the exploration rate of the meta-controller's nominal policy. -/
structure PlanInput (criterion : Criterion) (dimension : Dimension) where
  /-- The model of each option. -/
  models : Vector (Model dimension criterion) Acorn.FeatureConstants.skillCount
  /-- The meta-controller's option values, the stored feature vectors and the
  boundary's observers. -/
  values : PlanningResult criterion dimension
  /-- The reward rate of the host transitions. -/
  gain : RewardRate
  /-- The exploration rate of the meta-controller's nominal policy. -/
  rate : SwiftTd.ExploreRate

/-- What planning owns of a local state: the meta-controller's option values, the stored
feature vectors with the search-control position, the model caches, the last planning
errors and the count of planning work. -/
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

/-- The input of the planning arrow in a local state. -/
def planInput (state : TemporalControl interface profile config criterion dimension) :
    PlanInput criterion dimension :=
  ⟨state.runtime.lifecycle.consumers.skills.map (·.model), planningView.get state,
    state.average.rate, state.metaRate⟩

/-- The executed planning arrow at the picture's type: from the option models, the
option values and a feature vector to the option values. It is the executed
`planningBoundary` on a table of fresh options that hold the models, and a frozen
profile clears the last errors instead. -/
def planArrow (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (input : PlanInput criterion dimension) : PlanningResult criterion dimension :=
  if profile.mode == .frozen then
    { input.values with errors := Vector.replicate _ Binary32.zero }
  else
    planningBoundary (actions := interface.actions) (config := config)
      (discounts := interface.layout) selection input.values (input.models.map hold) features
      input.gain input.rate

/-- The executed boundary call realizes the planning arrow: for every selection and
feature vector, `TemporalControl.planFree` reads the local state through `planInput` and
writes the arrow's value into the planning view. -/
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

/-- Two local states with the same option models, planning view, reward rate and
meta-controller exploration rate are written with the same planning view. -/
theorem planFree_reads (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (first second : TemporalControl interface profile config criterion dimension)
    (same : planInput first = planInput second) :
    ∃ planned, first.planFree (planningBoundary selection) features =
        planningView.put first planned ∧
      second.planFree (planningBoundary selection) features =
        planningView.put second planned :=
  (planFree_realizes selection features).reads first second same

/-- Every planning boundary, whatever function it calls, writes the planning view only:
writing the old view back gives the old state. -/
theorem planFree_writes (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) :
    planningView.put (state.planFree plan features) (planningView.get state) = state :=
  rfl

/-- A planning boundary leaves the option policies and models, the primitive action
values, the prediction learners and the representation as they were. -/
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

/-! ## Experience produces state features -/

/-- The features of a frame are the coder's value at the receiver's bank, the frame's
words followed by the feedback of the stored predictions, and the frame's symbols. -/
theorem features_eq (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frame observation).active =
      encode dimension state.control.runtime.lifecycle.representation.bank
        (observation.words ++ feedbackWords interface.feedback interface.layout
          state.control.runtime.references.demonPredictions.words 0)
        observation.symbols :=
  (state.frame observation).fresh

/-- The unit outputs of a frame are the bank's activations on the frame's symbols. -/
theorem units_eq (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frame observation).units =
      state.control.runtime.lifecycle.representation.bank.activations observation.symbols :=
  (state.frame observation).freshUnits

/-- The coder reads a frame through its words and symbols only. Two frames with the same
words and symbols give the same features and unit outputs, whatever their signals,
declared potentials and achievement events are. -/
theorem frame_congr (state : Agent interface profile config criterion dimension planning)
    (first second : Frame interface) (words : first.words = second.words)
    (symbols : first.symbols = second.symbols) :
    (state.frame first).active = (state.frame second).active ∧
      (state.frame first).units = (state.frame second).units := by
  rw [features_eq, features_eq, units_eq, units_eq, words, symbols]
  exact ⟨rfl, rfl⟩

/-! ## The arrows outside the picture -/

/-- The host's achievement event of a frame: whether the preceding transition achieved
the goal the world installed. -/
structure Achievement where
  /-- The event. -/
  achieved : Bool

/-- The achievement event is declared as departure D8. -/
instance : Provenance Achievement := ⟨some .achievementEvent⟩

/-- The declared subtask potentials of a frame, departure D2. -/
def potentials (interface : Interface) : Oak.Extra interface where
  Carrier := DeclaredPotentials
  provenance := ⟨some .spatialPotentials⟩
  departure := .spatialPotentials
  registered := rfl
  read percept := percept.frame.declared

/-- The signal values of the prediction questions at a percept, departure D5. -/
def signals (interface : Interface) : Oak.Extra interface where
  Carrier := Cumulants interface.layout
  provenance := ⟨some .cumulants⟩
  departure := .cumulants
  registered := rfl
  read percept := signalValues percept.frame percept.reward

/-- The host's achievement event at a percept, departure D8. -/
def achievement (interface : Interface) : Oak.Extra interface where
  Carrier := Achievement
  departure := .achievementEvent
  registered := rfl
  read percept := ⟨percept.frame.achieved⟩

/-- The arrows outside the picture that the executed decision reads from a percept, each
with the departure it names. -/
def extras (interface : Interface) : List (Oak.Extra interface) :=
  [potentials interface, signals interface, achievement interface]

/-- The registered departures of the extra arrows: D2, D5 and D8. -/
theorem extras_departures (interface : Interface) :
    (extras interface).map (·.departure) =
      [.spatialPotentials, .cumulants, .achievementEvent] :=
  rfl

/-- The declared potentials a frame delivers carry the departure the arrow names. -/
theorem potentials_origin (percept : Percept interface) :
    ((potentials interface).read percept).origin = (potentials interface).departure :=
  rfl

/-- The signal values at a percept are the agent's reward question, which carries the
departure the arrow names, then the world's signals with the origins the world gave
them. -/
theorem signals_origin (percept : Percept interface) :
    (signals interface).read percept =
      .cons (some (signals interface).departure) (rewardSignal percept.reward)
        percept.frame.signals :=
  rfl

/-- The achievement arrow reads the frame's own flag. -/
theorem achievement_read (percept : Percept interface) :
    ((achievement interface).read percept).achieved = percept.frame.achieved :=
  rfl

/-- The completion boundary reads a frame through its signal values only. -/
theorem finish_signals (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (first second : Frame interface)
    (reward : Binary32) (decision : TemporalDecision interface.actions)
    (same : signalValues first reward = signalValues second reward) :
    state.finish features first reward decision =
      state.finish features second reward decision := by
  simp only [TemporalControl.finish_eq, same]

/-- The local transition reads a frame through two extra arrows only: its declared
potentials and its signal values. The reward word and the achievement event are its
other arguments. -/
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

/-- The full decision reads a percept through the features and unit outputs of its
frame, its reward word and the three extra arrows only: on two percepts that agree in
those, it returns the same decision and the same next state. The frames themselves can
differ in their words and symbols. -/
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
      (⟨first.frame.achieved⟩ : Achievement), ()) =
      (second.frame.declared, signalValues second.frame second.reward,
        (⟨second.frame.achieved⟩ : Achievement), ()) := extra
  simp only [Prod.mk.injEq, Achievement.mk.injEq, and_true] at unfolded
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

/-! ## The achievement event -/

/-- An option that settles its off-policy trajectory reads the achievement event
through its stopping decision only. -/
theorem settleFollowing_event (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (first second : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (same : ∀ following, skill.following = some following →
      skill.decideOption following.activation features potential first estimate rate =
        skill.decideOption following.activation features potential second estimate rate) :
    skill.settleFollowing models value features potential first estimate rate reward gain =
      skill.settleFollowing models value features potential second estimate rate reward
        gain := by
  unfold Skill.settleFollowing
  cases held : skill.following with
  | none => rfl
  | some following => simp only [same following held]

/-- An option that learns off-policy from a frame reads the achievement event through
its stopping decision only. -/
theorem followTemporal_event (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (first second : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32) (gain : RewardRate)
    (same : ∀ following, skill.following = some following →
      skill.decideOption following.activation features potential first estimate rate =
        skill.decideOption following.activation features potential second estimate rate) :
    skill.followTemporal models value features potential first estimate rate action behaviour
        reward gain =
      skill.followTemporal models value features potential second estimate rate action
        behaviour reward gain := by
  unfold Skill.followTemporal
  cases held : skill.following with
  | none => rfl
  | some following => simp only [same following held]

/-- A profile without a hierarchy has no option to end: its local transition does not
read the achievement event. -/
theorem step_event_primitive
    (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (observation : Frame interface) (reward : Binary32) (first second : Bool)
    (primitive : profile.usesHierarchy = false) :
    state.step planning features observation reward first =
      state.step planning features observation reward second := by
  unfold TemporalControl.step TemporalControl.select TemporalControl.selectWithOperations
    TemporalControl.takeoverValue TemporalControl.followOptions
  simp only [primitive, Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end AcornVerif.CurrentOak
