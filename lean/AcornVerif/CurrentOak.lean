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
`planningView`. So the planning view after the call is the arrow's value
(`planFree_planned`), and two local states with the same planning input have the same
planning view after it (`planFree_reads`).

`planningView` holds the meta-controller's values over the options, the stored feature
vectors with the search-control position, and three observers of the boundary itself:
the model caches, the last planning errors and a count of the work done. `planInput`
adds the option models and two scalars. The reward rate is learned from earlier
rewards; it enters the backed-up target (`ModelPrediction.target`), and the boundary
takes no reward word. The exploration rate of the meta-controller's nominal policy
completes the value function of `TemporalControl.valueFunction`. The profile's rate
policy supplies it (departure D6, `RateState.controller`): the declared constant under
the `declared` policy, the stored value of the authored schedule under `annealed`, and a
rate a learner derives under the two policies that no research profile selects.

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
event is a bare flag of the frame, and `achievement` reads it as it is.

## The achievement event

The registered operation is the stopping decision `Skill.decideOption`. Inside it the
event does one thing: it forces the ending with the reason `goal`
(`decideOption_event`, `Skill.goal_ends`).

For each of seven operations that take the achievement event, where the outcomes of the
stopping decisions it consults agree under two events, its results agree. That is
proved for every input of the operation. The seven are `Skill.settleFollowing`,
`Skill.settleTemporal` and `Skill.followTemporal` (`settleFollowing_event`,
`settleTemporal_event`, `followTemporal_event`), `followSlot` and
`TemporalControl.followOptions` (`followSlot_event`, `followOptions_event`),
`TemporalControl.takeoverValue` (`takeoverValue_event`) and
`TemporalControl.dispatchMeta` (`dispatchMeta_event`). An outcome is the `continuation`
of a decision: the decision without its ending reason. The hypothesis does not force the
two events equal: at the duration cap every decision stops whatever the event is
(`continuation_cap`). So a theorem fails if its operation's result differs between a set
and a clear event where the decisions stop under both, as it does if the operation
reads the event in a stopping case, or reads the ending reason.

Selection (`TemporalControl.selectWithOperations`) also takes the event: it consults the
executing option's stopping decision and hands the event to
`TemporalControl.atBoundary`. No such theorem covers those two.

These are statements about results, and they do not exclude every read of the event.
Where a decision continues the event is clear, because a set event forces the ending.
A read of the event there sees one value and changes no result, so it leaves every
theorem here true. That the operations contain no such read is read from their
definitions.

`step_event` shows that, where selection, `takeoverValue` and `followOptions` agree
under two events, `TemporalControl.step` agrees: the rest of the transition does not
depend on the event.
`TemporalControl.finish`, which credits the primitive action values, the prediction
learners and the options' questions, is handed the frame and reads it through its
signal values only (`finish_signals`), so it does not read the event. The tester takes
no frame. A profile without a hierarchy has no option to end, and
`step_event_primitive` shows that its local transition does not read the event.

The reason of an ending reaches no credit: `endTemporal_reason` and `closeOption_reason`
show that the terminal credit of an option and the state it leaves are the same
whatever the reason is. The reason goes into the end event of the returned decision.
`TemporalControl.finish` writes that event into the lifetime observations and stores
the decision as the last decision, which the observer reads; that is read from its
definition and no theorem here states it.

## What is not shown

No instance of `Oak` is built for the executed agent, and the executed agent is not
shown to conform to one. Four arrows are not separated from the composed step: `pose`
(the refresh of the ranked assignments), `solve` (the credit of the options, the
meta-controller and the primitive controller), `model` (the option models, whose
terminal target reads the current value function) and `act` (selection). Of `perceive`,
the coder is separated here; the prediction learners, whose outputs return as feedback
words, and the tester are not.

The tester is more than not separated: `perceive` has no argument for what it reads. In
`Oak.step` the next `Perception` is a function of the old perception and the percept
only. The executed tester runs at the end of every learning decision (`Agent.retire`),
and `Lifecycle.score` computes each unit's utility from the outgoing weights of its
readers: the primitive controller, the meta-controller, the option policies, the option
models and the prediction learners. That utility selects the unit to replace, so the
next bank depends on the options, values and models. In an instance whose `Perception`
carrier holds the bank, the next bank must be a function of that carrier and the
percept, so that carrier must also hold what the tester reads of the options, values
and models. An instance that keeps the bank in another carrier is not excluded. This is
a second open structural choice beside the order of the step, and neither remedy is
selected: an arrow by which feature construction reads the use of features by the other
boxes, or the tester's read declared as an arrow outside the picture (departure D7).

For a profile with a hierarchy, no theorem here follows the achievement event through
selection. `TemporalControl.selectWithOperations` takes the executing option's stopping
decision and hands the event to `TemporalControl.atBoundary`, which hands it to
`dispatchMeta` in a later state; no theorem states that chain. The exact open statement
is the composed step written once with the stopping rule as a parameter and no event,
equal to the executed step when the rule is `Skill.decideOption` at the frame's event. A
statement that some function of the stopping rule gives the step is no substitute: the
rule at a set event differs from the rule at a clear one, so such a function exists for
every step. The same parameterized form is what excludes every read of the event
outside the stopping decisions, which the theorems about results here do not.
-/

namespace AcornVerif.CurrentOak
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
  {actions : Word.Count} {discounts : List Discount} {mode : Bool}

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
  written _ _ := rfl

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
meta-controller exploration rate have the same planning view after the boundary call,
whatever else differs between them. -/
theorem planFree_reads (selection : PlanningSelection) (features : SwiftTd.ActiveSet dimension)
    (first second : TemporalControl interface profile config criterion dimension)
    (same : planInput first = planInput second) :
    planningView.get (first.planFree (planningBoundary selection) features) =
      planningView.get (second.planFree (planningBoundary selection) features) :=
  (planFree_realizes selection features).reads first second same

/-- After the boundary call the planning view of a local state is the planning arrow's
value at the state's planning input. -/
theorem planFree_planned (selection : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension)
    (state : TemporalControl interface profile config criterion dimension) :
    planningView.get (state.planFree (planningBoundary selection) features) =
      planArrow interface profile config selection features (planInput state) :=
  (planFree_realizes selection features).writes state

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

/-- The declared subtask potentials of a frame, departure D2. -/
def potentials (interface : Interface) : Oak.Extra interface where
  Carrier := DeclaredPotentials
  departure := .spatialPotentials
  read percept := percept.frame.declared

/-- The signal values of the prediction questions at a percept, departure D5. -/
def signals (interface : Interface) : Oak.Extra interface where
  Carrier := Cumulants interface.layout
  departure := .cumulants
  read percept := signalValues percept.frame percept.reward

/-- The host's achievement event at a percept, departure D8: whether the preceding
transition achieved the goal the world installed. -/
def achievement (interface : Interface) : Oak.Extra interface where
  Carrier := Bool
  departure := .achievementEvent
  read percept := percept.frame.achieved

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

/-! ## The achievement event -/

/-- The outcome of a stopping decision without its ending reason: the continuation where
the option continues, and nothing where it stops. -/
def continuation {activation : OptionActivation mode}
    (decision : OptionDecision actions dimension activation) :
    Option (OptionContinuation actions dimension activation) :=
  match decision with
  | .continuing next => some next
  | .ending _ => none

/-- Two stopping decisions with the same outcome both continue, with one continuation, or
both stop, each with its own reason. -/
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

/-- Inside the registered stopping operation the event does one thing: it forces the
ending with the reason `goal`. With the event clear the decision is the learned one. -/
theorem decideOption_event (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    skill.decideOption activation features potential goal estimate rate =
      if goal then .ending .goal
      else skill.decideOption activation features potential false estimate rate := by
  cases goal <;> rfl

/-- With the event set, the outcome of an option's stopping decision is a stop. So the
hypotheses of the theorems below hold between a set and a clear event exactly where the
learned decision stops as well. -/
theorem continuation_event (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (estimate : Binary32) (rate : ConsumerRate) :
    continuation (skill.decideOption activation features potential true estimate rate) = none :=
  rfl

/-- At the duration cap the outcome of an option's stopping decision is a stop whatever
the event is. So at the cap the hypotheses of the theorems below hold between a set and
a clear event, and their conclusions there say that the two events give one result. -/
theorem continuation_cap (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (capped : ¬ activation.age.val < Acorn.FeatureConstants.optionMaxDuration) :
    continuation (skill.decideOption activation features potential goal estimate rate) =
      none := by
  cases goal with
  | true => rfl
  | false => simp [Skill.decideOption, continuation, capped]

/-- Where the outcome of the stopping decision of a stored trajectory agrees under two
achievement events, settling the trajectory gives one result. The hypothesis admits a
set and a clear event wherever the learned decision stops, so the theorem fails if the
settling of a stopped trajectory depends on the event or on the ending reason. It does
not exclude a read of the event where the decision continues: there the event is
clear. -/
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
  unfold Skill.settleFollowing
  cases held : skill.following with
  | none => rfl
  | some following =>
    dsimp only
    rcases continuation_eq _ _ (same following held) with
      ⟨next, left, right⟩ | ⟨leftReason, rightReason, left, right⟩ <;>
      simp only [left, right]

/-- Where the outcome of the stopping decision of the stored trajectory agrees under two
achievement events, an invocation start settles it to one result. It fails if
`Skill.settleTemporal` depends on the event where it settles nothing or where the
trajectory stops under both events. It does not exclude a read where the decision
continues. -/
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
  unfold Skill.settleTemporal
  split
  · exact settleFollowing_event skill models value features potential first second estimate
      rate reward gain same
  · rfl

/-- Where the outcome of the stopping decision of a stored trajectory agrees under two
achievement events, the option's off-policy learning from the frame gives one result.
The hypothesis admits a set and a clear event wherever the learned decision stops, so
the theorem fails if the learning of a stopped trajectory, or of an option with no
trajectory, depends on the event or on the ending reason. It does not exclude a read of
the event where the decision continues: there the event is clear. -/
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
  unfold Skill.followTemporal
  cases held : skill.following with
  | none => rfl
  | some following =>
    dsimp only
    rcases continuation_eq _ _ (same following held) with
      ⟨next, left, right⟩ | ⟨leftReason, rightReason, left, right⟩ <;>
      simp only [left, right]

/-- Where the outcome of a slot's stopping decision agrees under two achievement events,
the slot's share of a followed frame is one result. An executing slot and a slot with no
supplied potential consult no decision, and the hypothesis asks nothing of them, so the
theorem fails if `followSlot` depends on the event for such a slot or for a stopped
trajectory. It does not exclude a read where the decision continues. -/
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
  unfold followSlot
  cases executing with
  | true => rfl
  | false =>
    cases found : skill.interest.potential features declared with
    | none => rfl
    | some potential =>
      exact followTemporal_event skill models value features potential first second estimate
        rate action behaviour reward gain (fun following held => same potential following rfl
          found held)

/-- Where the outcomes of the stopping decisions of the slots that are not executing
agree under two achievement events, the off-policy learning of the options gives one
state. The hypothesis names each such slot of the given state with a supplied potential
and a stored trajectory. The theorem fails if `TemporalControl.followOptions` depends on
the event for another slot, for a stopped trajectory, or outside the option table. It
does not exclude a read where a decision continues. -/
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

/-- Where the outcome of the interrupted option's stopping decision agrees under two
achievement events, the value its span closes toward is one value. It fails if
`TemporalControl.takeoverValue` depends on the event where it consults no decision or
where the decision stops under both events. It does not exclude a read where the
decision continues. -/
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

/-- Where the outcome of one stopping decision agrees under two achievement events, the
dispatch of a drawn meta action gives one result. The decision is that of the selected
option's stored trajectory, in the state after meta credit. The theorem fails if
`TemporalControl.dispatchMeta` depends on the event in the meta credit, the primitive
choice or the start of the option, or where the trajectory stops under both events. It
does not exclude a read where the decision continues. -/
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

/-- Where the outcome of the stopping decision of the stored trajectory agrees under two
achievement events, the start of an invocation whose first action is already drawn gives
one result. The start reads the event in its settlement only. -/
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
  unfold Skill.startTemporal
  rw [settleTemporal_event skill models value features potential first second estimate rate
    reward gain learning same]

/-- Where the outcome of the stopping decision of the selected option's stored trajectory
agrees under two achievement events, the start of that option from a recorded first action
gives one state. -/
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

/-- The owed writes of a draw-first selection read the achievement event at the start of
a selected option only: for every other record they are one state under two events.
`TemporalControl.settle_started` gives the remaining record as a call of
`TemporalControl.startOption`, which `startOption_event` covers. -/
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

/-- Where selection, the value an interrupted option's span closes toward and the
off-policy learning of the options agree under two achievement events, the local
transition agrees. So the rest of the transition does not depend on the event: the
theorem fails if the closing of the span or the completion boundary is made to depend
on it. -/
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

/-- The terminal credit of an option does not read the reason of its ending. -/
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

/-- Closing an option writes the same local state whatever the reason of its ending is:
the reason goes into the returned end event only. -/
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
