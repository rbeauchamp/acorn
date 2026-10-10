/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Models

/-!
# Executable expectation-model planning

Sutton, Machado et al., *Reward-Respecting Subtasks for Model-Based Reinforcement
Learning*, Artificial Intelligence 324 (2023) 104001, arXiv:2202.03466v4,
section 5, equation (19), p. 16: approximate value iteration moves the value of a
feature vector toward the backed-up value `r̂(x, o) + v̂(n̂(x, o), w)`, computed with
the current weights `w`. Acorn backs up each option's meta action value toward that
target through the current SwiftTD planning entry, one option after another, so
each backup reads the weights the previous one wrote. The source takes the maximum
over options inside the update of one state-value function; here the maximum is the
meta-controller's own greedy choice among the backed-up action values.

Search control (Sutton, Bowling and Pilarski, *The Alberta Plan for AI Research*,
arXiv:2208.11173v3 (2023), Step 9, p. 9) chooses where to back up. At each
planning boundary every option is backed up at the current feature vector and at
one stored earlier feature vector; the stored position moves one step per boundary
against the order frames were written in. The count of backups is fixed, so the
work of a boundary is bounded.

Wan, Naik & Sutton, *Average-Reward Learning and Planning with Options*,
NeurIPS 34 (2021), section 5, equations (18)–(23), supplies reward minus gain
times duration plus continuation; Acorn's gain belongs to real primitive credit.
The models and their targets evolve during the run.
-/
namespace Acorn.Features

variable {actions : Word.Count}

/-- Explicit research planning selection, separate from learning/frozen mode. -/
inductive PlanningSelection where
  /-- Model-free comparator; leave knowledge and clock unchanged. -/
  | none
  /-- Expectation-model backups of every option at the current and one stored frame. -/
  | expectation
  deriving DecidableEq

/-- Canonical spelling of each selection; the single text vocabulary shared by
CLI and native admission and by every provenance surface. -/
def PlanningSelection.name : PlanningSelection → String
  | .none => "none"
  | .expectation => "expectation"

/-- The single closed textual admission rule: exactly the two canonical
spellings parse; every other string is refused with `Option.none` and never
substituted. -/
def PlanningSelection.parse (text : String) : Option PlanningSelection :=
  if text = "none" then some .none
  else if text = "expectation" then some .expectation
  else Option.none

/-- Accepted spelling identifies exactly the selected constructor over the
entire string domain. -/
theorem PlanningSelection.parse_accepted (text : String) (selection : PlanningSelection) :
    PlanningSelection.parse text = some selection ↔
      text = PlanningSelection.name selection := by
  cases selection <;> by_cases hn : text = "none" <;> by_cases hs : text = "expectation" <;>
    simp_all [PlanningSelection.parse, PlanningSelection.name]

/-- The work list is derived from the complete option domain. -/
def planningSlots : List (Fin Acorn.FeatureConstants.skillCount) := List.ofFn id

/-- Feature vectors backed up at one boundary: the current one and one stored one. -/
def planningFrames : Nat := 2

/-- Plan through the actual learner without changing controller trajectory lags. -/
def Controller.plan {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    Controller config dimension actions × Binary32 :=
  let learner := controller.learners.get action
  let result := learner.state.planStep config features target
  let updated : Managed config dimension :=
    ⟨result.1, learner.phase, SwiftTd.Entry.apply_plan features target learner.state ▸
      .transition (.plan features target) trivial learner.admitted⟩
  ({ controller with learners := controller.learners.set action.val updated action.isLt }, result.2)

/-- One planning look-ahead: predict the option's outcome at the feature vector under
the value weights the controller holds now, and move the option's action value
toward the backed-up value. Returns the prediction and the planning error observed. -/
def PlanningResult.lookAhead {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    PlanningResult criterion dimension × ModelCache × Binary32 :=
  let prediction := (skills.get slot).model.predict ⟨state.controller, rate⟩ features
    ⟨0, by decide⟩
  let result := state.controller.plan (metaOfSkill slot) features (prediction.target gain)
  ({ state with controller := result.1 }, prediction.cache, result.2)

/-- Back up one option at the current feature vector. One fresh model prediction owns
both the cache observation and the planning write. -/
def PlanningResult.backup {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) : PlanningResult criterion dimension :=
  let result := state.lookAhead skills features gain rate slot
  { result.1 with
    predictions := result.1.predictions.set slot.val result.2.1 slot.isLt
    errors := result.1.errors.set slot.val result.2.2 slot.isLt }

/-- Back up one option at a stored feature vector. The observers describe the current
frame, so only the controller is written. -/
def PlanningResult.sweep {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) : PlanningResult criterion dimension :=
  (state.lookAhead skills features gain rate slot).1

/-- Back up every option at the observed feature vector, one after another, so each
backup reads the weights the previous one wrote. -/
def PlanningResult.backupAll {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    PlanningResult criterion dimension :=
  planningSlots.foldl (fun state slot => state.backup skills features gain rate slot) state

/-- Back up every option at a stored feature vector, one after another. -/
def PlanningResult.sweepAll {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    PlanningResult criterion dimension :=
  planningSlots.foldl (fun state slot => state.sweep skills features gain rate slot) state

/-- The lifetime work count saturates rather than wrapping. -/
def planningClock (clock : UInt64) : UInt64 :=
  UInt64.ofNat (min (clock.toNat + planningFrames * planningSlots.length) (2^64 - 1))

/-- Complete configured boundary work, using current skills rather than cache words:
every option at the current feature vector, then every option at the stored feature
vector search control selects, after which search control moves to the preceding
position. -/
def planningBoundary {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (selection : PlanningSelection) :
    PlanBoundary actions config criterion dimension discounts :=
  fun state skills features gain rate =>
    match selection with
    | .none => { state with errors := Vector.replicate _ .zero }
    | .expectation =>
      let current := state.backupAll skills features gain rate
      let swept := current.sweepAll skills current.recent.selected gain rate
      { swept with steps := planningClock state.steps, recent := swept.recent.advance }

/-- The expectation boundary, field by field: the controller, cache and errors after
both rounds of backups, the advanced work count and the advanced search control. -/
theorem planning_expectation {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    planningBoundary .expectation state skills features gain rate =
      ⟨((state.backupAll skills features gain rate).sweepAll skills
          (state.backupAll skills features gain rate).recent.selected gain rate).controller,
        ((state.backupAll skills features gain rate).sweepAll skills
          (state.backupAll skills features gain rate).recent.selected gain rate).predictions,
        planningClock state.steps,
        ((state.backupAll skills features gain rate).sweepAll skills
          (state.backupAll skills features gain rate).recent.selected gain rate).errors,
        ((state.backupAll skills features gain rate).sweepAll skills
          (state.backupAll skills features gain rate).recent.selected gain rate).recent.advance⟩ :=
  rfl

/-- The loop length is the configured option count, not an independently copied budget. -/
theorem planning_work : planningSlots.length = Acorn.FeatureConstants.skillCount := by simp [planningSlots]

/-- The no-planning comparator preserves learned state, the lifetime count and the
stored recent feature vectors. -/
theorem no_planning {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (planningBoundary .none state skills features gain rate).controller = state.controller ∧
    (planningBoundary .none state skills features gain rate).steps = state.steps ∧
    (planningBoundary .none state skills features gain rate).recent = state.recent :=
  ⟨rfl, rfl, rfl⟩

end Acorn.Features
