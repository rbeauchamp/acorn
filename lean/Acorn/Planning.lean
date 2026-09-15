/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Models

/-!
# Executable scalar-model planning

Sutton, Machado et al., *Reward-Respecting Subtasks for Model-Based Reinforcement
Learning*, Artificial Intelligence 324 (2023) 104001, arXiv:2202.03466v4,
section 5, equation (19). Acorn evaluates each scalar option model once in
slot order and applies the signed error through the current SwiftTD planning
entry. Wan, Naik & Sutton, *Average-Reward Learning and Planning with Options*,
NeurIPS 34 (2021), section 5, equations (18)–(23), supplies reward minus gain
times duration plus continuation; Acorn's gain belongs to real primitive credit.
The models and their targets evolve during the run.
-/
namespace Acorn.Features

/-- Explicit research planning selection, separate from learning/frozen mode. -/
inductive PlanningSelection where
  /-- Model-free comparator; leave knowledge and clock unchanged. -/
  | none
  /-- One signed backup per current option. -/
  | scalar
  deriving DecidableEq

/-- The work list is derived from the complete option domain. -/
def planningSlots : List (Fin Acorn.FeatureConstants.skillCount) := List.ofFn id

/-- Plan through the actual learner without changing controller trajectory lags. -/
def Controller.plan {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    Controller config dimension actions × Binary32 :=
  let learner := controller.learners.get action
  let result := learner.state.planStep config features target
  let updated : Managed config dimension :=
    ⟨result.1, learner.phase, .transition (.plan features target) trivial learner.admitted⟩
  ({ controller with learners := controller.learners.set action.val updated action.isLt }, result.2)

/-- One fresh model prediction owns both the cache observation and the planning write. -/
def PlanningResult.backup {config : Config} {criterion : Criterion} {dimension : Dimension}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) : PlanningResult criterion dimension :=
  let prediction := (skills.get slot).model.predict features ⟨0, by decide⟩
  let result := state.controller.plan (metaOfSkill slot) features (prediction.target gain)
  { state with
    controller := result.1
    predictions := state.predictions.set slot.val prediction.cache slot.isLt
    errors := state.errors.set slot.val result.2 slot.isLt }

/-- The lifetime work count saturates rather than wrapping. -/
def planningClock (clock : UInt64) : UInt64 :=
  UInt64.ofNat (min (clock.toNat + planningSlots.length) (2^64 - 1))

/-- Complete configured boundary work, using current skills rather than cache words. -/
def planningBoundary {config : Config} {criterion : Criterion} {dimension : Dimension}
    (selection : PlanningSelection) : PlanBoundary config criterion dimension :=
  fun state skills features gain =>
    match selection with
    | .none => { state with errors := Vector.replicate _ .zero }
    | .scalar =>
      let result := planningSlots.foldl (fun state slot => state.backup skills features gain slot) state
      { result with steps := planningClock state.steps }

/-- The loop length is the configured option count, not an independently copied budget. -/
theorem planning_work : planningSlots.length = Acorn.FeatureConstants.skillCount := by simp [planningSlots]

/-- The no-planning comparator preserves learned state and the lifetime count. -/
theorem no_planning {config : Config} {criterion : Criterion} {dimension : Dimension}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) :
    (planningBoundary .none state skills features gain).controller = state.controller ∧
    (planningBoundary .none state skills features gain).steps = state.steps := ⟨rfl, rfl⟩

end Acorn.Features
