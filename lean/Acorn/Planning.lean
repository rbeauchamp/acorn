import Acorn.Models

namespace Acorn.Features

variable {actions : Word.Count}

inductive PlanningSelection where
  | none
  | expectation
  deriving DecidableEq

def PlanningSelection.name : PlanningSelection → String
  | .none => "none"
  | .expectation => "expectation"

def PlanningSelection.parse (text : String) : Option PlanningSelection :=
  if text = "none" then some .none
  else if text = "expectation" then some .expectation
  else Option.none

theorem PlanningSelection.parse_accepted (text : String) (selection : PlanningSelection) :
    PlanningSelection.parse text = some selection ↔
      text = PlanningSelection.name selection := by
  cases selection <;> by_cases hn : text = "none" <;> by_cases hs : text = "expectation" <;>
    simp_all [PlanningSelection.parse, PlanningSelection.name]

def planningSlots : List (Fin Acorn.FeatureConstants.skillCount) := List.ofFn id

def planningFrames : Nat := 2

def Controller.planCosted {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    Costed (Controller config dimension actions × Binary32) :=
  let learner := controller.learners.get action
  Costed.bind (Costed.attach (learner.state.planStepCosted config features target)) fun result =>
    let updated : Managed config dimension :=
      ⟨result.val.1, learner.phase, by
        rw [result.property]
        exact SwiftTd.Entry.apply_plan features target learner.state ▸
          .transition (.plan features target) trivial learner.admitted⟩
    Costed.op .planClose
      ({ controller with learners := controller.learners.set action.val updated action.isLt },
        result.val.2)

def Controller.plan {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    Controller config dimension actions × Binary32 :=
  (controller.planCosted action features target).val

theorem Controller.plan_def {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    controller.plan action features target =
      let learner := controller.learners.get action
      let result := learner.state.planStep config features target
      let updated : Managed config dimension :=
        ⟨result.1, learner.phase, SwiftTd.Entry.apply_plan features target learner.state ▸
          .transition (.plan features target) trivial learner.admitted⟩
      ({ controller with learners := controller.learners.set action.val updated action.isLt },
        result.2) := rfl

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

def PlanningResult.sweep {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) : PlanningResult criterion dimension :=
  (state.lookAhead skills features gain rate slot).1

def PlanningResult.backupAll {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    PlanningResult criterion dimension :=
  planningSlots.foldl (fun state slot => state.backup skills features gain rate slot) state

def PlanningResult.sweepAll {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    PlanningResult criterion dimension :=
  planningSlots.foldl (fun state slot => state.sweep skills features gain rate slot) state

def planningClock (clock : UInt64) : UInt64 :=
  UInt64.ofNat (min (clock.toNat + planningFrames * planningSlots.length) (2^64 - 1))

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

theorem planning_work : planningSlots.length = Acorn.FeatureConstants.skillCount := by simp [planningSlots]

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
