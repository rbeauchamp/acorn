/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Planning
import AcornVerif.CurrentLearner
import AcornVerif.Resource.ModelWork

/-!
# Work of planning at a free boundary

Twins of the planning of `Acorn.Planning`. Expectation planning backs up every option at the
current frame and then every option at one stored frame, each backup a model prediction and
one planning step of the meta-controller's row of that option. A stored frame is an active
set of the agent's dimension, so its length is at most the capacity
(`AcornVerif.CurrentLearner.active_cardinality`); no theorem ties it to the length of a
frame's encoding, because a stored frame read from a checkpoint image is admitted at any
length up to the capacity.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}

/-- Twin of `PlanningResult.lookAhead`: the option model's prediction and the meta row's
planning step. -/
def lookAhead (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    Costed (PlanningResult criterion dimension × ModelCache × Binary32) := do
  let prediction ← predict κ (skills.get slot).model ⟨state.controller, rate⟩ features
    ⟨0, by decide⟩
  let result ← plan κ state.controller (metaOfSkill slot) features (prediction.target gain)
  Costed.op (κ .lookAhead) ({ state with controller := result.1 }, prediction.cache, result.2)

theorem lookAhead_val (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (lookAhead κ state skills features gain rate slot).val =
      state.lookAhead skills features gain rate slot := rfl

/-- Bound of one look-ahead over `width` features. -/
abbrev lookAheadBound (κ : Costs) (positions width : Nat) : Nat :=
  predictBound κ positions width + (planBound κ width + κ .planClose + κ .lookAhead)

theorem lookAhead_work (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (lookAhead κ state skills features gain rate slot).work ≤
      lookAheadBound κ (rankDimension dimension).capacity features.indices.length :=
  Costed.bind_work_le (predict_work κ _ _ features _) fun _ =>
    Costed.bind_work_le (plan_work κ state.controller _ features _) fun _ => Nat.le_refl _

/-- Twin of `PlanningResult.backup`. -/
def backup (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    Costed (PlanningResult criterion dimension) := do
  let result ← lookAhead κ state skills features gain rate slot
  Costed.op (κ .backupClose)
    { result.1 with
      predictions := result.1.predictions.set slot.val result.2.1 slot.isLt
      errors := result.1.errors.set slot.val result.2.2 slot.isLt }

/-- Twin of `PlanningResult.sweep`. -/
def sweep (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    Costed (PlanningResult criterion dimension) := do
  let result ← lookAhead κ state skills features gain rate slot
  Costed.pure result.1

/-- Twin of `PlanningResult.backupAll`: one backup for each option. -/
def backupAll (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    Costed (PlanningResult criterion dimension) :=
  Costed.foldl (κ .visit) (fun state slot => backup κ state skills features gain rate slot) state
    planningSlots

theorem backupAll_val (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (backupAll κ state skills features gain rate).val = state.backupAll skills features gain rate :=
  rfl

/-- Bound of the backups of every option over `width` features. -/
abbrev backupAllBound (κ : Costs) (positions width : Nat) : Nat :=
  Library.foldl.work (κ .visit) Acorn.FeatureConstants.skillCount
    (lookAheadBound κ positions width + κ .backupClose)

theorem backupAll_work (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (backupAll κ state skills features gain rate).work ≤
      backupAllBound κ (rankDimension dimension).capacity features.indices.length := by
  have folded := Costed.foldl_work_le (κ .visit)
    (lookAheadBound κ (rankDimension dimension).capacity features.indices.length + κ .backupClose)
    (fun state slot => backup κ state skills features gain rate slot) state planningSlots
    (fun state slot _ => Costed.bind_work_le (lookAhead_work κ state skills features gain rate slot)
      fun _ => Nat.le_refl _)
  rwa [planning_work] at folded

/-- Twin of `PlanningResult.sweepAll`: one sweep for each option. -/
def sweepAll (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    Costed (PlanningResult criterion dimension) :=
  Costed.foldl (κ .visit) (fun state slot => sweep κ state skills features gain rate slot) state
    planningSlots

/-- Bound of the sweeps of every option over `width` features. -/
abbrev sweepAllBound (κ : Costs) (positions width : Nat) : Nat :=
  Library.foldl.work (κ .visit) Acorn.FeatureConstants.skillCount
    (lookAheadBound κ positions width + 0)

theorem sweepAll_work (κ : Costs) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (sweepAll κ state skills features gain rate).work ≤
      sweepAllBound κ (rankDimension dimension).capacity features.indices.length := by
  have folded := Costed.foldl_work_le (κ .visit)
    (lookAheadBound κ (rankDimension dimension).capacity features.indices.length + 0)
    (fun state slot => sweep κ state skills features gain rate slot) state planningSlots
    (fun state slot _ => Costed.bind_work_le (lookAhead_work κ state skills features gain rate slot)
      fun _ => Nat.le_refl _)
  rwa [planning_work] at folded

/-- A look-ahead's bound grows with the width of its frame. -/
theorem lookAheadBound_mono (κ : Costs) (positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    lookAheadBound κ positions width ≤ lookAheadBound κ positions limit := by
  have m1 := Library.contains.control_mono (visit := κ .visit + κ .compare) fits
  have m1b := Library.append.control_mono (visit := κ .visit) fits
  have m2 := Library.foldl.work_mono (visit := κ .visit) (Nat.add_le_add_right fits 1)
    (Nat.le_refl (κ .sumTerm))
  have m3 := Library.filterMap.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .position))
  have m4 := expectedAtBound_mono κ positions (Nat.add_le_add_right fits 1)
  have m5 := Library.ofFn.work_mono (visit := κ .visit) (Nat.le_refl metaCount.word.toNat)
    (Nat.add_le_add_right m2 (κ .outcomeValue))
  have m6 := Library.foldl.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .sumTerm))
  have m7 := Library.map.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .read))
  have m8 := pass_mono (visit := κ .visit) fits (Nat.le_refl (κ .planElement))
  simp only [lookAheadBound, predictBound, lookaheadBound, outcomeValuesBound, rowInputBound,
    inputBound, planBound]
  omega

/-- The costed run of `planningBoundary`: no planning clears the errors; expectation planning
backs up every option at the frame, then at the stored frame search control selects. -/
def planningBoundaryRun (κ : Costs) (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    Costed (PlanningResult criterion dimension) :=
  match selection with
  | .none => do
    let errors ← Costed.replicate (κ .visit) Acorn.FeatureConstants.skillCount Binary32.zero
    Costed.op (κ .planBoundary) { state with errors := errors }
  | .expectation => do
    let current ← backupAll κ state skills features gain rate
    let swept ← sweepAll κ current skills current.recent.selected gain rate
    Costed.op (κ .planBoundary)
      { swept with steps := planningClock state.steps, recent := swept.recent.advance }

theorem planningBoundaryRun_val (κ : Costs) (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (planningBoundaryRun κ selection state skills features gain rate).val =
      planningBoundary selection state skills features gain rate := by
  cases selection <;> rfl

/-- Twin of `planningBoundary`. -/
def planningBoundary (κ : Costs) (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    Costed (PlanningResult criterion dimension) :=
  Costed.via (Features.planningBoundary selection state skills features gain rate)
    (planningBoundaryRun κ selection state skills features gain rate)

/-- Bound of a free boundary's planning over `width` features at a capacity. -/
abbrev planningBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  Library.replicate.control (κ .visit) Acorn.FeatureConstants.skillCount +
    (backupAllBound κ positions width + sweepAllBound κ positions capacity) + κ .planBoundary

theorem planningBoundary_work (κ : Costs) (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill actions config criterion dimension discounts)
      Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (planningBoundary κ selection state skills features gain rate).work ≤
      planningBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length := by
  change (planningBoundaryRun κ selection state skills features gain rate).work ≤ _
  cases selection
  · simp only [planningBoundaryRun, Costed.bind_work, planningBound]
    omega
  · unfold planningBoundaryRun
    refine Nat.le_trans (Costed.bind_work_le (backupAll_work κ state skills features gain rate)
      fun current => Costed.bind_work_le (show _ ≤ sweepAllBound κ _ dimension.capacity from
        Nat.le_trans (sweepAll_work κ current skills current.recent.selected gain rate)
          (Library.foldl.work_mono (Nat.le_refl _) (Nat.add_le_add_right
            (lookAheadBound_mono κ _ (CurrentLearner.active_cardinality _)) 0)))
        fun _ => Nat.le_refl _) ?_
    simp only [planningBound]
    omega

end AcornVerif.Resource.Twin
