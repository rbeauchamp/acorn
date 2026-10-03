/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Planning
import AcornVerif.CurrentFeatureConsumers
import AcornVerif.Options
import AcornVerif.CurrentModelArithmetic

/-!
# Executing option-model and planning contracts

These statements refer to the current managed learners. Sutton, Machado et al.,
Artificial Intelligence 324 (2023) 104001, arXiv:2202.03466v4, equations
(15)–(19); Wan, Naik & Sutton, *Average-Reward Learning and Planning with
Options*, NeurIPS 34 (2021), section 5, equations (18)–(23). They state what
planning writes and leaves alone, the work it counts and the storage of the
full-width model learners. The backed-up value's identity, its rounding bound and
the transition part's storage are in `AcornVerif.CurrentPlanning`.
-/
namespace AcornVerif.CurrentModels
open Acorn Acorn.Features CurrentLearner CurrentFeatureConsumers

variable {criterion : Criterion} {dimension : Dimension} {config : Features.Config}

/-- Discounted continuation and its backed-up target obey the actual horizon. -/
theorem discounted_target_bound (model : Model dimension .discounted)
    (value : ValueFunction .discounted dimension)
    (features : SwiftTd.ActiveSet dimension) (age : ModelAge) (gain : RewardRate) :
    Discount.g99.predictionRange.Contains ((model.predict value features age).target gain) :=
  (Prediction.project .g99 _).legal

/-- Terminal credit clears each physically stored full-width learner, over both
criteria, every value function and every terminal frame. -/
theorem terminal_clears (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (reader : PackedLearner dimension)
    (member : reader ∈ (model.terminal value features reward).stored) :
    reader.2.state.transient = TransientState.zero dimension := by
  cases model <;>
    simp only [Model.terminal, Model.stored, List.mem_cons, List.not_mem_nil, or_false] at member
  · rcases member with rfl | rfl <;> rfl
  · rcases member with rfl | rfl | rfl <;> rfl

/-- Closing a model learner's off-policy trajectory leaves it nothing eligible,
for every state, trace and target word. -/
theorem stop_trajectory_empty {learnerConfig : Acorn.Config}
    (learner : Managed learnerConfig dimension) (target : Binary32) :
    (learner.stopTrajectory target).state.eligibleCount = 0 := rfl

/-- A model restart credits no earlier transition: after its release the step's
first loop is the identity, so the step is exactly its second loop on the released
state, with the new lags. -/
theorem restart_trajectory_first {learnerConfig : Acorn.Config}
    (learner : Managed learnerConfig dimension) (delta vDelta decay : Binary32) :
    (learner.apply .release trivial).state.learnFirstLoop learnerConfig delta vDelta decay =
      (learner.apply .release trivial).state :=
  release_idle learner.state delta vDelta decay

/-- Terminal credit clears the row of every occupied position of the transition part. -/
theorem terminal_clears_rows (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (position : RankIdx dimension) (feature : FeatIdx dimension)
    (occupied : model.transition.ranked.slots[position.val] = some feature) :
    ((model.terminal value features reward).transition.rows[position.val]).state.transient =
      TransientState.zero (rankDimension dimension) := by
  cases model <;>
    simp [Model.terminal, Model.transition, Transition.terminal,
      Transition.updateRows] at occupied ⊢ <;>
    simp [occupied] <;> rfl

/-- Every full-width model learner after every update retains the existing schedule
and capacity. The transition rows are `CurrentPlanning.row_work`'s. -/
theorem model_schedule (model : Model dimension criterion)
    (reader : PackedLearner dimension) (_member : reader ∈ model.stored) :
    ScheduleInv reader.2.state reader.2.phase ∧ reader.2.state.eligibleCount ≤ dimension.capacity :=
  ⟨managed_schedule _, managed_capacity _⟩

/-- Physical model storage sums the actual learner shapes, excluding reader aliases. -/
def modelSlots (model : Model dimension criterion) : Nat :=
  (model.stored.map (fun reader => retainedSlots reader.2.state)).sum

/-- The logical retained storage of each model's full-width learners is linear in its
receiving dimension, independently of stream length; the transition part is
`CurrentPlanning.transition_storage`'s. Native object headers and allocator reuse are separate. -/
theorem model_storage (model : Model dimension criterion) :
    modelSlots model ≤ model.stored.length * (13 * dimension.capacity + 2) := by
  have bound (readers : List (PackedLearner dimension)) :
      (readers.map (fun reader => retainedSlots reader.2.state)).sum ≤
        readers.length * (13 * dimension.capacity + 2) := by
    induction readers with
    | nil => simp
    | cons reader rest ih =>
      have h := retained_slots_unique reader.2.state (managed_schedule reader.2).2.1
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact bound model.stored

/-- Controller planning never changes an unselected action learner. -/
theorem plan_other {cfg : Acorn.Config} {actions : Nat}
    (controller : Controller cfg dimension actions) (action other : Action actions)
    (different : other ≠ action) (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    ((controller.plan action features target).1.learners.get other) =
      controller.learners.get other := by
  have h : action.val ≠ other.val := fun h => different (Fin.ext h.symm)
  change (controller.learners.set action.val _ action.isLt)[other.val] =
    controller.learners[other.val]
  exact Vector.getElem_set_ne action.isLt other.isLt h

/-- Every planning row preserves its exact transient registers, including selected rows. -/
theorem plan_traces {cfg : Acorn.Config} {actions : Nat}
    (controller : Controller cfg dimension actions) (action row : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    ((controller.plan action features target).1.learners.get row).state.transient =
      (controller.learners.get row).state.transient := by
  by_cases same : row = action
  · subst row
    change (controller.learners.set action.val _ action.isLt)[action.val].state.transient = _
    rw [Vector.getElem_set_self]
    exact plan_transient _ _ _
  · rw [plan_other controller action row same]

/-- Controller lags and deferred restart flag are outside the planning write set. -/
theorem plan_lags {cfg : Acorn.Config} {actions : Nat}
    (controller : Controller cfg dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    (controller.plan action features target).1.vOld = controller.vOld ∧
    (controller.plan action features target).1.vDelta = controller.vDelta ∧
    (controller.plan action features target).1.restartPending = controller.restartPending :=
  ⟨rfl, rfl, rfl⟩

/-- One look-ahead cannot touch the primitive delegation row. -/
theorem lookAhead_primitive (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    ((state.lookAhead skills features gain rate slot).1.controller.learners.get ⟨0, by decide⟩) =
      state.controller.learners.get ⟨0, by decide⟩ := by
  apply plan_other
  intro same
  have := congrArg Fin.val same
  simp [metaOfSkill] at this

/-- Every look-ahead preserves every trajectory row. -/
theorem lookAhead_traces (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) (row : Action metaCount.word.toNat) :
    ((state.lookAhead skills features gain rate slot).1.controller.learners.get
        row).state.transient =
      (state.controller.learners.get row).state.transient := plan_traces _ _ _ _ _

/-- A look-ahead writes the controller only: the stored recent frames, the work
count and both observers are those it received. -/
theorem lookAhead_frame (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (state.lookAhead skills features gain rate slot).1.recent = state.recent ∧
      (state.lookAhead skills features gain rate slot).1.steps = state.steps ∧
      (state.lookAhead skills features gain rate slot).1.predictions = state.predictions ∧
      (state.lookAhead skills features gain rate slot).1.errors = state.errors :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Saturating work accumulation has exact mathematical count semantics. -/
theorem planning_clock_exact (clock : UInt64) :
    (planningClock clock).toNat =
      min (clock.toNat + planningFrames * planningSlots.length) (2^64 - 1) := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right (clock.toNat + planningFrames * planningSlots.length) (2^64 - 1)
  omega

/-- Work never wraps and adds at most the number of actually configured backups:
every option at each of the two feature vectors of a boundary. -/
theorem planning_clock_bounds (clock : UInt64) :
    clock.toNat ≤ (planningClock clock).toNat ∧
    (planningClock clock).toNat ≤ clock.toNat + planningFrames * planningSlots.length := by
  rw [planning_clock_exact]
  have := clock.toNat_lt
  omega

/-- A round of look-aheads at one feature vector keeps a property of the controller
that each look-ahead keeps, for both the observed and the stored frame. -/
theorem fold_controller (keeps : Controller (criterion.config .control) dimension
      metaCount.word.toNat → Prop)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (step : ∀ (state : PlanningResult criterion dimension)
      (slot : Fin Acorn.FeatureConstants.skillCount), keeps state.controller →
        keeps (state.lookAhead skills features gain rate slot).1.controller)
    (slots : List (Fin Acorn.FeatureConstants.skillCount))
    (state : PlanningResult criterion dimension) (holds : keeps state.controller) :
    keeps (slots.foldl (fun s slot => s.backup skills features gain rate slot)
        state).controller ∧
      keeps (slots.foldl (fun s slot => s.sweep skills features gain rate slot)
        state).controller := by
  induction slots generalizing state with
  | nil => exact ⟨holds, holds⟩
  | cons slot rest ih =>
    exact ⟨(ih (state.backup skills features gain rate slot) (step state slot holds)).1,
      (ih (state.sweep skills features gain rate slot) (step state slot holds)).2⟩

/-- The controller field of a constructed planning result. -/
theorem result_controller
    (controller : Controller (criterion.config .control) dimension metaCount.word.toNat)
    (predictions : Vector ModelCache Acorn.FeatureConstants.skillCount) (steps : UInt64)
    (errors : Vector Binary32 Acorn.FeatureConstants.skillCount)
    (recent : RecentFeatures dimension) :
    (PlanningResult.mk controller predictions steps errors recent).controller = controller := rfl

/-- The controller after an expectation boundary is the controller after both rounds
of backups: at the observed frame, then at the stored frame search control selects. -/
theorem boundary_controller (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (planningBoundary .expectation state skills features gain rate).controller =
      ((state.backupAll skills features gain rate).sweepAll skills
        (state.backupAll skills features gain rate).recent.selected gain rate).controller :=
  (congrArg PlanningResult.controller
    (planning_expectation state skills features gain rate)).trans (result_controller _ _ _ _ _)

/-- The complete boundary keeps a property of the controller that every look-ahead
keeps at every feature vector: both rounds, at the current and the stored frame. -/
theorem planning_controller (keeps : Controller (criterion.config .control) dimension
      metaCount.word.toNat → Prop)
    (selection : PlanningSelection) (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (step : ∀ (frame : SwiftTd.ActiveSet dimension) (state : PlanningResult criterion dimension)
      (slot : Fin Acorn.FeatureConstants.skillCount), keeps state.controller →
        keeps (state.lookAhead skills frame gain rate slot).1.controller)
    (holds : keeps state.controller) :
    keeps (planningBoundary selection state skills features gain rate).controller := by
  cases selection with
  | none => exact holds
  | expectation =>
    rw [boundary_controller]
    have current := (fold_controller keeps skills features gain rate (step features)
      planningSlots state holds).1
    exact (fold_controller keeps skills
      (state.backupAll skills features gain rate).recent.selected gain rate (step _)
      planningSlots (state.backupAll skills features gain rate) current).2

/-- The full executed boundary preserves the primitive row, regardless of model values. -/
theorem planning_primitive (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    ((planningBoundary selection state skills features gain rate).controller.learners.get
      ⟨0, by decide⟩) = state.controller.learners.get ⟨0, by decide⟩ :=
  planning_controller
    (fun controller => controller.learners.get ⟨0, by decide⟩ =
      state.controller.learners.get ⟨0, by decide⟩)
    selection state skills features gain rate
    (fun frame current slot kept =>
      (lookAhead_primitive current skills frame gain rate slot).trans kept) rfl

/-- Every planning write preserves all eligibility and adaptation transients. -/
theorem planning_traces (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate)
    (row : Action metaCount.word.toNat) :
    ((planningBoundary selection state skills features gain rate).controller.learners.get
      row).state.transient = (state.controller.learners.get row).state.transient :=
  planning_controller
    (fun controller => (controller.learners.get row).state.transient =
      (state.controller.learners.get row).state.transient)
    selection state skills features gain rate
    (fun frame current slot kept =>
      (lookAhead_traces current skills frame gain rate slot row).trans kept) rfl

/-- Planning keeps the controller's lags and deferred restart flag, at both frames. -/
theorem planning_lags (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) (rate : SwiftTd.ExploreRate) :
    (planningBoundary selection state skills features gain rate).controller.vOld =
        state.controller.vOld ∧
      (planningBoundary selection state skills features gain rate).controller.vDelta =
        state.controller.vDelta :=
  planning_controller
    (fun controller => controller.vOld = state.controller.vOld ∧
      controller.vDelta = state.controller.vDelta)
    selection state skills features gain rate
    (fun _ _ _ kept => kept) ⟨rfl, rfl⟩

/-- The executing work list contains each receiving option exactly once. -/
theorem planning_complete : planningSlots.Nodup ∧
    ∀ slot : Fin Acorn.FeatureConstants.skillCount, slot ∈ planningSlots := by
  simp [planningSlots, List.nodup_ofFn, Function.Injective]

/-- Stored interval membership implies the corresponding rational ordering. -/
theorem interval_numeric (range : Interval32) (value : Bounded32 range) :
    CurrentArithmetic.numerical32 range.lower ≤ CurrentArithmetic.numerical32 value.value ∧
    CurrentArithmetic.numerical32 value.value ≤ CurrentArithmetic.numerical32 range.upper :=
  ⟨(CurrentOrder.numerical32_order _ _ range.lowerFinite value.legal.1).mpr value.legal.2.1,
    (CurrentOrder.numerical32_order _ _ value.legal.1 range.upperFinite).mpr value.legal.2.2⟩

/-- The first returned option action performs no model credit in either mode. -/
theorem first_model_omitted {mode : Bool} (skill : Skill config criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256)
    (first : activation.age.val = 0) :
    (skill.stepTemporal (modelOperations criterion dimension) activation next reward gain
      rng).1.model =
      skill.model := by
  simp [Skill.stepTemporal_eq, first, Skill.optionStep]
  split <;> rfl

/-- Continuing model credit consumes raw reward and the pre-increment age,
independently of the centered policy cumulant and shaping potential. -/
theorem continuing_model_owner {mode : Bool} (skill : Skill config criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256)
    (learning : activation.learning = true) (continuing : 0 < activation.age.val) :
    (skill.stepTemporal (modelOperations criterion dimension) activation next reward gain
      rng).1.model =
      skill.model.step next.features activation.age reward := by
  simp [Skill.stepTemporal_eq, Skill.optionStep, learning, continuing, modelOperations]

/-- Every model transition retains its option objective. -/
theorem model_assignment {mode : Bool} (skill : Skill config criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporal (modelOperations criterion dimension) activation next reward gain
      rng).1.interest =
      skill.interest := by
  rw [Skill.stepTemporal_eq]
  split <;> dsimp only [Skill.optionStep] <;> split <;> rfl

/-- A changed unit identity resets the very model storage used by prediction and planning. -/
theorem changed_assignment_model {shape : PatchShape} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config)
    (changed : (state.lifecycle.consumers.skills[slot.val]).interest.sameAssignment target =
      false) :
    ((state.install slot target).lifecycle.consumers.skills[slot.val]).model =
      Model.initial dimension criterion := by
  simp [FreeDispatch.install, changed, Skill.initial]

/-- Feature-image restoration cold-starts physical model learners under the admitted criterion. -/
theorem restore_model {discounts : List Discount}
    (ensemble : Ensemble config criterion dimension discounts)
    (image : PrimaryImage dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    ((ensemble.restore image assignments).skills[slot.val]).model =
      Model.initial dimension criterion := by
  simp [Ensemble.restore]

/-- The model readers used by retirement cover the actual reset state and all its aliases. -/
theorem model_retirement (model : Model dimension criterion) (feature : FeatIdx dimension)
    (reader : PackedLearner dimension) (member : reader ∈ (model.retire feature).readers) :
    registers reader.2.state feature = Vector.replicate 9 Binary32.zero ∧
      (reader.2.state.weights.get feature).value = Binary32.zero ∧
      feature ∉ reader.2.state.transient.eligible := by
  rw [Model.retire_readers] at member
  obtain ⟨before, _, same⟩ := List.mem_map.mp member
  subst reader
  exact ⟨(retire_registers before.2.state feature).1,
    (retire_registers before.2.state feature).2.1, managed_retire_absent before.2 feature⟩

end AcornVerif.CurrentModels
