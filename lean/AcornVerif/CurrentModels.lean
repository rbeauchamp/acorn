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
# Executing scalar model and planning contracts

These statements refer to the current managed learners, not an independent
vector model. Sutton, Machado et al., Artificial Intelligence 324 (2023)
104001, arXiv:2202.03466v4, equations (15)–(19); Wan, Naik & Sutton,
*Average-Reward Learning and Planning with Options*, NeurIPS 34 (2021),
section 5, equations (18)–(23). The retained fixed-linear identities require
fixed weights and their stated expectation hypotheses; a terminal maximum and
moving scalar approximation do not inherit those identities or contraction.
-/
namespace AcornVerif.CurrentModels
open Acorn Acorn.Features CurrentLearner CurrentFeatureConsumers

variable {criterion : Criterion} {dimension : Dimension} {config : Features.Config}

/-- Differential continuation is the actual bounded ordered aggregate, with
no coefficient-sized output projection or finite-input assumption. -/
theorem differential_continuation_bound
    (reward continuation duration : Managed (Criterion.config .differential .demon) dimension)
    (features : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    let prediction := (Model.differential reward continuation duration).predict features age
    prediction.continuation.Finite ∧
      |CurrentArithmetic.numerical32 prediction.continuation| ≤
        CurrentPrediction.predictionRadius (modelInput .differential features age).indices.length :=
  prediction_bound continuation.state _

/-- Discounted continuation and its backed-up target obey the actual horizon. -/
theorem discounted_target_bound (model : Model dimension .discounted)
    (features : SwiftTd.ActiveSet dimension) (age : ModelAge) (gain : RewardRate) :
    Discount.g99.predictionRange.Contains ((model.predict features age).target gain) :=
  (Prediction.project .g99 _).legal

/-- Terminal credit clears each physically stored learner, over both criteria. -/
theorem terminal_clears (model : Model dimension criterion) (reward terminal : Binary32)
    (reader : PackedLearner dimension) (member : reader ∈ (model.terminal reward terminal).stored) :
    reader.2.state.transient = TransientState.zero dimension := by
  cases model <;>
    simp only [Model.terminal, Model.stored, List.mem_cons, List.not_mem_nil, or_false] at member
  · rcases member with rfl | rfl <;> rfl
  · rcases member with rfl | rfl | rfl <;> rfl

/-- All model state after every update retains the existing schedule and capacity. -/
theorem model_schedule (model : Model dimension criterion)
    (reader : PackedLearner dimension) (_member : reader ∈ model.stored) :
    ScheduleInv reader.2.state reader.2.phase ∧ reader.2.state.eligibleCount ≤ dimension.capacity :=
  ⟨managed_schedule _, managed_capacity _⟩

/-- Physical model storage sums the actual learner shapes, excluding reader aliases. -/
def modelSlots (model : Model dimension criterion) : Nat :=
  (model.stored.map (fun reader => retainedSlots reader.2.state)).sum

/-- Each model's logical retained storage is linear in its receiving dimension,
independently of stream length. Native object headers and allocator reuse are separate. -/
theorem model_storage (model : Model dimension criterion) :
    modelSlots model ≤ model.stored.length * (12 * dimension.capacity + 2) := by
  have bound (readers : List (PackedLearner dimension)) :
      (readers.map (fun reader => retainedSlots reader.2.state)).sum ≤
        readers.length * (12 * dimension.capacity + 2) := by
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

/-- One scalar backup cannot touch the primitive delegation row. -/
theorem backup_primitive (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    ((state.backup skills features gain slot).controller.learners.get ⟨0, by decide⟩) =
      state.controller.learners.get ⟨0, by decide⟩ := by
  apply plan_other
  intro same
  have := congrArg Fin.val same
  simp [metaOfSkill] at this

/-- Every scalar backup preserves every trajectory row. -/
theorem backup_traces (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) (row : Action metaCount.word.toNat) :
    ((state.backup skills features gain slot).controller.learners.get row).state.transient =
      (state.controller.learners.get row).state.transient := plan_traces _ _ _ _ _

/-- Saturating work accumulation has exact mathematical count semantics. -/
theorem planning_clock_exact (clock : UInt64) :
    (planningClock clock).toNat = min (clock.toNat + planningSlots.length) (2^64 - 1) := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right (clock.toNat + planningSlots.length) (2^64 - 1)
  omega

/-- Work never wraps and adds at most the number of actually configured backups. -/
theorem planning_clock_bounds (clock : UInt64) :
    clock.toNat ≤ (planningClock clock).toNat ∧
    (planningClock clock).toNat ≤ clock.toNat + planningSlots.length := by
  rw [planning_clock_exact]
  have := clock.toNat_lt
  omega

/-- The full executed fold preserves the primitive row, regardless of model values. -/
theorem planning_primitive (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate) :
    ((planningBoundary selection state skills features gain).controller.learners.get
      ⟨0, by decide⟩) = state.controller.learners.get ⟨0, by decide⟩ := by
  cases selection with
  | none => rfl
  | scalar =>
    change ((planningSlots.foldl (fun s slot => s.backup skills features gain slot)
      state).controller.learners.get ⟨0, by decide⟩) = _
    have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (state : PlanningResult criterion dimension) :
        ((slots.foldl (fun s slot => s.backup skills features gain slot)
          state).controller.learners.get ⟨0, by decide⟩) =
          state.controller.learners.get ⟨0, by decide⟩ := by
      induction slots generalizing state with
      | nil => rfl
      | cons slot rest ih =>
        exact (ih (state.backup skills features gain slot)).trans
          (backup_primitive state skills features gain slot)
    exact fold _ _

/-- Every planning write preserves all eligibility and adaptation transients. -/
theorem planning_traces (selection : PlanningSelection)
    (state : PlanningResult criterion dimension)
    (skills : Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount)
    (features : SwiftTd.ActiveSet dimension) (gain : RewardRate)
    (row : Action metaCount.word.toNat) :
    ((planningBoundary selection state skills features gain).controller.learners.get
      row).state.transient = (state.controller.learners.get row).state.transient := by
  cases selection with
  | none => rfl
  | scalar =>
    change ((planningSlots.foldl (fun s slot => s.backup skills features gain slot)
      state).controller.learners.get row).state.transient = _
    have fold (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (state : PlanningResult criterion dimension) :
        ((slots.foldl (fun s slot => s.backup skills features gain slot)
          state).controller.learners.get row).state.transient =
          (state.controller.learners.get row).state.transient := by
      induction slots generalizing state with
      | nil => rfl
      | cons slot rest ih =>
        exact (ih (state.backup skills features gain slot)).trans
          (backup_traces state skills features gain slot row)
    exact fold _ _

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

open CurrentArithmetic CurrentPrediction CurrentModelArithmetic

/-- The actual raw differential backup is finite under the actual producer ranges.
The rational envelope includes conservative machine-rounding slack; it is not a clip. -/
theorem differential_target_bound
    (r c d : Managed (Criterion.config .differential .demon) dimension)
    (features : SwiftTd.ActiveSet dimension) (age : ModelAge) (gain : RewardRate) :
    let prediction := (Model.differential r c d).predict features age
    (prediction.target gain).Finite ∧
      |numerical32 (prediction.target gain)| ≤
        predictionRadius (modelInput .differential features age).indices.length + 514 := by
  let prediction := (Model.differential r c d).predict features age
  have rb := interval_numeric _ prediction.reward
  have db := interval_numeric _ prediction.duration
  have gb := interval_numeric _ gain
  have endpoint0 : numerical32 Binary32.zero = 0 := by decide
  have endpoint1 : numerical32 (Binary32.mk 0x3f800000) = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ)^(-23 : Int) = 1
    norm_num
  have endpoint128 : numerical32
      (Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64) = 128 := by
    rw [show Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64 =
      Binary32.mk 0x43000000 by decide]
    change (1 : ℚ) * 8388608 * (2 : ℚ)^(-16 : Int) = 128
    norm_num
  simp only [Criterion.modelRewardRange, endpoint0, endpoint128] at rb
  simp only [modelDurationRange, Binary32.one, endpoint1, endpoint128] at db
  simp only [rewardRange, endpoint0, endpoint1] at gb
  have productBound : |numerical32 gain.value * numerical32 prediction.duration.value| ≤ 128 := by
    rw [abs_of_nonneg (mul_nonneg gb.1 (by linarith [db.1]))]
    nlinarith [gb.2, db.2]
  have product := small_mul gain.value prediction.duration.value gain.legal.1
    prediction.duration.legal.1 (by linarith)
  have productMag : |numerical32 (gain.value.mul prediction.duration.value)| ≤ 129 := by
    have triangle := abs_add_le
      (numerical32 (gain.value.mul prediction.duration.value) -
        numerical32 gain.value * numerical32 prediction.duration.value)
      (numerical32 gain.value * numerical32 prediction.duration.value)
    rw [sub_add_cancel] at triangle
    linarith [product.2]
  have differenceBound :
      |numerical32 prediction.reward.value -
        numerical32 (gain.value.mul prediction.duration.value)| ≤ 257 := by
    have triangle := abs_add_le (numerical32 prediction.reward.value)
      (-numerical32 (gain.value.mul prediction.duration.value))
    rw [← sub_eq_add_neg, abs_neg, abs_of_nonneg rb.1] at triangle
    linarith [rb.2]
  have difference := small_sub prediction.reward.value
    (gain.value.mul prediction.duration.value) prediction.reward.legal.1 product.1 (by linarith)
  have differenceMag :
      |numerical32 (prediction.reward.value.sub
        (gain.value.mul prediction.duration.value))| ≤ 258 := by
    have triangle := abs_add_le
      (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)) -
        (numerical32 prediction.reward.value -
          numerical32 (gain.value.mul prediction.duration.value)))
      (numerical32 prediction.reward.value -
        numerical32 (gain.value.mul prediction.duration.value))
    rw [sub_add_cancel] at triangle
    linarith [difference.2]
  have continuation := differential_continuation_bound r c d features age
  change prediction.continuation.Finite ∧ |numerical32 prediction.continuation| ≤
    predictionRadius (modelInput .differential features age).indices.length at continuation
  have radiusCap : predictionRadius
      (modelInput .differential features age).indices.length ≤ 4294967296 := by
    unfold predictionRadius
    have := Nat.min_le_right (modelInput .differential features age).indices.length (2^24)
    exact_mod_cast Nat.mul_le_mul_right 256 this
  have sumBound : |numerical32 (prediction.reward.value.sub
      (gain.value.mul prediction.duration.value)) + numerical32 prediction.continuation| <
      (2 : ℚ) ^ (33 : Int) := by
    have triangle := abs_add_le (numerical32 (prediction.reward.value.sub
      (gain.value.mul prediction.duration.value))) (numerical32 prediction.continuation)
    norm_num
    linarith [continuation.2]
  have sum := binary32_add_finite_strict_error
    (prediction.reward.value.sub (gain.value.mul prediction.duration.value))
    prediction.continuation difference.1 continuation.1 33 (by decide) sumBound
  have slack : |numerical32 (prediction.target gain) -
      (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)) +
        numerical32 prediction.continuation)| ≤ 256 := by
    have radius : (2 : ℚ)^(max ((33 : Int)-24) (-149))/2 = 256 := by norm_num
    simpa only [ModelPrediction.target, radius] using sum.2
  refine ⟨sum.1, ?_⟩
  have triangle := abs_add_le
    (numerical32 (prediction.target gain) -
      (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)) +
        numerical32 prediction.continuation))
    (numerical32 (prediction.reward.value.sub (gain.value.mul prediction.duration.value)) +
      numerical32 prediction.continuation)
  rw [sub_add_cancel] at triangle
  have inner := abs_add_le (numerical32 (prediction.reward.value.sub
    (gain.value.mul prediction.duration.value))) (numerical32 prediction.continuation)
  linarith [continuation.2]

/-- The first returned option action performs no model credit in either mode. -/
theorem first_model_omitted {mode : Bool} (skill : Skill config criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256)
    (first : activation.age.val = 0) :
    (skill.stepTemporal (modelOperations criterion dimension) activation next reward gain
      rng).1.model =
      skill.model := by
  simp [Skill.stepTemporal, first, Skill.optionStep]
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
  simp [Skill.stepTemporal, Skill.optionStep, learning, continuing, modelOperations]

/-- Every model transition retains its full option assignment identity. -/
theorem model_assignment {mode : Bool} (skill : Skill config criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporal (modelOperations criterion dimension) activation next reward gain
      rng).1.interest =
      skill.interest := by
  unfold Skill.stepTemporal
  split <;> dsimp only [Skill.optionStep] <;> split <;> rfl

/-- A changed full assignment resets the very model storage used by prediction and planning. -/
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
