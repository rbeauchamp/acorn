/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentLearner
import AcornVerif.CurrentRetirementRounding
import Acorn.FeatureLifecycle
import Acorn.Sarsa

/-!
# Executing replacement safety

A replaced unit enters with zero outgoing weight in every reader (Mahmood &
Sutton, *Representation Search through Generate and Test*, AAAI 2013 workshop,
p. 3: "The output weights wi of these new features are set to zero"; Dohare,
Hernandez-Garcia, Rahman, Mahmood & Sutton, *Maintaining Plasticity in Deep
Continual Learning*, arXiv:2306.13812v3 (2024), §6, p. 19: zero outgoing weights
"ensures that the newly added hidden units do not affect the already learned
function"). These
contracts concern the executed `Lifecycle.replace` and SwiftTD's
`NumericState.retireIndex` and `predict`: every reader's weight at the replaced
slot is the positive-zero word, every other weight is unchanged, every
prediction over an input without the slot is unchanged bit for bit, and adding
the new unit's term preserves the numerical value of every finite partial sum
under the pinned standard float model. Only the retired slot's own learner state
changes: every learner keeps its shared previous prediction and weight-change
aggregate, so its next TD error differs from the unreplaced one only through the
retired slot's weight.
-/

open Acorn Acorn.SwiftTd
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder

namespace AcornVerif.CurrentRetirement

/-- Adding positive zero preserves every finite numerical value, including negative zero. -/
theorem zero_add_numeric (word : Binary32) (finite : word.Finite) :
    (Binary32.zero.add word).Finite ∧
      numerical32 (Binary32.zero.add word) = numerical32 word := by
  have valid := model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)
  change ModelNormalized Format.binary32 (decoded32 word) ∧
    ModelFits Format.binary32 (decoded32 word) at valid
  have normal : ModelNormalized Format.binary32
      (UnpackedFloat.add Format.binary32 (.zero .positive) (decoded32 word)) := by
    cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelNormalized]
    split_ifs <;> simp
  have fits : ModelFits Format.binary32
      (UnpackedFloat.add Format.binary32 (.zero .positive) (decoded32 word)) := by
    cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelFits]
    split_ifs <;> simp
  have decoded := model_add32_decoded .zero word (by decide) finite normal fits
  refine ⟨(model_decoded32_finite _).mp ?_, ?_⟩
  · rw [decoded]
    exact model_normalized_finite _ _ normal
  · change unpackedValue (decoded32 _) = _
    rw [decoded]
    change unpackedValue (UnpackedFloat.add Format.binary32 (.zero .positive) (decoded32 word)) =
      unpackedValue (decoded32 word)
    cases h : decoded32 word with
    | zero sign => cases sign <;> rfl
    | _ => rfl

/-- Adding positive zero preserves every finite numerical value, including negative zero. -/
theorem add_zero_numeric (word : Binary32) (finite : word.Finite) :
    (word.add Binary32.zero).Finite ∧
      numerical32 (word.add Binary32.zero) = numerical32 word := by
  have valid := model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)
  change ModelNormalized Format.binary32 (decoded32 word) ∧
    ModelFits Format.binary32 (decoded32 word) at valid
  have normal : ModelNormalized Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 word) (.zero .positive)) := by
    cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelNormalized]
  have fits : ModelFits Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 word) (.zero .positive)) := by
    cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelFits]
  have decoded := model_add32_decoded word .zero finite (by decide) normal fits
  refine ⟨(model_decoded32_finite _).mp ?_, ?_⟩
  · rw [decoded]
    exact model_normalized_finite _ _ normal
  · change unpackedValue (decoded32 _) = _
    rw [decoded]
    change unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 word) (.zero .positive)) =
      unpackedValue (decoded32 word)
    cases h : decoded32 word with
    | zero sign => cases sign <;> rfl
    | _ => rfl

variable {config : Config} {dimension : Dimension}

/-- Retirement writes only the retired slot's weight. -/
theorem retireIndex_weight_other (state : NumericState config dimension)
    (idx other : FeatIdx dimension) (different : other ≠ idx) :
    (state.retireIndex idx).weights.get other = state.weights.get other := by
  have distinct : idx.val ≠ other.val := fun same => different (Fin.ext same.symm)
  unfold NumericState.retireIndex
  split <;> simp [NumericState.removeEligibleAt, NumericState.clearFeatureRegisters,
    NumericState.writeZ, NumericState.writeP, NumericState.writeZBar,
    NumericState.writeDeltaWeight, NumericState.writeZDelta, NumericState.writeH,
    NumericState.writeHOld, NumericState.writeHTemp, NumericState.writeLastAlpha,
    NumericState.writeWeight, NumericState.writeBetaValue, NumericState.writeStepSize,
    CurrentLearner.vector_get,
    Vector.getElem_set_ne _ _ distinct]

/-- Every prediction over an input without the retired slot is unchanged, bit for bit. -/
theorem retireIndex_predict (state : NumericState config dimension) (idx : FeatIdx dimension)
    (features : ActiveSet dimension) (absent : idx ∉ features.indices) :
    (state.retireIndex idx).predict features = state.predict features := by
  simp only [NumericState.predict, NumericState.linearPrediction_eq_sumFrom]
  congr 1
  apply List.map_congr_left
  intro other member
  have different : other ≠ idx := fun same => absent (same ▸ member)
  rw [retireIndex_weight_other state idx other different]

/-- A retired learner predicts every input as the unretired one would with only
the retired slot's weight replaced by positive zero. -/
theorem retireIndex_prediction (state : NumericState config dimension) (idx : FeatIdx dimension)
    (features : ActiveSet dimension) :
    (state.retireIndex idx).predict features = Binary32.sumFrom .zero
      (features.indices.map fun other =>
        if other = idx then Binary32.zero else (state.weights.get other).value) := by
  simp only [NumericState.predict, NumericState.linearPrediction_eq_sumFrom]
  congr 1
  apply List.map_congr_left
  intro other _
  by_cases same : other = idx
  · subst same
    simp [(CurrentLearner.retire_registers state other).2.1]
  · simp [same, retireIndex_weight_other state idx other same]

/-- **Next TD error after a replacement.** The shared previous prediction is kept,
so a retired learner's next TD error is the unretired error formula with only the
retired slot's weight replaced by positive zero, for every input and reward. -/
theorem retire_step_error (state : NumericState config dimension) (idx : FeatIdx dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    ((state.retireIndex idx).step config features reward).2.error =
        (reward.add (config.rule.gamma.mul (Binary32.sumFrom .zero (features.indices.map
          fun other =>
            if other = idx then Binary32.zero else (state.weights.get other).value)))).sub
          state.transient.vOld ∧
      (state.step config features reward).2.error =
        (reward.add (config.rule.gamma.mul (Binary32.sumFrom .zero (features.indices.map
          fun other => (state.weights.get other).value)))).sub state.transient.vOld := by
  refine ⟨?_, ?_⟩
  · simp only [CurrentLearner.step_observation, retireIndex_prediction,
      (CurrentLearner.retire_registers state idx).2.2.2.1]
  · simp only [CurrentLearner.step_observation, NumericState.predict,
      NumericState.linearPrediction_eq_sumFrom]

/-- Without the retired slot in the input, the next TD error is unchanged bit for bit. -/
theorem retire_step_error_absent (state : NumericState config dimension) (idx : FeatIdx dimension)
    (features : ActiveSet dimension) (reward : Binary32) (absent : idx ∉ features.indices) :
    ((state.retireIndex idx).step config features reward).2.error =
      (state.step config features reward).2.error := by
  simp only [CurrentLearner.step_observation, retireIndex_predict state idx features absent,
    (CurrentLearner.retire_registers state idx).2.2.2.1]

/-- A controller replacement keeps its shared previous value and weight-change
aggregate, and each action value differs only through the retired slot's weight, so
the shared TD error `r + γ·q(a) − vOld` differs only through that weight. -/
theorem controller_retire_values {actions : Nat}
    (controller : Features.Controller config dimension actions) (idx : FeatIdx dimension)
    (features : ActiveSet dimension) :
    (controller.retire idx).vOld = controller.vOld ∧
      (controller.retire idx).vDelta = controller.vDelta ∧
      ∀ action : Fin actions, ((controller.retire idx).predictAll features)[action.val] =
        Binary32.sumFrom .zero (features.indices.map fun other =>
          if other = idx then Binary32.zero
          else (controller.learners[action.val].state.weights.get other).value) := by
  cases controller with
  | mk learners vOld vDelta restart =>
    refine ⟨rfl, rfl, ?_⟩
    intro action
    have same := retireIndex_prediction learners[action.val].state idx features
    simp only [NumericState.predict] at same
    simpa [Features.Controller.predictAll, Features.Controller.retire, Features.Managed.retire,
      Features.Managed.apply, Entry.apply] using same

variable {shape : Features.PatchShape} {features : Features.Config} {criterion : Features.Criterion}
  {discounts : List Discount}

/-- A replaced unit enters with the positive-zero outgoing weight in every reader. -/
theorem replace_zero (state : Features.Lifecycle shape features criterion dimension discounts)
    (unit : Fin features.units.count) :
    ∀ reader ∈ (state.replace unit).consumers.readers,
      (reader.2.state.weights.get (Features.unitFeature dimension features unit)).value =
        Binary32.zero := by
  intro reader member
  rw [state.replace_readers unit] at member
  obtain ⟨prior, _, same⟩ := List.mem_map.mp member
  subst same
  exact (CurrentLearner.retire_registers prior.2.state
    (Features.unitFeature dimension features unit)).2.1

/-- **Local safety.** Replacement leaves every reader's prediction unchanged, bit for
bit, on every input in which the replaced slot is inactive. -/
theorem replace_predictions
    (state : Features.Lifecycle shape features criterion dimension discounts)
    (unit : Fin features.units.count) (input : ActiveSet dimension)
    (absent : Features.unitFeature dimension features unit ∉ input.indices) :
    (state.replace unit).consumers.readers.map (fun reader => reader.2.state.predict input) =
      state.consumers.readers.map (fun reader => reader.2.state.predict input) := by
  rw [state.replace_readers unit, List.map_map]
  apply List.map_congr_left
  intro reader _
  exact retireIndex_predict reader.2.state _ input absent

/-- Every reader keeps its shared previous prediction and weight-change aggregate
across a replacement. -/
theorem replace_aggregates (state : Features.Lifecycle shape features criterion dimension discounts)
    (unit : Fin features.units.count) :
    (state.replace unit).consumers.readers.map
        (fun reader => (reader.2.state.transient.vOld, reader.2.state.transient.vDelta)) =
      state.consumers.readers.map
        (fun reader => (reader.2.state.transient.vOld, reader.2.state.transient.vDelta)) := by
  rw [state.replace_readers unit, List.map_map]
  apply List.map_congr_left
  intro reader _
  have kept := CurrentLearner.retire_registers reader.2.state
    (Features.unitFeature dimension features unit)
  simp only [Function.comp, Features.PackedLearner.retire, Features.Managed.retire,
    Features.Managed.apply, Entry.apply]
  rw [kept.2.2.2.1, kept.2.2.2.2]

/-- The new unit's term preserves the numerical value of every finite partial sum
in every reader: its outgoing weight contributes nothing to any prediction. -/
theorem replace_neutral (state : Features.Lifecycle shape features criterion dimension discounts)
    (unit : Fin features.units.count) (reader : Features.PackedLearner dimension)
    (member : reader ∈ (state.replace unit).consumers.readers)
    (partialSum : Binary32) (finite : partialSum.Finite) :
    (partialSum.add
      (reader.2.state.weights.get (Features.unitFeature dimension features unit)).value).Finite ∧
      numerical32 (partialSum.add
        (reader.2.state.weights.get (Features.unitFeature dimension features unit)).value) =
        numerical32 partialSum := by
  rw [replace_zero state unit reader member]
  exact add_zero_numeric partialSum finite

end AcornVerif.CurrentRetirement
