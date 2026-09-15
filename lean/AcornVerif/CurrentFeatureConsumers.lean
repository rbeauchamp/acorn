/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureLifecycle
import AcornVerif.CurrentLearner

/-! # Executing consumer reset contracts

The admission invariant connects the lifecycle's actual learners to the current
learner's universal scheduling proof. No independently written update model is
assumed equivalent. Numeric primitives retain the learner's declared trust.
-/
namespace AcornVerif.CurrentFeatureConsumers
open Acorn Acorn.Features AcornVerif.CurrentLearner

/-- Every consumer's erased admission establishes the owning scheduling invariant. -/
theorem managed_schedule {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) : ScheduleInv learner.state learner.phase := by
  rcases learner with ⟨state, phase, admitted⟩
  induction admitted with
  | initial => exact ⟨initial_core, initial_ready.1, fun _ => initial_ready⟩
  | transition entry permitted _ ih => exact entry_schedule entry _ _ permitted ih

/-- Retiring from a unique eligibility array removes every occurrence of the slot. -/
theorem retire_absent {config : Acorn.Config} {dimension : Dimension}
    (state : NumericState config dimension) (feature : FeatIdx dimension)
    (unique : state.transient.eligible.toList.Nodup) :
    feature ∉ (state.retireIndex feature).transient.eligible := by
  unfold NumericState.retireIndex
  split
  · rename_i pos found
    obtain ⟨valid, same, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have equality : state.transient.eligible[pos] = feature := by simpa using same
    have removed := swap_remove_absent state.transient.eligible pos valid unique
    rw [equality] at removed
    exact removed
  · rename_i found
    intro member
    have absent := Array.findIdx?_eq_none_iff.mp found feature member
    simp at absent

/-- All phase-disciplined consumers remove the retired slot completely. -/
theorem managed_retire_absent {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (feature : FeatIdx dimension) :
    feature ∉ (learner.retire feature).state.transient.eligible :=
  retire_absent learner.state feature (managed_schedule learner).2.1

/-- The complete ensemble reset clears all register/knowledge words at every reader. -/
theorem ensemble_reset {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble config criterion dimension discounts) (feature : FeatIdx dimension)
    (reader : PackedLearner dimension) (member : reader ∈ (ensemble.retire feature).readers) :
    registers reader.2.state feature = Vector.replicate 9 Binary32.zero ∧
    (reader.2.state.weights.get feature).value = Binary32.zero ∧
    (reader.2.state.beta.get feature).value = reader.2.state.rails.initial.value ∧
    reader.2.state.transient.vOld = Binary32.zero ∧
    reader.2.state.transient.vDelta = Binary32.zero ∧
    feature ∉ reader.2.state.transient.eligible := by
  rw [Ensemble.retire_readers] at member
  obtain ⟨before, _, same⟩ := List.mem_map.mp member
  subst reader
  have cleared := retire_registers before.2.state feature
  have rails : (before.2.state.retireIndex feature).rails = before.2.state.rails := by
    unfold NumericState.retireIndex
    split <;> simp only [NumericState.writeBetaValue, NumericState.writeWeight,
      NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
      NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
      NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
      NumericState.writeLastAlpha, NumericState.removeEligibleAt]
  exact ⟨cleared.1, cleared.2.1,
    cleared.2.2.1.trans (congrArg (fun r : StepSizeRails before.1 => r.initial.value) rails.symm),
    cleared.2.2.2.1,
    cleared.2.2.2.2, managed_retire_absent before.2 feature⟩

/-- Eligibility storage and a complete reset scan are bounded for every managed
reader. The scheduler premise is carried by admission, not supplied by callers. -/
theorem managed_capacity {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) : learner.state.eligibleCount ≤ dimension.capacity :=
  eligible_cardinality learner.state (managed_schedule learner).2.1

/-- Summed eligibility work is bounded by the actual derived reader count.
Discounted model aliases overcount work safely; they do not omit stored learners. -/
theorem readers_capacity {dimension : Dimension} (readers : List (PackedLearner dimension)) :
    (readers.map (fun reader => reader.2.state.eligibleCount)).sum ≤
      readers.length * dimension.capacity := by
  induction readers with
  | nil => simp
  | cons reader rest ih =>
    have bound := managed_capacity reader.2
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The all-consumer scan and reset have a lifetime-independent eligibility bound. -/
theorem ensemble_capacity {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble config criterion dimension discounts) :
    (ensemble.readers.map (fun reader => reader.2.state.eligibleCount)).sum ≤
      (Acorn.FeatureConstants.primitiveCount + Acorn.FeatureConstants.metaActionCount +
        Acorn.FeatureConstants.skillCount * (Acorn.FeatureConstants.primitiveCount + 3) +
        discounts.length) *
        dimension.capacity := by
  have bound := readers_capacity ensemble.readers
  rw [Ensemble.reader_count] at bound
  exact bound

end AcornVerif.CurrentFeatureConsumers
