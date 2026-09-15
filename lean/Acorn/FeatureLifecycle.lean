/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConsumers
import Acorn.FeatureHistory

/-!
# Receiver-owned feature retirement

The scan, reset, generator and transcript belong to one immutable receiver.
No caller-supplied learner list or slot can authorize a replacement. Slot aliases
are intentional: all consumers of the hashed slot reset together. Task targets
and temporal prediction caches have separate lifetimes from feature storage.
-/
namespace Acorn.Features

/-- Current representation and every learned slot consumer share one owner. -/
structure Lifecycle (shape : PatchShape) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) where
  /-- Projection bank with reconstructible generator history. -/
  representation : Representation shape config
  /-- Complete receiving learner storage. -/
  consumers : Ensemble config criterion dimension discounts

/-- Scan in bank order, so the first wholly negligible slot owns this step. -/
def Lifecycle.candidate {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) : Option (Fin config.units.count) :=
  (List.finRange config.units.count).find? (fun unit =>
    state.consumers.negligible (unitFeature dimension config unit))

/-- A selected candidate has a canonical earlier prefix whose every slot
fails the same complete receiver predicate. This states first-match ordering. -/
theorem Lifecycle.candidate_first {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) (unit : Fin config.units.count)
    (selected : state.candidate = some unit) :
    state.consumers.negligible (unitFeature dimension config unit) = true ∧
      ∃ earlier later, List.finRange config.units.count = earlier ++ unit :: later ∧
        ∀ prior ∈ earlier, state.consumers.negligible (unitFeature dimension config prior) = false := by
  simpa [Lifecycle.candidate] using (List.find?_eq_some_iff_append.mp selected)

/-- Successful replacement is a transaction on the same receiver that admitted it.
The premises are erased and cannot be reused on another state. -/
def Lifecycle.replace {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts)
    (unit : Fin config.units.count) (room : state.representation.progress.CanRecord)
    (_eligible : state.consumers.negligible (unitFeature dimension config unit) = true) :
    Lifecycle shape config criterion dimension discounts :=
  ⟨state.representation.replace unit room,
    state.consumers.retire (unitFeature dimension config unit)⟩

/-- A successful result names the exact selected unit; refusal is atomic. -/
def Lifecycle.tryRetire {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) :
    Option (Fin config.units.count × Lifecycle shape config criterion dimension discounts) :=
  if room : state.representation.progress.CanRecord then
    match found : state.candidate with
    | none => none
    | some unit =>
      some (unit, state.replace unit room (by
        exact List.find?_some (p := fun candidate =>
          state.consumers.negligible (unitFeature dimension config candidate)) found))
  else none

/-- Ordinary advancement remains available after retirement capacity is exhausted. -/
def Lifecycle.advance {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) :
    Lifecycle shape config criterion dimension discounts :=
  { state with representation := state.representation.advance }

/-- Every successful transaction resets exactly every reader of its selected slot. -/
theorem Lifecycle.replace_readers {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts)
    (unit : Fin config.units.count) (room : state.representation.progress.CanRecord)
    (eligible : state.consumers.negligible (unitFeature dimension config unit) = true) :
    (state.replace unit room eligible).consumers.readers =
      state.consumers.readers.map (PackedLearner.retire (unitFeature dimension config unit)) :=
  Ensemble.retire_readers _ _

/-- No transcript room means no partial reset or generator consumption. -/
theorem Lifecycle.capacity_refuses {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts)
    (full : ¬state.representation.progress.CanRecord) : state.tryRetire = none := by
  simp [Lifecycle.tryRetire, full]

/-- Success is possible exactly with transcript room and the selected first candidate. -/
theorem Lifecycle.success_iff {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts)
    (unit : Fin config.units.count) (next : Lifecycle shape config criterion dimension discounts) :
    state.tryRetire = some (unit, next) ↔
      ∃ (room : state.representation.progress.CanRecord)
        (eligible : state.consumers.negligible (unitFeature dimension config unit) = true),
        state.candidate = some unit ∧ next = state.replace unit room eligible := by
  unfold Lifecycle.tryRetire
  split
  · rename_i room
    split
    · simp_all
    · rename_i selected found
      constructor
      · intro same
        cases same
        exact ⟨room, _, found, rfl⟩
      · rintro ⟨_, eligible, candidate, rfl⟩
        have same : selected = unit := Option.some.inj (found.symm.trans candidate)
        subst selected
        rfl
  · simp_all

/-- Refusal has precisely two causes; no incomplete transaction is returned. -/
theorem Lifecycle.refusal_iff {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) :
    state.tryRetire = none ↔
      ¬state.representation.progress.CanRecord ∨ state.candidate = none := by
  unfold Lifecycle.tryRetire
  split <;> simp_all
  split <;> simp_all

/-- Eligibility is a universal conjunction over the receiving storage. -/
theorem Ensemble.negligible_iff {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (consumers : Ensemble config criterion dimension discounts) (feature : FeatIdx dimension) :
    consumers.negligible feature = true ↔
      ∀ learner ∈ consumers.readers, learner.negligible feature = true := by
  simp [Ensemble.negligible]

end Acorn.Features
