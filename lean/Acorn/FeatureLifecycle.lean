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
No caller-supplied learner list or slot can authorize a replacement; the caller
supplies only whether it is at a free boundary. A unit that some slot holds as its
objective is eligible only there, so no live option loses its objective. Slot aliases
are intentional: all consumers of the hashed slot reset together. Task targets
and temporal prediction caches have separate lifetimes from feature storage; the
runtime retirement releases every task target naming the replaced unit.
-/
namespace Acorn.Features

/-- Current representation and every learned slot consumer share one owner. -/
structure Lifecycle (shape : PatchShape) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) where
  /-- Projection bank with reconstructible generator history. -/
  representation : Representation shape config
  /-- Complete receiving learner storage. -/
  consumers : Ensemble config criterion dimension discounts

/-- Whether some slot holds the unit as its learned objective. -/
def Ensemble.holds {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (unit : Fin config.units.count) : Bool :=
  ensemble.skills.toList.any (·.interest.held.holds unit)

/-- Feature retirement keeps every objective, so it keeps every held unit. -/
theorem Ensemble.retire_holds {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (feature : FeatIdx dimension) (unit : Fin config.units.count) :
    (ensemble.retire feature).holds unit = ensemble.holds unit := by
  simp [Ensemble.holds, Ensemble.retire, Skill.retire]

/-- A wholly negligible unit is eligible at a free boundary; elsewhere only while no
slot holds it as its objective. -/
def Lifecycle.eligible {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) (free : Bool)
    (unit : Fin config.units.count) : Bool :=
  state.consumers.negligible (unitFeature dimension config unit) &&
    (free || !state.consumers.holds unit)

/-- Scan in bank order, so the first eligible slot owns this step. -/
def Lifecycle.candidate {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) (free : Bool) :
    Option (Fin config.units.count) :=
  (List.finRange config.units.count).find? (state.eligible free)

/-- A selected candidate has a canonical earlier prefix whose every slot
fails the same complete receiver predicate. This states first-match ordering. -/
theorem Lifecycle.candidate_first {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) (free : Bool)
    (unit : Fin config.units.count) (selected : state.candidate free = some unit) :
    state.eligible free unit = true ∧
      ∃ earlier later, List.finRange config.units.count = earlier ++ unit :: later ∧
        ∀ prior ∈ earlier, state.eligible free prior = false := by
  simpa [Lifecycle.candidate] using (List.find?_eq_some_iff_append.mp selected)

/-- Away from a free boundary the selected candidate is held by no slot. -/
theorem Lifecycle.candidate_unheld {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts)
    (unit : Fin config.units.count) (selected : state.candidate false = some unit) :
    state.consumers.holds unit = false := by
  have eligible := (state.candidate_first false unit selected).1
  simp only [Lifecycle.eligible, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at eligible
  exact eligible.2

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
    (state : Lifecycle shape config criterion dimension discounts) (free : Bool) :
    Option (Fin config.units.count × Lifecycle shape config criterion dimension discounts) :=
  if room : state.representation.progress.CanRecord then
    match found : state.candidate free with
    | none => none
    | some unit =>
      some (unit, state.replace unit room (by
        have eligible := List.find?_some (p := state.eligible free) found
        simp only [Lifecycle.eligible, Bool.and_eq_true] at eligible
        exact eligible.1))
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
    (state : Lifecycle shape config criterion dimension discounts) (free : Bool)
    (full : ¬state.representation.progress.CanRecord) : state.tryRetire free = none := by
  simp [Lifecycle.tryRetire, full]

/-- Success is possible exactly with transcript room and the selected first candidate. -/
theorem Lifecycle.success_iff {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Lifecycle shape config criterion dimension discounts) (free : Bool)
    (unit : Fin config.units.count) (next : Lifecycle shape config criterion dimension discounts) :
    state.tryRetire free = some (unit, next) ↔
      ∃ (room : state.representation.progress.CanRecord)
        (eligible : state.consumers.negligible (unitFeature dimension config unit) = true),
        state.candidate free = some unit ∧ next = state.replace unit room eligible := by
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
    (state : Lifecycle shape config criterion dimension discounts) (free : Bool) :
    state.tryRetire free = none ↔
      ¬state.representation.progress.CanRecord ∨ state.candidate free = none := by
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
