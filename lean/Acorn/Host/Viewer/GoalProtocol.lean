/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Task

/-!
# Closed goal vocabulary

Emission, browser admission and item labels share these semantic domains.
Counts and coordinates keep their separate numeric wire limits.
-/
namespace Acorn.Host.Viewer

/-- Absence or one actual task family. -/
abbrev GoalKind := Option GoalFamily

/-- Absence, an inventory item, or a craftable; codes are never interval indices. -/
abbrev GoalItem := Option (Sum Item Craftable)

/-- Stable goal-family wire encoding. -/
def GoalKind.code : GoalKind → Nat
  | none => 0
  | some .reach => 1
  | some .collect => 2
  | some .craft => 3
  | some .survive => 4

/-- Stable item wire encoding comes from the host vocabulary. -/
def GoalItem.code : GoalItem → Nat
  | none => 0
  | some (.inl item) => item.code.toNat
  | some (.inr tool) => tool.code.toNat

/-- Complete goal-family vocabulary for the browser backend. -/
def goalKinds : List GoalKind := [none, some .reach, some .collect, some .craft, some .survive]

/-- Complete item vocabulary, including noncontiguous craftable codes. -/
def goalItems : List GoalItem :=
  [none, some (.inl .wood), some (.inl .stone), some (.inl .food), some (.inl .gold),
    some (.inr .axe), some (.inr .boat)]

/-- Every executable goal-family value is represented in browser admission. -/
theorem goalKinds_complete (kind : GoalKind) : kind ∈ goalKinds := by
  cases kind with
  | none => decide
  | some kind => cases kind <;> decide

/-- Every executable item value is represented in browser admission. -/
theorem goalItems_complete (item : GoalItem) : item ∈ goalItems := by
  cases item with
  | none => simp [goalItems]
  | some item => cases item with
    | inl item => cases item <;> simp [goalItems]
    | inr tool => cases tool <;> simp [goalItems]

/-- Every item label is covered by exhaustive matching over the host types. -/
def GoalItem.label : GoalItem → String
  | none => "—"
  | some (.inl .wood) => "Wood"
  | some (.inl .stone) => "Stone"
  | some (.inl .food) => "Food"
  | some (.inl .gold) => "Gold"
  | some (.inr .axe) => "Axe"
  | some (.inr .boat) => "Boat"

/-- Browser numeric goal-family domain is derived from the complete vocabulary. -/
def goalKindCodes : List Nat := goalKinds.map GoalKind.code

/-- Browser numeric item domain is derived from the complete vocabulary. -/
def goalItemCodes : List Nat := goalItems.map GoalItem.code

/-- Every emitted family code is admitted without a receiver-domain hypothesis. -/
theorem goalKind_admitted (kind : GoalKind) : kind.code ∈ goalKindCodes :=
  List.mem_map.mpr ⟨kind, goalKinds_complete kind, rfl⟩

/-- Every emitted item code is admitted without a receiver-domain hypothesis. -/
theorem goalItem_admitted (item : GoalItem) : item.code ∈ goalItemCodes :=
  List.mem_map.mpr ⟨item, goalItems_complete item, rfl⟩

/-- Decode the semantic family inventory used by browser admission. -/
def decodeGoalKind (code : Nat) : Option GoalKind :=
  goalKinds.find? (fun kind => kind.code == code)

/-- Goal-family meaning survives wire encoding for the complete domain. -/
theorem goalKind_roundtrip (kind : GoalKind) : decodeGoalKind kind.code = some kind := by
  cases kind with
  | none => rfl
  | some kind => cases kind <;> rfl

/-- Decode exactly the codes generated from the semantic item inventory. -/
def decodeGoalItem (code : Nat) : Option GoalItem :=
  goalItems.find? (fun item => item.code == code)

/-- Browser item lookup preserves the emitted meaning for every host item. -/
theorem goalItem_roundtrip (item : GoalItem) : decodeGoalItem item.code = some item := by
  cases item with
  | none => rfl
  | some item => cases item with
    | inl item => cases item <;> rfl
    | inr tool => cases tool <;> rfl

/-- Family codes are exact in the browser numeric representation. -/
theorem goalKind_safeInteger (kind : GoalKind) : kind.code < 2 ^ 53 := by
  cases kind with
  | none => decide
  | some kind => cases kind <;> decide

/-- Item codes remain exact through JSON parsing and JavaScript lookup. -/
theorem goalItem_safeInteger (item : GoalItem) : item.code < 2 ^ 53 := by
  cases item with
  | none => decide
  | some item => cases item with
    | inl item => cases item <;> decide
    | inr tool => cases tool <;> decide

end Acorn.Host.Viewer
