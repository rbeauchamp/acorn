import Acorn.Host.Task

namespace Acorn.Host.Viewer

abbrev GoalKind := Option GoalFamily

abbrev GoalItem := Option (Sum Item Craftable)

def GoalKind.code : GoalKind → Nat
  | none => 0
  | some .reach => 1
  | some .collect => 2
  | some .craft => 3
  | some .survive => 4

def GoalItem.code : GoalItem → Nat
  | none => 0
  | some (.inl item) => item.code.toNat
  | some (.inr tool) => tool.code.toNat

def goalKinds : List GoalKind := [none, some .reach, some .collect, some .craft, some .survive]

def goalItems : List GoalItem :=
  [none, some (.inl .wood), some (.inl .stone), some (.inl .food), some (.inl .gold),
    some (.inr .axe), some (.inr .boat)]

theorem goalKinds_complete (kind : GoalKind) : kind ∈ goalKinds := by
  cases kind with
  | none => decide
  | some kind => cases kind <;> decide

theorem goalItems_complete (item : GoalItem) : item ∈ goalItems := by
  cases item with
  | none => simp [goalItems]
  | some item => cases item with
    | inl item => cases item <;> simp [goalItems]
    | inr tool => cases tool <;> simp [goalItems]

def GoalItem.labels : GoalItem → String × String
  | none => ("—", "—")
  | some (.inl .wood) => ("Wood", "Wood")
  | some (.inl .stone) => ("Stone", "Stones")
  | some (.inl .food) => ("Food", "Food")
  | some (.inl .gold) => ("Gold", "Gold")
  | some (.inr .axe) => ("Axe", "Axes")
  | some (.inr .boat) => ("Boat", "Boats")

def goalKindCodes : List Nat := goalKinds.map GoalKind.code

def goalItemCodes : List Nat := goalItems.map GoalItem.code

theorem goalKind_admitted (kind : GoalKind) : kind.code ∈ goalKindCodes :=
  List.mem_map.mpr ⟨kind, goalKinds_complete kind, rfl⟩

theorem goalItem_admitted (item : GoalItem) : item.code ∈ goalItemCodes :=
  List.mem_map.mpr ⟨item, goalItems_complete item, rfl⟩

def decodeGoalKind (code : Nat) : Option GoalKind :=
  goalKinds.find? (fun kind => kind.code == code)

theorem goalKind_roundtrip (kind : GoalKind) : decodeGoalKind kind.code = some kind := by
  cases kind with
  | none => rfl
  | some kind => cases kind <;> rfl

def decodeGoalItem (code : Nat) : Option GoalItem :=
  goalItems.find? (fun item => item.code == code)

theorem goalItem_roundtrip (item : GoalItem) : decodeGoalItem item.code = some item := by
  cases item with
  | none => rfl
  | some item => cases item with
    | inl item => cases item <;> rfl
    | inr tool => cases tool <;> rfl

theorem goalKind_safeInteger (kind : GoalKind) : kind.code < 2 ^ 53 := by
  cases kind with
  | none => decide
  | some kind => cases kind <;> decide

theorem goalItem_safeInteger (item : GoalItem) : item.code < 2 ^ 53 := by
  cases item with
  | none => decide
  | some item => cases item with
    | inl item => cases item <;> decide
    | inr tool => cases tool <;> decide

end Acorn.Host.Viewer
