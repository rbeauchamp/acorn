import Init

namespace Acorn.Host.Viewer

structure Buffer (α : Type) (capacity : Nat) where
  values : List α
  bounded : values.length ≤ capacity

def Buffer.empty {α : Type} {capacity : Nat} : Buffer α capacity := ⟨[], by simp⟩

def Buffer.retain {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    Buffer α capacity :=
  let values := buffer.values ++ [value]
  ⟨values.drop (values.length - capacity), by simp only [List.length_drop]; omega⟩

def Buffer.offer {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    Option (Buffer α capacity) :=
  if h : buffer.values.length < capacity then
    some ⟨buffer.values ++ [value], by simp only [List.length_append, List.length_singleton]; omega⟩
  else none

def Buffer.pop {α : Type} {capacity : Nat} (buffer : Buffer α capacity) :
    Option (α × Buffer α capacity) :=
  match h : buffer.values with
  | [] => none
  | value :: rest => some (value, ⟨rest, by have := buffer.bounded; simp [h] at this; omega⟩)

theorem Buffer.retain_values {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    (buffer.retain value).values =
      (buffer.values ++ [value]).drop (buffer.values.length + 1 - capacity) := by
  simp [retain]

theorem Buffer.offer_iff {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    (buffer.offer value).isSome = true ↔ buffer.values.length < capacity := by
  simp [offer]

theorem Buffer.offer_values {α : Type} {capacity : Nat} (buffer next : Buffer α capacity)
    (value : α) (accepted : buffer.offer value = some next) :
    next.values = buffer.values ++ [value] := by
  unfold offer at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

def replayCapacity : Nat := 500

def subscriberCapacity : Nat := 4096

end Acorn.Host.Viewer
