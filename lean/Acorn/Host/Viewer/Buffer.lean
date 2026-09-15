/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Bounded observer storage

The two overflow policies have different meanings: replay retains the newest
suffix, while a subscriber preserves queued order and refuses a new frame when
full. Both operations construct a bounded result on every write. Payload byte
admission belongs to the wire owner; a cardinality bound alone is not a byte
bound. These definitions make no scheduling or delivery guarantee.
-/
namespace Acorn.Host.Viewer

/-- A sequence whose capacity is part of its type at every admission and write. -/
structure Buffer (α : Type) (capacity : Nat) where
  /-- Retained values in delivery order. -/
  values : List α
  /-- Capacity is enforced on stored state, not just an observation. -/
  bounded : values.length ≤ capacity

/-- Empty storage is admitted for every capacity, including zero. -/
def Buffer.empty {α : Type} {capacity : Nat} : Buffer α capacity := ⟨[], by simp⟩

/-- Replay retains exactly the newest suffix that fits its immutable capacity. -/
def Buffer.retain {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    Buffer α capacity :=
  let values := buffer.values ++ [value]
  ⟨values.drop (values.length - capacity), by simp only [List.length_drop]; omega⟩

/-- A full subscriber refuses a new value without disturbing queued values. -/
def Buffer.offer {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    Option (Buffer α capacity) :=
  if h : buffer.values.length < capacity then
    some ⟨buffer.values ++ [value], by simp only [List.length_append, List.length_singleton]; omega⟩
  else none

/-- Pop preserves the order of every remaining value. -/
def Buffer.pop {α : Type} {capacity : Nat} (buffer : Buffer α capacity) :
    Option (α × Buffer α capacity) :=
  match h : buffer.values with
  | [] => none
  | value :: rest => some (value, ⟨rest, by have := buffer.bounded; simp [h] at this; omega⟩)

/-- The replay operation is an exact suffix, independently of capacity or payload. -/
theorem Buffer.retain_values {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    (buffer.retain value).values =
      (buffer.values ++ [value]).drop (buffer.values.length + 1 - capacity) := by
  simp [retain]

/-- Subscriber admission succeeds exactly while there is a free slot. -/
theorem Buffer.offer_iff {α : Type} {capacity : Nat} (buffer : Buffer α capacity) (value : α) :
    (buffer.offer value).isSome = true ↔ buffer.values.length < capacity := by
  simp [offer]

/-- Every successful admission appends exactly the supplied value. -/
theorem Buffer.offer_values {α : Type} {capacity : Nat} (buffer next : Buffer α capacity)
    (value : α) (accepted : buffer.offer value = some next) :
    next.values = buffer.values ++ [value] := by
  unfold offer at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

/-- Fixed replay capacity of the supported viewer protocol. -/
def replayCapacity : Nat := 500

/-- Fixed per-connection live backlog; fullness means explicit frame refusal. -/
def subscriberCapacity : Nat := 4096

end Acorn.Host.Viewer
