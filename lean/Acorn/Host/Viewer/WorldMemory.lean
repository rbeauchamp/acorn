/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Lifecycle

/-!
# Run-owned sensed world

The map key is run/seed/side, independently of agent epoch. Every tile is either
unseen or one of the closed eight terrain kinds. A bounded packed byte array owns storage;
the seen count is derived from its cells, avoiding a second mutable fact.
Completeness is a separate claim and becomes partial across unobserved tails.
-/
namespace Acorn.Host.Viewer

/-- Largest server-retained world side under the current viewer contract. -/
def mapSideCapacity : Nat := 4096

/-- Side admission precedes map allocation. -/
abbrev MapSide := {side : Nat // 0 < side ∧ side ≤ mapSideCapacity}

/-- The same durable world can contain several logical agent epochs. -/
structure MapKey where
  /-- Durable world-run identifier. -/
  run : UInt64
  /-- Seed used to generate the world. -/
  seed : UInt64
  /-- Admitted side fixes the retained vector's exact shape. -/
  side : MapSide
  deriving DecidableEq

/-- Every stored cell is either unknown or a member of the complete terrain-kind domain. -/
abbrev MapCell := Option (Fin 8)

/-- No reader can manufacture a numeric kind for a tile the stream never supplied. -/
def MapCell.byte : MapCell → UInt8
  | none => 255
  | some kind => kind.val.toUInt8

/-- Disk/wire cell admission refuses codes outside the terrain domain and unseen marker. -/
def MapCell.admit (byte : UInt8) : Option MapCell :=
  if byte == 255 then some none
  else if h : byte.toNat < 8 then some (some ⟨byte.toNat, h⟩) else none

/-- Packed cells have both the exact world shape and the closed terrain-byte invariant. -/
structure MapBytes (key : MapKey) where
  /-- One physical payload byte per cell. -/
  bytes : ByteArray
  /-- Shape is checked before retaining the payload. -/
  size : bytes.size = key.side.val * key.side.val
  /-- Every byte is a terrain kind or the unseen marker. -/
  legal : ∀ (index : Nat) (bound : index < bytes.size),
    bytes[index].toNat < 8 ∨ bytes[index] = 255

private def admitMapPrefix (bytes : ByteArray) (start : Nat)
    (admitted : ∀ (index : Nat), index < start → ∀ (bound : index < bytes.size),
      bytes[index].toNat < 8 ∨ bytes[index] = 255) :
    Except String {_value : Unit // ∀ (index : Nat) (bound : index < bytes.size),
      bytes[index].toNat < 8 ∨ bytes[index] = 255} :=
  if bound : start < bytes.size then
    if legal : bytes[start].toNat < 8 ∨ bytes[start] = 255 then
      admitMapPrefix bytes (start + 1) (by
        intro index upper inside
        by_cases same : index = start
        · subst index; exact legal
        · exact admitted index (by omega) inside)
    else .error "invalid retained terrain byte"
  else .ok ⟨(), by intro index inside; exact admitted index (by omega) inside⟩
termination_by bytes.size - start

/-- Every byte is checked once by the proof-bearing admission loop, without a boxed cell array. -/
def MapBytes.admit (key : MapKey) (bytes : ByteArray) : Except String (MapBytes key) := do
  if shape : bytes.size = key.side.val * key.side.val then
    let legal ← admitMapPrefix bytes 0 (by intro index lower; omega)
    return ⟨bytes, shape, legal.property⟩
  else throw "retained map has the wrong cell count"

/-- Retained state is bound to one exact map shape and durable world identity. -/
structure WorldMemory (key : MapKey) where
  private mk ::
  /-- Packed row-major sensed kinds. -/
  private cells : MapBytes key
  /-- Missing observations are a persistent visible limitation. -/
  private incomplete : Bool := false
  /-- Nonwrapping local mutation identity, changed only by actual cell/marker writes. -/
  private changes : Nat := 0

/-- A new world's map contains no invented observations. -/
def WorldMemory.empty (key : MapKey) : WorldMemory key :=
  ⟨⟨⟨Array.replicate (key.side.val * key.side.val) 255⟩,
    by change (Array.replicate _ (255 : UInt8)).size = _; simp,
    by
      intro index bound
      right
      change (Array.replicate (key.side.val * key.side.val) (255 : UInt8))[index] = 255
      simp⟩, false, 0⟩

/-- Read-only cell snapshot, with no completeness-state write capability. -/
def WorldMemory.observations {key : MapKey} (memory : WorldMemory key) : MapBytes key := memory.cells

/-- Read-only incompleteness indicator for persistence and presentation. -/
def WorldMemory.isIncomplete {key : MapKey} (memory : WorldMemory key) : Bool := memory.incomplete

/-- Read-only revision avoids rescanning the whole world on each sensor window. -/
def WorldMemory.changeCount {key : MapKey} (memory : WorldMemory key) : Nat := memory.changes

/-- A restored map is always partial: unwritten observations may be absent. -/
def WorldMemory.restore (key : MapKey) (cells : MapBytes key) : WorldMemory key := ⟨cells, true, 0⟩

/-- Every write uses an index proved to belong to this map and preserves packed-byte legality. -/
def WorldMemory.paint {key : MapKey} (memory : WorldMemory key)
    (index : Fin (key.side.val * key.side.val)) (kind : Fin 8) : WorldMemory key :=
  let byte := UInt8.ofNatLT kind.val (by have := kind.isLt; change kind.val < 256; omega)
  have indexBound : index.val < memory.cells.bytes.size := by rw [memory.cells.size]; exact index.isLt
  if memory.cells.bytes[index.val] = byte then memory else
  let cells : MapBytes key :=
    ⟨memory.cells.bytes.set! index.val byte,
      by simpa using memory.cells.size,
      by
        intro other bound
        have original : other < memory.cells.bytes.size := by simpa using bound
        have indexBound : index.val < memory.cells.bytes.size := by rw [memory.cells.size]; exact index.isLt
        rw [ByteArray.getElem_set! _ _ _ _ indexBound original]
        split
        · left; simp [byte]
        · exact memory.cells.legal other original⟩
  { memory with cells, changes := memory.changes + 1 }

/-- Known cell count is derived from the packed payload, never updated independently. -/
def WorldMemory.seen {key : MapKey} (memory : WorldMemory key) : Nat :=
  memory.cells.bytes.data.toList.countP (· != 255)

/-- Publication of a partial snapshot never erases its known cells. -/
def WorldMemory.markPartial {key : MapKey} (memory : WorldMemory key) : WorldMemory key :=
  { memory with incomplete := true, changes := memory.changes + if memory.incomplete then 0 else 1 }

/-- Source window coordinates are clipped before constructing a map index. -/
def mapIndex (side : MapSide) (x y : Int) : Option (Fin (side.val * side.val)) :=
  if bounds : 0 ≤ x ∧ x < side.val ∧ 0 ≤ y ∧ y < side.val then
    have hx : x.toNat < side.val := by omega
    have hy : y.toNat < side.val := by omega
    have indexBound : y.toNat * side.val + x.toNat < side.val * side.val := by
      calc
        y.toNat * side.val + x.toNat < y.toNat * side.val + side.val := Nat.add_lt_add_left hx _
        _ = (y.toNat + 1) * side.val := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ side.val * side.val := Nat.mul_le_mul_right side.val (by omega)
    some ⟨y.toNat * side.val + x.toNat, indexBound⟩
  else none

/-- An entire typed 11-by-11 sensor window paints only in-world cells. -/
def WorldMemory.absorb {key : MapKey} (memory : WorldMemory key)
    (x y : Fin key.side.val) (tiles : Vector (Fin 8) 121) : WorldMemory key := Id.run do
  let mut memory := memory
  for index in [:121] do
    if h : index < 121 then
      let wx : Int := x.val + (index % 11 : Nat) - 5
      let wy : Int := y.val + (index / 11 : Nat) - 5
      if let some indexInMap := mapIndex key.side wx wy then
        memory := memory.paint indexInMap (tiles.get ⟨index, h⟩)
  return memory

/-- A known-cell count cannot exceed the receiver's exact map allocation. -/
theorem WorldMemory.seen_bound {key : MapKey} (memory : WorldMemory key) :
    memory.seen ≤ key.side.val * key.side.val := by
  have h := List.countP_le_length (p := (· != 255)) (l := memory.cells.bytes.data.toList)
  have size := memory.cells.size
  simpa [seen, ← size] using h

/-- Incompleteness never changes the world observations already retained. -/
theorem WorldMemory.partial_preserves {key : MapKey} (memory : WorldMemory key) :
    memory.markPartial.cells = memory.cells := rfl

/-- Reusing a paint revision universally means that no cell changed. -/
theorem WorldMemory.paint_same_revision {key : MapKey} (memory : WorldMemory key)
    (index : Fin (key.side.val * key.side.val)) (kind : Fin 8)
    (unchanged : (memory.paint index kind).changeCount = memory.changeCount) :
    (memory.paint index kind).observations = memory.observations := by
  unfold paint at unchanged ⊢
  dsimp only at unchanged ⊢
  split at unchanged <;> simp_all [changeCount, observations]

/-- A repeated partial marker does not manufacture another mutation. -/
theorem WorldMemory.partial_idempotent {key : MapKey} (memory : WorldMemory key) :
    memory.markPartial.markPartial = memory.markPartial := by
  simp [markPartial]

/-- The total logical cell count has the fixed server-side upper bound. -/
theorem MapKey.cell_bound (key : MapKey) :
    key.side.val * key.side.val ≤ mapSideCapacity * mapSideCapacity :=
  Nat.mul_le_mul key.side.property.2 key.side.property.2

end Acorn.Host.Viewer
