/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Encoding

/-!
# Compositional binary codecs

A codec consumes exactly its own encoding in front of every suffix. Products,
fixed vectors and refinements derive their writer/parser relationship from this
law. Words use little-endian base-256 digits, without native reinterpret casts.
-/
namespace Acorn.Checkpoint

/-- A total prefix parser and its writer, with the actual round-trip law. -/
structure Codec (α : Type) where
  /-- Canonical bytes in file order. -/
  encode : α → List UInt8
  /-- Consume one value, retaining the unconsumed suffix. -/
  decode : List UInt8 → Option (α × List UInt8)
  /-- Encoding consumes neither less nor more than its own bytes. -/
  roundtrip : ∀ value suffix, decode (encode value ++ suffix) = some (value, suffix)

/-- Pair fields have one shared ordered description. -/
def Codec.pair {α β : Type} (left : Codec α) (right : Codec β) : Codec (α × β) where
  encode value := left.encode value.1 ++ right.encode value.2
  decode bytes := do
    let (first, rest) ← left.decode bytes
    let (second, rest) ← right.decode rest
    some ((first, second), rest)
  roundtrip := by
    intro value suffix
    simp [List.append_assoc, left.roundtrip, right.roundtrip]

/-- Change representation through a checked inverse, with no second parser walk. -/
def Codec.iso {α β : Type} (codec : Codec α) (pack : α → β) (unpack : β → α)
    (inverse : ∀ value, pack (unpack value) = value) : Codec β where
  encode value := codec.encode (unpack value)
  decode bytes := do
    let (value, rest) ← codec.decode bytes
    some (pack value, rest)
  roundtrip := by intro value suffix; simp [codec.roundtrip, inverse]

/-- Admission checks the actual decoded value before constructing a refinement. -/
def Codec.refine {α : Type} (codec : Codec α) (legal : α → Prop)
    [DecidablePred legal] : Codec { value : α // legal value } where
  encode value := codec.encode value.val
  decode bytes := do
    let (value, rest) ← codec.decode bytes
    if h : legal value then some (⟨value, h⟩, rest) else none
  roundtrip := by intro value suffix; simp [codec.roundtrip, value.property]

/-- No bytes are needed for the unique unit value. -/
def unitCodec : Codec Unit where
  encode _ := []
  decode bytes := some ((), bytes)
  roundtrip := by intro value suffix; cases value; rfl

/-- One byte, refused on an empty input. -/
def byteCodec : Codec UInt8 where
  encode value := [value]
  decode
    | [] => none
    | head :: rest => some (head, rest)
  roundtrip := by intro value suffix; rfl

/-- Tail-recursive element decoding uses one accumulator, never one stack frame per element. -/
def decodeListInto {α : Type} (codec : Codec α) :
    Nat → List UInt8 → List α → Option (List α × List UInt8)
  | 0, bytes, reversed => some (reversed.reverse, bytes)
  | count + 1, bytes, reversed => do
    let (value, rest) ← codec.decode bytes
    decodeListInto codec count rest (value :: reversed)

/-- Read a fixed number of elements; the count comes from the receiving schema. -/
def decodeList {α : Type} (codec : Codec α) (count : Nat) (bytes : List UInt8) :
    Option (List α × List UInt8) := decodeListInto codec count bytes []

/-- List induction composes arbitrary element round trips through the executing accumulator. -/
theorem list_into_roundtrip {α : Type} (codec : Codec α) (values : List α)
    (suffix : List UInt8) (reversed : List α) :
    decodeListInto codec values.length (values.flatMap codec.encode ++ suffix) reversed =
      some (reversed.reverse ++ values, suffix) := by
  induction values generalizing reversed with
  | nil => simp [decodeListInto]
  | cons value values ih =>
    simp [decodeListInto, List.append_assoc, codec.roundtrip, ih]

/-- The whole fixed-count element sequence round-trips without a second evaluator. -/
theorem list_roundtrip {α : Type} (codec : Codec α) (values : List α) (suffix : List UInt8) :
    decodeList codec values.length (values.flatMap codec.encode ++ suffix) = some (values, suffix) := by
  simpa [decodeList] using list_into_roundtrip codec values suffix []

/-- Each successful read adds exactly its requested count to the accumulator. -/
theorem decodeListInto_length {α : Type} (codec : Codec α) (count : Nat)
    (bytes : List UInt8) (reversed values : List α) (rest : List UInt8)
    (decoded : decodeListInto codec count bytes reversed = some (values, rest)) :
    values.length = reversed.length + count := by
  induction count generalizing bytes reversed with
  | zero =>
    simp only [decodeListInto, Option.some.injEq, Prod.mk.injEq] at decoded
    rw [← decoded.1]
    simp
  | succ count ih =>
    simp only [decodeListInto] at decoded
    cases firstEq : codec.decode bytes with
    | none => simp [firstEq] at decoded
    | some first =>
      simp only [firstEq, bind, Option.bind] at decoded
      have length := ih first.2 (first.1 :: reversed) decoded
      simp only [List.length_cons] at length
      omega

/-- Successful fixed-count reads contain exactly the requested number of values. -/
theorem decodeList_length {α : Type} (codec : Codec α) (count : Nat) (bytes : List UInt8)
    (values : List α) (rest : List UInt8)
    (decoded : decodeList codec count bytes = some (values, rest)) : values.length = count := by
  simpa using decodeListInto_length codec count bytes [] values rest decoded

/-- Fixed-length sequences have no untrusted allocation count. -/
def vectorCodec {α : Type} (codec : Codec α) (count : Nat) : Codec (Vector α count) where
  encode values := values.toList.flatMap codec.encode
  decode bytes :=
    match h : decodeList codec count bytes with
    | none => none
    | some (values, rest) => some (⟨values.toArray, by simpa using decodeList_length codec count bytes values rest h⟩, rest)
  roundtrip := by
    intro values suffix
    have h := list_roundtrip codec values.toList suffix
    simp only [Vector.length_toList] at h
    split <;> rename_i result
    · rw [h] at result; contradiction
    · rw [h] at result
      cases result
      cases values
      simp [Vector.toList]

/-- Low byte first; the arithmetic definition applies to every natural word. -/
def encodeNat : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat value :: encodeNat width (value / 256)

/-- Read the same number of base-256 digits; truncated words are refused. -/
def decodeNat : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bytes => some (0, bytes)
  | width + 1, bytes => do
    let (digit, rest) ← byteCodec.decode bytes
    let (high, rest) ← decodeNat width rest
    some (digit.toNat + 256 * high, rest)

/-- Positional arithmetic proves round-trip without enumerating word values. -/
theorem nat_roundtrip (width value : Nat) (bound : value < 256 ^ width) (suffix : List UInt8) :
    decodeNat width (encodeNat width value ++ suffix) = some (value, suffix) := by
  induction width generalizing value with
  | zero =>
    have : value = 0 := by simpa using bound
    subst value
    rfl
  | succ width ih =>
    have high : value / 256 < 256 ^ width := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ, Nat.mul_comm] using bound
    simp only [encodeNat, List.cons_append, decodeNat, byteCodec, bind, Option.bind]
    rw [ih _ high]
    change some (value % 256 + 256 * (value / 256), suffix) = some (value, suffix)
    rw [Nat.mod_add_div]

/-- Every decoded positional word fits exactly its declared byte width. -/
theorem decodeNat_bound (width : Nat) (bytes : List UInt8) (value : Nat) (rest : List UInt8)
    (decoded : decodeNat width bytes = some (value, rest)) : value < 256 ^ width := by
  induction width generalizing bytes value rest with
  | zero => simp only [decodeNat, Option.some.injEq, Prod.mk.injEq] at decoded; simp [← decoded.1]
  | succ width ih =>
    cases bytes with
    | nil => simp [decodeNat, byteCodec] at decoded
    | cons digit bytes =>
      simp only [decodeNat, byteCodec, bind, Option.bind] at decoded
      cases highEq : decodeNat width bytes with
      | none => simp [highEq] at decoded
      | some high =>
        simp only [highEq, Option.some.injEq, Prod.mk.injEq] at decoded
        have h := ih bytes high.1 high.2 highEq
        have d := digit.toNat_lt
        rw [Nat.pow_succ]
        omega

/-- Fixed-width natural words carry their width bound in the value. -/
def wordCodec (width : Nat) : Codec (Fin (256 ^ width)) where
  encode value := encodeNat width value.val
  decode bytes := do
    match h : decodeNat width bytes with
    | none => none
    | some (value, rest) => some (⟨value, decodeNat_bound width bytes value rest h⟩, rest)
  roundtrip := by
    intro value suffix
    split <;> rename_i result
    · rw [nat_roundtrip width value.val value.isLt suffix] at result; contradiction
    · rw [nat_roundtrip width value.val value.isLt suffix] at result
      cases result
      rfl

/-- Two-byte machine word, least significant byte first. -/
def u16Codec : Codec UInt16 :=
  (wordCodec 2).iso (fun value => UInt16.ofNat value.val)
    (fun value => ⟨value.toNat, value.toNat_lt⟩) (by intro value; simp)

/-- Four-byte machine word, least significant byte first. -/
def u32Codec : Codec UInt32 :=
  (wordCodec 4).iso (fun value => UInt32.ofNat value.val)
    (fun value => ⟨value.toNat, value.toNat_lt⟩) (by intro value; simp)

/-- Eight-byte machine word, least significant byte first. -/
def u64Codec : Codec UInt64 :=
  (wordCodec 8).iso (fun value => UInt64.ofNat value.val)
    (fun value => ⟨value.toNat, value.toNat_lt⟩) (by intro value; simp)

/-- Floating values serialize their stored bits, including signed zero. -/
def binary32Codec : Codec Binary32 :=
  u32Codec.iso Binary32.mk Binary32.bits (by intro value; rfl)

/-- Wide totals serialize their stored bits without numeric conversion. -/
def binary64Codec : Codec Binary64 :=
  u64Codec.iso Binary64.mk Binary64.bits (by intro value; rfl)

end Acorn.Checkpoint
