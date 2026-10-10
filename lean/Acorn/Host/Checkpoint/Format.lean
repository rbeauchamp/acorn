/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Codec

/-!
# Formats of stored values

A format writes a value as bytes and reads a value back from the front of a byte list,
returning the bytes after it. A `Codec` carries its round-trip law in its value; a format
carries none, because the law of the format of a learner state needs invariants of the
learner that the proof library proves. The two laws are predicates of a format instead:
`Format.Lawful`, reading the bytes of a value returns the value, and `Format.Canonical`,
every value read is followed in its input by exactly the bytes returned, so no value has a
second encoding. Each combinator here proves that it keeps both (`Format.Exact`).
-/
namespace Acorn.Checkpoint

/-- A writer and a prefix reader of one stored type. -/
structure Format (α : Type) where
  /-- Bytes in file order. -/
  encode : α → List UInt8
  /-- Read one value from the front, returning the bytes after it. -/
  decode : List UInt8 → Option (α × List UInt8)

namespace Format

variable {α β : Type}

/-- Reading the bytes of a value, followed by any bytes, returns the value and those bytes. -/
abbrev Lawful (format : Format α) : Prop :=
  ∀ value suffix, format.decode (format.encode value ++ suffix) = some (value, suffix)

/-- Every value read is followed in its input by exactly the bytes returned. -/
abbrev Canonical (format : Format α) : Prop :=
  ∀ bytes value rest, format.decode bytes = some (value, rest) →
    bytes = format.encode value ++ rest

/-- Reading the bytes of one value, followed by any bytes, returns the value and those bytes. -/
abbrev LawfulAt (format : Format α) (value : α) : Prop :=
  ∀ suffix, format.decode (format.encode value ++ suffix) = some (value, suffix)

/-- Both laws: the format reads exactly the encodings of its values, each as its value. -/
structure Exact (format : Format α) : Prop where
  /-- Reading an encoding returns its value. -/
  lawful : format.Lawful
  /-- Only encodings are read. -/
  canonical : format.Canonical

end Format

/-- The format of a codec. -/
def Codec.format {α : Type} (codec : Codec α) : Format α := ⟨codec.encode, codec.decode⟩

/-- A canonical codec is an exact format; its round trip is its own law. -/
theorem Codec.format_exact {α : Type} {codec : Codec α} (canonical : codec.Canonical) :
    codec.format.Exact := ⟨codec.roundtrip, canonical⟩

namespace Format

variable {α β : Type}

/-- Two values in order. -/
def pair (left : Format α) (right : Format β) : Format (α × β) where
  encode value := left.encode value.1 ++ right.encode value.2
  decode bytes := do
    let (first, rest) ← left.decode bytes
    let (second, rest) ← right.decode rest
    some ((first, second), rest)

/-- Two canonical formats in order are canonical. -/
theorem pair_canonical {left : Format α} {right : Format β} (first : left.Canonical)
    (second : right.Canonical) : (left.pair right).Canonical := by
  intro bytes value rest decoded
  cases head : left.decode bytes with
  | none => simp [pair, head] at decoded
  | some found =>
    obtain ⟨read, middle⟩ := found
    cases tail : right.decode middle with
    | none => simp [pair, head, tail] at decoded
    | some found =>
      obtain ⟨later, last⟩ := found
      simp only [pair, head, tail, bind, Option.bind, Option.some.injEq,
        Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      rw [first _ _ _ head, second _ _ _ tail]
      simp [pair]

/-- Two exact formats in order are exact. -/
theorem pair_exact {left : Format α} {right : Format β} (first : left.Exact)
    (second : right.Exact) : (left.pair right).Exact :=
  ⟨fun value suffix => by simp [pair, List.append_assoc, first.lawful, second.lawful],
    pair_canonical first.canonical second.canonical⟩

/-- Two values each read back are read back in order. -/
theorem pair_lawfulAt {left : Format α} {right : Format β} {first : α} {second : β}
    (head : left.LawfulAt first) (tail : right.LawfulAt second) :
    (left.pair right).LawfulAt (first, second) := by
  intro suffix
  simp [pair, List.append_assoc, head, tail]

/-- Read a stored value and admit it into another type, which may refuse it. -/
def filterMap (format : Format α) (pack : α → Option β) (unpack : β → α) : Format β where
  encode value := format.encode (unpack value)
  decode bytes := do
    let (raw, rest) ← format.decode bytes
    let value ← pack raw
    some (value, rest)

/-- An admission of a canonical format is exact when the format reads back the stored form of
every value, the admission admits that form as the value, and every value it admits from a
stored form has that stored form. -/
theorem filterMap_exact_of {format : Format α} {pack : α → Option β} {unpack : β → α}
    (lawful : ∀ value suffix,
      format.decode (format.encode (unpack value) ++ suffix) = some (unpack value, suffix))
    (canonical : format.Canonical) (inverse : ∀ value, pack (unpack value) = some value)
    (packed : ∀ raw value, pack raw = some value → unpack value = raw) :
    (format.filterMap pack unpack).Exact := by
  constructor
  · intro value suffix
    simp [filterMap, lawful, inverse]
  · intro bytes value rest decoded
    cases inner : format.decode bytes with
    | none => simp [filterMap, inner] at decoded
    | some found =>
      obtain ⟨raw, tail⟩ := found
      cases built : pack raw with
      | none => simp [filterMap, inner, built] at decoded
      | some made =>
        simp only [filterMap, inner, built, bind, Option.bind, Option.some.injEq,
          Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        rw [canonical _ _ _ inner]
        simp [filterMap, packed raw made built]

/-- An admission of an exact format is exact when it admits the stored form of every value
as that value, and every value it admits from a stored form has that stored form. -/
theorem filterMap_exact {format : Format α} {pack : α → Option β} {unpack : β → α}
    (exact : format.Exact) (inverse : ∀ value, pack (unpack value) = some value)
    (packed : ∀ raw value, pack raw = some value → unpack value = raw) :
    (format.filterMap pack unpack).Exact :=
  filterMap_exact_of (fun value suffix => exact.lawful (unpack value) suffix) exact.canonical
    inverse packed

/-- Change representation through a total inverse pair. -/
def map (format : Format α) (pack : α → β) (unpack : β → α) : Format β :=
  format.filterMap (fun raw => some (pack raw)) unpack

/-- A representation change of an exact format is exact when the two maps are inverse. -/
theorem map_exact {format : Format α} {pack : α → β} {unpack : β → α}
    (exact : format.Exact) (inverse : ∀ value, pack (unpack value) = value)
    (packed : ∀ raw, unpack (pack raw) = raw) : (format.map pack unpack).Exact :=
  filterMap_exact exact (fun value => by simp [inverse]) (fun raw value built => by
    obtain rfl := Option.some.inj built
    exact packed raw)

/-- No bytes are needed for the unique unit value. -/
def unit : Format Unit := unitCodec.format

/-- The empty format is exact. -/
theorem unit_exact : unit.Exact := Codec.format_exact unitCodec_canonical

/-- One byte. -/
def byte : Format UInt8 := byteCodec.format

/-- The byte format is exact. -/
theorem byte_exact : byte.Exact := Codec.format_exact byteCodec_canonical

/-- A flag is the byte zero or the byte one; every other byte is refused. -/
def bool : Format Bool :=
  byte.filterMap (fun stored => if stored = 0 then some false else if stored = 1 then some true
    else none) (fun flag => if flag then 1 else 0)

/-- The flag format is exact. -/
theorem bool_exact : bool.Exact :=
  filterMap_exact byte_exact (fun flag => by cases flag <;> rfl) (fun stored flag built => by
    by_cases zero : stored = 0
    · subst zero
      simp only [↓reduceIte, Option.some.injEq] at built
      subst built
      rfl
    · by_cases one : stored = 1
      · subst one
        simp only [show (1 : UInt8) ≠ 0 by decide, ↓reduceIte, Option.some.injEq] at built
        subst built
        rfl
      · simp [zero, one] at built)

/-- A value of a closed finite type, stored as one byte: its position in a listing of all
its values. -/
def enum (values : List α) (position : α → Nat) : Format α :=
  byte.filterMap (fun stored => values[stored.toNat]?) (fun value => UInt8.ofNat (position value))

/-- An enumeration is exact when the listing holds every value at its position and has at
most 256 entries. -/
theorem enum_exact (values : List α) (position : α → Nat)
    (listed : ∀ value, values[position value]? = some value)
    (positions : ∀ (index : Nat) (inside : index < values.length), position values[index] = index)
    (fits : values.length ≤ 256) : (enum values position).Exact :=
  filterMap_exact byte_exact
    (fun value => by
      obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp (listed value)
      have small : (UInt8.ofNat (position value)).toNat = position value := by
        simp only [UInt8.toNat_ofNat']
        omega
      simp only [small, listed])
    (fun stored value found => by
      obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp found
      have placed := positions stored.toNat inside
      rw [same] at placed
      apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_ofNat', placed]
      exact Nat.mod_eq_of_lt stored.toNat_lt)

/-- An index below a count, stored as a fixed-width word; a word at or above the count is
refused. -/
def fin (width count : Nat) : Format (Fin count) :=
  (wordCodec width).format.filterMap
    (fun word => if h : word.val < count then some ⟨word.val, h⟩ else none)
    (fun index => ⟨index.val % 256 ^ width, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩)

/-- The index format is exact when every index fits the word width. -/
theorem fin_exact (width count : Nat) (fits : count ≤ 256 ^ width) : (fin width count).Exact :=
  filterMap_exact (Codec.format_exact (wordCodec_canonical width))
    (fun index => by
      have small : index.val % 256 ^ width = index.val :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le index.isLt fits)
      simp [small])
    (fun word index built => by
      split at built
      · obtain rfl := Option.some.inj built
        exact Fin.ext (Nat.mod_eq_of_lt word.isLt)
      · contradiction)

/-- An optional value: the byte zero for none, the byte one before a present value. -/
def option (format : Format α) : Format (Option α) where
  encode
    | none => [0]
    | some value => 1 :: format.encode value
  decode
    | [] => none
    | tag :: rest =>
      if tag = 0 then some (none, rest)
      else if tag = 1 then (format.decode rest).map fun (value, rest) => (some value, rest)
      else none

/-- An optional exact value is exact. -/
theorem option_exact {format : Format α} (exact : format.Exact) : format.option.Exact := by
  constructor
  · intro value suffix
    cases value with
    | none => rfl
    | some value =>
      simp [option, exact.lawful]
  · intro bytes value rest decoded
    cases bytes with
    | nil => simp [option] at decoded
    | cons tag tail =>
      by_cases zero : tag = 0
      · subst zero
        simp only [option, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        rfl
      · by_cases one : tag = 1
        · subst one
          cases inner : format.decode tail with
          | none => simp [option, inner] at decoded
          | some found =>
            obtain ⟨read, last⟩ := found
            simp only [option, show (1 : UInt8) ≠ 0 by decide, ↓reduceIte, inner,
              Option.map_some, Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨rfl, rfl⟩ := decoded
            rw [exact.canonical _ _ _ inner]
            rfl
        · simp [option, zero, one] at decoded

/-- One of two values: the byte zero before a left value, the byte one before a right one. -/
def sum (left : Format α) (right : Format β) : Format (α ⊕ β) where
  encode
    | .inl value => 0 :: left.encode value
    | .inr value => 1 :: right.encode value
  decode
    | [] => none
    | tag :: rest =>
      if tag = 0 then (left.decode rest).map fun (value, rest) => (.inl value, rest)
      else if tag = 1 then (right.decode rest).map fun (value, rest) => (.inr value, rest)
      else none

/-- A choice of two exact formats is exact. -/
theorem sum_exact {left : Format α} {right : Format β} (first : left.Exact)
    (second : right.Exact) : (left.sum right).Exact := by
  constructor
  · intro value suffix
    cases value with
    | inl value => simp [sum, first.lawful]
    | inr value => simp [sum, second.lawful]
  · intro bytes value rest decoded
    cases bytes with
    | nil => simp [sum] at decoded
    | cons tag tail =>
      by_cases zero : tag = 0
      · subst zero
        cases inner : left.decode tail with
        | none => simp [sum, inner] at decoded
        | some found =>
          obtain ⟨read, last⟩ := found
          simp only [sum, ↓reduceIte, inner, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          rw [first.canonical _ _ _ inner]
          rfl
      · by_cases one : tag = 1
        · subst one
          cases inner : right.decode tail with
          | none => simp [sum, inner] at decoded
          | some found =>
            obtain ⟨read, last⟩ := found
            simp only [sum, show (1 : UInt8) ≠ 0 by decide, ↓reduceIte, inner,
              Option.map_some, Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨rfl, rfl⟩ := decoded
            rw [second.canonical _ _ _ inner]
            rfl
        · simp [sum, zero, one] at decoded

/-- Read a fixed number of values with one accumulator. -/
def decodeInto (format : Format α) : Nat → List UInt8 → List α → Option (List α × List UInt8)
  | 0, bytes, reversed => some (reversed.reverse, bytes)
  | count + 1, bytes, reversed => do
    let (value, rest) ← format.decode bytes
    decodeInto format count rest (value :: reversed)

/-- Each successful read adds exactly its requested count to the accumulator. -/
theorem decodeInto_length (format : Format α) (count : Nat) (bytes : List UInt8)
    (reversed values : List α) (rest : List UInt8)
    (decoded : decodeInto format count bytes reversed = some (values, rest)) :
    values.length = reversed.length + count := by
  induction count generalizing bytes reversed with
  | zero =>
    simp only [decodeInto, Option.some.injEq, Prod.mk.injEq] at decoded
    rw [← decoded.1]
    simp
  | succ count ih =>
    simp only [decodeInto] at decoded
    cases first : format.decode bytes with
    | none => simp [first] at decoded
    | some found =>
      simp only [first, bind, Option.bind] at decoded
      have length := ih found.2 (found.1 :: reversed) decoded
      simp only [List.length_cons] at length
      omega

/-- Reading the encodings of a list returns the list after the accumulator. -/
theorem decodeInto_lawful {format : Format α} (lawful : format.Lawful) (values : List α)
    (suffix : List UInt8) (reversed : List α) :
    decodeInto format values.length (values.flatMap format.encode ++ suffix) reversed =
      some (reversed.reverse ++ values, suffix) := by
  induction values generalizing reversed with
  | nil => simp [decodeInto]
  | cons value values ih =>
    simp [decodeInto, List.append_assoc, lawful, ih]

/-- A list read value by value is the encoding of the values read after the accumulator,
followed by the returned bytes. -/
theorem decodeInto_written {format : Format α} (canonical : format.Canonical) :
    ∀ (count : Nat) (bytes : List UInt8) (reversed values : List α) (rest : List UInt8),
      decodeInto format count bytes reversed = some (values, rest) →
        ∃ read : List α, values = reversed.reverse ++ read ∧
          bytes = read.flatMap format.encode ++ rest
  | 0, bytes, reversed, values, rest, decoded => by
    simp only [decodeInto, Option.some.injEq, Prod.mk.injEq] at decoded
    exact ⟨[], by simp [decoded.1], by simp [decoded.2]⟩
  | count + 1, bytes, reversed, values, rest, decoded => by
    cases first : format.decode bytes with
    | none => simp [decodeInto, first] at decoded
    | some found =>
      obtain ⟨value, middle⟩ := found
      simp only [decodeInto, first, bind, Option.bind] at decoded
      obtain ⟨read, valuesRead, middleRead⟩ :=
        decodeInto_written canonical count middle (value :: reversed) values rest decoded
      refine ⟨value :: read, by simp [valuesRead], ?_⟩
      rw [canonical _ _ _ first, middleRead]
      simp

/-- A fixed number of values; the count is the type's, never a stored word. -/
def vector (format : Format α) (count : Nat) : Format (Vector α count) where
  encode values := values.toList.flatMap format.encode
  decode bytes :=
    match h : decodeInto format count bytes [] with
    | none => none
    | some (values, rest) =>
      some (⟨values.toArray, by simpa using decodeInto_length format count bytes [] values rest h⟩,
        rest)

/-- A fixed-count vector of an exact format is exact. -/
theorem vector_exact {format : Format α} (exact : format.Exact) (count : Nat) :
    (format.vector count).Exact := by
  constructor
  · intro values suffix
    have h := decodeInto_lawful exact.lawful values.toList suffix []
    simp only [Vector.length_toList, List.reverse_nil, List.nil_append] at h
    simp only [vector]
    split <;> rename_i result
    · rw [h] at result; contradiction
    · rw [h] at result
      cases result
      cases values
      simp [Vector.toList]
  · intro bytes value rest decoded
    simp only [vector] at decoded
    split at decoded
    · contradiction
    · rename_i values tail listDecoded
      simp only [Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      obtain ⟨read, valuesRead, bytesRead⟩ :=
        decodeInto_written exact.canonical count bytes [] values tail listDecoded
      simp only [List.reverse_nil, List.nil_append] at valuesRead
      subst valuesRead
      simpa [vector] using bytesRead

/-- A list of values: its length as an eight-byte word, then its values. A stored length
above `bound` is refused before any value is read, so the bound limits the work of a read. -/
def list (format : Format α) (bound : Nat) : Format (List α) where
  encode values := u64Codec.encode values.length.toUInt64 ++ values.flatMap format.encode
  decode bytes := do
    let (count, rest) ← u64Codec.decode bytes
    if count.toNat ≤ bound then decodeInto format count.toNat rest [] else none

/-- A list no longer than the bound is read back, when the bound fits the length word. -/
theorem list_lawful {format : Format α} (lawful : format.Lawful) (bound : Nat)
    (fits : bound < 2 ^ 64) (values : List α) (short : values.length ≤ bound)
    (suffix : List UInt8) :
    (format.list bound).decode ((format.list bound).encode values ++ suffix) =
      some (values, suffix) := by
  have exactCount : values.length.toUInt64.toNat = values.length :=
    Nat.mod_eq_of_lt (by omega)
  have h := decodeInto_lawful lawful values suffix []
  simp only [List.reverse_nil, List.nil_append] at h
  simp only [list, List.append_assoc, u64Codec.roundtrip, bind, Option.bind]
  simp only [exactCount, short, ↓reduceIte, h]

/-- The list format reads only encodings. -/
theorem list_canonical {format : Format α} (canonical : format.Canonical) (bound : Nat) :
    (format.list bound).Canonical := by
  intro bytes value rest decoded
  cases counted : u64Codec.decode bytes with
  | none => simp [list, counted] at decoded
  | some found =>
    obtain ⟨count, tail⟩ := found
    simp only [list, counted, bind, Option.bind] at decoded
    split at decoded
    · have length := decodeInto_length format count.toNat tail [] value rest decoded
      obtain ⟨read, valuesRead, tailRead⟩ :=
        decodeInto_written canonical count.toNat tail [] value rest decoded
      simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add]
        at valuesRead length
      have countWord : value.length.toUInt64 = count := by
        rw [length]
        exact UInt64.toNat_inj.mp (Nat.mod_eq_of_lt count.toNat_lt)
      rw [u64Codec_canonical _ _ _ counted]
      simp only [list, countWord, List.append_assoc]
      rw [tailRead, ← valuesRead]
    · contradiction

/-- A natural number in base 128, least significant digit first: each byte holds seven bits,
and its high bit says that a further byte follows. -/
def encodeNatural (value : Nat) : List UInt8 :=
  if value < 128 then [UInt8.ofNat value]
  else UInt8.ofNat (value % 128 + 128) :: encodeNatural (value / 128)
termination_by value
decreasing_by omega

/-- Read a base-128 natural. A further byte whose digits are all zero is refused, since the
writer never writes one, so every natural has one encoding. -/
def decodeNatural : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | digit :: rest =>
    if digit.toNat < 128 then some (digit.toNat, rest)
    else match decodeNatural rest with
      | none => none
      | some (high, tail) =>
        if high = 0 then none else some (digit.toNat - 128 + 128 * high, tail)

/-- A natural of any size. -/
def natural : Format Nat := ⟨encodeNatural, decodeNatural⟩

/-- Reading the encoding of a natural returns it. -/
theorem natural_lawful (value : Nat) (suffix : List UInt8) :
    decodeNatural (encodeNatural value ++ suffix) = some (value, suffix) := by
  by_cases small : value < 128
  · rw [encodeNatural]
    simp only [small, ↓reduceIte, List.cons_append, List.nil_append, decodeNatural]
    have exact : (UInt8.ofNat value).toNat = value := by
      simp only [UInt8.toNat_ofNat']
      omega
    simp [exact, small]
  · have tail := natural_lawful (value / 128) suffix
    rw [encodeNatural]
    simp only [small, ↓reduceIte, List.cons_append, decodeNatural]
    have digit : (UInt8.ofNat (value % 128 + 128)).toNat = value % 128 + 128 := by
      simp only [UInt8.toNat_ofNat']
      omega
    have positive : value / 128 ≠ 0 := by omega
    rw [tail, digit]
    simp only [show ¬value % 128 + 128 < 128 by omega, ↓reduceIte, positive,
      Option.some.injEq, Prod.mk.injEq, and_true]
    omega
termination_by value
decreasing_by omega

/-- A natural read is followed by exactly the returned bytes. -/
theorem natural_canonical : ∀ (bytes : List UInt8) (value : Nat) (rest : List UInt8),
    decodeNatural bytes = some (value, rest) → bytes = encodeNatural value ++ rest
  | [], _, _, decoded => by simp [decodeNatural] at decoded
  | digit :: tail, value, rest, decoded => by
    simp only [decodeNatural] at decoded
    by_cases small : digit.toNat < 128
    · simp only [small, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      rw [encodeNatural]
      simp only [small, ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq,
        and_true]
      exact UInt8.toNat_inj.mp (by simp only [UInt8.toNat_ofNat']; omega)
    · simp only [small, ↓reduceIte] at decoded
      cases inner : decodeNatural tail with
      | none => simp [inner] at decoded
      | some found =>
        obtain ⟨high, last⟩ := found
        simp only [inner] at decoded
        by_cases zero : high = 0
        · simp [zero] at decoded
        · simp only [zero, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          have written := natural_canonical tail high last inner
          have bound := digit.toNat_lt
          rw [encodeNatural]
          have large : ¬digit.toNat - 128 + 128 * high < 128 := by omega
          simp only [large, ↓reduceIte, List.cons_append, List.cons.injEq]
          refine ⟨UInt8.toNat_inj.mp ?_, ?_⟩
          · simp only [UInt8.toNat_ofNat']
            omega
          · have quotient : (digit.toNat - 128 + 128 * high) / 128 = high := by omega
            rw [quotient, written]

/-- The natural format is exact. -/
theorem natural_exact : natural.Exact := ⟨natural_lawful, natural_canonical⟩

end Format

end Acorn.Checkpoint
