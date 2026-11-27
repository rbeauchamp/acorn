import Acorn.Encoding

namespace Acorn.Checkpoint

structure Codec (α : Type) where
  encode : α → List UInt8
  decode : List UInt8 → Option (α × List UInt8)
  roundtrip : ∀ value suffix, decode (encode value ++ suffix) = some (value, suffix)

def Codec.pair {α β : Type} (left : Codec α) (right : Codec β) : Codec (α × β) where
  encode value := left.encode value.1 ++ right.encode value.2
  decode bytes := do
    let (first, rest) ← left.decode bytes
    let (second, rest) ← right.decode rest
    some ((first, second), rest)
  roundtrip := by
    intro value suffix
    simp [List.append_assoc, left.roundtrip, right.roundtrip]

def Codec.iso {α β : Type} (codec : Codec α) (pack : α → β) (unpack : β → α)
    (inverse : ∀ value, pack (unpack value) = value) : Codec β where
  encode value := codec.encode (unpack value)
  decode bytes := do
    let (value, rest) ← codec.decode bytes
    some (pack value, rest)
  roundtrip := by intro value suffix; simp [codec.roundtrip, inverse]

def Codec.refine {α : Type} (codec : Codec α) (legal : α → Prop)
    [DecidablePred legal] : Codec { value : α // legal value } where
  encode value := codec.encode value.val
  decode bytes := do
    let (value, rest) ← codec.decode bytes
    if h : legal value then some (⟨value, h⟩, rest) else none
  roundtrip := by intro value suffix; simp [codec.roundtrip, value.property]

def unitCodec : Codec Unit where
  encode _ := []
  decode bytes := some ((), bytes)
  roundtrip := by intro value suffix; cases value; rfl

def byteCodec : Codec UInt8 where
  encode value := [value]
  decode
    | [] => none
    | head :: rest => some (head, rest)
  roundtrip := by intro value suffix; rfl

def decodeListInto {α : Type} (codec : Codec α) :
    Nat → List UInt8 → List α → Option (List α × List UInt8)
  | 0, bytes, reversed => some (reversed.reverse, bytes)
  | count + 1, bytes, reversed => do
    let (value, rest) ← codec.decode bytes
    decodeListInto codec count rest (value :: reversed)

def decodeList {α : Type} (codec : Codec α) (count : Nat) (bytes : List UInt8) :
    Option (List α × List UInt8) := decodeListInto codec count bytes []

theorem list_into_roundtrip {α : Type} (codec : Codec α) (values : List α)
    (suffix : List UInt8) (reversed : List α) :
    decodeListInto codec values.length (values.flatMap codec.encode ++ suffix) reversed =
      some (reversed.reverse ++ values, suffix) := by
  induction values generalizing reversed with
  | nil => simp [decodeListInto]
  | cons value values ih =>
    simp [decodeListInto, List.append_assoc, codec.roundtrip, ih]

theorem list_roundtrip {α : Type} (codec : Codec α) (values : List α) (suffix : List UInt8) :
    decodeList codec values.length (values.flatMap codec.encode ++ suffix) = some (values, suffix) := by
  simpa [decodeList] using list_into_roundtrip codec values suffix []

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

theorem decodeList_length {α : Type} (codec : Codec α) (count : Nat) (bytes : List UInt8)
    (values : List α) (rest : List UInt8)
    (decoded : decodeList codec count bytes = some (values, rest)) : values.length = count := by
  simpa using decodeListInto_length codec count bytes [] values rest decoded

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

def encodeNat : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat value :: encodeNat width (value / 256)

def decodeNat : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bytes => some (0, bytes)
  | width + 1, bytes => do
    let (digit, rest) ← byteCodec.decode bytes
    let (high, rest) ← decodeNat width rest
    some (digit.toNat + 256 * high, rest)

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

theorem decodeNat_written (width : Nat) (bytes : List UInt8) (value : Nat)
    (rest : List UInt8) (decoded : decodeNat width bytes = some (value, rest)) :
    bytes = encodeNat width value ++ rest := by
  induction width generalizing bytes value rest with
  | zero =>
    simp only [decodeNat, Option.some.injEq, Prod.mk.injEq] at decoded
    simp [encodeNat, decoded.2]
  | succ width ih =>
    cases bytes with
    | nil => simp [decodeNat, byteCodec] at decoded
    | cons digit bytes =>
      simp only [decodeNat, byteCodec, bind, Option.bind] at decoded
      cases highEq : decodeNat width bytes with
      | none => simp [highEq] at decoded
      | some high =>
        simp only [highEq, Option.some.injEq, Prod.mk.injEq] at decoded
        have tail := ih bytes high.1 high.2 highEq
        have small := digit.toNat_lt
        have quotient : value / 256 = high.1 := by omega
        have low : UInt8.ofNat value = digit := by
          apply UInt8.toNat_inj.mp
          show value % 256 = digit.toNat
          omega
        rw [encodeNat, low, quotient, List.cons_append, ← decoded.2, ← tail]

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

def u16Codec : Codec UInt16 :=
  (wordCodec 2).iso (fun value => UInt16.ofNat value.val)
    (fun value => ⟨value.toNat, value.toNat_lt⟩) (by intro value; simp)

def u32Codec : Codec UInt32 :=
  (wordCodec 4).iso (fun value => UInt32.ofNat value.val)
    (fun value => ⟨value.toNat, value.toNat_lt⟩) (by intro value; simp)

def u64Codec : Codec UInt64 :=
  (wordCodec 8).iso (fun value => UInt64.ofNat value.val)
    (fun value => ⟨value.toNat, value.toNat_lt⟩) (by intro value; simp)

def binary32Codec : Codec Binary32 :=
  u32Codec.iso Binary32.mk Binary32.bits (by intro value; rfl)

def binary64Codec : Codec Binary64 :=
  u64Codec.iso Binary64.mk Binary64.bits (by intro value; rfl)

def Codec.Canonical {α : Type} (codec : Codec α) : Prop :=
  ∀ bytes value rest, codec.decode bytes = some (value, rest) → bytes = codec.encode value ++ rest

theorem Codec.pair_canonical {α β : Type} {left : Codec α} {right : Codec β}
    (leftCanonical : left.Canonical) (rightCanonical : right.Canonical) :
    (left.pair right).Canonical := by
  intro bytes value rest decoded
  cases first : left.decode bytes with
  | none => simp [Codec.pair, first] at decoded
  | some found =>
    obtain ⟨head, middle⟩ := found
    cases second : right.decode middle with
    | none => simp [Codec.pair, first, second] at decoded
    | some found =>
      obtain ⟨tail, last⟩ := found
      simp only [Codec.pair, first, second, bind, Option.bind, Option.some.injEq,
        Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      rw [leftCanonical _ _ _ first, rightCanonical _ _ _ second]
      simp [Codec.pair]

theorem Codec.iso_canonical {α β : Type} {codec : Codec α} {pack : α → β} {unpack : β → α}
    {inverse : ∀ value, pack (unpack value) = value} (canonical : codec.Canonical)
    (packed : ∀ value, unpack (pack value) = value) :
    (codec.iso pack unpack inverse).Canonical := by
  intro bytes value rest decoded
  cases inner : codec.decode bytes with
  | none => simp [Codec.iso, inner] at decoded
  | some found =>
    obtain ⟨read, tail⟩ := found
    simp only [Codec.iso, inner, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    rw [canonical _ _ _ inner]
    simp [Codec.iso, packed]

theorem unitCodec_canonical : unitCodec.Canonical := by
  intro bytes value rest decoded
  simp only [unitCodec, Option.some.injEq, Prod.mk.injEq] at decoded
  rw [← decoded.2]
  rfl

theorem byteCodec_canonical : byteCodec.Canonical := by
  intro bytes value rest decoded
  cases bytes with
  | nil => simp [byteCodec] at decoded
  | cons head tail =>
    simp only [byteCodec, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    rfl

theorem wordCodec_canonical (width : Nat) : (wordCodec width).Canonical := by
  intro bytes value rest decoded
  simp only [wordCodec] at decoded
  split at decoded
  · contradiction
  · rename_i read tail readDecoded
    simp only [Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    exact decodeNat_written width bytes read tail readDecoded

theorem u16Codec_canonical : u16Codec.Canonical :=
  Codec.iso_canonical (wordCodec_canonical 2) fun value =>
    Fin.ext (UInt16.toNat_ofNat_of_lt (by simp))

theorem u32Codec_canonical : u32Codec.Canonical :=
  Codec.iso_canonical (wordCodec_canonical 4) fun value =>
    Fin.ext (UInt32.toNat_ofNat_of_lt (by simp))

theorem u64Codec_canonical : u64Codec.Canonical :=
  Codec.iso_canonical (wordCodec_canonical 8) fun value =>
    Fin.ext (UInt64.toNat_ofNat_of_lt (by simp))

theorem binary32Codec_canonical : binary32Codec.Canonical :=
  Codec.iso_canonical u32Codec_canonical fun _ => rfl

theorem binary64Codec_canonical : binary64Codec.Canonical :=
  Codec.iso_canonical u64Codec_canonical fun _ => rfl

theorem decodeListInto_written {α : Type} {codec : Codec α} (canonical : codec.Canonical) :
    ∀ (count : Nat) (bytes : List UInt8) (reversed values : List α) (rest : List UInt8),
      decodeListInto codec count bytes reversed = some (values, rest) →
        ∃ read : List α, values = reversed.reverse ++ read ∧
          bytes = read.flatMap codec.encode ++ rest
  | 0, bytes, reversed, values, rest, decoded => by
    simp only [decodeListInto, Option.some.injEq, Prod.mk.injEq] at decoded
    exact ⟨[], by simp [decoded.1], by simp [decoded.2]⟩
  | count + 1, bytes, reversed, values, rest, decoded => by
    cases first : codec.decode bytes with
    | none => simp [decodeListInto, first] at decoded
    | some found =>
      obtain ⟨value, middle⟩ := found
      simp only [decodeListInto, first, bind, Option.bind] at decoded
      obtain ⟨read, valuesRead, middleRead⟩ :=
        decodeListInto_written canonical count middle (value :: reversed) values rest decoded
      refine ⟨value :: read, by simp [valuesRead], ?_⟩
      rw [canonical _ _ _ first, middleRead]
      simp

theorem vectorCodec_canonical {α : Type} {codec : Codec α} (canonical : codec.Canonical)
    (count : Nat) : (vectorCodec codec count).Canonical := by
  intro bytes value rest decoded
  simp only [vectorCodec] at decoded
  split at decoded
  · contradiction
  · rename_i values tail listDecoded
    simp only [Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    obtain ⟨read, valuesRead, bytesRead⟩ :=
      decodeListInto_written canonical count bytes [] values tail listDecoded
    simp only [List.reverse_nil, List.nil_append] at valuesRead
    subst valuesRead
    simpa [vectorCodec] using bytesRead

end Acorn.Checkpoint
