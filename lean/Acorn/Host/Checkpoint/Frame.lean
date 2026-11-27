import Acorn.Host.Checkpoint.Schema
import Acorn.Rng

namespace Acorn.Checkpoint

def magic : List UInt8 := Acorn.FeatureConstants.checkpointMagic

def Payload.signed (payload : Payload) : List UInt8 := headerCodec.encode payload.header ++ payload.body

@[noinline] def encode (payload : Payload) : List UInt8 :=
  magic ++ payload.signed ++ u64Codec.encode (Rng.fnv payload.signed)

@[noinline] def decode (bytes : List UInt8) : Option Payload := do
  if bytes.take magic.length != magic then none else do
    let rest := bytes.drop magic.length
    let signed := rest.take (rest.length - 8)
    let (checksum, tail) ← u64Codec.decode (rest.drop (rest.length - 8))
    if !tail.isEmpty || checksum != Rng.fnv signed then none else do
      let (header, body) ← headerCodec.decode signed
      some ⟨header, body⟩

theorem checksum_length (word : UInt64) : (u64Codec.encode word).length = 8 := by
  simp [u64Codec, Codec.iso, wordCodec, encodeNat]

theorem decode_frame (signed : List UInt8) (checksum : UInt64) :
    decode (magic ++ signed ++ u64Codec.encode checksum) =
      if checksum = Rng.fnv signed then
        (headerCodec.decode signed).map fun read => ⟨read.1, read.2⟩
      else none := by
  have trailer : (u64Codec.encode checksum).length = 8 := checksum_length _
  have front : (signed ++ u64Codec.encode checksum).take
      ((signed ++ u64Codec.encode checksum).length - 8) = signed := by
    rw [List.length_append, trailer, Nat.add_sub_cancel, List.take_left]
  have back : (signed ++ u64Codec.encode checksum).drop
      ((signed ++ u64Codec.encode checksum).length - 8) = u64Codec.encode checksum := by
    rw [List.length_append, trailer, Nat.add_sub_cancel, List.drop_left]
  have read := u64Codec.roundtrip checksum []
  rw [List.append_nil] at read
  unfold decode
  simp only [List.append_assoc, List.take_left, List.drop_left, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  simp only [front, back, read, bind, Option.bind, List.isEmpty_nil, Bool.not_true,
    Bool.false_or]
  by_cases same : checksum = Rng.fnv signed
  · simp only [same, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    cases headerCodec.decode signed <;> rfl
  · simp [same]

theorem roundtrip (payload : Payload) : decode (encode payload) = some payload := by
  rw [encode, decode_frame]
  simp [Payload.signed, headerCodec.roundtrip]

theorem decode_written (bytes : List UInt8) (payload : Payload)
    (decoded : decode bytes = some payload) : bytes = encode payload := by
  unfold decode at decoded
  split at decoded
  · contradiction
  · rename_i framed
    have framed : bytes.take magic.length = magic := by simpa using framed
    dsimp only at decoded
    generalize hrest : bytes.drop magic.length = rest at decoded
    cases trailer : u64Codec.decode (rest.drop (rest.length - 8)) with
    | none => simp [trailer] at decoded
    | some found =>
      obtain ⟨checksum, trailing⟩ := found
      simp only [trailer, bind, Option.bind] at decoded
      split at decoded
      · contradiction
      · rename_i checked
        simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_false, List.isEmpty_iff,
          bne_iff_ne, ne_eq, not_or, Decidable.not_not] at checked
        obtain ⟨rfl, sum⟩ := checked
        cases read : headerCodec.decode (rest.take (rest.length - 8)) with
        | none => simp [read] at decoded
        | some found =>
          obtain ⟨header, body⟩ := found
          simp only [read, Option.some.injEq] at decoded
          subst decoded
          have signed := headerCodec_canonical _ _ _ read
          have written := u64Codec_canonical _ _ _ trailer
          simp only [List.append_nil] at written
          rw [← List.take_append_drop magic.length bytes, framed, hrest,
            ← List.take_append_drop (rest.length - 8) rest, written, sum, signed]
          simp [encode, Payload.signed, List.append_assoc]

end Acorn.Checkpoint
