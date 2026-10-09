/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Schema

/-!
# Complete checkpoint framing

Magic, signed header/payload and final FNV word have disjoint roles. The checksum
covers the bytes actually consumed after the magic, including the clock and
identity header. It detects accidental mutation, not authenticity or correctness.
Trailing bytes and truncation are refused.
-/
namespace Acorn.Checkpoint

/-- OAKCKPT followed by the fixed magic suffix byte one. -/
def magic : List UInt8 := Acorn.FeatureConstants.checkpointMagic

/-- Complete file encoding; the version remains inside the signed payload. -/
@[noinline] def encode (dimension : Dimension) (payload : Payload dimension) : List UInt8 :=
  let signed := (payloadCodec dimension).encode payload
  magic ++ signed ++ u64Codec.encode (Rng.fnv signed)

/-- Full consumption and checksum are required after structural parsing. -/
@[noinline] def decode (dimension : Dimension) (bytes : List UInt8) : Option (Payload dimension) := do
  if bytes.take magic.length != magic then none else do
    let body := bytes.drop magic.length
    let (payload, tail) ← (payloadCodec dimension).decode body
    let (checksum, rest) ← u64Codec.decode tail
    if !rest.isEmpty || checksum != Rng.fnv (body.take (body.length - tail.length)) then none
    else some payload

/-- The actual complete writer/parser round trip covers every raw format value. -/
theorem roundtrip (dimension : Dimension) (payload : Payload dimension) :
    decode dimension (encode dimension payload) = some payload := by
  simp only [encode, decode, List.append_assoc, List.take_left, List.drop_left]
  rw [(payloadCodec dimension).roundtrip]
  simp only [bind, Option.bind]
  have checksum := u64Codec.roundtrip (Rng.fnv ((payloadCodec dimension).encode payload)) []
  simp only [List.append_nil] at checksum
  rw [checksum]
  simp [List.length_append]

/-- Decoding reads only the bytes that the writer writes: an accepted byte list is the
encoding of the payload that decoding returns (`payloadCodec_canonical`, and the checksum
and the empty suffix that decoding requires). -/
theorem decode_written (dimension : Dimension) (bytes : List UInt8) (payload : Payload dimension)
    (decoded : decode dimension bytes = some payload) : bytes = encode dimension payload := by
  unfold decode at decoded
  split at decoded
  · contradiction
  · rename_i framed
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at framed
    cases body : (payloadCodec dimension).decode (bytes.drop magic.length) with
    | none => simp [body] at decoded
    | some found =>
      obtain ⟨read, tail⟩ := found
      cases trailer : u64Codec.decode tail with
      | none => simp [body, trailer] at decoded
      | some found =>
        obtain ⟨checksum, trailing⟩ := found
        simp only [body, trailer, bind, Option.bind] at decoded
        split at decoded
        · contradiction
        · rename_i checked
          cases decoded
          simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_false, List.isEmpty_iff,
            bne_iff_ne, ne_eq, not_or, Decidable.not_not] at checked
          obtain ⟨rfl, sum⟩ := checked
          have signed := payloadCodec_canonical dimension _ _ _ body
          rw [signed, List.length_append, Nat.add_sub_cancel, List.take_left] at sum
          rw [← List.take_append_drop magic.length bytes, framed, signed,
            u64Codec_canonical _ _ _ trailer, sum]
          simp [encode]

end Acorn.Checkpoint
