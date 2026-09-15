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

end Acorn.Checkpoint
