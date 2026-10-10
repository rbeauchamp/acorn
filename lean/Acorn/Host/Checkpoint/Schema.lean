/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Codec
import Acorn.FeatureConstants

/-!
# Checkpoint format 19

A file holds a header and a body. The header holds the identity and configuration words of
the image, read before the body so that an image of another construction is refused before
any learner is read. The body is the exact image of the agent, whose schema is the formats
of `Acorn.Host.Checkpoint.Image`. Field order and widths define the serialized schema;
structural words remain untrusted until receiver-relative admission.
-/
namespace Acorn.Checkpoint

/-- Exact header after the eight-byte magic. -/
structure Header where
  /-- Layout and semantic generation, independent of the magic suffix. -/
  version : UInt32
  /-- Feature-space capacity. -/
  capacity : UInt32
  /-- Complete primary learner count. -/
  learners : UInt32
  /-- Feature seed. -/
  seed : UInt64
  /-- Saturating lifetime clock. -/
  clock : UInt64
  /-- Discounted or differential criterion. -/
  criterion : UInt32
  /-- Shared reward-rate bits. -/
  gain : Binary32
  /-- Positive sensory tiling count. -/
  tilings : UInt64
  /-- Bank capacity, stored as a full word before admission. -/
  units : UInt32
  /-- Exactly one denotes a resumable profile. -/
  supported : UInt32
  /-- Step order the saving agent ran under: `StepOrder.tag`. -/
  order : UInt32

/-- The header's single ordered schema drives both writing and reading. -/
def headerCodec : Codec Header :=
  (u32Codec.pair (u32Codec.pair (u32Codec.pair (u64Codec.pair (u64Codec.pair
    (u32Codec.pair (binary32Codec.pair (u64Codec.pair (u32Codec.pair
      (u32Codec.pair u32Codec)))))))))).iso
    (fun (version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported,
        order) =>
      ⟨version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported, order⟩)
    (fun h => (h.version, h.capacity, h.learners, h.seed, h.clock, h.criterion, h.gain,
      h.tilings, h.units, h.supported, h.order)) (by intro h; rfl)

/-- Canonical total of primitive, meta, option-action and demon blocks: the learner count
word of the header. -/
def primaryCount : Nat := Acorn.FeatureConstants.primitiveCount + Acorn.FeatureConstants.metaActionCount +
  Acorn.FeatureConstants.skillCount * Acorn.FeatureConstants.primitiveCount +
    Acorn.FeatureConstants.demonCount

/-- The raw signed payload: the header and the bytes of the body. Admission reads the body
under the receiving construction's image format. -/
structure Payload where
  /-- Complete identity and configuration header. -/
  header : Header
  /-- The bytes of the agent image. -/
  body : List UInt8

/-- The header codec is canonical. -/
theorem headerCodec_canonical : headerCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical u32Codec_canonical (Codec.pair_canonical u32Codec_canonical
      (Codec.pair_canonical u32Codec_canonical (Codec.pair_canonical u64Codec_canonical
      (Codec.pair_canonical u64Codec_canonical (Codec.pair_canonical u32Codec_canonical
      (Codec.pair_canonical binary32Codec_canonical (Codec.pair_canonical u64Codec_canonical
      (Codec.pair_canonical u32Codec_canonical
        (Codec.pair_canonical u32Codec_canonical u32Codec_canonical))))))))))
    fun _ => rfl

end Acorn.Checkpoint
