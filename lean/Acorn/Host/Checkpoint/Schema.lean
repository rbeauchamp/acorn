import Acorn.Host.Checkpoint.Codec
import Acorn.FeatureConstants

namespace Acorn.Checkpoint

structure Header where
  version : UInt32
  capacity : UInt32
  learners : UInt32
  seed : UInt64
  clock : UInt64
  criterion : UInt32
  gain : Binary32
  tilings : UInt64
  units : UInt32
  supported : UInt32
  order : UInt32

def headerCodec : Codec Header :=
  (u32Codec.pair (u32Codec.pair (u32Codec.pair (u64Codec.pair (u64Codec.pair
    (u32Codec.pair (binary32Codec.pair (u64Codec.pair (u32Codec.pair
      (u32Codec.pair u32Codec)))))))))).iso
    (fun (version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported,
        order) =>
      ⟨version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported, order⟩)
    (fun h => (h.version, h.capacity, h.learners, h.seed, h.clock, h.criterion, h.gain,
      h.tilings, h.units, h.supported, h.order)) (by intro h; rfl)

def primaryCount : Nat := Acorn.FeatureConstants.primitiveCount + Acorn.FeatureConstants.metaActionCount +
  Acorn.FeatureConstants.skillCount * Acorn.FeatureConstants.primitiveCount +
    Acorn.FeatureConstants.demonCount

structure Payload where
  header : Header
  body : List UInt8

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
