/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Snapshot

/-!
# Derived checkpoint resource bounds

The read limit of a construction is the largest encoding of an image of it, part by part
from the formats of `Acorn.Host.Checkpoint.Image`, so that native reading refuses a larger
file before it allocates the file image. Each part is bounded by its type: a vector by its
count, a list of slots by the capacity, since no slot of a learner's eligible list or of an
active set repeats, and the unit list by the bank size. The exact naturals of the
predictive-agreement evaluator are the one part that no type bounds; the limit allows
`naturalAllowance` bytes for each of them, and the writer refuses an image above the limit
(`Store.save`), so every file it writes can be read. No theorem here bounds the evaluator's
naturals of a reached agent. These bounds do not promise successful allocation on every
machine.
-/
namespace Acorn.Checkpoint
open Features Handcrafted

/-- Fixed-width positional encoding writes precisely its declared digit count. -/
theorem encodeNat_length (width value : Nat) : (encodeNat width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeNat, ih]

/-- The two-byte writer has its exact structural size. -/
theorem u16_size (value : UInt16) : (u16Codec.encode value).length = 2 :=
  encodeNat_length _ _

/-- The four-byte writer has its exact structural size. -/
theorem u32_size (value : UInt32) : (u32Codec.encode value).length = 4 :=
  encodeNat_length _ _

/-- The eight-byte writer has its exact structural size. -/
theorem u64_size (value : UInt64) : (u64Codec.encode value).length = 8 :=
  encodeNat_length _ _

/-- Binary32 storage occupies four bytes regardless of payload classification. -/
theorem binary32_size (value : Binary32) : (binary32Codec.encode value).length = 4 := u32_size _

/-- Binary64 storage occupies eight bytes regardless of payload classification. -/
theorem binary64_size (value : Binary64) : (binary64Codec.encode value).length = 8 := u64_size _

/-- A fixed-size element codec scales structurally with the number of elements. -/
theorem list_size {α : Type} (codec : Codec α) (size : Nat)
    (fixed : ∀ value, (codec.encode value).length = size) (values : List α) :
    (values.flatMap codec.encode).length = values.length * size := by
  induction values with
  | nil => simp
  | cons value values ih => simp [fixed, ih, Nat.add_mul, Nat.add_comm]

/-- The vector's type supplies the allocation and encoding count. -/
theorem vector_size {α : Type} (codec : Codec α) (size : Nat)
    (fixed : ∀ value, (codec.encode value).length = size) (count : Nat) (values : Vector α count) :
    ((vectorCodec codec count).encode values).length = count * size := by
  simpa [vectorCodec] using list_size codec size fixed values.toList

/-- The signed header occupies exactly fifty-six bytes. -/
theorem header_size (header : Header) : (headerCodec.encode header).length = 56 := by
  simp [headerCodec, Codec.iso, Codec.pair, u32_size, u64_size, binary32_size]

/-- The signed header extent agrees with the generated transition format owner. -/
theorem header_source_size : 8 + 56 = Acorn.FeatureConstants.checkpointHeaderBytes := rfl

/-- Sixteen bytes of framing and the fifty-six header bytes surround the body. -/
theorem encoded_size (payload : Payload) :
    (encode payload).length = 72 + payload.body.length := by
  simp [encode, Payload.signed, List.length_append, header_size, u64_size, magic,
    Acorn.FeatureConstants.checkpointMagic]
  omega

/-- Bytes allowed for one exact natural of the agreement evaluator in its base-128 encoding:
every natural below `2 ^ 28672`. -/
def naturalAllowance : Nat := 4096

/-- A learner of a feature space of `capacity` slots: weights, log step sizes, at most one
transient entry per slot, two transient words and the phase. -/
def managedBytes (capacity : Nat) : Nat := 48 * capacity + 17

/-- A controller of `actions` learners. -/
def controllerBytes (capacity actions : Nat) : Nat := actions * managedBytes capacity + 9

/-- A transition part of `width` ranked positions: the slots, one row per position and one
deviation learner per meta action. -/
def transitionBytes (width : Nat) : Nat :=
  5 * width + width * managedBytes width +
    Acorn.FeatureConstants.metaActionCount * managedBytes width

/-- An option model, at its largest criterion: three full-width learners and its transition
part. -/
def modelBytes (dimension : Dimension) : Nat :=
  3 * managedBytes dimension.capacity + transitionBytes (rankWidth dimension)

/-- An option's questions: one per signal, and the preceding set. -/
def questionsBytes (capacity signals : Nat) : Nat := signals * (8 * capacity + 1) + 8 + 4 * capacity

/-- One option slot: interest, policy, model, trajectory and questions. -/
def skillBytes (dimension : Dimension) (signals : Nat) : Nat :=
  17 + controllerBytes dimension.capacity Acorn.FeatureConstants.primitiveCount +
    modelBytes dimension + 7 + questionsBytes dimension.capacity signals

/-- Every learned consumer. -/
def ensembleBytes (dimension : Dimension) (signals : Nat) : Nat :=
  controllerBytes dimension.capacity Acorn.FeatureConstants.primitiveCount +
    controllerBytes dimension.capacity Acorn.FeatureConstants.metaActionCount +
    Acorn.FeatureConstants.skillCount * skillBytes dimension signals +
    signals * managedBytes dimension.capacity

/-- The process-local references: prediction and error words, model caches, occupancy,
planning words, the gap, the generator, the pending flag, the last decision and the recent
feature sets. -/
def referencesBytes (capacity signals : Nat) : Nat :=
  8 * signals + 36 + 24 + 8 + 12 + 1 + 4 + 32 + 1 + 150 +
    Acorn.FeatureConstants.optionMaxDuration * (8 + 4 * capacity) + 8

/-- One horizon's prediction accounting: the durable record, the pending returns and the
evaluator channel with its five naturals. -/
def demonStatsBytes : Nat := 727 + 5 * naturalAllowance

/-- Every lifetime observation, with two naturals per agreement point. -/
def statsBytes (signals : Nat) : Nat :=
  16 + 64 + 16 * Acorn.FeatureConstants.historyBins + signals * demonStatsBytes +
    16 * Acorn.FeatureConstants.historyBins + 40 * Acorn.FeatureConstants.skillCount + 96 +
    96 * Acorn.FeatureConstants.cycleBins + 9 +
    Acorn.FeatureConstants.historyBins * (9 + 2 * naturalAllowance) + 9 + 1

/-- The exact image of an agent of a construction: the representation with its unit list,
the consumers, the references, credit, gain, rate schedule and lifetime observations. -/
def imageBytes (construction : AgentConstruction) : Nat :=
  46 + 20 * construction.config.units.count + ensembleBytes construction.dimension demonLayout.length +
    referencesBytes construction.dimension.capacity demonLayout.length + 7 + 4 + 4 +
    statsBytes demonLayout.length

/-- The read limit of a construction: framing, header and the largest image. -/
def maximumBytes (construction : AgentConstruction) : Nat := 72 + imageBytes construction

end Acorn.Checkpoint
