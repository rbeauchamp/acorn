import Acorn.Host.Checkpoint.Snapshot

namespace Acorn.Checkpoint
open Features Handcrafted

theorem encodeNat_length (width value : Nat) : (encodeNat width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeNat, ih]

theorem u16_size (value : UInt16) : (u16Codec.encode value).length = 2 :=
  encodeNat_length _ _

theorem u32_size (value : UInt32) : (u32Codec.encode value).length = 4 :=
  encodeNat_length _ _

theorem u64_size (value : UInt64) : (u64Codec.encode value).length = 8 :=
  encodeNat_length _ _

theorem binary32_size (value : Binary32) : (binary32Codec.encode value).length = 4 := u32_size _

theorem binary64_size (value : Binary64) : (binary64Codec.encode value).length = 8 := u64_size _

theorem list_size {α : Type} (codec : Codec α) (size : Nat)
    (fixed : ∀ value, (codec.encode value).length = size) (values : List α) :
    (values.flatMap codec.encode).length = values.length * size := by
  induction values with
  | nil => simp
  | cons value values ih => simp [fixed, ih, Nat.add_mul, Nat.add_comm]

theorem vector_size {α : Type} (codec : Codec α) (size : Nat)
    (fixed : ∀ value, (codec.encode value).length = size) (count : Nat) (values : Vector α count) :
    ((vectorCodec codec count).encode values).length = count * size := by
  simpa [vectorCodec] using list_size codec size fixed values.toList

theorem header_size (header : Header) : (headerCodec.encode header).length = 56 := by
  simp [headerCodec, Codec.iso, Codec.pair, u32_size, u64_size, binary32_size]

theorem header_source_size : 8 + 56 = Acorn.FeatureConstants.checkpointHeaderBytes := rfl

theorem encoded_size (payload : Payload) :
    (encode payload).length = 72 + payload.body.length := by
  simp [encode, Payload.signed, List.length_append, header_size, u64_size, magic,
    Acorn.FeatureConstants.checkpointMagic]
  omega

def naturalAllowance : Nat := 4096

def managedBytes (capacity : Nat) : Nat := 48 * capacity + 17

def controllerBytes (capacity actions : Nat) : Nat := actions * managedBytes capacity + 9

def transitionBytes (width : Nat) : Nat :=
  5 * width + width * managedBytes width +
    Acorn.FeatureConstants.metaActionCount * managedBytes width

def modelBytes (dimension : Dimension) : Nat :=
  3 * managedBytes dimension.capacity + transitionBytes (rankWidth dimension)

def skillBytes (dimension : Dimension) : Nat :=
  17 + controllerBytes dimension.capacity Acorn.FeatureConstants.primitiveCount +
    modelBytes dimension + 7

def ensembleBytes (dimension : Dimension) (signals : Nat) : Nat :=
  controllerBytes dimension.capacity Acorn.FeatureConstants.primitiveCount +
    controllerBytes dimension.capacity Acorn.FeatureConstants.metaActionCount +
    Acorn.FeatureConstants.skillCount * skillBytes dimension +
    signals * managedBytes dimension.capacity

def referencesBytes (capacity signals : Nat) : Nat :=
  8 * signals + 36 + 24 + 8 + 12 + 1 + 4 + 32 + 1 + 150 +
    Acorn.FeatureConstants.optionMaxDuration * (8 + 4 * capacity) + 8

def demonStatsBytes : Nat := 727 + 5 * naturalAllowance

def statsBytes (signals : Nat) : Nat :=
  16 + 64 + 16 * Acorn.FeatureConstants.historyBins + signals * demonStatsBytes +
    16 * Acorn.FeatureConstants.historyBins + 40 * Acorn.FeatureConstants.skillCount + 96 +
    96 * Acorn.FeatureConstants.cycleBins + 9 +
    Acorn.FeatureConstants.historyBins * (9 + 2 * naturalAllowance) + 9 + 1

def imageBytes (construction : AgentConstruction) : Nat :=
  46 + 20 * construction.config.units.count + ensembleBytes construction.dimension demonLayout.length +
    referencesBytes construction.dimension.capacity demonLayout.length + 7 + 4 + 4 +
    statsBytes demonLayout.length

def maximumBytes (construction : AgentConstruction) : Nat := 72 + imageBytes construction

end Acorn.Checkpoint
