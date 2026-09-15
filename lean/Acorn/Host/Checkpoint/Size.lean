/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Snapshot

/-!
# Derived checkpoint resource bounds

Lengths come from the actual codec schemas. The receiver's capacity and bounded
transcript determine the maximum file size before native reading allocates the
file image. These bounds do not promise successful allocation on every machine.
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

/-- Every saved assignment occupies exactly four words. -/
theorem assignment_size (assignment : AssignmentWords) : (assignmentCodec.encode assignment).length = 16 := by
  simp [assignmentCodec, Codec.iso, Codec.pair, u32_size]

/-- Two arrays of binary32 words determine primary knowledge size. -/
theorem knowledge_size (dimension : Dimension) (image : KnowledgeImage dimension) :
    ((knowledgeCodec dimension).encode image).length = dimension.capacity * 8 := by
  simp only [knowledgeCodec, Codec.iso, Codec.pair, List.length_append,
    vector_size binary32Codec 4 binary32_size]
  omega

/-- Heterogeneous channel count is inherited from the immutable horizon list. -/
theorem demonImages_size (dimension : Dimension) (discounts : List Discount)
    (images : DemonImages dimension discounts) :
    ((demonImagesCodec dimension discounts).encode images).length = discounts.length * (dimension.capacity * 8) := by
  induction images with
  | nil => simp [demonImagesCodec, Codec.iso, unitCodec]
  | cons head tail ih =>
    simp [demonImagesCodec, Codec.iso, Codec.pair, knowledge_size, ih, Nat.add_mul, Nat.add_comm]

/-- Every primary learner contributes exactly two complete arrays. -/
theorem primary_size (dimension : Dimension) (image : PrimaryImage dimension demonLayout) :
    ((primaryCodec dimension).encode image).length = primaryCount * (dimension.capacity * 8) := by
  simp only [primaryCodec, Codec.iso, Codec.pair, List.length_append,
    vector_size (knowledgeCodec dimension) (dimension.capacity * 8) (knowledge_size dimension),
    vector_size (vectorCodec (knowledgeCodec dimension) Acorn.FeatureConstants.primitiveCount)
      (Acorn.FeatureConstants.primitiveCount * (dimension.capacity * 8))
      (vector_size (knowledgeCodec dimension) (dimension.capacity * 8) (knowledge_size dimension) _),
    demonImages_size]
  simp only [primaryCount, Acorn.FeatureConstants.primitiveCount, Acorn.FeatureConstants.metaActionCount,
    Acorn.FeatureConstants.skillCount, Nat.add_mul]
  omega

/-- Count and binary64 sum occupy two wide words. -/
theorem sum_size (words : SumWords) : (sumCodec.encode words).length = 16 := by
  simp [sumCodec, Codec.pair, u64_size, binary64_size]

/-- Goal triples occupy twenty-four bytes. -/
theorem goal_size (words : GoalWords) : (goalCodec.encode words).length = 24 := by
  simp [goalCodec, Codec.pair, u64_size]

/-- Episode counters occupy five wide words. -/
theorem episodes_size (record : Lifetime.OptionEpisodes) : (episodesCodec.encode record).length = 40 := by
  simp [episodesCodec, Codec.iso, Codec.pair, u64_size, vector_size u64Codec 8 u64_size]

/-- Exact fixed-size lifetime extent derived from the complete schema. -/
def lifetimeBytes : Nat :=
  16 + 4 * 16 + Acorn.FeatureConstants.historyBins * 16 + demonLayout.length * 16 +
    demonLayout.length * 4 + demonLayout.length * 4 + Acorn.FeatureConstants.historyBins * 16 +
    Acorn.FeatureConstants.skillCount * 40 + 4 * 24 + 4 * (Acorn.FeatureConstants.cycleBins * 24)

/-- No duration of experience changes the lifetime record's byte count. -/
theorem lifetime_size (record : LifetimeWords) : (lifetimeCodec.encode record).length = lifetimeBytes := by
  simp [lifetimeCodec, lifetimeBytes, Codec.iso, Codec.pair,
    sum_size, vector_size sumCodec 16 sum_size, vector_size binary32Codec 4 binary32_size,
    vector_size episodesCodec 40 episodes_size, vector_size goalCodec 24 goal_size,
    vector_size (vectorCodec goalCodec Acorn.FeatureConstants.cycleBins)
      (Acorn.FeatureConstants.cycleBins * 24) (vector_size goalCodec 24 goal_size _), Nat.add_assoc]
  omega

/-- The signed header extent agrees with the generated transition format owner. -/
theorem header_source_size : 8 + 56 = Acorn.FeatureConstants.checkpointHeaderBytes := rfl

/-- The fixed lifetime extent agrees with the generated transition record owner. -/
theorem lifetime_source_size : lifetimeBytes = Acorn.FeatureConstants.checkpointLifetimeBytes := rfl

/-- One replacement event occupies ten bytes. -/
theorem event_size (event : UInt64 × UInt16) : (eventCodec.encode event).length = 10 := by
  simp [eventCodec, Codec.pair, u64_size, u16_size]

/-- Transcript size is its checked count word plus its exact events. -/
theorem transcript_size (events : Transcript) :
    (transcriptCodec.encode events).length = 4 + events.val.length * 10 := by
  simp [transcriptCodec, u32_size, list_size eventCodec 10 event_size]

/-- Payload size is linear in receiving capacity and actual transcript length. -/
def payloadBytes (dimension : Dimension) (events : Nat) : Nat :=
  56 + Acorn.FeatureConstants.skillCount * 16 + primaryCount * (dimension.capacity * 8) +
    lifetimeBytes + (4 + events * 10)

/-- The byte count applies to the actual writer, for arbitrary payload contents. -/
theorem payload_size (dimension : Dimension) (payload : Payload dimension) :
    ((payloadCodec dimension).encode payload).length = payloadBytes dimension payload.events.val.length := by
  simp [payloadCodec, payloadBytes, Codec.iso, Codec.pair, header_size,
    vector_size assignmentCodec 16 assignment_size, primary_size, lifetime_size, transcript_size,
    Nat.add_assoc]

/-- Sixteen bytes of framing surround the signed payload. -/
theorem encoded_size (dimension : Dimension) (payload : Payload dimension) :
    (encode dimension payload).length = 16 + payloadBytes dimension payload.events.val.length := by
  simp [encode, List.length_append, payload_size, u64_size, magic, Acorn.FeatureConstants.checkpointMagic, Nat.add_assoc]
  omega

/-- The receiver admits at most one replacement event per bank unit. -/
def maximumBytes (construction : AgentConstruction) : Nat :=
  16 + payloadBytes construction.dimension construction.config.units.count

/-- Snapshot allocation has a lifetime-independent bound derived from the receiver. -/
theorem snapshot_size_bound (construction : AgentConstruction) (state : construction.State) :
    (encode construction.dimension (snapshot construction state)).length ≤ maximumBytes construction := by
  rw [encoded_size]
  have bound := (snapshotImage construction state).features.progress.legal.1
  simp only [snapshot, imagePayload, transcriptWords, Progress.words, List.length_map,
    maximumBytes, payloadBytes]
  omega

end Acorn.Checkpoint
