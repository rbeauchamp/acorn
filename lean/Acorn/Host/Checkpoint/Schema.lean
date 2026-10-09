/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Codec
import Acorn.Host.AgentAdmission

/-!
# Checkpoint format 18

Field order, widths and fixed collection shapes define the serialized schema.
Structural words remain untrusted until receiver-relative admission. Knowledge accepts all
binary32 words and is projected only by each receiving learner's closed rule.
-/
namespace Acorn.Checkpoint
open Features Handcrafted

/-- Exact format-18 header after the eight-byte magic. -/
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

/-- Assignment words retain the exact saved target and bonus. -/
def assignmentCodec : Codec AssignmentWords :=
  (u32Codec.pair (u32Codec.pair (u32Codec.pair u32Codec))).iso
    (fun (tag, unit, feature, bonus) => ⟨tag, unit, feature, bonus⟩)
    (fun a => (a.tag, a.unit, a.feature, a.bonus)) (by intro a; rfl)

/-- One primary learner stores weights followed by log step sizes. -/
def knowledgeCodec (dimension : Dimension) : Codec (KnowledgeImage dimension) :=
  ((vectorCodec binary32Codec dimension.capacity).pair (vectorCodec binary32Codec dimension.capacity)).iso
    (fun (weights, beta) => ⟨weights, beta⟩) (fun image => (image.weights, image.beta))
    (by intro image; rfl)

/-- Demon blocks follow the receiving horizon layout in order. -/
def demonImagesCodec (dimension : Dimension) : (discounts : List Discount) → Codec (DemonImages dimension discounts)
  | [] => unitCodec.iso (fun _ => .nil) (fun _ => ()) (by intro images; cases images; rfl)
  | _ :: rest => ((knowledgeCodec dimension).pair (demonImagesCodec dimension rest)).iso
      (fun (head, tail) => .cons head tail)
      (fun | .cons head tail => (head, tail)) (by intro images; cases images; rfl)

/-- Primary learner segment order is shared structurally by parser and writer. -/
def primaryCodec (dimension : Dimension) : Codec (PrimaryImage Grid.actions dimension demonLayout) :=
  ((vectorCodec (knowledgeCodec dimension) Acorn.FeatureConstants.primitiveCount).pair
    ((vectorCodec (knowledgeCodec dimension) Acorn.FeatureConstants.metaActionCount).pair
    ((vectorCodec (vectorCodec (knowledgeCodec dimension) Acorn.FeatureConstants.primitiveCount)
      Acorn.FeatureConstants.skillCount).pair (demonImagesCodec dimension demonLayout)))).iso
    (fun (control, metaController, skills, demons) => ⟨control, metaController, skills, demons⟩)
    (fun image => (image.control, image.metaController, image.skills, image.demons)) (by intro image; rfl)

/-- Raw lifetime totals, prior to their horizon-specific admission. -/
abbrev SumWords := UInt64 × Binary64

/-- Count precedes the exact binary64 sum. -/
def sumCodec : Codec SumWords := u64Codec.pair binary64Codec

/-- Raw option counters retain the three reason counts in their declared order. -/
def episodesCodec : Codec Lifetime.OptionEpisodes :=
  (u64Codec.pair (u64Codec.pair (vectorCodec u64Codec 3))).iso
    (fun (started, duration, reasons) => ⟨started, duration, reasons⟩)
    (fun record => (record.started, record.duration, record.reasons)) (by intro record; rfl)

/-- Goal totals before the subset and empty-record checks. -/
abbrev GoalWords := UInt64 × UInt64 × UInt64

/-- Attempts, successes, then completed-attempt steps. -/
def goalCodec : Codec GoalWords := u64Codec.pair (u64Codec.pair u64Codec)

/-- Raw fixed-size lifetime payload; column order is part of format 18. -/
structure LifetimeWords where
  /-- Overall reward count and sum. -/
  reward : SumWords
  /-- Four family totals. -/
  rewardByFamily : Vector SumWords 4
  /-- Sixty-four logarithmic reward buckets. -/
  rewardHistory : Vector SumWords Acorn.FeatureConstants.historyBins
  /-- Eleven horizon-relative squared-error totals. -/
  squaredErrors : Vector SumWords demonLayout.length
  /-- Eleven exact return words, in demon order. -/
  returns : Vector Binary32 demonLayout.length
  /-- Eleven exact signed-error words, in demon order. -/
  errors : Vector Binary32 demonLayout.length
  /-- Sixty-four widest-horizon squared-error buckets. -/
  errorHistory : Vector SumWords Acorn.FeatureConstants.historyBins
  /-- All three option episode counters. -/
  options : Vector Lifetime.OptionEpisodes Acorn.FeatureConstants.skillCount
  /-- Four goal-family totals. -/
  goals : Vector GoalWords 4
  /-- Each family's complete fixed multiresolution goal history. -/
  goalCycles : Vector (Vector GoalWords Acorn.FeatureConstants.cycleBins) 4

/-- One ordered schema covers every durable field, including the column-major demons. -/
def lifetimeCodec : Codec LifetimeWords :=
  (sumCodec.pair ((vectorCodec sumCodec 4).pair
    ((vectorCodec sumCodec Acorn.FeatureConstants.historyBins).pair
    ((vectorCodec sumCodec demonLayout.length).pair
    ((vectorCodec binary32Codec demonLayout.length).pair
    ((vectorCodec binary32Codec demonLayout.length).pair
    ((vectorCodec sumCodec Acorn.FeatureConstants.historyBins).pair
    ((vectorCodec episodesCodec Acorn.FeatureConstants.skillCount).pair
    ((vectorCodec goalCodec 4).pair
      (vectorCodec (vectorCodec goalCodec Acorn.FeatureConstants.cycleBins) 4)))))))))).iso
    (fun (reward, family, history, squared, returns, errors, errorHistory, options, goals, cycles) =>
      ⟨reward, family, history, squared, returns, errors, errorHistory, options, goals, cycles⟩)
    (fun r => (r.reward, r.rewardByFamily, r.rewardHistory, r.squaredErrors, r.returns,
      r.errors, r.errorHistory, r.options, r.goals, r.goalCycles)) (by intro r; rfl)

/-- Canonical total of primitive, meta, option-action and demon blocks. -/
def primaryCount : Nat := Acorn.FeatureConstants.primitiveCount + Acorn.FeatureConstants.metaActionCount +
  Acorn.FeatureConstants.skillCount * Acorn.FeatureConstants.primitiveCount + demonLayout.length

/-- Latest replacement: presence tag, lifetime step, then bank unit. -/
def lastCodec : Codec LastWords := u32Codec.pair (u64Codec.pair u16Codec)

/-- One unit's generator origin, birth clock and utility bits. -/
def unitStateCodec : Codec UnitWords := u64Codec.pair (u64Codec.pair binary32Codec)

/-- A format-level count has at most one entry per largest admitted bank slot. -/
abbrev UnitList := { units : List UnitWords // units.length ≤ 65535 }

/-- The count is admitted before any variable-length decoding loop starts. -/
def unitListCodec : Codec UnitList where
  encode units := u32Codec.encode units.val.length.toUInt32 ++ units.val.flatMap unitStateCodec.encode
  decode bytes := do
    let (count, rest) ← u32Codec.decode bytes
    if bound : count.toNat ≤ 65535 then
      match h : decodeList unitStateCodec count.toNat rest with
      | none => none
      | some (units, rest') =>
        some (⟨units, by rw [decodeList_length unitStateCodec count.toNat rest units rest' h]; exact bound⟩,
          rest')
    else none
  roundtrip := by
    intro units suffix
    have exactCount : units.val.length.toUInt32.toNat = units.val.length :=
      Nat.mod_eq_of_lt (by have := units.property; omega)
    simp only [List.append_assoc, u32Codec.roundtrip, bind, Option.bind]
    simp only [exactCount, units.property, ↓reduceDIte]
    split <;> rename_i parsed
    · rw [exactCount, list_roundtrip] at parsed; contradiction
    · rw [exactCount, list_roundtrip] at parsed
      cases parsed
      rfl

/-- Raw generator and tester words: continuation, credit, count, latest event and units. -/
structure TesterWords where
  /-- Generator continuation. -/
  stream : UInt64
  /-- Accrued credit. -/
  credit : UInt32
  /-- Lifetime replacement count. -/
  replaced : UInt64
  /-- Latest replacement. -/
  last : LastWords
  /-- Every unit in bank order. -/
  units : UnitList

/-- The tester block's single ordered schema. -/
def testerCodec : Codec TesterWords :=
  (u64Codec.pair (u32Codec.pair (u64Codec.pair (lastCodec.pair unitListCodec)))).iso
    (fun (stream, credit, replaced, last, units) => ⟨stream, credit, replaced, last, units⟩)
    (fun t => (t.stream, t.credit, t.replaced, t.last, t.units)) (by intro t; rfl)

/-- Receiver-relative raw progress: the header's clock supplies the rest. -/
def TesterWords.progress (words : TesterWords) : ProgressWords :=
  ⟨words.stream, words.credit, words.replaced, words.last, words.units.val⟩

/-- The complete raw signed payload, parameterized only by receiving shape. -/
structure Payload (dimension : Dimension) where
  /-- Complete identity and configuration header. -/
  header : Header
  /-- Exactly three saved objectives. -/
  assignments : Vector AssignmentWords Acorn.FeatureConstants.skillCount
  /-- Every primary learner, in canonical segment order. -/
  primary : PrimaryImage Grid.actions dimension demonLayout
  /-- All durable observation fields. -/
  lifetime : LifetimeWords
  /-- Generator and tester state. -/
  tester : TesterWords

/-- Whole-payload round trip follows from the one shared schema. -/
def payloadCodec (dimension : Dimension) : Codec (Payload dimension) :=
  (headerCodec.pair ((vectorCodec assignmentCodec Acorn.FeatureConstants.skillCount).pair
    ((primaryCodec dimension).pair (lifetimeCodec.pair testerCodec)))).iso
    (fun (header, assignments, primary, lifetime, tester) => ⟨header, assignments, primary, lifetime, tester⟩)
    (fun p => (p.header, p.assignments, p.primary, p.lifetime, p.tester)) (by intro p; rfl)

/-! ## Canonical decoding

Every codec of the format reads back only the bytes that it writes. Each one is built from
canonical codecs by pairs, fixed vectors and representation changes that lose nothing, and
the count of the unit list is the length of the list it reads. -/

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

/-- The assignment codec is canonical. -/
theorem assignmentCodec_canonical : assignmentCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical u32Codec_canonical (Codec.pair_canonical u32Codec_canonical
      (Codec.pair_canonical u32Codec_canonical u32Codec_canonical)))
    fun _ => rfl

/-- The codec of one primary learner is canonical. -/
theorem knowledgeCodec_canonical (dimension : Dimension) : (knowledgeCodec dimension).Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical (vectorCodec_canonical binary32Codec_canonical _)
      (vectorCodec_canonical binary32Codec_canonical _))
    fun _ => rfl

/-- The codec of the demon blocks is canonical for every horizon layout. -/
theorem demonImagesCodec_canonical (dimension : Dimension) :
    ∀ discounts : List Discount, (demonImagesCodec dimension discounts).Canonical
  | [] => Codec.iso_canonical unitCodec_canonical fun _ => rfl
  | _ :: rest =>
    Codec.iso_canonical
      (Codec.pair_canonical (knowledgeCodec_canonical dimension)
        (demonImagesCodec_canonical dimension rest))
      fun _ => rfl

/-- The codec of the primary image is canonical. -/
theorem primaryCodec_canonical (dimension : Dimension) : (primaryCodec dimension).Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical (vectorCodec_canonical (knowledgeCodec_canonical dimension) _)
      (Codec.pair_canonical (vectorCodec_canonical (knowledgeCodec_canonical dimension) _)
      (Codec.pair_canonical
        (vectorCodec_canonical (vectorCodec_canonical (knowledgeCodec_canonical dimension) _) _)
        (demonImagesCodec_canonical dimension demonLayout))))
    fun _ => rfl

/-- The codec of one total is canonical. -/
theorem sumCodec_canonical : sumCodec.Canonical :=
  Codec.pair_canonical u64Codec_canonical binary64Codec_canonical

/-- The codec of the option counters is canonical. -/
theorem episodesCodec_canonical : episodesCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical u64Codec_canonical
      (Codec.pair_canonical u64Codec_canonical (vectorCodec_canonical u64Codec_canonical _)))
    fun _ => rfl

/-- The codec of one goal aggregate is canonical. -/
theorem goalCodec_canonical : goalCodec.Canonical :=
  Codec.pair_canonical u64Codec_canonical
    (Codec.pair_canonical u64Codec_canonical u64Codec_canonical)

/-- The lifetime codec is canonical. -/
theorem lifetimeCodec_canonical : lifetimeCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical sumCodec_canonical
      (Codec.pair_canonical (vectorCodec_canonical sumCodec_canonical _)
      (Codec.pair_canonical (vectorCodec_canonical sumCodec_canonical _)
      (Codec.pair_canonical (vectorCodec_canonical sumCodec_canonical _)
      (Codec.pair_canonical (vectorCodec_canonical binary32Codec_canonical _)
      (Codec.pair_canonical (vectorCodec_canonical binary32Codec_canonical _)
      (Codec.pair_canonical (vectorCodec_canonical sumCodec_canonical _)
      (Codec.pair_canonical (vectorCodec_canonical episodesCodec_canonical _)
      (Codec.pair_canonical (vectorCodec_canonical goalCodec_canonical _)
        (vectorCodec_canonical (vectorCodec_canonical goalCodec_canonical _) _))))))))))
    fun _ => rfl

/-- The codec of the latest replacement is canonical. -/
theorem lastCodec_canonical : lastCodec.Canonical :=
  Codec.pair_canonical u32Codec_canonical
    (Codec.pair_canonical u64Codec_canonical u16Codec_canonical)

/-- The codec of one unit is canonical. -/
theorem unitStateCodec_canonical : unitStateCodec.Canonical :=
  Codec.pair_canonical u64Codec_canonical
    (Codec.pair_canonical u64Codec_canonical binary32Codec_canonical)

/-- The unit-list codec is canonical: the count that it reads is the length of the list that
it returns. -/
theorem unitListCodec_canonical : unitListCodec.Canonical := by
  intro bytes value rest decoded
  cases counted : u32Codec.decode bytes with
  | none => simp [unitListCodec, counted] at decoded
  | some found =>
    obtain ⟨count, tail⟩ := found
    simp only [unitListCodec, counted, bind, Option.bind] at decoded
    split at decoded
    · split at decoded
      · contradiction
      · rename_i units suffix listed
        simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        have length := decodeList_length unitStateCodec count.toNat tail units suffix listed
        obtain ⟨read, unitsRead, tailRead⟩ :=
          decodeListInto_written unitStateCodec_canonical count.toNat tail [] units suffix listed
        simp only [List.reverse_nil, List.nil_append] at unitsRead
        have countWord : units.length.toUInt32 = count := by
          rw [length]
          exact UInt32.toNat_inj.mp (Nat.mod_eq_of_lt count.toNat_lt)
        rw [u32Codec_canonical _ _ _ counted]
        simp only [unitListCodec, countWord, List.append_assoc]
        rw [tailRead, ← unitsRead]
    · contradiction

/-- The tester codec is canonical. -/
theorem testerCodec_canonical : testerCodec.Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical u64Codec_canonical (Codec.pair_canonical u32Codec_canonical
      (Codec.pair_canonical u64Codec_canonical
        (Codec.pair_canonical lastCodec_canonical unitListCodec_canonical))))
    fun _ => rfl

/-- The payload codec is canonical. -/
theorem payloadCodec_canonical (dimension : Dimension) : (payloadCodec dimension).Canonical :=
  Codec.iso_canonical
    (Codec.pair_canonical headerCodec_canonical
      (Codec.pair_canonical (vectorCodec_canonical assignmentCodec_canonical _)
      (Codec.pair_canonical (primaryCodec_canonical dimension)
        (Codec.pair_canonical lifetimeCodec_canonical testerCodec_canonical))))
    fun _ => rfl

end Acorn.Checkpoint
