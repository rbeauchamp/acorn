/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Codec
import Acorn.Host.AgentAdmission

/-!
# Checkpoint format 14

Field order, widths and fixed collection shapes match `src/agent/checkpoint.rs`
and the `durable_record!` declaration in `src/agent/lifetime.rs`. Structural
words remain untrusted until receiver-relative admission. Knowledge accepts all
binary32 words and is projected only by each receiving learner's closed rule.
-/
namespace Acorn.Checkpoint
open Features Handcrafted

/-- Exact format-14 header after the eight-byte magic. -/
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
  /-- Canonical Boolean pending-ranking word. -/
  pending : UInt32

/-- The header's single ordered schema drives both writing and reading. -/
def headerCodec : Codec Header :=
  (u32Codec.pair (u32Codec.pair (u32Codec.pair (u64Codec.pair (u64Codec.pair
    (u32Codec.pair (binary32Codec.pair (u64Codec.pair (u32Codec.pair
      (u32Codec.pair u32Codec)))))))))).iso
    (fun (version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported, pending) =>
      ⟨version, capacity, learners, seed, clock, criterion, gain, tilings, units, supported, pending⟩)
    (fun h => (h.version, h.capacity, h.learners, h.seed, h.clock, h.criterion, h.gain,
      h.tilings, h.units, h.supported, h.pending)) (by intro h; rfl)

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
def primaryCodec (dimension : Dimension) : Codec (PrimaryImage dimension demonLayout) :=
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

/-- Raw fixed-size lifetime payload; column order is part of format 14. -/
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

/-- Replacement event: lifetime step, then bank unit. -/
def eventCodec : Codec (UInt64 × UInt16) := u64Codec.pair u16Codec

/-- A format-level count has at most one event per largest admitted bank slot. -/
abbrev Transcript := { events : List (UInt64 × UInt16) // events.length ≤ 65535 }

/-- The count is admitted before any variable-length decoding loop starts. -/
def transcriptCodec : Codec Transcript where
  encode events := u32Codec.encode events.val.length.toUInt32 ++ events.val.flatMap eventCodec.encode
  decode bytes := do
    let (count, rest) ← u32Codec.decode bytes
    if bound : count.toNat ≤ 65535 then
      match h : decodeList eventCodec count.toNat rest with
      | none => none
      | some (events, rest') =>
        some (⟨events, by rw [decodeList_length eventCodec count.toNat rest events rest' h]; exact bound⟩, rest')
    else none
  roundtrip := by
    intro events suffix
    have exactCount : events.val.length.toUInt32.toNat = events.val.length :=
      Nat.mod_eq_of_lt (by have := events.property; omega)
    simp only [List.append_assoc, u32Codec.roundtrip, bind, Option.bind]
    simp only [exactCount, events.property, ↓reduceDIte]
    split <;> rename_i parsed
    · rw [exactCount, list_roundtrip] at parsed; contradiction
    · rw [exactCount, list_roundtrip] at parsed
      cases parsed
      rfl

/-- The complete raw signed payload, parameterized only by receiving shape. -/
structure Payload (dimension : Dimension) where
  /-- Complete identity and configuration header. -/
  header : Header
  /-- Exactly three saved objectives. -/
  assignments : Vector AssignmentWords Acorn.FeatureConstants.skillCount
  /-- Every primary learner, in canonical segment order. -/
  primary : PrimaryImage dimension demonLayout
  /-- All durable observation fields. -/
  lifetime : LifetimeWords
  /-- Bounded replacement transcript. -/
  events : Transcript

/-- Whole-payload round trip follows from the one shared schema. -/
def payloadCodec (dimension : Dimension) : Codec (Payload dimension) :=
  (headerCodec.pair ((vectorCodec assignmentCodec Acorn.FeatureConstants.skillCount).pair
    ((primaryCodec dimension).pair (lifetimeCodec.pair transcriptCodec)))).iso
    (fun (header, assignments, primary, lifetime, events) => ⟨header, assignments, primary, lifetime, events⟩)
    (fun p => (p.header, p.assignments, p.primary, p.lifetime, p.events)) (by intro p; rfl)

end Acorn.Checkpoint
