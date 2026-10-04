/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.SwiftTd

/-!
# Current opaque feature construction

Indices use the receiving dimension; active sets retain first occurrences.
Host channel choices belong to the explicitly declared composition boundary.

Mahmood and Sutton, *Representation Search through Generate and Test*,
AAAI 2013 workshop, PDF page 3 (linear threshold units and feature replacement),
https://armahmood.github.io/files/MS-RepSearch-AAAI-WS-2013.pdf.
The current adaptation samples 32 inputs with replacement from the symbol
positions, hash-binarizes them, and uses threshold zero. It does not implement
the paper's imprinting threshold. A unit's projection is determined by its
recorded generator origin, so the bank is reconstructed from origins alone.
-/
namespace Acorn.Features

/-- An uninterpreted channel and value. -/
structure SensorWord where
  /-- Channel salt. -/
  channel : UInt64
  /-- Channel value. -/
  value : UInt64
  deriving DecidableEq

/-- Append an absent index, preserving every existing position. -/
def insert {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) : SwiftTd.ActiveSet dimension :=
  if h : index ∈ active.indices then active else
    ⟨active.indices ++ [index], by
      simp only [List.nodup_append]
      refine ⟨active.nodup, by simp, ?_⟩
      intro a ha b hb he
      have hb : b = index := by simpa using hb
      exact h ((he.trans hb) ▸ ha)⟩

/-- Insertion adds exactly the supplied membership. -/
theorem mem_insert {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index query : FeatIdx dimension) :
    query ∈ (insert active index).indices ↔ query ∈ active.indices ∨ query = index := by
  unfold insert
  split <;> simp_all

/-- Existing active order is an exact prefix after insertion. -/
theorem insert_order {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) :
    (insert active index).indices = active.indices ++
      (if index ∈ active.indices then [] else [index]) := by
  unfold insert
  split <;> simp_all

/-- Filtering retains the union of prior and incoming membership. -/
theorem mem_fold {dimension : Dimension} (indices : List (FeatIdx dimension))
    (active : SwiftTd.ActiveSet dimension) (query : FeatIdx dimension) :
    query ∈ (indices.foldl insert active).indices ↔
      query ∈ active.indices ∨ query ∈ indices := by
  induction indices generalizing active with
  | nil => simp
  | cons head tail ih => simp [List.foldl_cons, ih, mem_insert, or_assoc]

/-- Insertion needs at most one additional active position. -/
theorem insert_length {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) : (insert active index).indices.length ≤ active.indices.length + 1 := by
  rw [insert_order]
  split <;> simp

/-- First-occurrence filtering cannot create more positions than it reads. -/
theorem fold_length {dimension : Dimension} (indices : List (FeatIdx dimension))
    (active : SwiftTd.ActiveSet dimension) :
    (indices.foldl insert active).indices.length ≤ active.indices.length + indices.length := by
  induction indices generalizing active with
  | nil => simp
  | cons head tail ih =>
    have tailBound := ih (insert active head)
    have headBound := insert_length active head
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- Unique construction keeps a reverse output and dimension-indexed membership.
The membership relation is erased; native updates need no scan of prior indices. -/
structure UniqueBuilder (dimension : Dimension) where
  /-- Reverse first-occurrence order. -/
  reversed : List (FeatIdx dimension)
  /-- Native membership scratch. -/
  seen : Vector Bool dimension.capacity
  /-- Membership agrees at every slot, including after each insertion. -/
  exact : ∀ index, seen[index.val] = decide (index ∈ reversed)
  /-- No prior index repeats. -/
  nodup : reversed.Nodup

/-- Empty output and a clear membership vector. -/
def UniqueBuilder.empty (dimension : Dimension) : UniqueBuilder dimension :=
  ⟨[], Vector.replicate dimension.capacity false, by simp, by simp⟩

/-- Constant-index admission followed by a single slot write and list cons. -/
def UniqueBuilder.add {dimension : Dimension} (builder : UniqueBuilder dimension)
    (index : FeatIdx dimension) : UniqueBuilder dimension :=
  if h : builder.seen[index.val] = true then builder else
    have absent : index ∉ builder.reversed := by
      simpa [builder.exact] using h
    { reversed := index :: builder.reversed
      seen := builder.seen.set index.val true index.isLt
      exact := by
        intro query
        by_cases he : query = index
        · subst query
          simp
        · have hv : query.val ≠ index.val := fun e => he (Fin.ext e)
          simp [Ne.symm hv, builder.exact, he]
      nodup := List.nodup_cons.mpr ⟨absent, builder.nodup⟩ }

/-- Forward first-occurrence output. The scratch dies at this boundary. -/
def UniqueBuilder.finish {dimension : Dimension} (builder : UniqueBuilder dimension) :
    SwiftTd.ActiveSet dimension := ⟨builder.reversed.reverse, by
      apply List.pairwise_reverse.mpr
      exact builder.nodup.imp (fun h => Ne.symm h)⟩

/-- The scratch-backed operation is exactly ordered absent insertion. -/
theorem UniqueBuilder.add_finish {dimension : Dimension} (builder : UniqueBuilder dimension)
    (index : FeatIdx dimension) : (builder.add index).finish = insert builder.finish index := by
  unfold UniqueBuilder.add insert UniqueBuilder.finish
  simp only [builder.exact, decide_eq_true_eq, List.mem_reverse]
  split <;> simp_all [List.reverse_cons]

/-- The efficient fold implements the ordered insertion fold on all inputs. -/
theorem UniqueBuilder.fold_finish {dimension : Dimension} (indices : List (FeatIdx dimension))
    (builder : UniqueBuilder dimension) :
    (indices.foldl UniqueBuilder.add builder).finish = indices.foldl insert builder.finish := by
  induction indices generalizing builder with
  | nil => rfl
  | cons head tail ih => simp [List.foldl_cons, ih, UniqueBuilder.add_finish]

/-- First-occurrence filtering, using one native membership flag per dimension slot. -/
def unique {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    SwiftTd.ActiveSet dimension :=
  (indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)).finish

/-- Complete ordering correspondence with the first-occurrence insertion definition. -/
theorem unique_order {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    unique indices = indices.foldl insert (SwiftTd.ActiveSet.empty dimension) := by
  exact UniqueBuilder.fold_finish indices (UniqueBuilder.empty dimension)

/-- Collisions remove multiplicity without removing any feature. -/
theorem mem_unique {dimension : Dimension} (indices : List (FeatIdx dimension))
    (query : FeatIdx dimension) : query ∈ (unique indices).indices ↔ query ∈ indices := by
  simp [unique_order, mem_fold, SwiftTd.ActiveSet.empty]

/-- Every active set is binary by construction. -/
theorem unique_nodup {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    (unique indices).indices.Nodup := (unique indices).nodup

/-- Legal generator input shape: a positive number of opaque symbol positions. A
world lays its own structure over them, such as a square patch followed by context
words, or a whole grid. -/
structure PatchShape where
  /-- Generator input positions. -/
  inputs : Nat
  /-- There is a position to sample. -/
  positive : 0 < inputs
  /-- Every input position fits a two-byte checksum word. -/
  bounded : inputs ≤ 65536

/-- Sampled input position and sign, legal at storage. -/
structure Sample (shape : PatchShape) where
  /-- Sampled symbol position of the shape. -/
  input : Fin shape.inputs
  /-- True denotes positive one. -/
  positive : Bool

/-- The position reads the high word and the sign the low bit, so they use disjoint bits. -/
def Sample.ofWord (shape : PatchShape) (word : UInt64) : Sample shape where
  input := ⟨(word >>> 32).toNat % shape.inputs, Nat.mod_lt _ shape.positive⟩
  positive := (word &&& 1) != 0

/-- Exactly 32 signed samples. Slots are derived separately from seed and unit. -/
abbrev Projection (shape : PatchShape) := Vector (Sample shape) 32

/-- Fixed-size drawing from the current SplitMix continuation. -/
def drawSamples (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    Vector (Sample shape) count × Rng.SplitMix64 :=
  count.dfold (α := fun i _ => Vector (Sample shape) i × Rng.SplitMix64)
    (fun _ _ (samples, stream) =>
      let (word, next) := stream.next
      (samples.push (Sample.ofWord shape word), next)) (#v[], stream)

/-- One more sample extends the same prefix by the next stream output. -/
theorem drawSamples_succ (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    drawSamples shape (count + 1) stream =
      ((drawSamples shape count stream).1.push
        (Sample.ofWord shape (drawSamples shape count stream).2.next.1),
        (drawSamples shape count stream).2.next.2) := by
  simp only [drawSamples, Nat.dfold_succ]

/-- The generator consumes precisely one wrapping increment per sampled symbol position. -/
theorem drawSamples_stream (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    (drawSamples shape count stream).2.state = stream.state + Rng.increment * count.toUInt64 := by
  induction count with
  | zero => simp [drawSamples]
  | succ count ih =>
    simp only [drawSamples_succ, Rng.SplitMix64.next, ih]
    simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.mul_add, UInt64.add_assoc]

/-- Nonzero bank size fits the durable UInt16 interface. -/
structure BankSize where
  /-- Live units. -/
  count : Nat
  /-- Empty banks are not admitted. -/
  positive : 0 < count
  /-- Current nonzero UInt16 capacity. -/
  bounded : count ≤ 65535

/-- Immutable generate-and-test schedule. Each step accrues one credit per
eligible unit, and every `period` credits replace one unit, so the replacement
rate is `ρ = 1/period` per eligible unit per step. A unit is eligible once its
age exceeds `maturity`. The contribution utility decays by `decay` (η) and
weighs the current contribution by `complement` (1 − η). -/
structure Tester where
  /-- Credits per replacement: `1/ρ`. -/
  period : Nat
  /-- Replacement needs positive accrual. -/
  positive : 0 < period
  /-- The accrued remainder fits its durable UInt32 word. -/
  bounded : period ≤ 4294967296
  /-- Steps of protection after generation. -/
  maturity : Nat
  /-- The utility trace's decay word, η. -/
  decay : Binary32
  /-- The current contribution's weight word, 1 − η. -/
  complement : Binary32

/-- Immutable bank configuration. -/
structure Config where
  /-- Campaign feature salt. -/
  seed : UInt64
  /-- Full public tiling-count word. -/
  tilings : UInt64
  /-- At least one sensory tiling. -/
  tilingsPositive : 0 < tilings.toNat
  /-- Bank capacity. -/
  units : BankSize
  /-- Declared replacement rate, maturity and utility decay. -/
  tester : Tester

/-- Complete live projection cache and future generator state. -/
structure Bank (shape : PatchShape) (config : Config) where
  /-- Fixed-size projections. -/
  projections : Vector (Projection shape) config.units.count
  /-- Replacement generator continuation. -/
  stream : Rng.SplitMix64

/-- Generator words one projection consumes. -/
def projectionStride : UInt64 := Rng.increment * 32

/-- A projection is the next 32 samples after its recorded generator state. -/
def drawProjection (shape : PatchShape) (origin : UInt64) : Projection shape :=
  (drawSamples shape 32 ⟨origin⟩).1

/-- Drawing a projection advances the generator by exactly one stride. -/
theorem drawSamples_projection (shape : PatchShape) (origin : UInt64) :
    drawSamples shape 32 ⟨origin⟩ = (drawProjection shape origin, ⟨origin + projectionStride⟩) := by
  have advanced := drawSamples_stream shape 32 ⟨origin⟩
  refine Prod.ext rfl ?_
  change (drawSamples shape 32 ⟨origin⟩).2 = ⟨origin + Rng.increment * 32⟩
  exact congrArg Rng.SplitMix64.mk advanced

/-- The cache determined by every unit's recorded origin and the continuation. -/
def Bank.build (shape : PatchShape) {config : Config}
    (origins : Vector UInt64 config.units.count) (stream : UInt64) : Bank shape config :=
  ⟨origins.map (drawProjection shape), ⟨stream⟩⟩

/-- The campaign generator's domain-separated key. -/
def generatorKey (config : Config) : UInt64 := Rng.streamKey config.seed 0x1D1D000000000001

/-- Initial units are drawn from one stream in bank order. -/
def initialOrigins (config : Config) : Vector UInt64 config.units.count :=
  Vector.ofFn fun unit => generatorKey config + projectionStride * unit.val.toUInt64

/-- The continuation after every initial unit. -/
def initialStream (config : Config) : UInt64 :=
  generatorKey config + projectionStride * config.units.count.toUInt64

/-- Seed-derived bank with the current domain-separated stream key. -/
def Bank.initial (shape : PatchShape) (config : Config) : Bank shape config :=
  Bank.build shape (initialOrigins config) (initialStream config)

/-- A unit's slot depends on its number and seed, including after replacement. -/
def unitFeature (dimension : Dimension) (config : Config) (unit : Fin config.units.count) :
    FeatIdx dimension :=
  FeatIdx.fromHash dimension (Rng.hash3 (config.seed ^^^ 0x1D) 0x1D unit.val.toUInt64)

/-- Replace one projection using the constructor's stream continuation. -/
def Bank.replace {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (unit : Fin config.units.count) : Bank shape config :=
  let (projection, stream) := drawSamples shape 32 bank.stream
  ⟨bank.projections.set unit.val projection unit.isLt, stream⟩

/-- Replacement changes only the selected projection; aliases retain their own samples. -/
theorem Bank.replace_other {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (unit other : Fin config.units.count) (different : other ≠ unit) :
    (bank.replace unit).projections[other.val] = bank.projections[other.val] := by
  have ne : unit.val ≠ other.val := fun same => different (Fin.ext same.symm)
  simp [Bank.replace, ne]

/-- The selected projection is exactly the next 32 samples, without reseeding. -/
theorem Bank.replace_selected {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (unit : Fin config.units.count) :
    (bank.replace unit).projections[unit.val] = (drawSamples shape 32 bank.stream).1 ∧
    (bank.replace unit).stream = (drawSamples shape 32 bank.stream).2 := by
  simp [Bank.replace]

/-- Replacing a built bank's unit is the bank built with that unit's origin at the
continuation and the continuation one stride later. -/
theorem Bank.build_replace (shape : PatchShape) {config : Config}
    (origins : Vector UInt64 config.units.count) (stream : UInt64) (unit : Fin config.units.count) :
    (Bank.build shape origins stream).replace unit =
      Bank.build shape (origins.set unit.val stream unit.isLt) (stream + projectionStride) := by
  simp only [Bank.replace, Bank.build, drawSamples_projection, Vector.map_set]

/-- Stable identity digest over ordered position/sign triples. This detects
mutation; neither collisions nor equal digests establish representation equality. -/
def Bank.checksum {shape : PatchShape} {config : Config} (bank : Bank shape config) : UInt64 :=
  bank.projections.toList.foldl (fun hash projection =>
    projection.toList.foldl (fun hash sample =>
      Rng.fnvStep (Rng.fnvStep (Rng.fnvStep hash sample.input.val.toUInt8)
        (sample.input.val / 256).toUInt8) (if sample.positive then 1 else 0)) hash) Rng.fnvOffset

/-- Opaque generator input: one 64-bit code per symbol position of the shape. -/
abbrev Patch (shape : PatchShape) := Vector UInt64 shape.inputs

/-- One sample contributes only minus one, zero, or plus one. -/
def sampleTerm {shape : PatchShape} (seed : UInt64) (unit sampleNumber : Nat)
    (patch : Patch shape) (sample : Sample shape) : Int :=
  let code := patch.get sample.input
  let bit := (Rng.hash3 (seed ^^^ unit.toUInt64) sampleNumber.toUInt64 code) &&& 1
  if bit == 0 then 0 else if sample.positive then 1 else -1

/-- Every sample, including every raw input word, belongs to the signed unit range. -/
theorem sampleTerm_bounds {shape : PatchShape} (seed : UInt64) (unit sampleNumber : Nat)
    (patch : Patch shape) (sample : Sample shape) :
    -1 ≤ sampleTerm seed unit sampleNumber patch sample ∧
      sampleTerm seed unit sampleNumber patch sample ≤ 1 := by
  simp only [sampleTerm]
  split
  · omega
  · split <;> omega

/-- A structural integer sum bound avoids any enumeration of patch configurations. -/
theorem signed_sum_bounds (terms : List Int)
    (bounded : ∀ term ∈ terms, -1 ≤ term ∧ term ≤ 1) :
    -(terms.length : Int) ≤ terms.sum ∧ terms.sum ≤ (terms.length : Int) := by
  induction terms with
  | nil => simp
  | cons head tail ih =>
    have headBound := bounded head (by simp)
    have tailBound := ih (fun term member => bounded term (List.mem_cons_of_mem _ member))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Signed projection over exactly 32 terms. -/
def projectionValue {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) : Int :=
  ((bank.projections.get unit).toList.zipIdx.map fun (sample, j) =>
    sampleTerm config.seed unit.val j patch sample).sum

/-- The executing projection fits the current signed accumulator for every input. -/
theorem projectionValue_bounds {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    -32 ≤ projectionValue bank patch unit ∧ projectionValue bank patch unit ≤ 32 := by
  have bounded := signed_sum_bounds
    ((bank.projections.get unit).toList.zipIdx.map fun (sample, j) =>
      sampleTerm config.seed unit.val j patch sample) (by
        intro term member
        obtain ⟨⟨sample, j⟩, _, same⟩ := List.mem_map.mp member
        subst term
        exact sampleTerm_bounds config.seed unit.val j patch sample)
  simpa [projectionValue] using bounded

/-- Each unit's binary output on one input: its signed projection is positive. -/
def Bank.activations {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) : Vector Bool config.units.count :=
  Vector.ofFn fun unit => decide (0 < projectionValue bank patch unit)

/-- Tiling-major sensor words. -/
def tiledFeatures (dimension : Dimension) (config : Config) (words : List SensorWord) :
    List (FeatIdx dimension) :=
  (List.range config.tilings.toNat).flatMap (fun tiling => words.map fun word =>
    FeatIdx.fromHash dimension (Rng.hash3 (config.seed ^^^ tiling.toUInt64)
      word.channel word.value))

/-- Active bank units in bank order, each at its slot. -/
def imprintFeatures (dimension : Dimension) (config : Config)
    (active : Vector Bool config.units.count) : List (FeatIdx dimension) :=
  (List.finRange config.units.count).filterMap (fun unit =>
    if active[unit.val] then some (unitFeature dimension config unit) else none)

/-- Raw order: tiling-major sensor words, then the given active bank units. -/
def rawEncodeWith (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) : List (FeatIdx dimension) :=
  tiledFeatures dimension config words ++ imprintFeatures dimension config active

/-- Raw order: tiling-major sensor words, then positive bank units. -/
def rawEncode (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    List (FeatIdx dimension) :=
  rawEncodeWith dimension config words (bank.activations patch)

/-- Repeated opaque-word maps have an exact structural work count. -/
theorem tiled_length {α β γ : Type} (tiles : List α) (words : List β) (encodeWord : α → β → γ) :
    (tiles.flatMap (fun tile => words.map (encodeWord tile))).length = tiles.length * words.length := by
  induction tiles with
  | nil => simp
  | cons tile rest ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- Every admitted tiling word, bank size and unit output has a derived raw-encoding bound. -/
theorem rawEncodeWith_length (dimension : Dimension) (config : Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (rawEncodeWith dimension config words active).length ≤
      config.tilings.toNat * words.length + config.units.count := by
  have imprintBound := List.length_filterMap_le
    (fun unit : Fin config.units.count =>
      if active[unit.val] then some (unitFeature dimension config unit) else none)
    (List.finRange config.units.count)
  simp only [List.length_finRange] at imprintBound
  simp only [rawEncodeWith, tiledFeatures, imprintFeatures, List.length_append, tiled_length,
    List.length_range]
  omega

/-- Every admitted tiling word and bank size has a derived raw-encoding bound. -/
theorem rawEncode_length (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    (rawEncode dimension bank words patch).length ≤
      config.tilings.toNat * words.length + config.units.count :=
  rawEncodeWith_length dimension config words (bank.activations patch)

/-- Encoding from supplied unit outputs, the argument SwiftTD consumes. -/
def encodeWith (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) : SwiftTd.ActiveSet dimension :=
  unique (rawEncodeWith dimension config words active)

/-- Encoding returns the actual binary-feature argument consumed by SwiftTD. -/
def encode (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    SwiftTd.ActiveSet dimension := encodeWith dimension config words (bank.activations patch)

/-- Every raw feature survives and every active feature came from the raw encoding. -/
theorem encode_membership (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape)
    (index : FeatIdx dimension) :
    index ∈ (encode dimension bank words patch).indices ↔
      index ∈ rawEncode dimension bank words patch := mem_unique _ _

/-- The unique encoding from any unit outputs satisfies the raw-input resource bound. -/
theorem encodeWith_length (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) :
    (encodeWith dimension config words active).indices.length ≤
      config.tilings.toNat * words.length + config.units.count := by
  have filtered := fold_length (rawEncodeWith dimension config words active)
    (SwiftTd.ActiveSet.empty dimension)
  have rawBound := rawEncodeWith_length dimension config words active
  rw [← unique_order] at filtered
  simp only [SwiftTd.ActiveSet.empty, List.length_nil, Nat.zero_add] at filtered
  simpa [encodeWith] using Nat.le_trans filtered rawBound

/-- The actual unique encoding satisfies the same raw-input resource bound. -/
theorem encode_length (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    (encode dimension bank words patch).indices.length ≤
      config.tilings.toNat * words.length + config.units.count :=
  encodeWith_length dimension config words (bank.activations patch)

end Acorn.Features
