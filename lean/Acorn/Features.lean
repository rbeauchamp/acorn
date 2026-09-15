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
The current adaptation samples 32 cells with replacement, hash-binarizes inputs,
and uses threshold zero. It does not implement the paper's imprinting threshold.
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

/-- Legal patch side: odd and byte-representable. -/
structure PatchShape where
  /-- Side length. -/
  side : Nat
  /-- A centre exists. -/
  odd : side % 2 = 1
  /-- Coordinates fit the byte interface. -/
  bounded : side ≤ 255

/-- Odd natural sides are nonempty. -/
theorem PatchShape.positive (shape : PatchShape) : 0 < shape.side := by
  have := shape.odd
  omega

/-- Sampled cell and sign, with coordinates legal at storage. -/
structure Sample (shape : PatchShape) where
  /-- Row in the receiving patch. -/
  row : Fin shape.side
  /-- Column in the receiving patch. -/
  col : Fin shape.side
  /-- True denotes positive one. -/
  positive : Bool

/-- Extract columns, rows and signs in the current bit order. -/
def Sample.ofWord (shape : PatchShape) (word : UInt64) : Sample shape where
  row := ⟨(word >>> 8).toNat % shape.side, Nat.mod_lt _ shape.positive⟩
  col := ⟨word.toNat % shape.side, Nat.mod_lt _ shape.positive⟩
  positive := ((word >>> 16) &&& 1) != 0

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

/-- The generator consumes precisely one wrapping increment per sampled cell. -/
theorem drawSamples_stream (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    (drawSamples shape count stream).2.state = stream.state + Rng.increment * count.toUInt64 := by
  induction count with
  | zero => simp [drawSamples]
  | succ count ih =>
    simp only [drawSamples_succ, Rng.SplitMix64.next, ih]
    simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.mul_add, UInt64.add_assoc]

/-- Nonzero bank size fits the durable UInt16 interface. -/
structure BankSize where
  /-- Live units and maximum transcript length. -/
  count : Nat
  /-- Empty banks are not admitted. -/
  positive : 0 < count
  /-- Current nonzero UInt16 capacity. -/
  bounded : count ≤ 65535

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

/-- Complete live projection and future generator state. -/
structure Bank (shape : PatchShape) (config : Config) where
  /-- Fixed-size projections. -/
  projections : Vector (Projection shape) config.units.count
  /-- Replacement generator continuation. -/
  stream : Rng.SplitMix64

/-- Draw each projection from one stream, in bank order. -/
def drawBank (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    Vector (Projection shape) count × Rng.SplitMix64 :=
  count.dfold (α := fun i _ => Vector (Projection shape) i × Rng.SplitMix64)
    (fun _ _ (projections, stream) =>
      let (projection, next) := drawSamples shape 32 stream
      (projections.push projection, next)) (#v[], stream)

/-- Each bank extension draws exactly the next projection from the same stream. -/
theorem drawBank_succ (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    drawBank shape (count + 1) stream =
      ((drawBank shape count stream).1.push
        (drawSamples shape 32 (drawBank shape count stream).2).1,
        (drawSamples shape 32 (drawBank shape count stream).2).2) := by
  simp only [drawBank, Nat.dfold_succ]

/-- Seed-derived bank with the current domain-separated stream key. -/
def Bank.initial (shape : PatchShape) (config : Config) : Bank shape config :=
  let (projections, stream) := drawBank shape config.units.count
    ⟨Rng.streamKey config.seed 0x1D1D000000000001⟩
  ⟨projections, stream⟩

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

/-- Stable identity digest over ordered row/column/sign triples. This detects
mutation; neither collisions nor equal digests establish representation equality. -/
def Bank.checksum {shape : PatchShape} {config : Config} (bank : Bank shape config) : UInt64 :=
  bank.projections.toList.foldl (fun hash projection =>
    projection.toList.foldl (fun hash sample =>
      Rng.fnvStep (Rng.fnvStep (Rng.fnvStep hash sample.row.val.toUInt8)
        sample.col.val.toUInt8) (if sample.positive then 1 else 0)) hash) Rng.fnvOffset

/-- Square opaque patch with the sampled-coordinate shape. -/
abbrev Patch (shape : PatchShape) := Vector (Vector UInt8 shape.side) shape.side

/-- One sample contributes only minus one, zero, or plus one. -/
def sampleTerm {shape : PatchShape} (seed : UInt64) (unit sampleNumber : Nat)
    (patch : Patch shape) (sample : Sample shape) : Int :=
  let code := (patch.get sample.row).get sample.col
  let bit := (Rng.hash3 (seed ^^^ unit.toUInt64) sampleNumber.toUInt64 code.toUInt64) &&& 1
  if bit == 0 then 0 else if sample.positive then 1 else -1

/-- Every sample, including every raw patch byte, belongs to the signed unit range. -/
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

/-- Raw order: tiling-major sensor words, then positive bank units. -/
def rawEncode (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    List (FeatIdx dimension) :=
  (List.range config.tilings.toNat).flatMap (fun tiling => words.map fun word =>
    FeatIdx.fromHash dimension (Rng.hash3 (config.seed ^^^ tiling.toUInt64)
      word.channel word.value)) ++
  (List.finRange config.units.count).filterMap (fun unit =>
    if 0 < projectionValue bank patch unit then some (unitFeature dimension config unit) else none)

/-- Repeated opaque-word maps have an exact structural work count. -/
theorem tiled_length {α β γ : Type} (tiles : List α) (words : List β) (encodeWord : α → β → γ) :
    (tiles.flatMap (fun tile => words.map (encodeWord tile))).length = tiles.length * words.length := by
  induction tiles with
  | nil => simp
  | cons tile rest ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- Every admitted tiling word and bank size has a derived raw-encoding bound. -/
theorem rawEncode_length (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    (rawEncode dimension bank words patch).length ≤
      config.tilings.toNat * words.length + config.units.count := by
  have imprintBound := List.length_filterMap_le
    (fun unit : Fin config.units.count =>
      if 0 < projectionValue bank patch unit then some (unitFeature dimension config unit) else none)
    (List.finRange config.units.count)
  simp only [List.length_finRange] at imprintBound
  simp only [rawEncode, List.length_append, tiled_length, List.length_range]
  omega

/-- Encoding returns the actual binary-feature argument consumed by SwiftTD. -/
def encode (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    SwiftTd.ActiveSet dimension := unique (rawEncode dimension bank words patch)

/-- Every raw feature survives and every active feature came from the raw encoding. -/
theorem encode_membership (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape)
    (index : FeatIdx dimension) :
    index ∈ (encode dimension bank words patch).indices ↔
      index ∈ rawEncode dimension bank words patch := mem_unique _ _

/-- The actual unique encoding satisfies the same raw-input resource bound. -/
theorem encode_length (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    (encode dimension bank words patch).indices.length ≤
      config.tilings.toNat * words.length + config.units.count := by
  have filtered := fold_length (rawEncode dimension bank words patch) (SwiftTd.ActiveSet.empty dimension)
  have rawBound := rawEncode_length dimension bank words patch
  rw [← unique_order] at filtered
  simp only [SwiftTd.ActiveSet.empty, List.length_nil, Nat.zero_add] at filtered
  simpa [encode] using Nat.le_trans filtered rawBound

end Acorn.Features
