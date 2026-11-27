import Acorn.SwiftTd

namespace Acorn.Features

structure SensorWord where
  channel : UInt64
  value : UInt64
  deriving DecidableEq

def insertCosted {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) : Costed (SwiftTd.ActiveSet dimension) :=
  Costed.charge .insert do
    let present ← Costed.attach (Costed.mem index active.indices dimension.wordBound)
    Costed.dite (present.val = true) (fun _ => Costed.pure active) fun absent => do
      have h : index ∉ active.indices := fun member => absent (by
        rw [present.property, Costed.mem_val]
        exact decide_eq_true member)
      let joined ← Costed.attach (Costed.append active.indices [index])
      Costed.pure ⟨joined.val, by
        rw [joined.property, Costed.append_val]
        simp only [List.nodup_append]
        refine ⟨active.nodup, by simp, ?_⟩
        intro a ha b hb he
        have hb : b = index := by simpa using hb
        exact h ((he.trans hb) ▸ ha)⟩

def insert {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) : SwiftTd.ActiveSet dimension :=
  (insertCosted active index).val

theorem insert_def {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) :
    insert active index = if h : index ∈ active.indices then active else
      ⟨active.indices ++ [index], by
        simp only [List.nodup_append]
        refine ⟨active.nodup, by simp, ?_⟩
        intro a ha b hb he
        have hb : b = index := by simpa using hb
        exact h ((he.trans hb) ▸ ha)⟩ := by
  show (if present : decide (index ∈ active.indices) = true then active else _) = _
  split <;> split
  · rfl
  · rename_i present absent
    exact absurd (of_decide_eq_true present) absent
  · rename_i absent present
    exact absurd (decide_eq_true present) absent
  · rfl

theorem mem_insert {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index query : FeatIdx dimension) :
    query ∈ (insert active index).indices ↔ query ∈ active.indices ∨ query = index := by
  rw [insert_def]
  split <;> simp_all

theorem insert_order {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) :
    (insert active index).indices = active.indices ++
      (if index ∈ active.indices then [] else [index]) := by
  rw [insert_def]
  split <;> simp_all

theorem mem_fold {dimension : Dimension} (indices : List (FeatIdx dimension))
    (active : SwiftTd.ActiveSet dimension) (query : FeatIdx dimension) :
    query ∈ (indices.foldl insert active).indices ↔
      query ∈ active.indices ∨ query ∈ indices := by
  induction indices generalizing active with
  | nil => simp
  | cons head tail ih => simp [List.foldl_cons, ih, mem_insert, or_assoc]

theorem insert_length {dimension : Dimension} (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) : (insert active index).indices.length ≤ active.indices.length + 1 := by
  rw [insert_order]
  split <;> simp

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

structure UniqueBuilder (dimension : Dimension) where
  reversed : List (FeatIdx dimension)
  seen : Vector Bool dimension.capacity
  exact : ∀ index, seen[index.val] = decide (index ∈ reversed)
  nodup : reversed.Nodup

def UniqueBuilder.emptyCosted (dimension : Dimension) : Costed (UniqueBuilder dimension) := do
  let reversed : List (FeatIdx dimension) := []
  let seen ← Costed.attach (Costed.replicate dimension.capacity false)
  Costed.pure ⟨reversed, seen.val, by rw [seen.property, Costed.replicate_val]; simp [reversed],
    by simp [reversed]⟩

def UniqueBuilder.empty (dimension : Dimension) : UniqueBuilder dimension :=
  (UniqueBuilder.emptyCosted dimension).val

theorem UniqueBuilder.empty_def (dimension : Dimension) :
    UniqueBuilder.empty dimension =
      ⟨[], Vector.replicate dimension.capacity false, by simp, by simp⟩ := rfl

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

def UniqueBuilder.finishCosted {dimension : Dimension} (builder : UniqueBuilder dimension) :
    Costed (SwiftTd.ActiveSet dimension) := do
  let forward ← Costed.attach (Costed.reverse builder.reversed)
  Costed.pure ⟨forward.val, by
    rw [forward.property, Costed.reverse_val]
    apply List.pairwise_reverse.mpr
    exact builder.nodup.imp (fun h => Ne.symm h)⟩

def UniqueBuilder.finish {dimension : Dimension} (builder : UniqueBuilder dimension) :
    SwiftTd.ActiveSet dimension :=
  builder.finishCosted.val

theorem UniqueBuilder.finish_def {dimension : Dimension} (builder : UniqueBuilder dimension) :
    builder.finish = ⟨builder.reversed.reverse, by
      apply List.pairwise_reverse.mpr
      exact builder.nodup.imp (fun h => Ne.symm h)⟩ := rfl

theorem UniqueBuilder.add_finish {dimension : Dimension} (builder : UniqueBuilder dimension)
    (index : FeatIdx dimension) : (builder.add index).finish = insert builder.finish index := by
  simp only [UniqueBuilder.finish_def]
  unfold UniqueBuilder.add
  rw [insert_def]
  simp only [builder.exact, decide_eq_true_eq, List.mem_reverse]
  split <;> simp_all [List.reverse_cons]

theorem UniqueBuilder.fold_finish {dimension : Dimension} (indices : List (FeatIdx dimension))
    (builder : UniqueBuilder dimension) :
    (indices.foldl UniqueBuilder.add builder).finish = indices.foldl insert builder.finish := by
  induction indices generalizing builder with
  | nil => rfl
  | cons head tail ih => simp [List.foldl_cons, ih, UniqueBuilder.add_finish]

def uniqueCosted {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    Costed (SwiftTd.ActiveSet dimension) := do
  let empty ← UniqueBuilder.emptyCosted dimension
  let built ← Costed.foldl (fun builder index => Costed.op .uniqueAdd (builder.add index)) empty
    indices
  built.finishCosted

def unique {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    SwiftTd.ActiveSet dimension :=
  (uniqueCosted indices).val

theorem unique_def {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    unique indices = (indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)).finish :=
  rfl

theorem unique_order {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    unique indices = indices.foldl insert (SwiftTd.ActiveSet.empty dimension) := by
  exact UniqueBuilder.fold_finish indices (UniqueBuilder.empty dimension)

theorem mem_unique {dimension : Dimension} (indices : List (FeatIdx dimension))
    (query : FeatIdx dimension) : query ∈ (unique indices).indices ↔ query ∈ indices := by
  simp [unique_order, mem_fold, SwiftTd.ActiveSet.empty]

theorem unique_nodup {dimension : Dimension} (indices : List (FeatIdx dimension)) :
    (unique indices).indices.Nodup := (unique indices).nodup

structure PatchShape where
  inputs : Nat
  positive : 0 < inputs
  bounded : inputs ≤ 65536

structure Sample (shape : PatchShape) where
  input : Fin shape.inputs
  positive : Bool

def Sample.ofWord (shape : PatchShape) (word : UInt64) : Sample shape where
  input := ⟨(word >>> 32).toNat % shape.inputs, Nat.mod_lt _ shape.positive⟩
  positive := (word &&& 1) != 0

abbrev Projection (shape : PatchShape) := Vector (Sample shape) 32

def drawSamples (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    Vector (Sample shape) count × Rng.SplitMix64 :=
  count.dfold (α := fun i _ => Vector (Sample shape) i × Rng.SplitMix64)
    (fun _ _ (samples, stream) =>
      let (word, next) := stream.next
      (samples.push (Sample.ofWord shape word), next)) (#v[], stream)

theorem drawSamples_succ (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    drawSamples shape (count + 1) stream =
      ((drawSamples shape count stream).1.push
        (Sample.ofWord shape (drawSamples shape count stream).2.next.1),
        (drawSamples shape count stream).2.next.2) := by
  simp only [drawSamples, Nat.dfold_succ]

theorem drawSamples_stream (shape : PatchShape) (count : Nat) (stream : Rng.SplitMix64) :
    (drawSamples shape count stream).2.state = stream.state + Rng.increment * count.toUInt64 := by
  induction count with
  | zero => simp [drawSamples]
  | succ count ih =>
    simp only [drawSamples_succ, Rng.SplitMix64.next, ih]
    simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.mul_add, UInt64.add_assoc]

structure BankSize where
  count : Nat
  positive : 0 < count
  bounded : count ≤ 65535

structure Tester where
  period : Nat
  positive : 0 < period
  bounded : period ≤ 4294967296
  maturity : Nat
  decay : Binary32
  complement : Binary32

structure Config where
  seed : UInt64
  tilings : UInt64
  tilingsPositive : 0 < tilings.toNat
  units : BankSize
  tester : Tester

structure Bank (shape : PatchShape) (config : Config) where
  projections : Vector (Projection shape) config.units.count
  stream : Rng.SplitMix64

def projectionStride : UInt64 := Rng.increment * 32

def drawProjection (shape : PatchShape) (origin : UInt64) : Projection shape :=
  (drawSamples shape 32 ⟨origin⟩).1

theorem drawSamples_projection (shape : PatchShape) (origin : UInt64) :
    drawSamples shape 32 ⟨origin⟩ = (drawProjection shape origin, ⟨origin + projectionStride⟩) := by
  have advanced := drawSamples_stream shape 32 ⟨origin⟩
  refine Prod.ext rfl ?_
  change (drawSamples shape 32 ⟨origin⟩).2 = ⟨origin + Rng.increment * 32⟩
  exact congrArg Rng.SplitMix64.mk advanced

def Bank.build (shape : PatchShape) {config : Config}
    (origins : Vector UInt64 config.units.count) (stream : UInt64) : Bank shape config :=
  ⟨origins.map (drawProjection shape), ⟨stream⟩⟩

def generatorKey (config : Config) : UInt64 := Rng.streamKey config.seed 0x1D1D000000000001

def initialOrigins (config : Config) : Vector UInt64 config.units.count :=
  Vector.ofFn fun unit => generatorKey config + projectionStride * unit.val.toUInt64

def initialStream (config : Config) : UInt64 :=
  generatorKey config + projectionStride * config.units.count.toUInt64

def Bank.initial (shape : PatchShape) (config : Config) : Bank shape config :=
  Bank.build shape (initialOrigins config) (initialStream config)

def unitFeature (dimension : Dimension) (config : Config) (unit : Fin config.units.count) :
    FeatIdx dimension :=
  FeatIdx.fromHash dimension (Rng.hash3 (config.seed ^^^ 0x1D) 0x1D unit.val.toUInt64)

def Bank.replace {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (unit : Fin config.units.count) : Bank shape config :=
  let (projection, stream) := drawSamples shape 32 bank.stream
  ⟨bank.projections.set unit.val projection unit.isLt, stream⟩

theorem Bank.replace_other {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (unit other : Fin config.units.count) (different : other ≠ unit) :
    (bank.replace unit).projections[other.val] = bank.projections[other.val] := by
  have ne : unit.val ≠ other.val := fun same => different (Fin.ext same.symm)
  simp [Bank.replace, ne]

theorem Bank.replace_selected {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (unit : Fin config.units.count) :
    (bank.replace unit).projections[unit.val] = (drawSamples shape 32 bank.stream).1 ∧
    (bank.replace unit).stream = (drawSamples shape 32 bank.stream).2 := by
  simp [Bank.replace]

theorem Bank.build_replace (shape : PatchShape) {config : Config}
    (origins : Vector UInt64 config.units.count) (stream : UInt64) (unit : Fin config.units.count) :
    (Bank.build shape origins stream).replace unit =
      Bank.build shape (origins.set unit.val stream unit.isLt) (stream + projectionStride) := by
  simp only [Bank.replace, Bank.build, drawSamples_projection, Vector.map_set]

def Bank.checksum {shape : PatchShape} {config : Config} (bank : Bank shape config) : UInt64 :=
  bank.projections.toList.foldl (fun hash projection =>
    projection.toList.foldl (fun hash sample =>
      Rng.fnvStep (Rng.fnvStep (Rng.fnvStep hash sample.input.val.toUInt8)
        (sample.input.val / 256).toUInt8) (if sample.positive then 1 else 0)) hash) Rng.fnvOffset

abbrev Patch (shape : PatchShape) := Vector UInt64 shape.inputs

def sampleTerm {shape : PatchShape} (seed : UInt64) (unit sampleNumber : Nat)
    (patch : Patch shape) (sample : Sample shape) : Int :=
  let code := patch.get sample.input
  let bit := (Rng.hash3 (seed ^^^ unit.toUInt64) sampleNumber.toUInt64 code) &&& 1
  if bit == 0 then 0 else if sample.positive then 1 else -1

theorem sampleTerm_bounds {shape : PatchShape} (seed : UInt64) (unit sampleNumber : Nat)
    (patch : Patch shape) (sample : Sample shape) :
    -1 ≤ sampleTerm seed unit sampleNumber patch sample ∧
      sampleTerm seed unit sampleNumber patch sample ≤ 1 := by
  simp only [sampleTerm]
  split
  · omega
  · split <;> omega

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

def projectionValueCosted {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) : Costed Int := do
  let start := 0
  let samples ← Costed.toList (bank.projections.get unit)
  let numbered ← Costed.zipIdx samples start
  let terms ← Costed.map (fun (sample, j) =>
    Costed.op .sampleTerm (sampleTerm config.seed unit.val j patch sample)) numbered
  Costed.sum terms

def projectionValue {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) : Int :=
  (projectionValueCosted bank patch unit).val

theorem projectionValue_def {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    projectionValue bank patch unit =
      ((bank.projections.get unit).toList.zipIdx.map fun (sample, j) =>
        sampleTerm config.seed unit.val j patch sample).sum := rfl

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
  simpa [projectionValue_def] using bounded

def Bank.activationsCosted {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) : Costed (Vector Bool config.units.count) :=
  Costed.ofFn fun unit => do
    let zero : Int := 0
    let value ← projectionValueCosted bank patch unit
    Costed.op .activation (decide (zero < value))

def Bank.activations {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) : Vector Bool config.units.count :=
  (bank.activationsCosted patch).val

theorem Bank.activations_def {shape : PatchShape} {config : Config} (bank : Bank shape config)
    (patch : Patch shape) :
    bank.activations patch = Vector.ofFn fun unit => decide (0 < projectionValue bank patch unit) :=
  rfl

def tiledFeaturesCosted (dimension : Dimension) (config : Config) (words : List SensorWord) :
    Costed (List (FeatIdx dimension)) := do
  let tilings ← Costed.range config.tilings.toNat
  Costed.flatMap (fun tiling => Costed.map (fun word => Costed.op .hashFeature
    (FeatIdx.fromHash dimension (Rng.hash3 (config.seed ^^^ tiling.toUInt64)
      word.channel word.value))) words) tilings

def tiledFeatures (dimension : Dimension) (config : Config) (words : List SensorWord) :
    List (FeatIdx dimension) :=
  (tiledFeaturesCosted dimension config words).val

theorem tiledFeatures_def (dimension : Dimension) (config : Config) (words : List SensorWord) :
    tiledFeatures dimension config words =
      (List.range config.tilings.toNat).flatMap (fun tiling => words.map fun word =>
        FeatIdx.fromHash dimension (Rng.hash3 (config.seed ^^^ tiling.toUInt64)
          word.channel word.value)) := rfl

def imprintFeaturesCosted (dimension : Dimension) (config : Config)
    (active : Vector Bool config.units.count) : Costed (List (FeatIdx dimension)) := do
  let units ← Costed.finRange config.units.count
  Costed.filterMap (fun unit => Costed.op .imprint
    (if active[unit.val] then some (unitFeature dimension config unit) else none)) units

def imprintFeatures (dimension : Dimension) (config : Config)
    (active : Vector Bool config.units.count) : List (FeatIdx dimension) :=
  (imprintFeaturesCosted dimension config active).val

theorem imprintFeatures_def (dimension : Dimension) (config : Config)
    (active : Vector Bool config.units.count) :
    imprintFeatures dimension config active =
      (List.finRange config.units.count).filterMap (fun unit =>
        if active[unit.val] then some (unitFeature dimension config unit) else none) := rfl

def rawEncodeWithCosted (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) : Costed (List (FeatIdx dimension)) := do
  let tiled ← tiledFeaturesCosted dimension config words
  let imprinted ← imprintFeaturesCosted dimension config active
  Costed.append tiled imprinted

def rawEncodeWith (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) : List (FeatIdx dimension) :=
  (rawEncodeWithCosted dimension config words active).val

theorem rawEncodeWith_def (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) :
    rawEncodeWith dimension config words active =
      tiledFeatures dimension config words ++ imprintFeatures dimension config active := rfl

def rawEncode (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    List (FeatIdx dimension) :=
  rawEncodeWith dimension config words (bank.activations patch)

theorem tiled_length {α β γ : Type} (tiles : List α) (words : List β) (encodeWord : α → β → γ) :
    (tiles.flatMap (fun tile => words.map (encodeWord tile))).length = tiles.length * words.length := by
  induction tiles with
  | nil => simp
  | cons tile rest ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem rawEncodeWith_length (dimension : Dimension) (config : Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (rawEncodeWith dimension config words active).length ≤
      config.tilings.toNat * words.length + config.units.count := by
  have imprintBound := List.length_filterMap_le
    (fun unit : Fin config.units.count =>
      if active[unit.val] then some (unitFeature dimension config unit) else none)
    (List.finRange config.units.count)
  simp only [List.length_finRange] at imprintBound
  simp only [rawEncodeWith_def, tiledFeatures_def, imprintFeatures_def, List.length_append,
    tiled_length,
    List.length_range]
  omega

theorem rawEncode_length (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    (rawEncode dimension bank words patch).length ≤
      config.tilings.toNat * words.length + config.units.count :=
  rawEncodeWith_length dimension config words (bank.activations patch)

def encodeWithCosted (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) : Costed (SwiftTd.ActiveSet dimension) := do
  let raw ← rawEncodeWithCosted dimension config words active
  uniqueCosted raw

def encodeWith (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) : SwiftTd.ActiveSet dimension :=
  (encodeWithCosted dimension config words active).val

theorem encodeWith_def (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) :
    encodeWith dimension config words active =
      unique (rawEncodeWith dimension config words active) := rfl

def encode (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    SwiftTd.ActiveSet dimension := encodeWith dimension config words (bank.activations patch)

theorem encode_membership (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape)
    (index : FeatIdx dimension) :
    index ∈ (encode dimension bank words patch).indices ↔
      index ∈ rawEncode dimension bank words patch := mem_unique _ _

theorem encodeWith_length (dimension : Dimension) (config : Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) :
    (encodeWith dimension config words active).indices.length ≤
      config.tilings.toNat * words.length + config.units.count := by
  have filtered := fold_length (rawEncodeWith dimension config words active)
    (SwiftTd.ActiveSet.empty dimension)
  have rawBound := rawEncodeWith_length dimension config words active
  rw [← unique_order] at filtered
  simp only [SwiftTd.ActiveSet.empty, List.length_nil, Nat.zero_add] at filtered
  simpa [encodeWith_def] using Nat.le_trans filtered rawBound

theorem encode_length (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    (encode dimension bank words patch).indices.length ≤
      config.tilings.toNat * words.length + config.units.count :=
  encodeWith_length dimension config words (bank.activations patch)

end Acorn.Features
