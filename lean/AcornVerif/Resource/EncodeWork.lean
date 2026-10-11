/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Agent
import AcornVerif.Resource.LearnerWork

/-!
# Work of the encoding of a frame

Twins of the words the coder reads (`Agent.words`) and the encoding of a frame (`Agent.frame`). The
clock advance is charged under the `choose` site in `AcornVerif.Resource.StepWork`. The words are
the world's frame words and one feedback word for each stored prediction. Each generated unit sums
32 samples of the frame's patch. The sensor words are hashed once for each tiling, the active units
are appended, and the list is made unique with one membership flag for each feature slot. The flags
are written in full for every frame, so the encoding's work includes the capacity of the feature
space whatever the frame (`Features.UniqueBuilder.empty`).
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-! ## The words the coder reads -/

/-- The costed recursion of `PredictionCache.words`: one read for each stored prediction, and a
visit for its end. -/
def cacheWordsRun (κ : Costs) : {discounts : List Discount} → PredictionCache discounts →
    Costed (List Binary32)
  | _, .nil => Costed.op (κ .visit) []
  | _, .cons value rest => do
    let tail ← cacheWordsRun κ rest
    Costed.op (κ .visit + κ .read) (value.value :: tail)

theorem cacheWordsRun_val (κ : Costs) {discounts : List Discount}
    (cache : PredictionCache discounts) : (cacheWordsRun κ cache).val = cache.words := by
  induction cache with
  | nil => rfl
  | cons value rest ih =>
    simp only [cacheWordsRun, Costed.bind_val, ih]
    rfl

theorem cacheWordsRun_work (κ : Costs) {discounts : List Discount}
    (cache : PredictionCache discounts) :
    (cacheWordsRun κ cache).work ≤ pass (κ .visit) discounts.length (κ .read) := by
  induction cache with
  | nil => simp [cacheWordsRun]
  | cons value rest ih =>
    simp only [cacheWordsRun, Costed.bind_work, pass, List.length_cons, Nat.succ_mul] at ih ⊢
    omega

/-- The costed recursion of `feedbackWords`: one word for each stored prediction, and a visit for
its end. -/
def feedbackWordsRun (κ : Costs) (base : UInt64) :
    List Discount → List Binary32 → Nat → Costed (List SensorWord)
  | discount :: discounts, value :: values, index => do
    let tail ← feedbackWordsRun κ base discounts values (index + 1)
    Costed.op (κ .visit + κ .feedbackWord)
      (⟨base + index.toUInt64, (predictionBucket value discount.horizon).val.toUInt64⟩ :: tail)
  | [], _, _ => Costed.op (κ .visit) []
  | _ :: _, [], _ => Costed.op (κ .visit) []

theorem feedbackWordsRun_val (κ : Costs) (base : UInt64) (discounts : List Discount)
    (values : List Binary32) (index : Nat) :
    (feedbackWordsRun κ base discounts values index).val =
      feedbackWords base discounts values index := by
  induction discounts generalizing values index with
  | nil => cases values <;> rfl
  | cons discount rest ih =>
    cases values with
    | nil => rfl
    | cons value others =>
      simp only [feedbackWordsRun, Costed.bind_val, ih]
      rfl

theorem feedbackWordsRun_work (κ : Costs) (base : UInt64) (discounts : List Discount)
    (values : List Binary32) (index : Nat) :
    (feedbackWordsRun κ base discounts values index).work ≤
      pass (κ .visit) discounts.length (κ .feedbackWord) := by
  induction discounts generalizing values index with
  | nil => cases values <;> simp [feedbackWordsRun]
  | cons discount rest ih =>
    cases values with
    | nil => simp [feedbackWordsRun]
    | cons value others =>
      have tail := ih others (index + 1)
      simp only [feedbackWordsRun, Costed.bind_work, pass, List.length_cons, Nat.succ_mul] at tail ⊢
      omega

/-- Twin of `Agent.words`: the stored predictions read, their feedback words, and the
frame's words copied before them. -/
def words (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : Costed (List SensorWord) := do
  let stored ← Costed.via state.control.runtime.references.demonPredictions.words
    (cacheWordsRun κ state.control.runtime.references.demonPredictions)
  let feedback ← Costed.via (feedbackWords interface.feedback interface.layout stored 0)
    (feedbackWordsRun κ interface.feedback interface.layout stored 0)
  Costed.scanList .append (κ .visit) observation.words (observation.words ++ feedback)

theorem words_val (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : (words κ state observation).val = state.words observation :=
  rfl

/-- Bound of the words at `frameWords` frame words and `questions` stored predictions. -/
abbrev wordsBound (κ : Costs) (frameWords questions : Nat) : Nat :=
  pass (κ .visit) questions (κ .read) + pass (κ .visit) questions (κ .feedbackWord) +
    Library.append.control (κ .visit) frameWords

theorem words_work (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (words κ state observation).work ≤ wordsBound κ interface.words interface.layout.length := by
  have stored := cacheWordsRun_work κ state.control.runtime.references.demonPredictions
  have feedback := feedbackWordsRun_work κ interface.feedback interface.layout
    state.control.runtime.references.demonPredictions.words 0
  have frame := Library.append.control_mono (visit := κ .visit) observation.bounded
  simp only [words, Costed.bind_work, wordsBound]
  omega

/-! ## The generated units -/

/-- Twin of `projectionValue`: the projection's samples listed and numbered, one term for
each, and the integer sum. -/
def projectionValue {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) : Costed Int := do
  let samples ← Costed.scanVector .toList (κ .visit) (bank.projections.get unit)
    (bank.projections.get unit).toList
  let numbered ← Costed.scanList .zipIdx (κ .visit) samples samples.zipIdx
  let terms ← Costed.map (κ .visit)
    (fun (sample, j) => Costed.op (κ .sampleTerm) (sampleTerm config.seed unit.val j patch sample))
    numbered
  Costed.scanList .sum (κ .visit + κ .sumTerm) terms terms.sum

theorem projectionValue_val {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    (projectionValue κ bank patch unit).val = Features.projectionValue bank patch unit := rfl

/-- Bound of one unit's projection over its 32 samples. -/
abbrev projectionBound (κ : Costs) : Nat :=
  Library.toList.control (κ .visit) 32 + Library.zipIdx.control (κ .visit) 32 +
    (Library.map.work (κ .visit) 32 (κ .sampleTerm)) +
    Library.sum.control (κ .visit + κ .sumTerm) 32

theorem projectionValue_work {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    (projectionValue κ bank patch unit).work ≤ projectionBound κ := by
  unfold projectionValue
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _) (Costed.bind_work_le_at
    (Nat.le_refl _) (Costed.bind_work_le_at (Costed.map_work_le (κ .visit) (κ .sampleTerm) _ _
      fun item _ => ?_) (Nat.le_refl _)))) ?_
  · obtain ⟨sample, j⟩ := item
    exact Nat.le_refl _
  · simp only [Vector.length_toList, List.length_zipIdx, List.length_map, projectionBound]
    omega

/-- Twin of `Bank.activations`: one projection for each unit. -/
def activations {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) : Costed (Vector Bool config.units.count) :=
  Costed.ofFn (κ .visit) fun unit => do
    let value ← projectionValue κ bank patch unit
    Costed.op (κ .activation) (decide (0 < value))

theorem activations_val {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) : (activations κ bank patch).val = bank.activations patch := rfl

theorem activations_work {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) :
    (activations κ bank patch).work ≤
      Library.ofFn.work (κ .visit) config.units.count (projectionBound κ + κ .activation) :=
  Costed.ofFn_work_le _ _ _ fun unit =>
    Costed.bind_work_le (projectionValue_work κ bank patch unit) fun _ => Nat.le_refl _

/-! ## The encoding -/

/-- Twin of `tiledFeatures`: the tilings listed, then for each tiling one hash for each word
and the copy of that tiling's features into the result. -/
def tiledFeatures (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) : Costed (List (FeatIdx dimension)) := do
  let tilings ← Costed.scanList .range (κ .visit) (List.range config.tilings.toNat)
    (List.range config.tilings.toNat)
  Costed.flatMap (κ .visit)
    (fun tiling => do
      let hashed ← Costed.map (κ .visit)
        (fun word => Costed.op (κ .hashFeature)
          (FeatIdx.fromHash dimension (Rng.hash3 (config.seed ^^^ tiling.toUInt64)
            word.channel word.value)))
        words
      Costed.scanList .flatMapResult (κ .visit) hashed hashed)
    tilings

theorem tiledFeatures_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) :
    (tiledFeatures κ dimension config words).val = Features.tiledFeatures dimension config words :=
  rfl

/-- Bound of the tiled features of `size` words. -/
abbrev tiledBound (κ : Costs) (tilings size : Nat) : Nat :=
  Library.range.control (κ .visit) tilings +
    Library.flatMap.work (κ .visit) tilings
      (Library.map.work (κ .visit) size (κ .hashFeature) +
        Library.flatMapResult.control (κ .visit) size)

theorem tiledFeatures_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) :
    (tiledFeatures κ dimension config words).work ≤
      tiledBound κ config.tilings.toNat words.length := by
  unfold tiledFeatures
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.flatMap_work_le (κ .visit)
      (Library.map.work (κ .visit) words.length (κ .hashFeature) +
        Library.flatMapResult.control (κ .visit) words.length) _ _
      fun tiling _ => ?_)) ?_
  · refine Nat.le_trans (Costed.bind_work_le_at
      (Costed.map_work_le (κ .visit) (κ .hashFeature) _ words fun _ _ => Nat.le_refl _)
      (Nat.le_refl _)) ?_
    simp only [List.length_map]
    omega
  · simp only [List.length_range, tiledBound]
    omega

/-- Twin of `imprintFeatures`: the units listed, then one test for each. -/
def imprintFeatures (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (active : Vector Bool config.units.count) : Costed (List (FeatIdx dimension)) := do
  let units ← Costed.scanList .finRange (κ .visit) (List.finRange config.units.count)
    (List.finRange config.units.count)
  Costed.filterMap (κ .visit)
    (fun unit => Costed.op (κ .imprint)
      (if active[unit.val] then some (unitFeature dimension config unit) else none))
    units

theorem imprintFeatures_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (active : Vector Bool config.units.count) :
    (imprintFeatures κ dimension config active).val =
      Features.imprintFeatures dimension config active := rfl

theorem imprintFeatures_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (active : Vector Bool config.units.count) :
    (imprintFeatures κ dimension config active).work ≤
      Library.finRange.control (κ .visit) config.units.count +
        (Library.filterMap.work (κ .visit) config.units.count (κ .imprint)) :=
    by
  unfold imprintFeatures
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.filterMap_work_le (κ .visit) (κ .imprint) _ _ fun _ _ => Nat.le_refl _)) ?_
  simp only [List.length_finRange]
  omega

/-- Twin of `unique`: the membership flags written, one admission for each raw feature,
and the reversal of the result. -/
def unique (κ : Costs) (indices : List (FeatIdx dimension)) :
    Costed (SwiftTd.ActiveSet dimension) := do
  let empty ← Costed.via (UniqueBuilder.empty dimension)
    (Costed.replicate (κ .visit) dimension.capacity false)
  let built ← Costed.foldl (κ .visit)
    (fun builder index => Costed.op (κ .uniqueAdd) (builder.add index)) empty indices
  Costed.scanList .reverse (κ .visit) built.reversed built.finish

theorem unique_val (κ : Costs) (indices : List (FeatIdx dimension)) :
    (unique κ indices).val = Features.unique indices := rfl

/-- The flags the twin writes are the empty builder's. -/
theorem unique_flags (κ : Costs) (dimension : Dimension) :
    (Costed.replicate (κ .visit) dimension.capacity false).val =
      (UniqueBuilder.empty dimension).seen := rfl

/-- Bound of a unique encoding of `size` raw features. -/
abbrev uniqueBound (κ : Costs) (capacity size : Nat) : Nat :=
  Library.replicate.control (κ .visit) capacity + Library.foldl.work (κ .visit) size (κ .uniqueAdd) +
    Library.reverse.control (κ .visit) size

theorem unique_work (κ : Costs) (indices : List (FeatIdx dimension)) :
    (unique κ indices).work ≤ uniqueBound κ dimension.capacity indices.length := by
  have length : (indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)).reversed.length ≤
      indices.length := by
    have bound := fold_length indices (SwiftTd.ActiveSet.empty dimension)
    rw [← unique_order] at bound
    simpa [Features.unique, UniqueBuilder.finish, SwiftTd.ActiveSet.empty] using bound
  have scaled := Library.reverse.control_mono (visit := κ .visit) length
  unfold unique
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _) (Costed.bind_work_le_at
    (Costed.foldl_work_le (κ .visit) (κ .uniqueAdd) _ _ _ fun _ _ _ => Nat.le_refl _)
    scaled)) ?_
  simp only [uniqueBound]
  omega

/-- Twin of `encodeWith`: the tiled and imprinted features, their concatenation, and the
unique encoding. -/
def encodeWith (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    Costed (SwiftTd.ActiveSet dimension) := do
  let tiled ← tiledFeatures κ dimension config words
  let imprinted ← imprintFeatures κ dimension config active
  let raw ← Costed.scanList .append (κ .visit) tiled (tiled ++ imprinted)
  unique κ raw

theorem encodeWith_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (encodeWith κ dimension config words active).val =
      Features.encodeWith dimension config words active := rfl

/-- Bound of an encoding at a capacity, a tiling count, `size` words and `units` units. -/
abbrev encodeBound (κ : Costs) (capacity tilings size units : Nat) : Nat :=
  tiledBound κ tilings size +
    (Library.finRange.control (κ .visit) units +
      (Library.filterMap.work (κ .visit) units (κ .imprint))) +
    Library.append.control (κ .visit) (tilings * size) +
    uniqueBound κ capacity (tilings * size + units)

theorem encodeWith_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (encodeWith κ dimension config words active).work ≤
      encodeBound κ dimension.capacity config.tilings.toNat words.length config.units.count := by
  have tiled := tiledFeatures_work κ dimension config words
  have imprinted := imprintFeatures_work κ dimension config active
  have tiledLength : (Features.tiledFeatures dimension config words).length =
      config.tilings.toNat * words.length := by
    simpa only [Features.tiledFeatures, List.length_range] using
      tiled_length (List.range config.tilings.toNat) words _
  have rawLength := rawEncodeWith_length dimension config words active
  have unique := unique_work κ (Features.rawEncodeWith dimension config words active)
  have flags := Library.foldl.work_mono (visit := κ .visit) rawLength (Nat.le_refl (κ .uniqueAdd))
  have copies := Library.reverse.control_mono (visit := κ .visit) rawLength
  unfold encodeWith
  refine Nat.le_trans (Costed.bind_work_le_at tiled (Costed.bind_work_le_at imprinted
    (Costed.bind_work_le_at (Nat.le_refl _) unique))) ?_
  simp only [tiledFeatures_val, tiledLength, encodeBound, uniqueBound] at *
  omega

/-- The costed composition of `EncodingFrame.compute` at an agent's frame: the words, the
unit outputs and the encoding. -/
def frameRun (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    Costed (Vector Bool config.units.count × SwiftTd.ActiveSet dimension) := do
  let read ← words κ state observation
  let units ← activations κ state.control.runtime.lifecycle.representation.bank
    observation.symbols
  let active ← encodeWith κ dimension config read units
  Costed.pure (units, active)

theorem frameRun_val (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (frameRun κ state observation).val =
      ((state.frame observation).units, (state.frame observation).active) := rfl

/-- Twin of `Agent.frame`. -/
def frame (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    Costed (EncodingFrame dimension state.control.runtime.lifecycle.representation.bank
      (state.words observation) observation.symbols) :=
  Costed.via (state.frame observation) (frameRun κ state observation)

/-- Bound of a frame's encoding for an interface, a capacity and a feature configuration. -/
abbrev frameBound (κ : Costs) (interface : Interface) (capacity : Nat)
    (config : Features.Config) : Nat :=
  wordsBound κ interface.words interface.layout.length +
    Library.ofFn.work (κ .visit) config.units.count (projectionBound κ + κ .activation) +
    encodeBound κ capacity config.tilings.toNat (interface.words + interface.layout.length)
      config.units.count

/-- An encoding's bound grows with the number of words. -/
theorem encodeBound_mono (κ : Costs) (capacity tilings units : Nat) {size limit : Nat}
    (fits : size ≤ limit) :
    encodeBound κ capacity tilings size units ≤ encodeBound κ capacity tilings limit units := by
  have hashes := Library.map.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .hashFeature))
  have copies := Library.flatMapResult.control_mono (visit := κ .visit) fits
  have tiles := Library.flatMap.work_mono (visit := κ .visit) (Nat.le_refl tilings)
    (Nat.add_le_add hashes copies)
  have raw := Nat.mul_le_mul_left tilings fits
  have rawCopies := Library.append.control_mono (visit := κ .visit) raw
  have admits := Library.foldl.work_mono (visit := κ .visit) (Nat.add_le_add_right raw units)
    (Nat.le_refl (κ .uniqueAdd))
  have reversed := Library.reverse.control_mono (visit := κ .visit) (Nat.add_le_add_right raw units)
  simp only [encodeBound, tiledBound, uniqueBound]
  omega

theorem frame_work (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (frame κ state observation).work ≤ frameBound κ interface dimension.capacity config := by
  have read := words_work κ state observation
  have units := activations_work κ state.control.runtime.lifecycle.representation.bank
    observation.symbols
  have encoded := Nat.le_trans
    (encodeWith_work κ dimension config (state.words observation)
      (state.control.runtime.lifecycle.representation.bank.activations observation.symbols))
    (encodeBound_mono κ dimension.capacity config.tilings.toNat config.units.count
      (state.words_length observation))
  change (frameRun κ state observation).work ≤ _
  unfold frameRun
  refine Nat.le_trans (Costed.bind_work_le_at read (Costed.bind_work_le_at units
    (Costed.bind_work_le_at encoded (Nat.le_refl _)))) ?_
  simp only [frameBound]
  omega

end AcornVerif.Resource.Twin
