/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Agent
import AcornVerif.Resource.LearnerWork

/-!
# Work of the encoding of a frame

The bounds of the costed definitions of the words the coder reads (`Agent.wordsCosted`) and of the
encoding of a frame (`Agent.frameCosted`), whose values are the executed `Agent.words` and
`Agent.frame`. The clock advance is charged under the `choose` site in
`AcornVerif.Resource.StepWork`. The words are the world's frame words and one feedback word for
each stored prediction. Each generated unit sums 32 samples of the frame's patch. The sensor words
are hashed once for each tiling, the active units are appended, and the list is made unique with
one membership flag for each feature slot. The flags are written in full for every frame, so the
encoding's work includes the capacity of the feature space whatever the frame
(`Features.UniqueBuilder.emptyCosted`).

Each definition here is the executed function with the bound proved of its costed definition as
its work, and its `_costed` theorem checks that the costed definition is within it. The compiled
`feedbackWords` builds each word before its recursive call and conses it on the return, so its
costed definition charges the word before the descent and a visit on the return.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-! ## The words the coder reads -/

theorem cacheWordsCosted_within (κ : Costs) {discounts : List Discount}
    (cache : PredictionCache discounts) :
    cache.wordsCosted.Within κ (pass (κ .visit) discounts.length (κ .read)) := by
  induction cache with
  | nil => exact (Acorn.Costed.op_within _ _ κ).mono (by simp [pass])
  | cons value rest ih =>
    refine (Acorn.Costed.charge_within
      (Acorn.Costed.bind_within ih (Acorn.Costed.op_within _ _ κ))).mono ?_
    simp only [pass, List.length_cons, Nat.succ_mul]
    omega

theorem feedbackWordsCosted_within (κ : Costs) (base : UInt64) (discounts : List Discount)
    (values : List Binary32) (index : Nat) :
    (feedbackWordsCosted base discounts values index).Within κ
      (pass (κ .visit) discounts.length (κ .feedbackWord)) := by
  induction discounts generalizing values index with
  | nil =>
    cases values <;> exact (Acorn.Costed.op_within _ _ κ).mono (by simp [pass])
  | cons discount rest ih =>
    cases values with
    | nil =>
      refine (Acorn.Costed.op_within _ _ κ).mono ?_
      simp only [pass]
      omega
    | cons value others =>
      refine (Acorn.Costed.charge_within
        (Acorn.Costed.bind_within (ih others (index + 1)) (Acorn.Costed.op_within _ _ κ))).mono ?_
      simp only [pass, List.length_cons, Nat.succ_mul]
      omega

/-- Bound of the words at `frameWords` frame words and `questions` stored predictions. -/
abbrev wordsBound (κ : Costs) (frameWords questions : Nat) : Nat :=
  pass (κ .visit) questions (κ .read) + pass (κ .visit) questions (κ .feedbackWord) +
    Library.append.control (κ .visit) frameWords

theorem wordsCosted_within (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.wordsCosted observation).Within κ
      (wordsBound κ interface.words interface.layout.length) := by
  have frame := Library.append.control_mono (visit := κ .visit) observation.bounded
  unfold Agent.wordsCosted
  refine Acorn.Costed.Within.mono
    (Acorn.Costed.bind_within (cacheWordsCosted_within κ _)
      (Acorn.Costed.bind_within (feedbackWordsCosted_within κ _ _ _ _)
        (Acorn.Costed.append_within _ _ κ))) ?_
  simp only [wordsBound]
  omega

/-- The words the coder reads, with the bound of their costed definition. -/
def words (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : Costed (List SensorWord) :=
  ⟨state.words observation, wordsBound κ interface.words interface.layout.length⟩

theorem words_val (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : (words κ state observation).val = state.words observation :=
  rfl

theorem words_work (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (words κ state observation).work ≤ wordsBound κ interface.words interface.layout.length :=
  Nat.le_refl _

theorem words_costed (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.wordsCosted observation).Within κ (words κ state observation).work :=
  wordsCosted_within κ state observation

/-! ## The generated units -/

/-- Bound of one unit's projection over its 32 samples. -/
abbrev projectionBound (κ : Costs) : Nat :=
  Library.toList.control (κ .visit) 32 + Library.zipIdx.control (κ .visit) 32 +
    (Library.map.work (κ .visit) 32 (κ .sampleTerm)) +
    Library.sum.control (κ .visit + κ .sumTerm) 32

theorem projectionValueCosted_within {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    (projectionValueCosted bank patch unit).Within κ (projectionBound κ) := by
  unfold projectionValueCosted
  refine Acorn.Costed.Within.mono
    (Acorn.Costed.bind_within (Acorn.Costed.toList_within _ κ)
      (Acorn.Costed.bind_within (Acorn.Costed.zipIdx_within _ _ κ)
        (Acorn.Costed.bind_within
          (Acorn.Costed.map_within (bound := κ .sampleTerm) fun item _ => ?_)
          (Acorn.Costed.sum_within _ κ)))) ?_
  · obtain ⟨sample, j⟩ := item
    exact Acorn.Costed.op_within _ _ κ
  · simp only [Acorn.Costed.toList_val, Acorn.Costed.zipIdx_val, Acorn.Costed.map_val,
      Vector.length_toList, List.length_zipIdx, List.length_map, projectionBound]
    omega

/-- A unit's projection, with the bound of its costed definition. -/
def projectionValue {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) : Costed Int :=
  ⟨Features.projectionValue bank patch unit, projectionBound κ⟩

theorem projectionValue_val {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    (projectionValue κ bank patch unit).val = Features.projectionValue bank patch unit := rfl

theorem projectionValue_work {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    (projectionValue κ bank patch unit).work ≤ projectionBound κ :=
  Nat.le_refl _

theorem projectionValue_costed {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) (unit : Fin config.units.count) :
    (projectionValueCosted bank patch unit).Within κ (projectionValue κ bank patch unit).work :=
  projectionValueCosted_within κ bank patch unit

theorem activationsCosted_within {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) :
    (bank.activationsCosted patch).Within κ
      (Library.ofFn.work (κ .visit) config.units.count (projectionBound κ + κ .activation)) :=
  Acorn.Costed.ofFn_within fun unit =>
    Acorn.Costed.bind_within (projectionValueCosted_within κ bank patch unit)
      (Acorn.Costed.op_within _ _ κ)

/-- The units' outputs, with the bound of their costed definition. -/
def activations {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) : Costed (Vector Bool config.units.count) :=
  ⟨bank.activations patch,
    Library.ofFn.work (κ .visit) config.units.count (projectionBound κ + κ .activation)⟩

theorem activations_val {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) : (activations κ bank patch).val = bank.activations patch := rfl

theorem activations_work {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) :
    (activations κ bank patch).work ≤
      Library.ofFn.work (κ .visit) config.units.count (projectionBound κ + κ .activation) :=
  Nat.le_refl _

theorem activations_costed {shape : PatchShape} (κ : Costs) (bank : Bank shape config)
    (patch : Patch shape) :
    (bank.activationsCosted patch).Within κ (activations κ bank patch).work :=
  activationsCosted_within κ bank patch

/-! ## The encoding -/

/-- Bound of the tiled features of `size` words. -/
abbrev tiledBound (κ : Costs) (tilings size : Nat) : Nat :=
  Library.range.control (κ .visit) tilings +
    Library.flatMap.work (κ .visit) tilings
      (Library.map.work (κ .visit) size (κ .hashFeature) +
        Library.flatMapResult.control (κ .visit) size)

theorem tiledFeaturesCosted_within (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) :
    (tiledFeaturesCosted dimension config words).Within κ
      (tiledBound κ config.tilings.toNat words.length) := by
  unfold tiledFeaturesCosted
  refine Acorn.Costed.bind_within (Acorn.Costed.range_within _ κ) ?_
  refine (Acorn.Costed.flatMap_within (size := words.length)
    (fun _ _ => Acorn.Costed.map_within fun _ _ => Acorn.Costed.op_within _ _ κ)
    (fun _ _ => by simp [Acorn.Costed.map_val])).mono ?_
  simp [Acorn.Costed.range_val]

/-- The tiled features, with the bound of their costed definition. -/
def tiledFeatures (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) : Costed (List (FeatIdx dimension)) :=
  ⟨Features.tiledFeatures dimension config words,
    tiledBound κ config.tilings.toNat words.length⟩

theorem tiledFeatures_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) :
    (tiledFeatures κ dimension config words).val = Features.tiledFeatures dimension config words :=
  rfl

theorem tiledFeatures_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) :
    (tiledFeatures κ dimension config words).work ≤
      tiledBound κ config.tilings.toNat words.length :=
  Nat.le_refl _

theorem tiledFeatures_costed (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) :
    (tiledFeaturesCosted dimension config words).Within κ
      (tiledFeatures κ dimension config words).work :=
  tiledFeaturesCosted_within κ dimension config words

theorem imprintFeaturesCosted_within (κ : Costs) (dimension : Dimension)
    (config : Features.Config) (active : Vector Bool config.units.count) :
    (imprintFeaturesCosted dimension config active).Within κ
      (Library.finRange.control (κ .visit) config.units.count +
        (Library.filterMap.work (κ .visit) config.units.count (κ .imprint))) := by
  unfold imprintFeaturesCosted
  refine Acorn.Costed.bind_within (Acorn.Costed.finRange_within _ κ) ?_
  refine (Acorn.Costed.filterMap_within fun _ _ => Acorn.Costed.op_within _ _ κ).mono ?_
  simp [Acorn.Costed.finRange_val]

/-- The imprinted features, with the bound of their costed definition. -/
def imprintFeatures (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (active : Vector Bool config.units.count) : Costed (List (FeatIdx dimension)) :=
  ⟨Features.imprintFeatures dimension config active,
    Library.finRange.control (κ .visit) config.units.count +
      (Library.filterMap.work (κ .visit) config.units.count (κ .imprint))⟩

theorem imprintFeatures_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (active : Vector Bool config.units.count) :
    (imprintFeatures κ dimension config active).val =
      Features.imprintFeatures dimension config active := rfl

theorem imprintFeatures_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (active : Vector Bool config.units.count) :
    (imprintFeatures κ dimension config active).work ≤
      Library.finRange.control (κ .visit) config.units.count +
        (Library.filterMap.work (κ .visit) config.units.count (κ .imprint)) :=
  Nat.le_refl _

theorem imprintFeatures_costed (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (active : Vector Bool config.units.count) :
    (imprintFeaturesCosted dimension config active).Within κ
      (imprintFeatures κ dimension config active).work :=
  imprintFeaturesCosted_within κ dimension config active

/-- Bound of a unique encoding of `size` raw features. -/
abbrev uniqueBound (κ : Costs) (capacity size : Nat) : Nat :=
  Library.replicate.control (κ .visit) capacity + Library.foldl.work (κ .visit) size (κ .uniqueAdd) +
    Library.reverse.control (κ .visit) size

theorem emptyCosted_within (κ : Costs) (dimension : Dimension) :
    (UniqueBuilder.emptyCosted dimension).Within κ
      (Library.replicate.control (κ .visit) dimension.capacity) :=
  (Acorn.Costed.bind_within (Acorn.Costed.attach_within (Acorn.Costed.replicate_within _ _ κ))
    (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _))

theorem finishCosted_within (κ : Costs) (builder : UniqueBuilder dimension) :
    builder.finishCosted.Within κ (Library.reverse.control (κ .visit) builder.reversed.length) :=
  (Acorn.Costed.bind_within (Acorn.Costed.attach_within (Acorn.Costed.reverse_within _ κ))
    (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _))

theorem uniqueCosted_within (κ : Costs) (indices : List (FeatIdx dimension)) :
    (uniqueCosted indices).Within κ (uniqueBound κ dimension.capacity indices.length) := by
  have length : (indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)).reversed.length ≤
      indices.length := by
    have bound := fold_length indices (SwiftTd.ActiveSet.empty dimension)
    rw [← unique_order] at bound
    simpa [unique_def, UniqueBuilder.finish_def, SwiftTd.ActiveSet.empty] using bound
  unfold uniqueCosted
  refine Acorn.Costed.Within.mono
    (Acorn.Costed.bind_within (emptyCosted_within κ dimension)
      (Acorn.Costed.bind_within
        (Acorn.Costed.foldl_within (bound := κ .uniqueAdd) fun _ _ _ =>
          Acorn.Costed.op_within _ _ κ)
        ((finishCosted_within κ _).mono (Library.control_mono _ length)))) ?_
  simp only [uniqueBound]
  omega

/-- The unique encoding, with the bound of its costed definition. -/
def unique (κ : Costs) (indices : List (FeatIdx dimension)) :
    Costed (SwiftTd.ActiveSet dimension) :=
  ⟨Features.unique indices, uniqueBound κ dimension.capacity indices.length⟩

theorem unique_val (κ : Costs) (indices : List (FeatIdx dimension)) :
    (unique κ indices).val = Features.unique indices := rfl

theorem unique_work (κ : Costs) (indices : List (FeatIdx dimension)) :
    (unique κ indices).work ≤ uniqueBound κ dimension.capacity indices.length :=
  Nat.le_refl _

theorem unique_costed (κ : Costs) (indices : List (FeatIdx dimension)) :
    (uniqueCosted indices).Within κ (unique κ indices).work :=
  uniqueCosted_within κ indices

/-- Bound of an encoding at a capacity, a tiling count, `size` words and `units` units. -/
abbrev encodeBound (κ : Costs) (capacity tilings size units : Nat) : Nat :=
  tiledBound κ tilings size +
    (Library.finRange.control (κ .visit) units +
      (Library.filterMap.work (κ .visit) units (κ .imprint))) +
    Library.append.control (κ .visit) (tilings * size) +
    uniqueBound κ capacity (tilings * size + units)

theorem rawEncodeWithCosted_within (κ : Costs) (dimension : Dimension)
    (config : Features.Config) (words : List SensorWord)
    (active : Vector Bool config.units.count) :
    (rawEncodeWithCosted dimension config words active).Within κ
      (tiledBound κ config.tilings.toNat words.length +
        ((Library.finRange.control (κ .visit) config.units.count +
          (Library.filterMap.work (κ .visit) config.units.count (κ .imprint))) +
        Library.append.control (κ .visit) (config.tilings.toNat * words.length))) := by
  have tiledLength : (Features.tiledFeatures dimension config words).length =
      config.tilings.toNat * words.length := by
    simpa only [tiledFeatures_def, List.length_range] using
      tiled_length (List.range config.tilings.toNat) words _
  unfold rawEncodeWithCosted
  refine Acorn.Costed.bind_within (tiledFeaturesCosted_within κ dimension config words) ?_
  refine Acorn.Costed.bind_within (imprintFeaturesCosted_within κ dimension config active) ?_
  exact (Acorn.Costed.append_within _ _ κ).mono
    (Nat.le_of_eq (congrArg (Library.append.control (κ .visit)) tiledLength))

theorem encodeWithCosted_within (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (encodeWithCosted dimension config words active).Within κ
      (encodeBound κ dimension.capacity config.tilings.toNat words.length config.units.count) := by
  have rawLength := rawEncodeWith_length dimension config words active
  have admits := Library.foldl.work_mono (visit := κ .visit) rawLength (Nat.le_refl (κ .uniqueAdd))
  have copies := Library.reverse.control_mono (visit := κ .visit) rawLength
  unfold encodeWithCosted
  refine Acorn.Costed.Within.mono
    (Acorn.Costed.bind_within (rawEncodeWithCosted_within κ dimension config words active)
      (uniqueCosted_within κ (rawEncodeWith dimension config words active))) ?_
  simp only [encodeBound, uniqueBound]
  omega

/-- The encoding, with the bound of its costed definition. -/
def encodeWith (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    Costed (SwiftTd.ActiveSet dimension) :=
  ⟨Features.encodeWith dimension config words active,
    encodeBound κ dimension.capacity config.tilings.toNat words.length config.units.count⟩

theorem encodeWith_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (encodeWith κ dimension config words active).val =
      Features.encodeWith dimension config words active := rfl

theorem encodeWith_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (encodeWith κ dimension config words active).work ≤
      encodeBound κ dimension.capacity config.tilings.toNat words.length config.units.count :=
  Nat.le_refl _

theorem encodeWith_costed (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (words : List SensorWord) (active : Vector Bool config.units.count) :
    (encodeWithCosted dimension config words active).Within κ
      (encodeWith κ dimension config words active).work :=
  encodeWithCosted_within κ dimension config words active

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

/-- Bound of a frame's encoding for an interface, a capacity and a feature configuration. -/
abbrev frameBound (κ : Costs) (interface : Interface) (capacity : Nat)
    (config : Features.Config) : Nat :=
  wordsBound κ interface.words interface.layout.length +
    Library.ofFn.work (κ .visit) config.units.count (projectionBound κ + κ .activation) +
    encodeBound κ capacity config.tilings.toNat (interface.words + interface.layout.length)
      config.units.count

theorem computeCosted_within {shape : PatchShape} (κ : Costs) (dimension : Dimension)
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    (EncodingFrame.computeCosted dimension bank words patch).Within κ
      (Library.ofFn.work (κ .visit) config.units.count (projectionBound κ + κ .activation) +
        (encodeBound κ dimension.capacity config.tilings.toNat words.length config.units.count +
          0)) :=
  Acorn.Costed.bind_within (Acorn.Costed.attach_within (activationsCosted_within κ bank patch))
    (Acorn.Costed.bind_within
      (Acorn.Costed.attach_within (encodeWithCosted_within κ dimension config words _))
      (Acorn.Costed.pure_within _ κ))

theorem frameCosted_within (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frameCosted observation).Within κ
      (frameBound κ interface dimension.capacity config) := by
  have encoded := encodeBound_mono κ dimension.capacity config.tilings.toNat config.units.count
    (state.words_length observation)
  unfold Agent.frameCosted
  refine Acorn.Costed.Within.mono
    (Acorn.Costed.bind_within (Acorn.Costed.attach_within (wordsCosted_within κ state observation))
      (computeCosted_within κ dimension state.control.runtime.lifecycle.representation.bank
        (state.words observation) observation.symbols)) ?_
  simp only [frameBound]
  omega

/-- The encoding of a frame, with the bound of its costed definition. -/
def frame (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    Costed (EncodingFrame dimension state.control.runtime.lifecycle.representation.bank
      (state.words observation) observation.symbols) :=
  ⟨state.frame observation, frameBound κ interface dimension.capacity config⟩

theorem frame_val (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) : (frame κ state observation).val = state.frame observation :=
  rfl

theorem frame_work (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (frame κ state observation).work ≤ frameBound κ interface dimension.capacity config :=
  Nat.le_refl _

theorem frame_costed (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (observation : Frame interface) :
    (state.frameCosted observation).Within κ (frame κ state observation).work :=
  frameCosted_within κ state observation

end AcornVerif.Resource.Twin
