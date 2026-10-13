/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Models
import AcornVerif.Resource.ControlWork

/-!
# Work of the option models

The bounds of the costed definitions of an option model's input, of its ranked features
(`Acorn.RankedFeatures`), of its prediction, of its updates and of its restart (`Acorn.Models`).
Each definition here is the executed function with the bound proved of its costed definition as
its work, and its `_costed` theorem checks that the costed definition is within it. A transition
part has one row
for each ranked position, `(rankDimension dimension).capacity` rows, each an admitted learner
over the ranked positions, and one deviation learner for each meta action. A row's input is
the frame's active ranked positions and the bias position, so it has at most one position
more than the frame has active features (`RankedFeatures.input_length`). A prediction reads
every row; an update visits every row and updates the rows of occupied positions.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {dimension : Dimension} {criterion : Criterion} {count : Word.Count}

/-! ## Active sets of the models -/

/-- Bound of a model input over `width` features. -/
abbrev inputBound (κ : Costs) (width : Nat) : Nat :=
  κ .insert + (Library.contains.control (κ .visit + κ .compare) width +
    Library.append.control (κ .visit) width)

theorem insertCosted_within (κ : Costs) (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) :
    (insertCosted active index).Within κ (inputBound κ active.indices.length) := by
  unfold insertCosted inputBound
  refine Acorn.Costed.charge_within
    (Acorn.Costed.bind_within (Acorn.Costed.attach_within (Acorn.Costed.mem_within _ _ κ)) ?_)
  exact Acorn.Costed.dite_within (fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
    fun _ => (Acorn.Costed.bind_within
      (Acorn.Costed.attach_within (Acorn.Costed.append_within _ _ κ))
      (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _))

/-- An insertion, with the bound of its costed definition. -/
def insert (κ : Costs) (active : SwiftTd.ActiveSet dimension) (index : FeatIdx dimension) :
    Costed (SwiftTd.ActiveSet dimension) :=
  ⟨Features.insert active index, inputBound κ active.indices.length⟩

theorem insert_val (κ : Costs) (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) : (insert κ active index).val = Features.insert active index :=
  rfl

theorem insert_work (κ : Costs) (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) :
    (insert κ active index).work ≤ inputBound κ active.indices.length :=
  Nat.le_refl _

theorem insert_costed (κ : Costs) (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) :
    (insertCosted active index).Within κ (insert κ active index).work :=
  insertCosted_within κ active index

theorem modelInputCosted_within (κ : Costs) (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    (modelInputCosted criterion base age).Within κ
      (κ .hashFeature + inputBound κ base.indices.length) := by
  cases criterion
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)
  · exact Acorn.Costed.bind_within (Acorn.Costed.op_within _ _ κ) (insertCosted_within κ base _)

/-- A model input, with the bound of its costed definition. -/
def modelInput (κ : Costs) (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (SwiftTd.ActiveSet dimension) :=
  ⟨Features.modelInput criterion base age, κ .hashFeature + inputBound κ base.indices.length⟩

theorem modelInput_val (κ : Costs) (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (modelInput κ criterion base age).val = Features.modelInput criterion base age := rfl

theorem modelInput_work (κ : Costs) (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (modelInput κ criterion base age).work ≤
      κ .hashFeature + inputBound κ base.indices.length :=
  Nat.le_refl _

theorem modelInput_costed (κ : Costs) (criterion : Criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    (modelInputCosted criterion base age).Within κ (modelInput κ criterion base age).work :=
  modelInputCosted_within κ criterion base age

/-- A model input has at most one feature more than the frame. -/
theorem modelInput_length (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (Features.modelInput criterion base age).indices.length ≤ base.indices.length + 1 := by
  cases criterion
  · exact Nat.le_succ _
  · exact insert_length base _

theorem activeCosted_within (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.activeCosted features).Within κ
      (Library.filterMap.work (κ .visit) features.indices.length (κ .position)) :=
  (Acorn.Costed.bind_within
    (Acorn.Costed.attach_within
      (Acorn.Costed.filterMap_within fun _ _ => Acorn.Costed.op_within _ _ κ))
    (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _))

/-- The active positions, with the bound of their costed definition. -/
def rankedActive (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Costed (SwiftTd.ActiveSet (rankDimension dimension)) :=
  ⟨ranked.active features,
    Library.filterMap.work (κ .visit) features.indices.length (κ .position)⟩

theorem rankedActive_work (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (rankedActive κ ranked features).work ≤
      Library.filterMap.work (κ .visit) features.indices.length (κ .position) :=
  Nat.le_refl _

theorem rankedActive_costed (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.activeCosted features).Within κ (rankedActive κ ranked features).work :=
  activeCosted_within κ ranked features

/-- Bound of a row input over `width` features. -/
abbrev rowInputBound (κ : Costs) (width : Nat) : Nat :=
  (Library.filterMap.work (κ .visit) width (κ .position)) +
    (κ .rankWidth + (κ .rankWidth + inputBound κ width))

theorem inputCosted_within (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.inputCosted features).Within κ (rowInputBound κ features.indices.length) := by
  have tested := Library.contains.control_mono (visit := κ .visit + κ .compare)
    (ranked.active_length features)
  have appended := Library.append.control_mono (visit := κ .visit) (ranked.active_length features)
  unfold RankedFeatures.inputCosted
  refine Acorn.Costed.Within.mono (Acorn.Costed.charge_within
    (Acorn.Costed.bind_within (activeCosted_within κ ranked features)
      (Acorn.Costed.bind_within (Acorn.Costed.op_within _ _ κ)
        (insertCosted_within κ (ranked.active features) (RankedFeatures.bias dimension))))) ?_
  simp only [rowInputBound, inputBound]
  omega

/-- A row input, with the bound of its costed definition. -/
def rankedInput (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Costed (SwiftTd.ActiveSet (rankDimension dimension)) :=
  ⟨ranked.input features, rowInputBound κ features.indices.length⟩

theorem rankedInput_val (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (rankedInput κ ranked features).val = ranked.input features := rfl

theorem rankedInput_work (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (rankedInput κ ranked features).work ≤ rowInputBound κ features.indices.length :=
  Nat.le_refl _

theorem rankedInput_costed (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.inputCosted features).Within κ (rankedInput κ ranked features).work :=
  inputCosted_within κ ranked features

/-- Bound of the occupied positions of a ranking of `width` positions. -/
abbrev occupiedBound (κ : Costs) (width : Nat) : Nat :=
  κ .rankWidth + Library.finRange.control (κ .visit) width +
    (Library.filterMap.work (κ .visit) width (κ .read))

theorem occupiedCosted_within (κ : Costs) (ranked : RankedFeatures dimension) :
    ranked.occupiedCosted.Within κ (occupiedBound κ (rankDimension dimension).capacity) := by
  unfold RankedFeatures.occupiedCosted occupiedBound
  refine Acorn.Costed.bind_within
    (Acorn.Costed.charge_within (Acorn.Costed.finRange_within _ κ)) ?_
  refine (Acorn.Costed.filterMap_within fun _ _ => Acorn.Costed.op_within _ _ κ).mono ?_
  simp [Acorn.Costed.charge_val, Acorn.Costed.finRange_val]

/-- The occupied positions, with the bound of their costed definition. -/
def occupied (κ : Costs) (ranked : RankedFeatures dimension) :
    Costed (List (RankIdx dimension × FeatIdx dimension)) :=
  ⟨ranked.occupied, occupiedBound κ (rankDimension dimension).capacity⟩

theorem occupied_val (κ : Costs) (ranked : RankedFeatures dimension) :
    (occupied κ ranked).val = ranked.occupied := rfl

theorem occupied_work (κ : Costs) (ranked : RankedFeatures dimension) :
    (occupied κ ranked).work ≤ occupiedBound κ (rankDimension dimension).capacity :=
  Nat.le_refl _

theorem occupied_costed (κ : Costs) (ranked : RankedFeatures dimension) :
    ranked.occupiedCosted.Within κ (occupied κ ranked).work :=
  occupiedCosted_within κ ranked

/-- Bound of an indicator over `width` features and `positions` ranked positions. -/
abbrev indicatorBound (κ : Costs) (width positions : Nat) : Nat :=
  (Library.filterMap.work (κ .visit) width (κ .position)) +
    (κ .rankWidth + Library.replicate.control (κ .visit) positions) +
    Library.foldl.work (κ .visit) width (κ .write)

theorem indicatorCosted_within (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.indicatorCosted features).Within κ
      (indicatorBound κ features.indices.length (rankDimension dimension).capacity) := by
  have scaled : Library.foldl.work (κ .visit) (ranked.active features).indices.length
        (κ .write) ≤ Library.foldl.work (κ .visit) features.indices.length (κ .write) :=
    Library.foldl.work_mono (ranked.active_length features) (Nat.le_refl _)
  unfold RankedFeatures.indicatorCosted
  refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
    (Acorn.Costed.charge_within (Acorn.Costed.replicate_within _ _ κ))
    (Acorn.Costed.bind_within (activeCosted_within κ ranked features)
      (Acorn.Costed.foldl_within (items := (ranked.active features).indices) (bound := κ .write)
        fun _ _ _ => Acorn.Costed.op_within _ _ κ))) ?_
  simp only [indicatorBound]
  omega

/-- The indicator, with the bound of its costed definition. -/
def indicator (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Costed (Vector Expectation (rankDimension dimension).capacity) :=
  ⟨ranked.indicator features,
    indicatorBound κ features.indices.length (rankDimension dimension).capacity⟩

theorem indicator_val (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (indicator κ ranked features).val = ranked.indicator features := rfl

theorem indicator_work (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (indicator κ ranked features).work ≤
      indicatorBound κ features.indices.length (rankDimension dimension).capacity :=
  Nat.le_refl _

theorem indicator_costed (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (ranked.indicatorCosted features).Within κ (indicator κ ranked features).work :=
  indicatorCosted_within κ ranked features

/-! ## Predictions -/

/-- Bound of the ranked values at `positions` ranked positions. -/
abbrev rankedValuesBound (κ : Costs) (positions : Nat) : Nat :=
  occupiedBound κ positions +
    Library.vectorMap.work (κ .visit) metaCount.word.toNat
      (Library.foldl.work (κ .visit) positions (κ .productTerm))

theorem rankedValuesCosted_within (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    (value.rankedValuesCosted ranked expected).Within κ
      (rankedValuesBound κ (rankDimension dimension).capacity) := by
  unfold ValueFunction.rankedValuesCosted rankedValuesBound
  refine Acorn.Costed.bind_within (occupiedCosted_within κ ranked) ?_
  exact Acorn.Costed.mapVector_within fun _ _ =>
    (sumMapCosted_pure_within κ .productTerm .zero _ _).mono
      (Library.foldl.work_mono (RankedFeatures.occupied_length ranked) (Nat.le_refl _))

/-- The ranked values, with the bound of their costed definition. -/
def rankedValues (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    Costed (Vector Binary32 metaCount.word.toNat) :=
  ⟨value.rankedValues ranked expected, rankedValuesBound κ (rankDimension dimension).capacity⟩

theorem rankedValues_val (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    (rankedValues κ value ranked expected).val = value.rankedValues ranked expected := rfl

theorem rankedValues_work (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    (rankedValues κ value ranked expected).work ≤
      rankedValuesBound κ (rankDimension dimension).capacity :=
  Nat.le_refl _

theorem rankedValues_costed (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    (value.rankedValuesCosted ranked expected).Within κ
      (rankedValues κ value ranked expected).work :=
  rankedValuesCosted_within κ value ranked expected

/-- Bound of a nominal value over `size` values under either criterion. -/
abbrev comparisonBound (κ : Costs) (size : Nat) : Nat := expectedBound κ size + bestBound κ size

theorem comparisonValueCosted_within (κ : Costs) (criterion : Criterion)
    (policy : PolicySnapshot count) :
    (comparisonValueCosted criterion policy).Within κ (comparisonBound κ count.word.toNat) := by
  cases criterion
  · exact (bestCosted_within κ policy).mono (Nat.le_add_left _ _)
  · exact (expectedCosted_within κ policy).mono (Nat.le_add_right _ _)

/-- A nominal value, with the bound of its costed definition. -/
def comparisonValue (κ : Costs) (criterion : Criterion) (policy : PolicySnapshot count) :
    Costed Binary32 :=
  ⟨Features.comparisonValue criterion policy, comparisonBound κ count.word.toNat⟩

theorem comparisonValue_val (κ : Costs) (criterion : Criterion) (policy : PolicySnapshot count) :
    (comparisonValue κ criterion policy).val = Features.comparisonValue criterion policy := rfl

theorem comparisonValue_work (κ : Costs) (criterion : Criterion) (policy : PolicySnapshot count) :
    (comparisonValue κ criterion policy).work ≤ comparisonBound κ count.word.toNat :=
  Nat.le_refl _

theorem comparisonValue_costed (κ : Costs) (criterion : Criterion)
    (policy : PolicySnapshot count) :
    (comparisonValueCosted criterion policy).Within κ
      (comparisonValue κ criterion policy).work :=
  comparisonValueCosted_within κ criterion policy

/-- Bound of the rows' predictions at `positions` rows over `width` inputs. -/
abbrev expectedAtBound (κ : Costs) (positions width : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) positions
    (Library.foldl.work (κ .visit) width (κ .sumTerm) + κ .project)

theorem expectedAtCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    (transition.expectedAtCosted input).Within κ
      (expectedAtBound κ (rankDimension dimension).capacity input.indices.length) :=
  Acorn.Costed.mapVector_within fun row _ =>
    Acorn.Costed.bind_within (linearPredictionCosted_within κ row.state input)
      (Acorn.Costed.op_within _ _ κ)

/-- The rows' expected values, with the bound of their costed definition. -/
def expectedAt (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    Costed (Vector Expectation (rankDimension dimension).capacity) :=
  ⟨transition.expectedAt input,
    expectedAtBound κ (rankDimension dimension).capacity input.indices.length⟩

theorem expectedAt_val (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    (expectedAt κ transition input).val = transition.expectedAt input := rfl

theorem expectedAt_work (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    (expectedAt κ transition input).work ≤
      expectedAtBound κ (rankDimension dimension).capacity input.indices.length :=
  Nat.le_refl _

theorem expectedAt_costed (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    (transition.expectedAtCosted input).Within κ (expectedAt κ transition input).work :=
  expectedAtCosted_within κ transition input

/-- Bound of a predicted outcome's values over `width` features at `positions` rows. -/
abbrev outcomeValuesBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + expectedAtBound κ positions (width + 1) +
    rankedValuesBound κ positions +
    Library.ofFn.work (κ .visit) metaCount.word.toNat
      (Library.foldl.work (κ .visit) (width + 1) (κ .sumTerm) + κ .outcomeValue)

/-- A row-prediction bound grows with the input width. -/
theorem expectedAtBound_mono (κ : Costs) (positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    expectedAtBound κ positions width ≤ expectedAtBound κ positions limit :=
  Library.vectorMap.work_mono (Nat.le_refl _)
    (Nat.add_le_add_right (Library.foldl.work_mono fits (Nat.le_refl _)) _)

theorem outcomeValuesCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (transition.outcomeValuesCosted value features shared).Within κ
      (outcomeValuesBound κ (rankDimension dimension).capacity features.indices.length) := by
  have width := transition.ranked.input_length features
  have expected := expectedAtBound_mono κ (rankDimension dimension).capacity width
  have deviations := Library.ofFn.work_mono (visit := κ .visit)
    (Nat.le_refl metaCount.word.toNat)
    (Nat.add_le_add_right (Library.foldl.work_mono (visit := κ .visit) width
      (Nat.le_refl (κ .sumTerm))) (κ .outcomeValue))
  unfold Transition.outcomeValuesCosted
  refine Acorn.Costed.Within.mono
    (Acorn.Costed.bind_within (inputCosted_within κ transition.ranked features)
      (Acorn.Costed.bind_within
        (expectedAtCosted_within κ transition (transition.ranked.input features))
        (Acorn.Costed.bind_within
          (rankedValuesCosted_within κ value transition.ranked
            (transition.expectedAt (transition.ranked.input features)))
          (Acorn.Costed.ofFn_within (bound := Library.foldl.work (κ .visit)
              (transition.ranked.input features).indices.length (κ .sumTerm) + κ .outcomeValue)
            fun action => Acorn.Costed.bind_within
              (linearPredictionCosted_within κ (transition.deviations.get action).state
                (transition.ranked.input features))
              (Acorn.Costed.op_within _ _ κ))))) ?_
  simp only [outcomeValuesBound] at expected deviations ⊢
  omega

/-- A predicted outcome's values, with the bound of their costed definition. -/
def outcomeValues (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Costed (Vector Binary32 metaCount.word.toNat) :=
  ⟨transition.outcomeValues value features shared,
    outcomeValuesBound κ (rankDimension dimension).capacity features.indices.length⟩

theorem outcomeValues_val (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (outcomeValues κ transition value features shared).val =
      transition.outcomeValues value features shared := rfl

theorem outcomeValues_work (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (outcomeValues κ transition value features shared).work ≤
      outcomeValuesBound κ (rankDimension dimension).capacity features.indices.length :=
  Nat.le_refl _

theorem outcomeValues_costed (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (transition.outcomeValuesCosted value features shared).Within κ
      (outcomeValues κ transition value features shared).work :=
  outcomeValuesCosted_within κ transition value features shared

/-- Bound of a look-ahead over `width` features at `positions` rows. -/
abbrev lookaheadBound (κ : Costs) (positions width : Nat) : Nat :=
  outcomeValuesBound κ positions width + comparisonBound κ metaCount.word.toNat

theorem lookaheadCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (transition.lookaheadCosted value features shared).Within κ
      (lookaheadBound κ (rankDimension dimension).capacity features.indices.length) :=
  Acorn.Costed.bind_within (outcomeValuesCosted_within κ transition value features shared)
    (comparisonValueCosted_within κ criterion _)

/-- A look-ahead, with the bound of its costed definition. -/
def lookahead (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Costed Binary32 :=
  ⟨transition.lookahead value features shared,
    lookaheadBound κ (rankDimension dimension).capacity features.indices.length⟩

theorem lookahead_val (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (lookahead κ transition value features shared).val =
      transition.lookahead value features shared := rfl

theorem lookahead_work (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (lookahead κ transition value features shared).work ≤
      lookaheadBound κ (rankDimension dimension).capacity features.indices.length :=
  Nat.le_refl _

theorem lookahead_costed (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (transition.lookaheadCosted value features shared).Within κ
      (lookahead κ transition value features shared).work :=
  lookaheadCosted_within κ transition value features shared

/-- Bound of a model prediction over `width` features. -/
abbrev predictBound (κ : Costs) (positions width : Nat) : Nat :=
  κ .hashFeature + inputBound κ width +
    (3 * Library.foldl.work (κ .visit) (width + 1) (κ .sumTerm) +
      lookaheadBound κ positions width + κ .prediction)

theorem predictCosted_within (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (model.predictCosted value base age).Within κ
      (predictBound κ (rankDimension dimension).capacity base.indices.length) := by
  have width := modelInput_length criterion base age
  have read := fun (learner : NumericState (criterion.config .demon) dimension) =>
    (linearPredictionCosted_within κ learner (Features.modelInput criterion base age)).mono
      (Library.foldl.work_mono width (Nat.le_refl (κ .sumTerm)))
  cases model with
  | discounted reward continuation transition =>
    unfold Model.predictCosted
    refine Acorn.Costed.Within.mono
      (Acorn.Costed.bind_within (modelInputCosted_within κ _ base age)
        (Acorn.Costed.bind_within (read reward.state)
          (Acorn.Costed.bind_within (read continuation.state)
            (Acorn.Costed.bind_within (lookaheadCosted_within κ transition value base
                (continuation.state.linearPrediction (Features.modelInput .discounted base age)))
              (Acorn.Costed.op_within _ _ κ))))) ?_
    simp only [predictBound]
    omega
  | differential reward continuation duration transition =>
    unfold Model.predictCosted
    refine Acorn.Costed.Within.mono
      (Acorn.Costed.bind_within (modelInputCosted_within κ _ base age)
        (Acorn.Costed.bind_within (read reward.state)
          (Acorn.Costed.bind_within (read continuation.state)
            (Acorn.Costed.bind_within (lookaheadCosted_within κ transition value base
                (continuation.state.linearPrediction (Features.modelInput .differential base age)))
              (Acorn.Costed.bind_within (read duration.state)
                (Acorn.Costed.op_within _ _ κ)))))) ?_
    simp only [predictBound]
    omega

/-- A model prediction, with the bound of its costed definition. -/
def predict (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (ModelPrediction criterion) :=
  ⟨model.predict value base age, predictBound κ (rankDimension dimension).capacity
    base.indices.length⟩

theorem predict_val (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : (predict κ model value base age).val = model.predict value base age := rfl

theorem predict_work (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (predict κ model value base age).work ≤
      predictBound κ (rankDimension dimension).capacity base.indices.length :=
  Nat.le_refl _

theorem predict_costed (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (model.predictCosted value base age).Within κ (predict κ model value base age).work :=
  predictCosted_within κ model value base age

/-! ## Updates -/

/-- A row learner's bound grows with its input width. -/
theorem secondLoopBound_mono (κ : Costs) {width limit : Nat} (fits : width ≤ limit) :
    secondLoopBound κ width ≤ secondLoopBound κ limit := by
  have := Library.map.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .read))
  have := Library.foldl.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .sumTerm))
  have := pass_mono (visit := κ .visit) fits (Nat.le_refl (κ .secondElement))
  simp only [secondLoopBound]
  omega

theorem beginBound_mono (κ : Costs) (capacity : Nat) {width limit : Nat} (fits : width ≤ limit) :
    beginBound κ capacity width ≤ beginBound κ capacity limit := by
  have := Library.foldl.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .sumTerm))
  have := secondLoopBound_mono κ fits
  simp only [beginBound]
  omega

theorem stepBound_mono (κ : Costs) (count : Nat) {width limit : Nat} (fits : width ≤ limit) :
    stepBound κ count width ≤ stepBound κ count limit := by
  have := Library.foldl.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .sumTerm))
  have := secondLoopBound_mono κ fits
  simp only [stepBound]
  omega

/-- A learner record's entry is within the bound of its entry at the capacity of its
dimension. -/
theorem applyCosted_capacity (κ : Costs) {learnerConfig : Acorn.Config} {space : Dimension}
    (learner : Managed learnerConfig space) (entry : SwiftTd.Entry space)
    (permitted : SwiftTd.Permitted entry learner.phase) :
    (learner.applyCosted entry permitted).Within κ
      (κ .managedEntry + entryBound κ space.capacity space.capacity entry) :=
  (managedApply_costed κ learner entry permitted).mono
    (managedApply_work κ learner entry permitted)

/-- Bound of a model update at `positions` rows, by bounds of a row's and a deviation
learner's update. -/
abbrev updateRowsBound (κ : Costs) (positions rowBound deviationBound : Nat) : Nat :=
  Library.mapFinIdx.work (κ .visit) positions rowBound +
    (Library.mapFinIdx.work (κ .visit) metaCount.word.toNat deviationBound + κ .modelClose)

theorem updateRowsCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Acorn.Costed (Managed (criterion.config .demon) (rankDimension dimension)))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Acorn.Costed (Managed (criterion.config .demon) (rankDimension dimension)))
    (rowBound deviationBound : Nat)
    (rowFits : ∀ position row, (update position row).Within κ rowBound)
    (deviationFits : ∀ action learner, (deviate action learner).Within κ deviationBound) :
    (transition.updateRowsCosted update deviate).Within κ
      (updateRowsBound κ (rankDimension dimension).capacity rowBound deviationBound) := by
  cases transition
  unfold Transition.updateRowsCosted updateRowsBound
  refine Acorn.Costed.bind_within (Acorn.Costed.mapFinIdx_within fun _ => ?_)
    (Acorn.Costed.bind_within (Acorn.Costed.mapFinIdx_within fun _ => deviationFits _ _)
      (Acorn.Costed.op_within _ _ κ))
  exact Acorn.Costed.ite_within (fun _ => rowFits _ _)
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

/-- Bound of a transition part's start over `width` features. -/
abbrev transitionBeginBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + (κ .rankWidth + updateRowsBound κ positions
    (κ .managedEntry + beginBound κ positions (width + 1))
    (κ .managedEntry + beginBound κ positions (width + 1)))

theorem transitionBeginCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transition.beginCosted features).Within κ
      (transitionBeginBound κ (rankDimension dimension).capacity features.indices.length) := by
  have width := transition.ranked.input_length features
  unfold Transition.beginCosted transitionBeginBound
  refine Acorn.Costed.bind_within (inputCosted_within κ transition.ranked features) ?_
  exact Acorn.Costed.charge_within (updateRowsCosted_within κ transition _ _ _ _
    (fun _ row => (applyCosted_capacity κ row _ _).mono
      (Nat.add_le_add_left (beginBound_mono κ _ width) _))
    (fun _ learner => (applyCosted_capacity κ learner _ _).mono
      (Nat.add_le_add_left (beginBound_mono κ _ width) _)))

/-- A transition part's start, with the bound of its costed definition. -/
def transitionBegin (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) :=
  ⟨transition.begin features,
    transitionBeginBound κ (rankDimension dimension).capacity features.indices.length⟩

theorem transitionBegin_val (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionBegin κ transition features).val = transition.begin features := rfl

theorem transitionBegin_work (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionBegin κ transition features).work ≤
      transitionBeginBound κ (rankDimension dimension).capacity features.indices.length :=
  Nat.le_refl _

theorem transitionBegin_costed (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transition.beginCosted features).Within κ (transitionBegin κ transition features).work :=
  transitionBeginCosted_within κ transition features

/-- Bound of a transition part's step over `width` features. -/
abbrev transitionStepBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + (κ .rankWidth + updateRowsBound κ positions
    (κ .managedEntry + stepBound κ positions (width + 1))
    (κ .managedEntry + stepBound κ positions (width + 1)))

theorem transitionStepCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transition.stepCosted features).Within κ
      (transitionStepBound κ (rankDimension dimension).capacity features.indices.length) := by
  have width := transition.ranked.input_length features
  unfold Transition.stepCosted transitionStepBound
  refine Acorn.Costed.bind_within (inputCosted_within κ transition.ranked features) ?_
  exact Acorn.Costed.charge_within (updateRowsCosted_within κ transition _ _ _ _
    (fun _ row => (applyCosted_capacity κ row _ _).mono
      (Nat.add_le_add_left (stepBound_mono κ _ width) _))
    (fun _ learner => (applyCosted_capacity κ learner _ _).mono
      (Nat.add_le_add_left (stepBound_mono κ _ width) _)))

/-- A transition part's step, with the bound of its costed definition. -/
def transitionStep (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) :=
  ⟨transition.step features,
    transitionStepBound κ (rankDimension dimension).capacity features.indices.length⟩

theorem transitionStep_val (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionStep κ transition features).val = transition.step features := rfl

theorem transitionStep_work (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionStep κ transition features).work ≤
      transitionStepBound κ (rankDimension dimension).capacity features.indices.length :=
  Nat.le_refl _

theorem transitionStep_costed (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transition.stepCosted features).Within κ (transitionStep κ transition features).work :=
  transitionStepCosted_within κ transition features

/-- Bound of an outcome over `width` features at `positions` ranked positions. -/
abbrev outcomeBound (κ : Costs) (positions width : Nat) : Nat :=
  indicatorBound κ width positions +
    (predictAllBound κ metaCount.word.toNat width + (rankedValuesBound κ positions +
      (comparisonBound κ metaCount.word.toNat + (comparisonBound κ metaCount.word.toNat +
        (Library.ofFn.work (κ .visit) metaCount.word.toNat (κ .deviation) + 0)))))

theorem outcomeCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (transition.outcomeCosted value features).Within κ
      (outcomeBound κ (rankDimension dimension).capacity features.indices.length) :=
  Acorn.Costed.bind_within (indicatorCosted_within κ transition.ranked features)
    (Acorn.Costed.bind_within (predictAllCosted_within κ value.controller features)
      (Acorn.Costed.bind_within (rankedValuesCosted_within κ value transition.ranked _)
        (Acorn.Costed.bind_within (comparisonValueCosted_within κ criterion _)
          (Acorn.Costed.bind_within (comparisonValueCosted_within κ criterion _)
            (Acorn.Costed.bind_within
              (Acorn.Costed.ofFn_within fun _ => Acorn.Costed.op_within _ _ κ)
              (Acorn.Costed.pure_within _ κ))))))

/-- An outcome, with the bound of its costed definition. -/
def outcome (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Costed (Outcome dimension) :=
  ⟨transition.outcome value features,
    outcomeBound κ (rankDimension dimension).capacity features.indices.length⟩

theorem outcome_val (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (outcome κ transition value features).val = transition.outcome value features := by
  unfold outcome
  rfl

theorem outcome_work (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (outcome κ transition value features).work ≤
      outcomeBound κ (rankDimension dimension).capacity features.indices.length :=
  Nat.le_refl _

theorem outcome_costed (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (transition.outcomeCosted value features).Within κ
      (outcome κ transition value features).work :=
  outcomeCosted_within κ transition value features

/-- A model learner's bound of a terminal entry. -/
abbrev modelTerminalBound (κ : Costs) (capacity : Nat) : Nat :=
  κ .managedEntry + terminalBound κ capacity capacity

theorem transitionTerminalCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transition.terminalCosted outcome).Within κ
      ((κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
        (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)
        (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity))) :=
  Acorn.Costed.charge_within (updateRowsCosted_within κ transition _ _ _ _
    (fun _ row => Acorn.Costed.charge_within (applyCosted_capacity κ row _ _))
    (fun _ learner => Acorn.Costed.charge_within (applyCosted_capacity κ learner _ _)))

/-- A transition part's terminal step, with the bound of its costed definition. -/
def transitionTerminal (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  ⟨transition.terminal outcome,
    κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
    (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)
    (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)⟩

theorem transitionTerminal_val (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionTerminal κ transition outcome).val = transition.terminal outcome := rfl

theorem transitionTerminal_work (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionTerminal κ transition outcome).work ≤
      (κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
        (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)
        (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)) :=
  Nat.le_refl _

theorem transitionTerminal_costed (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transition.terminalCosted outcome).Within κ (transitionTerminal κ transition outcome).work :=
  transitionTerminalCosted_within κ transition outcome

/-- Bound of a stopped trajectory at a capacity. -/
abbrev stopTrajectoryBound (κ : Costs) (capacity : Nat) : Nat :=
  κ .learnerError + ((κ .managedEntry + firstLoopBound κ capacity) +
    (κ .managedEntry + releaseBound κ capacity))

theorem stopTrajectoryCosted_within {learnerConfig : Acorn.Config} {space : Dimension}
    (κ : Costs) (learner : Managed learnerConfig space) (target : Binary32) :
    (learner.stopTrajectoryCosted target).Within κ (stopTrajectoryBound κ space.capacity) :=
  Acorn.Costed.charge_within (Acorn.Costed.bind_within
    (Acorn.Costed.attach_within (applyCosted_capacity κ learner _ _))
    (applyCosted_capacity κ _ .release _))

/-- A stopped trajectory, with the bound of its costed definition. -/
def stopTrajectory {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    Costed (Managed learnerConfig space) :=
  ⟨learner.stopTrajectory target, stopTrajectoryBound κ space.capacity⟩

theorem stopTrajectory_val {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    (stopTrajectory κ learner target).val = learner.stopTrajectory target := rfl

theorem stopTrajectory_work {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    (stopTrajectory κ learner target).work ≤ stopTrajectoryBound κ space.capacity :=
  Nat.le_refl _

theorem stopTrajectory_costed {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    (learner.stopTrajectoryCosted target).Within κ (stopTrajectory κ learner target).work :=
  stopTrajectoryCosted_within κ learner target

theorem transitionStopCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transition.stopCosted outcome).Within κ
      ((κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
        (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity)
        (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity))) :=
  Acorn.Costed.charge_within (updateRowsCosted_within κ transition _ _ _ _
    (fun _ row => Acorn.Costed.charge_within (stopTrajectoryCosted_within κ row _))
    (fun _ learner => Acorn.Costed.charge_within (stopTrajectoryCosted_within κ learner _)))

/-- A transition part's stopped trajectory, with the bound of its costed definition. -/
def transitionStop (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  ⟨transition.stop outcome, κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
    (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity)
    (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity)⟩

theorem transitionStop_val (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionStop κ transition outcome).val = transition.stop outcome := rfl

theorem transitionStop_work (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionStop κ transition outcome).work ≤
      (κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
        (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity)
        (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity)) :=
  Nat.le_refl _

theorem transitionStop_costed (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transition.stopCosted outcome).Within κ (transitionStop κ transition outcome).work :=
  transitionStopCosted_within κ transition outcome

/-- Bound of a restarted trajectory over `width` features at a capacity. -/
abbrev restartTrajectoryBound (κ : Costs) (capacity width : Nat) : Nat :=
  (κ .managedEntry + releaseBound κ capacity) + (κ .managedEntry + stepBound κ capacity width)

theorem restartTrajectoryCosted_within {learnerConfig : Acorn.Config} {space : Dimension}
    (κ : Costs) (learner : Managed learnerConfig space) (features : SwiftTd.ActiveSet space) :
    (learner.restartTrajectoryCosted features).Within κ
      (restartTrajectoryBound κ space.capacity features.indices.length) :=
  Acorn.Costed.bind_within (applyCosted_capacity κ learner .release trivial)
    (applyCosted_capacity κ _ (.step features .zero) trivial)

/-- Bound of a transition part's restart over `width` features. -/
abbrev transitionRestartBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + (κ .rankWidth + updateRowsBound κ positions
    (restartTrajectoryBound κ positions (width + 1))
    (restartTrajectoryBound κ positions (width + 1)))

theorem transitionRestartCosted_within (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transition.restartCosted features).Within κ
      (transitionRestartBound κ (rankDimension dimension).capacity features.indices.length) := by
  have width := transition.ranked.input_length features
  unfold Transition.restartCosted transitionRestartBound
  refine Acorn.Costed.bind_within (inputCosted_within κ transition.ranked features) ?_
  exact Acorn.Costed.charge_within (updateRowsCosted_within κ transition _ _ _ _
    (fun _ row => (restartTrajectoryCosted_within κ row _).mono
      (Nat.add_le_add_left (Nat.add_le_add_left (stepBound_mono κ _ width) _) _))
    (fun _ learner => (restartTrajectoryCosted_within κ learner _).mono
      (Nat.add_le_add_left (Nat.add_le_add_left (stepBound_mono κ _ width) _) _)))

/-! ## A whole model -/

/-- Bound of a model start over `width` features. -/
abbrev modelBeginBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  κ .hashFeature + inputBound κ width +
    (3 * (κ .managedEntry + beginBound κ capacity (width + 1)) +
      (transitionBeginBound κ positions width + κ .modelClose))

theorem modelBeginCosted_within (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) :
    (model.beginCosted base).Within κ
      (modelBeginBound κ dimension.capacity (rankDimension dimension).capacity
        base.indices.length) := by
  have width := modelInput_length criterion base ⟨0, by decide⟩
  have learner := fun {learnerConfig : Acorn.Config} (row : Managed learnerConfig dimension) =>
    (applyCosted_capacity κ row (.beginTrajectory (Features.modelInput criterion base
      ⟨0, by decide⟩)) trivial).mono
      (Nat.add_le_add_left (beginBound_mono κ dimension.capacity width) _)
  cases model with
  | discounted r c t =>
    unfold Model.beginCosted
    refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
      (modelInputCosted_within κ _ base _)
      (Acorn.Costed.bind_within (learner r) (Acorn.Costed.bind_within (learner c)
        (Acorn.Costed.bind_within (transitionBeginCosted_within κ t base)
          (Acorn.Costed.op_within _ _ κ))))) ?_
    simp only [modelBeginBound]
    omega
  | differential r c d t =>
    unfold Model.beginCosted
    refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
      (modelInputCosted_within κ _ base _)
      (Acorn.Costed.bind_within (learner r) (Acorn.Costed.bind_within (learner c)
        (Acorn.Costed.bind_within (learner d)
          (Acorn.Costed.bind_within (transitionBeginCosted_within κ t base)
            (Acorn.Costed.op_within _ _ κ)))))) ?_
    simp only [modelBeginBound]
    omega

/-- A model start, with the bound of its costed definition. -/
def modelBegin (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) : Costed (Model dimension criterion) :=
  ⟨model.begin base,
    modelBeginBound κ dimension.capacity (rankDimension dimension).capacity base.indices.length⟩

theorem modelBegin_val (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) : (modelBegin κ model base).val = model.begin base := rfl

theorem modelBegin_work (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) :
    (modelBegin κ model base).work ≤
      modelBeginBound κ dimension.capacity (rankDimension dimension).capacity
        base.indices.length :=
  Nat.le_refl _

theorem modelBegin_costed (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) :
    (model.beginCosted base).Within κ (modelBegin κ model base).work :=
  modelBeginCosted_within κ model base

/-- Bound of a model step over `width` features. -/
abbrev modelStepBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  κ .hashFeature + inputBound κ width +
    (3 * (κ .managedEntry + stepBound κ capacity (width + 1)) +
      (transitionStepBound κ positions width + κ .modelClose))

theorem modelStepCosted_within (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    (model.stepCosted base age reward).Within κ
      (modelStepBound κ dimension.capacity (rankDimension dimension).capacity
        base.indices.length) := by
  have width := modelInput_length criterion base age
  have learner := fun {learnerConfig : Acorn.Config} (row : Managed learnerConfig dimension)
      (target : Binary32) =>
    (applyCosted_capacity κ row (.step (Features.modelInput criterion base age) target)
      trivial).mono (Nat.add_le_add_left (stepBound_mono κ dimension.capacity width) _)
  cases model with
  | discounted r c t =>
    unfold Model.stepCosted
    refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
      (modelInputCosted_within κ _ base age)
      (Acorn.Costed.bind_within (learner r reward) (Acorn.Costed.bind_within (learner c .zero)
        (Acorn.Costed.bind_within (transitionStepCosted_within κ t base)
          (Acorn.Costed.op_within _ _ κ))))) ?_
    simp only [modelStepBound]
    omega
  | differential r c d t =>
    unfold Model.stepCosted
    refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
      (modelInputCosted_within κ _ base age)
      (Acorn.Costed.bind_within (learner r reward) (Acorn.Costed.bind_within (learner c .zero)
        (Acorn.Costed.bind_within (learner d .one)
          (Acorn.Costed.bind_within (transitionStepCosted_within κ t base)
            (Acorn.Costed.op_within _ _ κ)))))) ?_
    simp only [modelStepBound]
    omega

/-- A model step, with the bound of its costed definition. -/
def modelStep (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    Costed (Model dimension criterion) :=
  ⟨model.step base age reward,
    modelStepBound κ dimension.capacity (rankDimension dimension).capacity base.indices.length⟩

theorem modelStep_val (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    (modelStep κ model base age reward).val = model.step base age reward := rfl

theorem modelStep_work (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    (modelStep κ model base age reward).work ≤
      modelStepBound κ dimension.capacity (rankDimension dimension).capacity
        base.indices.length :=
  Nat.le_refl _

theorem modelStep_costed (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    (model.stepCosted base age reward).Within κ (modelStep κ model base age reward).work :=
  modelStepCosted_within κ model base age reward

/-- Bound of a model's terminal step over `width` features. -/
abbrev modelTerminalWorkBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  outcomeBound κ positions width + (3 * modelTerminalBound κ capacity +
    ((κ .rankWidth + updateRowsBound κ positions
      (κ .learnerError + modelTerminalBound κ positions)
      (κ .learnerError + modelTerminalBound κ positions)) + κ .modelClose))

theorem modelTerminalCosted_within (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (model.terminalCosted value features reward).Within κ
      (modelTerminalWorkBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length) := by
  have learner := fun {learnerConfig : Acorn.Config} (row : Managed learnerConfig dimension)
      (target : Binary32) =>
    show (row.applyCosted (.terminal target) trivial).Within κ
        (modelTerminalBound κ dimension.capacity) from
      applyCosted_capacity κ row (.terminal target) trivial
  cases model with
  | discounted r c t =>
    unfold Model.terminalCosted
    refine Acorn.Costed.Within.mono
      (Acorn.Costed.bind_within (outcomeCosted_within κ t value features)
        (Acorn.Costed.bind_within (learner r _) (Acorn.Costed.bind_within (learner c _)
          (Acorn.Costed.bind_within (transitionTerminalCosted_within κ t _)
            (Acorn.Costed.op_within _ _ κ))))) ?_
    simp only [modelTerminalWorkBound]
    omega
  | differential r c d t =>
    unfold Model.terminalCosted
    refine Acorn.Costed.Within.mono
      (Acorn.Costed.bind_within (outcomeCosted_within κ t value features)
        (Acorn.Costed.bind_within (learner r _) (Acorn.Costed.bind_within (learner c _)
          (Acorn.Costed.bind_within (learner d _)
            (Acorn.Costed.bind_within (transitionTerminalCosted_within κ t _)
              (Acorn.Costed.op_within _ _ κ)))))) ?_
    simp only [modelTerminalWorkBound]
    omega

/-- A model's terminal step, with the bound of its costed definition. -/
def modelTerminal (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  ⟨model.terminal value features reward, modelTerminalWorkBound κ dimension.capacity
    (rankDimension dimension).capacity features.indices.length⟩

theorem modelTerminal_val (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelTerminal κ model value features reward).val = model.terminal value features reward :=
  rfl

theorem modelTerminal_work (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelTerminal κ model value features reward).work ≤
      modelTerminalWorkBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length :=
  Nat.le_refl _

theorem modelTerminal_costed (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (model.terminalCosted value features reward).Within κ
      (modelTerminal κ model value features reward).work :=
  modelTerminalCosted_within κ model value features reward

/-- Bound of a model's stopped trajectory over `width` features. -/
abbrev modelStopBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  outcomeBound κ positions width + (3 * stopTrajectoryBound κ capacity +
    ((κ .rankWidth + updateRowsBound κ positions
      (κ .learnerError + stopTrajectoryBound κ positions)
      (κ .learnerError + stopTrajectoryBound κ positions)) + κ .modelClose))

theorem modelStopCosted_within (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (model.stopCosted value features reward).Within κ
      (modelStopBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length) := by
  cases model with
  | discounted r c t =>
    unfold Model.stopCosted
    refine Acorn.Costed.Within.mono
      (Acorn.Costed.bind_within (outcomeCosted_within κ t value features)
        (Acorn.Costed.bind_within (stopTrajectoryCosted_within κ r _)
          (Acorn.Costed.bind_within (stopTrajectoryCosted_within κ c _)
            (Acorn.Costed.bind_within (transitionStopCosted_within κ t _)
              (Acorn.Costed.op_within _ _ κ))))) ?_
    simp only [modelStopBound]
    omega
  | differential r c d t =>
    unfold Model.stopCosted
    refine Acorn.Costed.Within.mono
      (Acorn.Costed.bind_within (outcomeCosted_within κ t value features)
        (Acorn.Costed.bind_within (stopTrajectoryCosted_within κ r _)
          (Acorn.Costed.bind_within (stopTrajectoryCosted_within κ c _)
            (Acorn.Costed.bind_within (stopTrajectoryCosted_within κ d _)
              (Acorn.Costed.bind_within (transitionStopCosted_within κ t _)
                (Acorn.Costed.op_within _ _ κ)))))) ?_
    simp only [modelStopBound]
    omega

/-- A model's stopped trajectory, with the bound of its costed definition. -/
def modelStop (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  ⟨model.stop value features reward,
    modelStopBound κ dimension.capacity (rankDimension dimension).capacity
      features.indices.length⟩

theorem modelStop_val (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelStop κ model value features reward).val = model.stop value features reward := rfl

theorem modelStop_work (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelStop κ model value features reward).work ≤
      modelStopBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length :=
  Nat.le_refl _

theorem modelStop_costed (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (model.stopCosted value features reward).Within κ
      (modelStop κ model value features reward).work :=
  modelStopCosted_within κ model value features reward

/-- Bound of a model restart over `width` features. -/
abbrev modelRestartBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  κ .hashFeature + inputBound κ width +
    (3 * restartTrajectoryBound κ capacity (width + 1) +
      (transitionRestartBound κ positions width + κ .modelClose))

theorem modelRestartCosted_within (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    (model.restartCosted base age).Within κ
      (modelRestartBound κ dimension.capacity (rankDimension dimension).capacity
        base.indices.length) := by
  have width := modelInput_length criterion base age
  have learner := fun {learnerConfig : Acorn.Config} (row : Managed learnerConfig dimension) =>
    (restartTrajectoryCosted_within κ row (Features.modelInput criterion base age)).mono
      (Nat.add_le_add_left (Nat.add_le_add_left (stepBound_mono κ dimension.capacity width) _) _)
  cases model with
  | discounted r c t =>
    unfold Model.restartCosted
    refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
      (modelInputCosted_within κ _ base age)
      (Acorn.Costed.bind_within (learner r) (Acorn.Costed.bind_within (learner c)
        (Acorn.Costed.bind_within (transitionRestartCosted_within κ t base)
          (Acorn.Costed.op_within _ _ κ))))) ?_
    simp only [modelRestartBound, restartTrajectoryBound]
    omega
  | differential r c d t =>
    unfold Model.restartCosted
    refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
      (modelInputCosted_within κ _ base age)
      (Acorn.Costed.bind_within (learner r) (Acorn.Costed.bind_within (learner c)
        (Acorn.Costed.bind_within (learner d)
          (Acorn.Costed.bind_within (transitionRestartCosted_within κ t base)
            (Acorn.Costed.op_within _ _ κ)))))) ?_
    simp only [modelRestartBound, restartTrajectoryBound]
    omega

end AcornVerif.Resource.Twin
