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
(`Acorn.RankedFeatures`) and of its prediction (`Acorn.Models`), and twins of its updates, which
are not yet costed. Each definition here for a costed definition is the executed function with
the bound proved of its costed definition as its work, and its `_costed` theorem checks that the
costed definition is within it. A transition part has one row
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

/-- Twin of `Transition.updateRows`: every row visited, the rows of occupied positions
updated, and every deviation learner updated. -/
def updateRows (κ : Costs) (transition : Transition dimension criterion)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Costed (Managed (criterion.config .demon) (rankDimension dimension)))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Costed (Managed (criterion.config .demon) (rankDimension dimension))) :
    Costed (Transition dimension criterion) := do
  let rows ← Costed.mapFinIdx (κ .visit)
    (fun index row bound => Costed.ite ((transition.ranked.slots[index]'bound).isSome = true)
      (update ⟨index, bound⟩ row) (Costed.pure row))
    transition.rows
  let deviations ← Costed.mapFinIdx (κ .visit)
    (fun index learner bound => deviate ⟨index, bound⟩ learner) transition.deviations
  Costed.op (κ .modelClose) ⟨transition.ranked, rows, deviations⟩

/-- Bound of a model update at `positions` rows, by bounds of a row's and a deviation
learner's update. -/
abbrev updateRowsBound (κ : Costs) (positions rowBound deviationBound : Nat) : Nat :=
  Library.mapFinIdx.work (κ .visit) positions rowBound +
    (Library.mapFinIdx.work (κ .visit) metaCount.word.toNat deviationBound + κ .modelClose)

theorem updateRows_work (κ : Costs) (transition : Transition dimension criterion)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Costed (Managed (criterion.config .demon) (rankDimension dimension)))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Costed (Managed (criterion.config .demon) (rankDimension dimension)))
    (rowBound deviationBound : Nat)
    (rowFits : ∀ position row, (update position row).work ≤ rowBound)
    (deviationFits : ∀ action learner, (deviate action learner).work ≤ deviationBound) :
    (updateRows κ transition update deviate).work ≤
      updateRowsBound κ (rankDimension dimension).capacity rowBound deviationBound :=
  Costed.bind_work_le
    (Costed.mapFinIdx_work_le (κ .visit) rowBound _ _ fun _ _ _ =>
      Nat.le_trans (Costed.ite_work_le _ _ _) (Nat.max_le.mpr ⟨rowFits _ _, Nat.zero_le _⟩))
    fun _ => Costed.bind_work_le
      (Costed.mapFinIdx_work_le (κ .visit) deviationBound _ _ fun _ _ _ => deviationFits _ _)
      fun _ => Nat.le_refl _

/-- Twin of `Transition.begin`: the row input, the ranked dimension the updates read, which
evaluates the ranked width, and the updates. -/
def transitionBegin (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) := do
  let input ← rankedInput κ transition.ranked features
  Costed.charge (κ .rankWidth)
    (updateRows κ transition (fun _ row => managedApply κ row (.beginTrajectory input) trivial)
      (fun _ learner => managedApply κ learner (.beginTrajectory input) trivial))

theorem transitionBegin_val (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionBegin κ transition features).val = transition.begin features := by
  cases transition
  rfl

/-- Bound of a transition part's start over `width` features. -/
abbrev transitionBeginBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + (κ .rankWidth + updateRowsBound κ positions
    (κ .managedEntry + beginBound κ positions (width + 1))
    (κ .managedEntry + beginBound κ positions (width + 1)))

theorem transitionBegin_work (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionBegin κ transition features).work ≤
      transitionBeginBound κ (rankDimension dimension).capacity features.indices.length := by
  have width := transition.ranked.input_length features
  unfold transitionBegin
  exact Costed.bind_work_le_at (rankedInput_work κ transition.ranked features)
    (Costed.charge_work_le (updateRows_work κ transition _ _ _ _
      (fun _ row => Nat.le_trans (managedApply_work κ row (.beginTrajectory _) trivial)
        (Nat.add_le_add_left (beginBound_mono κ _ width) _))
      (fun _ learner => Nat.le_trans (managedApply_work κ learner (.beginTrajectory _) trivial)
        (Nat.add_le_add_left (beginBound_mono κ _ width) _))))

/-- Twin of `Transition.step`: the row input, the ranked dimension the updates read, which
evaluates the ranked width, and the updates. -/
def transitionStep (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) := do
  let input ← rankedInput κ transition.ranked features
  Costed.charge (κ .rankWidth)
    (updateRows κ transition (fun _ row => managedApply κ row (.step input .zero) trivial)
      (fun _ learner => managedApply κ learner (.step input .zero) trivial))

theorem transitionStep_val (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionStep κ transition features).val = transition.step features := by
  cases transition
  rfl

/-- Bound of a transition part's step over `width` features. -/
abbrev transitionStepBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + (κ .rankWidth + updateRowsBound κ positions
    (κ .managedEntry + stepBound κ positions (width + 1))
    (κ .managedEntry + stepBound κ positions (width + 1)))

theorem transitionStep_work (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionStep κ transition features).work ≤
      transitionStepBound κ (rankDimension dimension).capacity features.indices.length := by
  have width := transition.ranked.input_length features
  unfold transitionStep
  exact Costed.bind_work_le_at (rankedInput_work κ transition.ranked features)
    (Costed.charge_work_le (updateRows_work κ transition _ _ _ _
      (fun _ row => Nat.le_trans (managedApply_work κ row (.step _ _) trivial)
        (Nat.add_le_add_left (stepBound_mono κ _ width) _))
      (fun _ learner => Nat.le_trans (managedApply_work κ learner (.step _ _) trivial)
        (Nat.add_le_add_left (stepBound_mono κ _ width) _))))

/-- Twin of `Transition.outcome`: the indicator, the value function's predictions, the
ranked values, the two nominal values and each meta action's deviation. -/
def outcome (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Costed (Outcome dimension) := do
  let seen ← indicator κ transition.ranked features
  let complete ← predictAll κ value.controller features
  let ranked ← rankedValues κ value transition.ranked seen
  let all ← comparisonValue κ criterion (⟨complete, value.epsilon⟩ : PolicySnapshot metaCount)
  let part ← comparisonValue κ criterion (⟨ranked, value.epsilon⟩ : PolicySnapshot metaCount)
  let residual := all.sub part
  let deviations ← Costed.ofFn (κ .visit) fun action => Costed.op (κ .deviation)
    (criterion.rule.gamma.mul (((complete.get action).sub (ranked.get action)).sub residual))
  Costed.pure ⟨seen, criterion.rule.gamma.mul residual, deviations⟩

theorem outcome_val (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (outcome κ transition value features).val = transition.outcome value features := rfl

/-- Bound of an outcome over `width` features at `positions` ranked positions. -/
abbrev outcomeBound (κ : Costs) (positions width : Nat) : Nat :=
  indicatorBound κ width positions +
    (predictAllBound κ metaCount.word.toNat width + (rankedValuesBound κ positions +
      (comparisonBound κ metaCount.word.toNat + (comparisonBound κ metaCount.word.toNat +
        (Library.ofFn.work (κ .visit) metaCount.word.toNat (κ .deviation) + 0)))))

theorem outcome_work (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (outcome κ transition value features).work ≤
      outcomeBound κ (rankDimension dimension).capacity features.indices.length :=
  Costed.bind_work_le (indicator_work κ transition.ranked features) fun seen =>
    Costed.bind_work_le (predictAll_work κ value.controller features) fun complete =>
      Costed.bind_work_le (rankedValues_work κ value transition.ranked seen) fun ranked =>
        Costed.bind_work_le (comparisonValue_work κ criterion
          (⟨complete, value.epsilon⟩ : PolicySnapshot metaCount)) fun _ =>
          Costed.bind_work_le (comparisonValue_work κ criterion
            (⟨ranked, value.epsilon⟩ : PolicySnapshot metaCount)) fun _ =>
            Costed.bind_work_le (Costed.ofFn_work_le _ _ _ fun _ => Nat.le_refl _) fun _ =>
              Nat.le_refl _

/-- A model learner's bound of a terminal entry. -/
abbrev modelTerminalBound (κ : Costs) (capacity : Nat) : Nat :=
  κ .managedEntry + terminalBound κ capacity capacity

/-- Twin of `Transition.terminal`: the ranked dimension the updates read, which evaluates the
ranked width, and the updates, each with the target it reads. -/
def transitionTerminal (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  Costed.charge (κ .rankWidth) (updateRows κ transition
    (fun position row => Costed.charge (κ .learnerError) (managedApply κ row
      (.terminal (criterion.rule.gamma.mul (outcome.seen.get position).value)) trivial))
    (fun action learner => Costed.charge (κ .learnerError)
      (managedApply κ learner (.terminal (outcome.deviations.get action)) trivial)))

theorem transitionTerminal_val (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionTerminal κ transition outcome).val = transition.terminal outcome := by
  cases transition
  rfl

theorem transitionTerminal_work (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionTerminal κ transition outcome).work ≤
      κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
        (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)
        (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity) :=
  Costed.charge_work_le (updateRows_work κ transition _ _ _ _
    (fun _ row => Costed.charge_work_le (managedApply_work κ row (.terminal _) trivial))
    (fun _ learner => Costed.charge_work_le (managedApply_work κ learner (.terminal _) trivial)))

/-- Twin of `Managed.stopTrajectory`: the error, a first loop, then a release. -/
def stopTrajectory {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    Costed (Managed learnerConfig space) := Costed.charge (κ .learnerError) (do
  let first ← managedApply κ learner
    (.first (target.sub learner.state.transient.vOld) learner.state.transient.vDelta .zero) trivial
  managedApply κ first .release trivial)

theorem stopTrajectory_val {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    (stopTrajectory κ learner target).val = learner.stopTrajectory target := rfl

/-- Bound of a stopped trajectory at a capacity. -/
abbrev stopTrajectoryBound (κ : Costs) (capacity : Nat) : Nat :=
  κ .learnerError + ((κ .managedEntry + firstLoopBound κ capacity) +
    (κ .managedEntry + releaseBound κ capacity))

theorem stopTrajectory_work {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    (stopTrajectory κ learner target).work ≤ stopTrajectoryBound κ space.capacity :=
  Costed.charge_work_le (Costed.bind_work_le (managedApply_work κ learner (.first _ _ _) trivial)
    fun first => managedApply_work κ first .release trivial)

/-- Twin of `Transition.stop`: the ranked dimension the updates read, which evaluates the ranked
width, and the updates, each with the target it reads. -/
def transitionStop (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  Costed.charge (κ .rankWidth) (updateRows κ transition
    (fun position row => Costed.charge (κ .learnerError) (stopTrajectory κ row
      (criterion.rule.gamma.mul (outcome.seen.get position).value)))
    (fun action learner => Costed.charge (κ .learnerError)
      (stopTrajectory κ learner (outcome.deviations.get action))))

theorem transitionStop_val (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionStop κ transition outcome).val = transition.stop outcome := by
  cases transition
  rfl

theorem transitionStop_work (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionStop κ transition outcome).work ≤
      κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
        (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity)
        (κ .learnerError + stopTrajectoryBound κ (rankDimension dimension).capacity) :=
  Costed.charge_work_le (updateRows_work κ transition _ _ _ _
    (fun _ row => Costed.charge_work_le (stopTrajectory_work κ row _))
    (fun _ learner => Costed.charge_work_le (stopTrajectory_work κ learner _)))

/-! ## A whole model -/

/-- The costed composition of `Model.begin`: the model input, then each learner's start. -/
def modelBeginRun (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) : Costed (Model dimension criterion) :=
  match model with
  | .discounted reward continuation transition => do
    let features ← modelInput κ .discounted base ⟨0, by decide⟩
    let reward ← managedApply κ reward (.beginTrajectory features) trivial
    let continuation ← managedApply κ continuation (.beginTrajectory features) trivial
    let transition ← transitionBegin κ transition base
    Costed.op (κ .modelClose) (.discounted reward continuation transition)
  | .differential reward continuation duration transition => do
    let features ← modelInput κ .differential base ⟨0, by decide⟩
    let reward ← managedApply κ reward (.beginTrajectory features) trivial
    let continuation ← managedApply κ continuation (.beginTrajectory features) trivial
    let duration ← managedApply κ duration (.beginTrajectory features) trivial
    let transition ← transitionBegin κ transition base
    Costed.op (κ .modelClose) (.differential reward continuation duration transition)

theorem modelBeginRun_val (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) : (modelBeginRun κ model base).val = model.begin base := by
  cases model <;> simp only [modelBeginRun, Costed.bind_val, transitionBegin_val] <;> rfl

/-- Twin of `Model.begin`. -/
def modelBegin (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) : Costed (Model dimension criterion) :=
  Costed.via (model.begin base) (modelBeginRun κ model base)

/-- Bound of a model start over `width` features. -/
abbrev modelBeginBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  κ .hashFeature + inputBound κ width +
    (3 * (κ .managedEntry + beginBound κ capacity (width + 1)) +
      (transitionBeginBound κ positions width + κ .modelClose))

theorem modelBegin_work (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) :
    (modelBegin κ model base).work ≤
      modelBeginBound κ dimension.capacity (rankDimension dimension).capacity
        base.indices.length := by
  have width := fun criterion age => modelInput_length (dimension := dimension) criterion base age
  have learner := fun {config : Acorn.Config} (row : Managed config dimension)
      (features : SwiftTd.ActiveSet dimension)
      (fits : features.indices.length ≤ base.indices.length + 1) =>
    Nat.le_trans (managedApply_work κ row (.beginTrajectory features) trivial)
      (Nat.add_le_add_left (beginBound_mono κ dimension.capacity fits) _)
  change (modelBeginRun κ model base).work ≤ _
  cases model with
  | discounted reward continuation transition =>
    unfold modelBeginRun
    refine Nat.le_trans (Costed.bind_work_le_at
      (modelInput_work κ .discounted base ⟨0, by decide⟩)
      (Costed.bind_work_le_at (learner reward _ (width _ _))
        (Costed.bind_work_le (learner continuation _ (width _ _)) fun _ =>
          Costed.bind_work_le (transitionBegin_work κ transition base) fun _ =>
            Nat.le_refl _))) ?_
    simp only [modelBeginBound]
    omega
  | differential reward continuation duration transition =>
    unfold modelBeginRun
    refine Nat.le_trans (Costed.bind_work_le_at
      (modelInput_work κ .differential base ⟨0, by decide⟩)
      (Costed.bind_work_le_at (learner reward _ (width _ _))
        (Costed.bind_work_le (learner continuation _ (width _ _)) fun _ =>
          Costed.bind_work_le (learner duration _ (width _ _)) fun _ =>
            Costed.bind_work_le (transitionBegin_work κ transition base) fun _ =>
              Nat.le_refl _))) ?_
    simp only [modelBeginBound]
    omega

/-- The costed composition of `Model.step`: the model input, then each learner's step. -/
def modelStepRun (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    Costed (Model dimension criterion) :=
  match model with
  | .discounted r c transition => do
    let features ← modelInput κ .discounted base age
    let r ← managedApply κ r (.step features reward) trivial
    let c ← managedApply κ c (.step features .zero) trivial
    let transition ← transitionStep κ transition base
    Costed.op (κ .modelClose) (.discounted r c transition)
  | .differential r c d transition => do
    let features ← modelInput κ .differential base age
    let r ← managedApply κ r (.step features reward) trivial
    let c ← managedApply κ c (.step features .zero) trivial
    let d ← managedApply κ d (.step features .one) trivial
    let transition ← transitionStep κ transition base
    Costed.op (κ .modelClose) (.differential r c d transition)

theorem modelStepRun_val (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    (modelStepRun κ model base age reward).val = model.step base age reward := by
  cases model <;> simp only [modelStepRun, Costed.bind_val, transitionStep_val] <;> rfl

/-- Twin of `Model.step`. -/
def modelStep (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    Costed (Model dimension criterion) :=
  Costed.via (model.step base age reward) (modelStepRun κ model base age reward)

/-- Bound of a model step over `width` features. -/
abbrev modelStepBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  κ .hashFeature + inputBound κ width +
    (3 * (κ .managedEntry + stepBound κ capacity (width + 1)) +
      (transitionStepBound κ positions width + κ .modelClose))

theorem modelStep_work (κ : Costs) (model : Model dimension criterion)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) (reward : Binary32) :
    (modelStep κ model base age reward).work ≤
      modelStepBound κ dimension.capacity (rankDimension dimension).capacity
        base.indices.length := by
  have width := modelInput_length (dimension := dimension) criterion base age
  have learner := fun {config : Acorn.Config} (row : Managed config dimension)
      (features : SwiftTd.ActiveSet dimension) (target : Binary32)
      (fits : features.indices.length ≤ base.indices.length + 1) =>
    Nat.le_trans (managedApply_work κ row (.step features target) trivial)
      (Nat.add_le_add_left (stepBound_mono κ dimension.capacity fits) _)
  change (modelStepRun κ model base age reward).work ≤ _
  cases model with
  | discounted r c transition =>
    unfold modelStepRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ .discounted base age)
      (Costed.bind_work_le_at (learner r _ _ width)
        (Costed.bind_work_le (learner c _ _ width) fun _ =>
          Costed.bind_work_le (transitionStep_work κ transition base) fun _ =>
            Nat.le_refl _))) ?_
    simp only [modelStepBound]
    omega
  | differential r c d transition =>
    unfold modelStepRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ .differential base age)
      (Costed.bind_work_le_at (learner r _ _ width)
        (Costed.bind_work_le (learner c _ _ width) fun _ =>
          Costed.bind_work_le (learner d _ _ width) fun _ =>
            Costed.bind_work_le (transitionStep_work κ transition base) fun _ =>
              Nat.le_refl _))) ?_
    simp only [modelStepBound]
    omega

/-- The costed composition of `Model.terminal`: the outcome, then each learner's terminal
step. -/
def modelTerminalRun (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  match model with
  | .discounted r c transition => do
    let result ← outcome κ transition value features
    let r ← managedApply κ r (.terminal reward) trivial
    let c ← managedApply κ c (.terminal result.shared) trivial
    let transition ← transitionTerminal κ transition result
    Costed.op (κ .modelClose) (.discounted r c transition)
  | .differential r c d transition => do
    let result ← outcome κ transition value features
    let r ← managedApply κ r (.terminal reward) trivial
    let c ← managedApply κ c (.terminal result.shared) trivial
    let d ← managedApply κ d (.terminal .one) trivial
    let transition ← transitionTerminal κ transition result
    Costed.op (κ .modelClose) (.differential r c d transition)

theorem modelTerminalRun_val (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelTerminalRun κ model value features reward).val =
      model.terminal value features reward := by
  cases model <;> simp only [modelTerminalRun, Costed.bind_val, transitionTerminal_val] <;> rfl

/-- Twin of `Model.terminal`. -/
def modelTerminal (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  Costed.via (model.terminal value features reward) (modelTerminalRun κ model value features reward)

/-- Bound of a model's terminal step over `width` features. -/
abbrev modelTerminalWorkBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  outcomeBound κ positions width + (3 * modelTerminalBound κ capacity +
    ((κ .rankWidth + updateRowsBound κ positions
      (κ .learnerError + modelTerminalBound κ positions)
      (κ .learnerError + modelTerminalBound κ positions)) + κ .modelClose))

theorem modelTerminal_work (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelTerminal κ model value features reward).work ≤
      modelTerminalWorkBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length := by
  have learner := fun {config : Acorn.Config} (row : Managed config dimension)
      (target : Binary32) =>
    show (managedApply κ row (.terminal target) trivial).work ≤
        modelTerminalBound κ dimension.capacity from
      managedApply_work κ row (.terminal target) trivial
  change (modelTerminalRun κ model value features reward).work ≤ _
  cases model with
  | discounted r c transition =>
    unfold modelTerminalRun
    refine Nat.le_trans (Costed.bind_work_le (outcome_work κ transition value features) fun _ =>
      Costed.bind_work_le (learner r _) fun _ =>
        Costed.bind_work_le (learner c _) fun _ =>
          Costed.bind_work_le (transitionTerminal_work κ transition _) fun _ =>
            Nat.le_refl _) ?_
    change _ ≤ outcomeBound κ (rankDimension dimension).capacity features.indices.length +
      (3 * modelTerminalBound κ dimension.capacity +
        ((κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
          (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)
          (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)) +
          κ .modelClose))
    omega
  | differential r c d transition =>
    unfold modelTerminalRun
    refine Nat.le_trans (Costed.bind_work_le (outcome_work κ transition value features) fun _ =>
      Costed.bind_work_le (learner r _) fun _ =>
        Costed.bind_work_le (learner c _) fun _ =>
          Costed.bind_work_le (learner d _) fun _ =>
            Costed.bind_work_le (transitionTerminal_work κ transition _) fun _ =>
              Nat.le_refl _) ?_
    change _ ≤ outcomeBound κ (rankDimension dimension).capacity features.indices.length +
      (3 * modelTerminalBound κ dimension.capacity +
        ((κ .rankWidth + updateRowsBound κ (rankDimension dimension).capacity
          (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)
          (κ .learnerError + modelTerminalBound κ (rankDimension dimension).capacity)) +
          κ .modelClose))
    omega

/-- The costed composition of `Model.stop`: the outcome, then each learner's stopped
trajectory. -/
def modelStopRun (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  match model with
  | .discounted r c transition => do
    let result ← outcome κ transition value features
    let r ← stopTrajectory κ r reward
    let c ← stopTrajectory κ c result.shared
    let transition ← transitionStop κ transition result
    Costed.op (κ .modelClose) (.discounted r c transition)
  | .differential r c d transition => do
    let result ← outcome κ transition value features
    let r ← stopTrajectory κ r reward
    let c ← stopTrajectory κ c result.shared
    let d ← stopTrajectory κ d .one
    let transition ← transitionStop κ transition result
    Costed.op (κ .modelClose) (.differential r c d transition)

theorem modelStopRun_val (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelStopRun κ model value features reward).val = model.stop value features reward := by
  cases model <;> simp only [modelStopRun, Costed.bind_val, transitionStop_val] <;> rfl

/-- Twin of `Model.stop`. -/
def modelStop (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  Costed.via (model.stop value features reward) (modelStopRun κ model value features reward)

/-- Bound of a model's stopped trajectory over `width` features. -/
abbrev modelStopBound (κ : Costs) (capacity positions width : Nat) : Nat :=
  outcomeBound κ positions width + (3 * stopTrajectoryBound κ capacity +
    ((κ .rankWidth + updateRowsBound κ positions
      (κ .learnerError + stopTrajectoryBound κ positions)
      (κ .learnerError + stopTrajectoryBound κ positions)) + κ .modelClose))

theorem modelStop_work (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    (modelStop κ model value features reward).work ≤
      modelStopBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length := by
  change (modelStopRun κ model value features reward).work ≤ _
  cases model with
  | discounted r c transition =>
    unfold modelStopRun
    refine Nat.le_trans (Costed.bind_work_le (outcome_work κ transition value features) fun _ =>
      Costed.bind_work_le (stopTrajectory_work κ r _) fun _ =>
        Costed.bind_work_le (stopTrajectory_work κ c _) fun _ =>
          Costed.bind_work_le (transitionStop_work κ transition _) fun _ =>
            Nat.le_refl _) ?_
    simp only [modelStopBound]
    omega
  | differential r c d transition =>
    unfold modelStopRun
    refine Nat.le_trans (Costed.bind_work_le (outcome_work κ transition value features) fun _ =>
      Costed.bind_work_le (stopTrajectory_work κ r _) fun _ =>
        Costed.bind_work_le (stopTrajectory_work κ c _) fun _ =>
          Costed.bind_work_le (stopTrajectory_work κ d _) fun _ =>
            Costed.bind_work_le (transitionStop_work κ transition _) fun _ =>
              Nat.le_refl _) ?_
    simp only [modelStopBound]
    omega

end AcornVerif.Resource.Twin
