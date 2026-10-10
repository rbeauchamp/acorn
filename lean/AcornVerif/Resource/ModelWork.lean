/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Models
import AcornVerif.Resource.ControlWork

/-!
# Work of the option models

Twins of an option model's prediction and updates (`Acorn.Models`) and of the ranked
features its transition part reads (`Acorn.RankedFeatures`). A transition part has one row
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

/-- Twin of `insert`: the membership test of the active set, then the append. -/
def insert (κ : Costs) (active : SwiftTd.ActiveSet dimension) (index : FeatIdx dimension) :
    Costed (SwiftTd.ActiveSet dimension) :=
  Costed.charge (κ .insert) (do
    Costed.discard (Costed.scanList .contains (κ .visit + κ .compare) active.indices
      (decide (index ∈ active.indices)))
    Costed.scanList .append (κ .visit) active.indices (Features.insert active index))

theorem insert_work (κ : Costs) (active : SwiftTd.ActiveSet dimension)
    (index : FeatIdx dimension) :
    (insert κ active index).work = κ .insert +
      (Library.contains.control (κ .visit + κ .compare) active.indices.length +
        Library.append.control (κ .visit) active.indices.length) :=
  rfl

/-- The costed composition of `modelInput`: nothing, or the age slot inserted. -/
def modelInputRun (κ : Costs) (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (SwiftTd.ActiveSet dimension) :=
  match criterion with
  | .discounted => Costed.pure base
  | .differential => insert κ base (age.feature dimension)

theorem modelInputRun_val (κ : Costs) (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (modelInputRun κ criterion base age).val = Features.modelInput criterion base age := by
  cases criterion <;> rfl

/-- Twin of `modelInput`. -/
def modelInput (κ : Costs) (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (SwiftTd.ActiveSet dimension) :=
  Costed.via (Features.modelInput criterion base age) (modelInputRun κ criterion base age)

/-- Bound of a model input over `width` features. -/
abbrev inputBound (κ : Costs) (width : Nat) : Nat :=
  κ .insert + (Library.contains.control (κ .visit + κ .compare) width +
    Library.append.control (κ .visit) width)

theorem modelInput_work (κ : Costs) (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (modelInput κ criterion base age).work ≤ inputBound κ base.indices.length := by
  change (modelInputRun κ criterion base age).work ≤ _
  cases criterion
  · exact Nat.zero_le _
  · exact Nat.le_of_eq (insert_work κ base _)

/-- A model input has at most one feature more than the frame. -/
theorem modelInput_length (criterion : Criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (Features.modelInput criterion base age).indices.length ≤ base.indices.length + 1 := by
  cases criterion
  · exact Nat.le_succ _
  · exact insert_length base _

/-- Twin of `RankedFeatures.active`: one position lookup for each active feature. -/
def rankedActive (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Costed (SwiftTd.ActiveSet (rankDimension dimension)) :=
  Costed.via (ranked.active features)
    (Costed.filterMap (κ .visit) (fun feature => Costed.op (κ .position) (ranked.position feature))
      features.indices)

/-- The lookups compute the executed active positions. -/
theorem rankedActive_run (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (Costed.filterMap (κ .visit) (fun feature => Costed.op (κ .position) (ranked.position feature))
      features.indices).val = (ranked.active features).indices := rfl

theorem rankedActive_work (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (rankedActive κ ranked features).work ≤
      Library.filterMap.work (κ .visit) features.indices.length (κ .position) :=
  Costed.filterMap_work_le _ _ _ _ fun _ _ => Nat.le_refl _

/-- Twin of `RankedFeatures.input`: the active positions and the bias appended. -/
def rankedInput (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Costed (SwiftTd.ActiveSet (rankDimension dimension)) := do
  let active ← rankedActive κ ranked features
  Costed.charge (κ .rankWidth) (insert κ active (RankedFeatures.bias dimension))

theorem rankedInput_val (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (rankedInput κ ranked features).val = ranked.input features := rfl

/-- Bound of a row input over `width` features. -/
abbrev rowInputBound (κ : Costs) (width : Nat) : Nat :=
  (Library.filterMap.work (κ .visit) width (κ .position)) +
    (κ .rankWidth + inputBound κ width)

theorem rankedInput_work (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (rankedInput κ ranked features).work ≤ rowInputBound κ features.indices.length := by
  have tested : Library.contains.control (κ .visit + κ .compare)
        (rankedActive κ ranked features).val.indices.length ≤
      Library.contains.control (κ .visit + κ .compare) features.indices.length :=
    Library.contains.control_mono (ranked.active_length features)
  have appended : Library.append.control (κ .visit)
        (rankedActive κ ranked features).val.indices.length ≤
      Library.append.control (κ .visit) features.indices.length :=
    Library.append.control_mono (ranked.active_length features)
  unfold rankedInput
  refine Nat.le_trans (Costed.bind_work_le_at (rankedActive_work κ ranked features)
    (Costed.charge_work_le (Nat.le_of_eq (insert_work κ _ (RankedFeatures.bias dimension))))) ?_
  simp only [rowInputBound, inputBound]
  omega

/-- Twin of `RankedFeatures.occupied`: the positions listed, then one read for each. -/
def occupied (κ : Costs) (ranked : RankedFeatures dimension) :
    Costed (List (RankIdx dimension × FeatIdx dimension)) := do
  let positions ← Costed.charge (κ .rankWidth) (Costed.scanList .finRange (κ .visit)
    (List.finRange (rankDimension dimension).capacity)
    (List.finRange (rankDimension dimension).capacity))
  Costed.filterMap (κ .visit)
    (fun position => Costed.op (κ .read)
      ((ranked.slots[position.val]).map fun feature => (position, feature)))
    positions

theorem occupied_val (κ : Costs) (ranked : RankedFeatures dimension) :
    (occupied κ ranked).val = ranked.occupied := rfl

/-- Bound of the occupied positions of a ranking of `width` positions. -/
abbrev occupiedBound (κ : Costs) (width : Nat) : Nat :=
  κ .rankWidth + Library.finRange.control (κ .visit) width +
    (Library.filterMap.work (κ .visit) width (κ .read))

theorem occupied_work (κ : Costs) (ranked : RankedFeatures dimension) :
    (occupied κ ranked).work ≤ occupiedBound κ (rankDimension dimension).capacity := by
  unfold occupied
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.filterMap_work_le (κ .visit) (κ .read) _ _ fun _ _ => Nat.le_refl _)) ?_
  simp only [List.length_finRange, occupiedBound]
  omega

/-- Twin of `RankedFeatures.indicator`: the active positions, a vector of absent values,
and one write for each active position. -/
def indicator (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Costed (Vector Expectation (rankDimension dimension).capacity) := do
  let active ← rankedActive κ ranked features
  let absent ← Costed.charge (κ .rankWidth)
    (Costed.replicate (κ .visit) (rankDimension dimension).capacity Expectation.absent)
  Costed.foldl (κ .visit)
    (fun seen position => Costed.op (κ .write)
      (seen.set position.val Expectation.present position.isLt))
    absent active.indices

theorem indicator_val (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (indicator κ ranked features).val = ranked.indicator features := rfl

/-- Bound of an indicator over `width` features and `positions` ranked positions. -/
abbrev indicatorBound (κ : Costs) (width positions : Nat) : Nat :=
  (Library.filterMap.work (κ .visit) width (κ .position)) +
    (κ .rankWidth + Library.replicate.control (κ .visit) positions) +
    Library.foldl.work (κ .visit) width (κ .write)

theorem indicator_work (κ : Costs) (ranked : RankedFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (indicator κ ranked features).work ≤
      indicatorBound κ features.indices.length (rankDimension dimension).capacity := by
  have scaled : Library.foldl.work (κ .visit) (rankedActive κ ranked features).val.indices.length
        (κ .write) ≤ Library.foldl.work (κ .visit) features.indices.length (κ .write) :=
    Library.foldl.work_mono (ranked.active_length features) (Nat.le_refl _)
  unfold indicator
  refine Nat.le_trans (Costed.bind_work_le_at (rankedActive_work κ ranked features)
    (Costed.bind_work_le_at (Nat.le_refl _)
      (Costed.foldl_work_le (κ .visit) (κ .write) _ _ _ fun _ _ _ => Nat.le_refl _))) ?_
  simp only [indicatorBound]
  omega

/-! ## Predictions -/

/-- Twin of `ValueFunction.rankedValues`: the occupied positions, then for each meta action
one product for each occupied position. -/
def rankedValues (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    Costed (Vector Binary32 metaCount.word.toNat) := do
  let occupied ← occupied κ ranked
  Costed.mapVector (κ .visit)
    (fun learner => sumMap κ .productTerm .zero occupied fun entry =>
      (learner.state.weights.get entry.2).value.mul (expected.get entry.1).value)
    value.controller.learners

theorem rankedValues_val (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    (rankedValues κ value ranked expected).val = value.rankedValues ranked expected := rfl

/-- Bound of the ranked values at `positions` ranked positions. -/
abbrev rankedValuesBound (κ : Costs) (positions : Nat) : Nat :=
  occupiedBound κ positions +
    Library.vectorMap.work (κ .visit) metaCount.word.toNat
      (Library.foldl.work (κ .visit) positions (κ .productTerm))

theorem rankedValues_work (κ : Costs) (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    (rankedValues κ value ranked expected).work ≤
      rankedValuesBound κ (rankDimension dimension).capacity := by
  unfold rankedValues
  refine Nat.le_trans (Costed.bind_work_le_at (occupied_work κ ranked)
    (Costed.mapVector_work_le (κ .visit)
      (Library.foldl.work (κ .visit) (rankDimension dimension).capacity (κ .productTerm)) _ _
      fun _ _ =>
        Nat.le_trans (sumMap_work κ .productTerm .zero _ _)
          (Library.foldl.work_mono (RankedFeatures.occupied_length ranked) (Nat.le_refl _)))) ?_
  exact Nat.le_refl _

/-- The costed composition of `comparisonValue`: the policy mean or the maximum. -/
def comparisonRun (κ : Costs) (criterion : Criterion) (policy : PolicySnapshot count) :
    Costed Binary32 :=
  match criterion with
  | .differential => expected κ policy
  | .discounted => best κ policy

theorem comparisonRun_val (κ : Costs) (criterion : Criterion) (policy : PolicySnapshot count) :
    (comparisonRun κ criterion policy).val = Features.comparisonValue criterion policy := by
  cases criterion <;> rfl

/-- Twin of `comparisonValue`. -/
def comparisonValue (κ : Costs) (criterion : Criterion) (policy : PolicySnapshot count) :
    Costed Binary32 :=
  Costed.via (Features.comparisonValue criterion policy) (comparisonRun κ criterion policy)

/-- Bound of a nominal value over `size` values under either criterion. -/
abbrev comparisonBound (κ : Costs) (size : Nat) : Nat := expectedBound κ size + bestBound κ size

theorem comparisonValue_work (κ : Costs) (criterion : Criterion) (policy : PolicySnapshot count) :
    (comparisonValue κ criterion policy).work ≤ comparisonBound κ count.word.toNat := by
  change (comparisonRun κ criterion policy).work ≤ _
  cases criterion
  · exact Nat.le_trans (best_work κ policy) (Nat.le_add_left _ _)
  · exact Nat.le_trans (expected_work κ policy) (Nat.le_add_right _ _)

/-- Twin of `Transition.expectedAt`: one prediction for each row. -/
def expectedAt (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    Costed (Vector Expectation (rankDimension dimension).capacity) :=
  Costed.mapVector (κ .visit)
    (fun row => do
      let raw ← linearPrediction κ row.state input
      Costed.op (κ .project) (Bounded32.project expectationRange raw))
    transition.rows

theorem expectedAt_val (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    (expectedAt κ transition input).val = transition.expectedAt input := rfl

/-- Bound of the rows' predictions at `positions` rows over `width` inputs. -/
abbrev expectedAtBound (κ : Costs) (positions width : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) positions
    (Library.foldl.work (κ .visit) width (κ .sumTerm) + κ .project)

theorem expectedAt_work (κ : Costs) (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    (expectedAt κ transition input).work ≤
      expectedAtBound κ (rankDimension dimension).capacity input.indices.length :=
  Costed.mapVector_work_le _ _ _ _ fun row _ =>
    Costed.bind_work_le (linearPrediction_work κ row.state input) fun _ => Nat.le_refl _

/-- Twin of `Transition.outcomeValues`: the row input, the rows' predictions, the ranked
values, then each meta action's deviation and value. -/
def outcomeValues (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Costed (Vector Binary32 metaCount.word.toNat) := do
  let input ← rankedInput κ transition.ranked features
  let expected ← expectedAt κ transition input
  let ranked ← rankedValues κ value transition.ranked expected
  let wide := Conversion.widen shared
  Costed.ofFn (κ .visit) fun action => do
    let deviation ← linearPrediction κ (transition.deviations.get action).state input
    Costed.op (κ .outcomeValue)
      (Conversion.narrow (((Conversion.widen (ranked.get action)).add wide).add
        (Conversion.widen deviation)))

theorem outcomeValues_val (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (outcomeValues κ transition value features shared).val =
      transition.outcomeValues value features shared := rfl

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

theorem outcomeValues_work (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (outcomeValues κ transition value features shared).work ≤
      outcomeValuesBound κ (rankDimension dimension).capacity features.indices.length := by
  have width := transition.ranked.input_length features
  unfold outcomeValues
  refine Nat.le_trans (Costed.bind_work_le_at (rankedInput_work κ transition.ranked features)
    (Costed.bind_work_le_at (Nat.le_trans (expectedAt_work κ transition _)
      (expectedAtBound_mono κ _ width))
      (Costed.bind_work_le_at (rankedValues_work κ value transition.ranked _)
        (Costed.ofFn_work_le (κ .visit)
          (Library.foldl.work (κ .visit) (features.indices.length + 1) (κ .sumTerm) +
            κ .outcomeValue) _
          fun action =>
          Costed.bind_work_le (Nat.le_trans
            (linearPrediction_work κ (transition.deviations.get action).state _)
            (Library.foldl.work_mono width (Nat.le_refl _))) fun _ => Nat.le_refl _)))) ?_
  exact Nat.le_of_eq (by simp only [outcomeValuesBound]; omega)

/-- Twin of `Transition.lookahead`. -/
def lookahead (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Costed Binary32 := do
  let values ← outcomeValues κ transition value features shared
  comparisonValue κ criterion (⟨values, value.epsilon⟩ : PolicySnapshot metaCount)

theorem lookahead_val (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (lookahead κ transition value features shared).val =
      transition.lookahead value features shared := rfl

/-- Bound of a look-ahead over `width` features at `positions` rows. -/
abbrev lookaheadBound (κ : Costs) (positions width : Nat) : Nat :=
  outcomeValuesBound κ positions width + comparisonBound κ metaCount.word.toNat

theorem lookahead_work (κ : Costs) (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    (lookahead κ transition value features shared).work ≤
      lookaheadBound κ (rankDimension dimension).capacity features.indices.length :=
  Costed.bind_work_le (outcomeValues_work κ transition value features shared) fun _ =>
    comparisonValue_work κ criterion _

/-- The costed composition of `Model.predict`: the model input, then each learner's
prediction and the look-ahead of the transition part. -/
def predictRun (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (ModelPrediction criterion) :=
  match model with
  | .discounted reward continuation transition => do
    let features ← modelInput κ .discounted base age
    let r ← linearPrediction κ reward.state features
    let c ← linearPrediction κ continuation.state features
    let look ← lookahead κ transition value base c
    Costed.op (κ .prediction)
      ⟨Bounded32.project _ r, Criterion.discounted.modelContinuation look,
        Bounded32.project _ .one⟩
  | .differential reward continuation duration transition => do
    let features ← modelInput κ .differential base age
    let r ← linearPrediction κ reward.state features
    let c ← linearPrediction κ continuation.state features
    let look ← lookahead κ transition value base c
    let d ← linearPrediction κ duration.state features
    Costed.op (κ .prediction) ⟨Bounded32.project _ r, look, Bounded32.project _ d⟩

theorem predictRun_val (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : (predictRun κ model value base age).val = model.predict value base age := by
  cases model <;> rfl

/-- Twin of `Model.predict`. -/
def predict (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (ModelPrediction criterion) :=
  Costed.via (model.predict value base age) (predictRun κ model value base age)

/-- Bound of a model prediction over `width` features. -/
abbrev predictBound (κ : Costs) (positions width : Nat) : Nat :=
  inputBound κ width + (3 * Library.foldl.work (κ .visit) (width + 1) (κ .sumTerm) +
    lookaheadBound κ positions width + κ .prediction)

theorem predict_work (κ : Costs) (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    (predict κ model value base age).work ≤
      predictBound κ (rankDimension dimension).capacity base.indices.length := by
  have width := modelInput_length criterion base age
  have read := fun (learner : NumericState (criterion.config .demon) dimension) =>
    Nat.le_trans (linearPrediction_work κ learner (Features.modelInput criterion base age))
      (Library.foldl.work_mono width (Nat.le_refl (κ .sumTerm)))
  change (predictRun κ model value base age).work ≤ _
  cases model with
  | discounted reward continuation transition =>
    unfold predictRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ _ base age)
      (Costed.bind_work_le_at (read reward.state) (Costed.bind_work_le_at (read continuation.state)
        (Costed.bind_work_le (lookahead_work κ transition value base _) fun _ =>
          Nat.le_refl _)))) ?_
    simp only [predictBound]
    omega
  | differential reward continuation duration transition =>
    unfold predictRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ _ base age)
      (Costed.bind_work_le_at (read reward.state) (Costed.bind_work_le_at (read continuation.state)
        (Costed.bind_work_le (lookahead_work κ transition value base _) fun _ =>
          Costed.bind_work_le (read duration.state) fun _ => Nat.le_refl _)))) ?_
    simp only [predictBound]
    omega

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

/-- Twin of `Transition.begin`. -/
def transitionBegin (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) := do
  let input ← rankedInput κ transition.ranked features
  updateRows κ transition (fun _ row => managedApply κ row (.beginTrajectory input) trivial)
    (fun _ learner => managedApply κ learner (.beginTrajectory input) trivial)

theorem transitionBegin_val (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionBegin κ transition features).val = transition.begin features := by
  cases transition
  rfl

/-- Bound of a transition part's start over `width` features. -/
abbrev transitionBeginBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + updateRowsBound κ positions (beginBound κ positions (width + 1))
    (beginBound κ positions (width + 1))

theorem transitionBegin_work (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionBegin κ transition features).work ≤
      transitionBeginBound κ (rankDimension dimension).capacity features.indices.length := by
  have width := transition.ranked.input_length features
  unfold transitionBegin
  exact Costed.bind_work_le_at (rankedInput_work κ transition.ranked features)
    (updateRows_work κ transition _ _ _ _
      (fun _ row => Nat.le_trans (managedApply_work κ row (.beginTrajectory _) trivial)
        (beginBound_mono κ _ width))
      (fun _ learner => Nat.le_trans (managedApply_work κ learner (.beginTrajectory _) trivial)
        (beginBound_mono κ _ width)))

/-- Twin of `Transition.step`. -/
def transitionStep (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) := do
  let input ← rankedInput κ transition.ranked features
  updateRows κ transition (fun _ row => managedApply κ row (.step input .zero) trivial)
    (fun _ learner => managedApply κ learner (.step input .zero) trivial)

theorem transitionStep_val (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionStep κ transition features).val = transition.step features := by
  cases transition
  rfl

/-- Bound of a transition part's step over `width` features. -/
abbrev transitionStepBound (κ : Costs) (positions width : Nat) : Nat :=
  rowInputBound κ width + updateRowsBound κ positions (stepBound κ positions (width + 1))
    (stepBound κ positions (width + 1))

theorem transitionStep_work (κ : Costs) (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    (transitionStep κ transition features).work ≤
      transitionStepBound κ (rankDimension dimension).capacity features.indices.length := by
  have width := transition.ranked.input_length features
  unfold transitionStep
  exact Costed.bind_work_le_at (rankedInput_work κ transition.ranked features)
    (updateRows_work κ transition _ _ _ _
      (fun _ row => Nat.le_trans (managedApply_work κ row (.step _ _) trivial)
        (stepBound_mono κ _ width))
      (fun _ learner => Nat.le_trans (managedApply_work κ learner (.step _ _) trivial)
        (stepBound_mono κ _ width)))

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
  Costed.bind_work_le (indicator_work κ transition.ranked features) fun _ =>
    Costed.bind_work_le (predictAll_work κ value.controller features) fun _ =>
      Costed.bind_work_le (rankedValues_work κ value transition.ranked _) fun _ =>
        Costed.bind_work_le (comparisonValue_work κ criterion _) fun _ =>
          Costed.bind_work_le (comparisonValue_work κ criterion _) fun _ =>
            Costed.bind_work_le (Costed.ofFn_work_le _ _ _ fun _ => Nat.le_refl _) fun _ =>
              Nat.le_refl _

/-- Twin of `Transition.terminal`. -/
def transitionTerminal (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  updateRows κ transition
    (fun position row => managedApply κ row
      (.terminal (criterion.rule.gamma.mul (outcome.seen.get position).value)) trivial)
    (fun action learner => managedApply κ learner (.terminal (outcome.deviations.get action))
      trivial)

theorem transitionTerminal_val (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionTerminal κ transition outcome).val = transition.terminal outcome := by
  cases transition
  rfl

theorem transitionTerminal_work (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionTerminal κ transition outcome).work ≤
      updateRowsBound κ (rankDimension dimension).capacity
        (terminalBound κ (rankDimension dimension).capacity (rankDimension dimension).capacity)
        (terminalBound κ (rankDimension dimension).capacity (rankDimension dimension).capacity) :=
  updateRows_work κ transition _ _ _ _ (fun _ row => managedApply_work κ row (.terminal _) trivial)
    (fun _ learner => managedApply_work κ learner (.terminal _) trivial)

/-- Twin of `Managed.stopTrajectory`: a first loop, then a release. -/
def stopTrajectory {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    Costed (Managed learnerConfig space) := do
  let first ← managedApply κ learner
    (.first (target.sub learner.state.transient.vOld) learner.state.transient.vDelta .zero) trivial
  managedApply κ first .release trivial

theorem stopTrajectory_val {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    (stopTrajectory κ learner target).val = learner.stopTrajectory target := rfl

/-- Bound of a stopped trajectory at a capacity. -/
abbrev stopTrajectoryBound (κ : Costs) (capacity : Nat) : Nat :=
  firstLoopBound κ capacity + releaseBound κ capacity

theorem stopTrajectory_work {learnerConfig : Acorn.Config} {space : Dimension} (κ : Costs)
    (learner : Managed learnerConfig space) (target : Binary32) :
    (stopTrajectory κ learner target).work ≤ stopTrajectoryBound κ space.capacity :=
  Costed.bind_work_le (managedApply_work κ learner (.first _ _ _) trivial) fun first =>
    managedApply_work κ first .release trivial

/-- Twin of `Transition.stop`. -/
def transitionStop (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  updateRows κ transition
    (fun position row => stopTrajectory κ row
      (criterion.rule.gamma.mul (outcome.seen.get position).value))
    (fun action learner => stopTrajectory κ learner (outcome.deviations.get action))

theorem transitionStop_val (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionStop κ transition outcome).val = transition.stop outcome := by
  cases transition
  rfl

theorem transitionStop_work (κ : Costs) (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    (transitionStop κ transition outcome).work ≤
      updateRowsBound κ (rankDimension dimension).capacity
        (stopTrajectoryBound κ (rankDimension dimension).capacity)
        (stopTrajectoryBound κ (rankDimension dimension).capacity) :=
  updateRows_work κ transition _ _ _ _ (fun _ row => stopTrajectory_work κ row _)
    (fun _ learner => stopTrajectory_work κ learner _)

/-! ## A whole model -/

/-- A model learner's bound of a terminal entry. -/
abbrev modelTerminalBound (κ : Costs) (capacity : Nat) : Nat := terminalBound κ capacity capacity

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
  inputBound κ width + (3 * beginBound κ capacity (width + 1) +
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
      (beginBound_mono κ dimension.capacity fits)
  change (modelBeginRun κ model base).work ≤ _
  cases model with
  | discounted reward continuation transition =>
    unfold modelBeginRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ _ base _)
      (Costed.bind_work_le_at (learner reward _ (width _ _))
        (Costed.bind_work_le (learner continuation _ (width _ _)) fun _ =>
          Costed.bind_work_le (transitionBegin_work κ transition base) fun _ =>
            Nat.le_refl _))) ?_
    simp only [modelBeginBound]
    omega
  | differential reward continuation duration transition =>
    unfold modelBeginRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ _ base _)
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
  inputBound κ width + (3 * stepBound κ capacity (width + 1) +
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
      (stepBound_mono κ dimension.capacity fits)
  change (modelStepRun κ model base age reward).work ≤ _
  cases model with
  | discounted r c transition =>
    unfold modelStepRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ _ base _)
      (Costed.bind_work_le_at (learner r _ _ width)
        (Costed.bind_work_le (learner c _ _ width) fun _ =>
          Costed.bind_work_le (transitionStep_work κ transition base) fun _ =>
            Nat.le_refl _))) ?_
    simp only [modelStepBound]
    omega
  | differential r c d transition =>
    unfold modelStepRun
    refine Nat.le_trans (Costed.bind_work_le_at (modelInput_work κ _ base _)
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
    (updateRowsBound κ positions (terminalBound κ positions positions)
      (terminalBound κ positions positions) + κ .modelClose))

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
        (updateRowsBound κ (rankDimension dimension).capacity
          (terminalBound κ (rankDimension dimension).capacity (rankDimension dimension).capacity)
          (terminalBound κ (rankDimension dimension).capacity (rankDimension dimension).capacity) +
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
        (updateRowsBound κ (rankDimension dimension).capacity
          (terminalBound κ (rankDimension dimension).capacity (rankDimension dimension).capacity)
          (terminalBound κ (rankDimension dimension).capacity (rankDimension dimension).capacity) +
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
    (updateRowsBound κ positions (stopTrajectoryBound κ positions)
      (stopTrajectoryBound κ positions) + κ .modelClose))

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
