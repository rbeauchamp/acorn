import Acorn.FeatureRefresh
import AcornVerif.Resource.OptionWork

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}

def learnerInitialRun (κ : Costs) (learnerConfig : Acorn.Config) (space : Dimension) :
    Costed Unit := do
  Costed.discard (Costed.replicate (κ .visit) space.capacity
    (Weight.project learnerConfig.rule .zero))
  let rails := StepSizeRails.ofConfig learnerConfig
  Costed.discard (Costed.replicate (κ .visit) space.capacity rails.initial)
  Costed.discard (Costed.replicate (κ .visit) space.capacity rails.initial.alpha)
  Costed.discard (zeroTransient κ space)
  Costed.op (κ .initialState) ()

abbrev learnerInitialBound (κ : Costs) (capacity : Nat) : Nat :=
  Library.replicate.control (κ .visit) capacity + (Library.replicate.control (κ .visit) capacity +
    (Library.replicate.control (κ .visit) capacity +
    (zeroBound κ capacity + κ .initialState)))

theorem learnerInitialRun_work (κ : Costs) (learnerConfig : Acorn.Config) (space : Dimension) :
    (learnerInitialRun κ learnerConfig space).work ≤ learnerInitialBound κ space.capacity :=
  Costed.bind_work_le (Nat.le_refl _) fun _ => Costed.bind_work_le (Nat.le_refl _) fun _ =>
    Costed.bind_work_le (Nat.le_refl _) fun _ =>
      Costed.bind_work_le (zeroTransient_work κ space) fun _ => Nat.le_refl _

def managedInitial (κ : Costs) (learnerConfig : Acorn.Config) (space : Dimension) :
    Costed (Managed learnerConfig space) :=
  Costed.via (Managed.initial learnerConfig space) (learnerInitialRun κ learnerConfig space)

def controllerInitial (κ : Costs) (learnerConfig : Acorn.Config) (space : Dimension)
    (rows : Nat) : Costed (Controller learnerConfig space rows) := do
  let learners ← Costed.ofFn (κ .visit) fun _ => managedInitial κ learnerConfig space
  Costed.op (κ .controllerClose) ⟨learners, .zero, .zero, false⟩

theorem controllerInitial_val (κ : Costs) (learnerConfig : Acorn.Config) (space : Dimension)
    (rows : Nat) :
    (controllerInitial κ learnerConfig space rows).val =
      Controller.initial learnerConfig space rows := rfl

abbrev controllerInitialBound (κ : Costs) (rows capacity : Nat) : Nat :=
  Library.ofFn.work (κ .visit) rows (learnerInitialBound κ capacity) + κ .controllerClose

theorem controllerInitial_work (κ : Costs) (learnerConfig : Acorn.Config) (space : Dimension)
    (rows : Nat) :
    (controllerInitial κ learnerConfig space rows).work ≤
      controllerInitialBound κ rows space.capacity :=
  Costed.bind_work_le (Costed.ofFn_work_le _ _ _ fun _ =>
    learnerInitialRun_work κ learnerConfig space) fun _ => Nat.le_refl _

def tabulate (κ : Costs)
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity) :
    Costed (Vector Nat dimension.capacity) := do
  let positions ← Costed.charge (κ .rankWidth) (Costed.scanList .finRange (κ .visit)
    (List.finRange (rankDimension dimension).capacity)
    (List.finRange (rankDimension dimension).capacity))
  let table ← Costed.replicate (κ .visit) dimension.capacity 0
  Costed.foldl (κ .visit)
    (fun table position => Costed.op (κ .write) (tabulateStep slots table position))
    table positions

theorem tabulate_val (κ : Costs)
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity) :
    (tabulate κ slots).val = Features.tabulate slots := rfl

abbrev tabulateBound (κ : Costs) (capacity positions : Nat) : Nat :=
  κ .rankWidth + Library.finRange.control (κ .visit) positions +
    (Library.replicate.control (κ .visit) capacity +
      Library.foldl.work (κ .visit) positions (κ .write))

theorem tabulate_work (κ : Costs)
    (slots : Vector (Option (FeatIdx dimension)) (rankDimension dimension).capacity) :
    (tabulate κ slots).work ≤
      tabulateBound κ dimension.capacity (rankDimension dimension).capacity := by
  unfold tabulate
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _) (Costed.bind_work_le_at
    (Nat.le_refl _) (Costed.foldl_work_le (κ .visit) (κ .write) _ _ _ fun _ _ _ =>
      Nat.le_refl _))) ?_
  simp only [List.length_finRange, tabulateBound]
  omega

def rankedEmpty (κ : Costs) (dimension : Dimension) : Costed (RankedFeatures dimension) :=
  Costed.via (RankedFeatures.empty dimension) (do
    let slots ← Costed.charge (κ .rankWidth)
      (Costed.replicate (κ .visit) (rankDimension dimension).capacity none)
    tabulate κ slots)

abbrev rankedEmptyBound (κ : Costs) (capacity positions : Nat) : Nat :=
  (κ .rankWidth + Library.replicate.control (κ .visit) positions) +
    tabulateBound κ capacity positions

theorem rankedEmpty_work (κ : Costs) (dimension : Dimension) :
    (rankedEmpty κ dimension).work ≤
      rankedEmptyBound κ dimension.capacity (rankDimension dimension).capacity :=
  Costed.bind_work_le (Nat.le_refl _) fun slots => tabulate_work κ slots

def transitionInitial (κ : Costs) (dimension : Dimension) (criterion : Criterion) :
    Costed (Transition dimension criterion) := do
  let empty ← rankedEmpty κ dimension
  let fresh ← managedInitial κ (criterion.config .demon) (rankDimension dimension)
  let rows ← Costed.charge (κ .rankWidth)
    (Costed.replicate (κ .visit) (rankDimension dimension).capacity fresh)
  let deviations ← Costed.replicate (κ .visit) Acorn.FeatureConstants.metaActionCount fresh
  Costed.pure ⟨empty, rows, deviations⟩

theorem transitionInitial_val (κ : Costs) (dimension : Dimension) (criterion : Criterion) :
    (transitionInitial κ dimension criterion).val = Transition.initial dimension criterion := rfl

abbrev transitionInitialBound (κ : Costs) (capacity positions : Nat) : Nat :=
  rankedEmptyBound κ capacity positions + (learnerInitialBound κ positions +
    ((κ .rankWidth + Library.replicate.control (κ .visit) positions) +
      (Library.replicate.control (κ .visit) Acorn.FeatureConstants.metaActionCount + 0)))

theorem transitionInitial_work (κ : Costs) (dimension : Dimension) (criterion : Criterion) :
    (transitionInitial κ dimension criterion).work ≤
      transitionInitialBound κ dimension.capacity (rankDimension dimension).capacity :=
  Costed.bind_work_le (rankedEmpty_work κ dimension) fun _ =>
    Costed.bind_work_le (learnerInitialRun_work κ _ _) fun _ =>
      Costed.bind_work_le (Nat.le_refl _) fun _ =>
        Costed.bind_work_le (Nat.le_refl _) fun _ => Nat.le_refl _

def modelInitialRun (κ : Costs) (dimension : Dimension) (criterion : Criterion) :
    Costed (Model dimension criterion) :=
  match criterion with
  | .discounted => do
    let fresh ← managedInitial κ (Criterion.config .discounted .demon) dimension
    let transition ← transitionInitial κ dimension .discounted
    Costed.pure (.discounted fresh fresh transition)
  | .differential => do
    let fresh ← managedInitial κ (Criterion.config .differential .demon) dimension
    let transition ← transitionInitial κ dimension .differential
    Costed.pure (.differential fresh fresh fresh transition)

theorem modelInitialRun_val (κ : Costs) (dimension : Dimension) (criterion : Criterion) :
    (modelInitialRun κ dimension criterion).val = Model.initial dimension criterion := by
  cases criterion <;> rfl

def modelInitial (κ : Costs) (dimension : Dimension) (criterion : Criterion) :
    Costed (Model dimension criterion) :=
  Costed.via (Model.initial dimension criterion) (modelInitialRun κ dimension criterion)

abbrev modelInitialBound (κ : Costs) (capacity positions : Nat) : Nat :=
  learnerInitialBound κ capacity + transitionInitialBound κ capacity positions

theorem modelInitial_work (κ : Costs) (dimension : Dimension) (criterion : Criterion) :
    (modelInitial κ dimension criterion).work ≤
      modelInitialBound κ dimension.capacity (rankDimension dimension).capacity := by
  change (modelInitialRun κ dimension criterion).work ≤ _
  cases criterion <;>
  · refine Nat.le_trans (Costed.bind_work_le (learnerInitialRun_work κ _ _) fun _ =>
      Costed.bind_work_le (transitionInitial_work κ dimension _) fun _ => Nat.le_refl 0) ?_
    simp only [modelInitialBound]
    omega

def skillInitial (κ : Costs) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (interest : Interest config) :
    Costed (Skill actions config criterion dimension discounts) := do
  let policy ← controllerInitial κ _ dimension actions.word.toNat
  let model ← modelInitial κ dimension criterion
  Costed.pure ⟨interest, policy, model, none⟩

theorem skillInitial_val (κ : Costs) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (interest : Interest config) :
    (skillInitial (actions := actions) (discounts := discounts) κ config criterion dimension
      interest).val = Skill.initial config criterion dimension interest := rfl

abbrev skillInitialBound (κ : Costs) (rows capacity positions : Nat) : Nat :=
  controllerInitialBound κ rows capacity + (modelInitialBound κ capacity positions + 0)

theorem skillInitial_work (κ : Costs) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) (interest : Interest config) :
    (skillInitial (actions := actions) (discounts := discounts) κ config criterion dimension
      interest).work ≤
      skillInitialBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity :=
  Costed.bind_work_le (controllerInitial_work κ _ dimension _) fun _ =>
    Costed.bind_work_le (modelInitial_work κ dimension criterion) fun _ => Nat.le_refl _

def resetAction (κ : Costs) {learnerConfig : Acorn.Config} {rows : Nat}
    (controller : Controller learnerConfig dimension rows) (action : Fin rows) :
    Costed (Controller learnerConfig dimension rows) := do
  let fresh ← managedInitial κ learnerConfig dimension
  Costed.op (κ .write)
    { controller with
      learners := controller.learners.set action.val fresh action.isLt
      restartPending := true }

theorem resetAction_val (κ : Costs) {learnerConfig : Acorn.Config} {rows : Nat}
    (controller : Controller learnerConfig dimension rows) (action : Fin rows) :
    (resetAction κ controller action).val = controller.resetAction action := rfl

theorem resetAction_work (κ : Costs) {learnerConfig : Acorn.Config} {rows : Nat}
    (controller : Controller learnerConfig dimension rows) (action : Fin rows) :
    (resetAction κ controller action).work ≤ learnerInitialBound κ dimension.capacity + κ .write :=
  Costed.bind_work_le (learnerInitialRun_work κ learnerConfig dimension) fun _ => Nat.le_refl _

def candidateList (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) : Costed (List (Candidate config)) := do
  let units ← Costed.scanList .finRange (κ .visit) (List.finRange config.units.count)
    (List.finRange config.units.count)
  Costed.filterMap (κ .visit)
    (fun unit => Costed.op (κ .rankCandidate) (candidateOfWeight config weights unit)) units

abbrev candidateListBound (κ : Costs) (units : Nat) : Nat :=
  Library.finRange.control (κ .visit) units +
    (Library.filterMap.work (κ .visit) units (κ .rankCandidate))

theorem candidateList_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (candidateList κ dimension config weights).work ≤ candidateListBound κ config.units.count := by
  unfold candidateList
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.filterMap_work_le (κ .visit) (κ .rankCandidate) _ _ fun _ _ => Nat.le_refl _)) ?_
  simp only [List.length_finRange, candidateListBound]
  omega

theorem candidateList_length (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    ((List.finRange config.units.count).filterMap (candidateOfWeight config weights)).length ≤
      config.units.count := by
  simpa using List.length_filterMap_le (candidateOfWeight config weights)
    (List.finRange config.units.count)

def rankedRun (κ : Costs) : Nat → List (Candidate config) → Costed (List (Candidate config))
  | 0, _ => Costed.op (κ .visit) []
  | count + 1, items =>
      match Features.best items with
      | none => Costed.charge (κ .visit) (Costed.op (κ .visit) [])
      | some chosen => Costed.charge
          (Library.foldl.work (κ .visit) items.length (κ .compare) +
            Library.filter.work (κ .visit) items.length (κ .compare)) (do
        let rest ← rankedRun κ count (withoutBlock items chosen)
        Costed.op (κ .visit) (chosen :: rest))

theorem rankedRun_val (κ : Costs) (count : Nat) (items : List (Candidate config)) :
    (rankedRun κ count items).val = ranked count items := by
  induction count generalizing items with
  | zero => rfl
  | succ count ih =>
    rw [rankedRun, ranked]
    cases Features.best items with
    | none => rfl
    | some chosen => simp only [Costed.bind_val, ih]

abbrev rankedBound (κ : Costs) (count size : Nat) : Nat :=
  pass (κ .visit) count (Library.foldl.work (κ .visit) size (κ .compare) +
    Library.filter.work (κ .visit) size (κ .compare))

theorem rankedRun_work (κ : Costs) (count : Nat) (items : List (Candidate config)) (size : Nat)
    (fits : items.length ≤ size) : (rankedRun κ count items).work ≤ rankedBound κ count size := by
  induction count generalizing items with
  | zero => simp [rankedRun]
  | succ count ih =>
    have best := Library.foldl.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .compare))
    have drop := Library.filter.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .compare))
    rw [rankedRun]
    cases Features.best items with
    | none =>
      simp only [rankedBound, pass, Nat.succ_mul]
      omega
    | some chosen =>
      have rest := ih (withoutBlock items chosen)
        (Nat.le_trans (List.length_filter_le _ _) fits)
      simp only [Costed.bind_work, rankedBound, pass, Nat.succ_mul] at rest ⊢
      omega

def rankedBlocks (κ : Costs) (count : Nat) (items : List (Candidate config)) :
    Costed (List (Candidate config)) :=
  Costed.via (ranked count items) (rankedRun κ count items)

def rankedCandidates (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) : Costed (List (Candidate config)) := do
  let items ← candidateList κ dimension config weights
  rankedBlocks κ Acorn.FeatureConstants.skillCount items

theorem rankedCandidates_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (rankedCandidates κ dimension config weights).val =
      Features.rankedCandidates dimension config weights := rfl

abbrev rankedCandidatesBound (κ : Costs) (units : Nat) : Nat :=
  candidateListBound κ units + rankedBound κ Acorn.FeatureConstants.skillCount units

theorem rankedCandidates_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (rankedCandidates κ dimension config weights).work ≤
      rankedCandidatesBound κ config.units.count :=
  Costed.bind_work_le_at (candidateList_work κ dimension config weights)
    (rankedRun_work κ _ _ _ (candidateList_length dimension config weights))

def rankAssignments (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    Costed (Vector (Assignment config) Acorn.FeatureConstants.skillCount) :=
  Costed.via (Features.rankAssignments dimension config weights held) (do
    Costed.discard (rankedCandidates κ dimension config weights)
    Costed.op (κ .assignmentTable) ())

theorem rankAssignments_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    (rankAssignments κ dimension config weights held).work ≤
      rankedCandidatesBound κ config.units.count + κ .assignmentTable :=
  Costed.bind_work_le (rankedCandidates_work κ dimension config weights) fun _ => Nat.le_refl _

variable {shape : PatchShape} {payload : Type}

def installRun (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) : Costed Unit :=
  let previous := state.lifecycle.consumers.skills[slot.val]
  Costed.charge (κ .install) (Costed.ite (previous.interest.sameAssignment target = true)
    (Costed.pure ())
    (do
      Costed.discard (skillInitial (actions := actions) (discounts := .g99 :: discounts) κ config
        criterion dimension (.learned target))
      Costed.discard (resetAction κ state.lifecycle.consumers.metaController (metaOfSkill slot))))

def install (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    Costed (FreeDispatch shape actions config criterion dimension discounts payload) :=
  Costed.via (state.install slot target) (installRun κ state slot target)

abbrev installBound (κ : Costs) (rows capacity positions : Nat) : Nat :=
  κ .install + (skillInitialBound κ rows capacity positions +
    (learnerInitialBound κ capacity + κ .write))

theorem install_work (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (slot : Fin Acorn.FeatureConstants.skillCount) (target : Assignment config) :
    (install κ state slot target).work ≤
      installBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity := by
  change (installRun κ state slot target).work ≤ _
  unfold installRun
  exact Costed.charge_work_le (Costed.ite_work_bound _ (Nat.zero_le _)
    (Costed.bind_work_le (Costed.discard_work_le (skillInitial_work κ _ _ _ _)) fun _ =>
      Costed.discard_work_le (resetAction_work κ _ _)))

def refreshRanked (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    Costed (FreeDispatch shape actions config criterion dimension discounts payload) := do
  let held ← Costed.mapVector (κ .visit) (fun skill => Costed.op (κ .read) skill.interest.held)
    state.lifecycle.consumers.skills
  let targets ← rankAssignments κ dimension config state.lifecycle.consumers.demons.rankingWeights
    held
  Costed.foldl (κ .visit) (fun current slot => install κ current slot targets[slot.val]) state
    (List.finRange Acorn.FeatureConstants.skillCount)

theorem refreshRanked_val (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    (refreshRanked κ state).val = state.refreshRanked := rfl

abbrev refreshRankedBound (κ : Costs) (rows capacity positions units : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) Acorn.FeatureConstants.skillCount (κ .read) +
    (rankedCandidatesBound κ units + κ .assignmentTable +
      Library.foldl.work (κ .visit) Acorn.FeatureConstants.skillCount
        (installBound κ rows capacity positions))

theorem refreshRanked_work (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    (refreshRanked κ state).work ≤
      refreshRankedBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
        config.units.count := by
  unfold refreshRanked
  refine Nat.le_trans (Costed.bind_work_le
    (Costed.mapVector_work_le (κ .visit) (κ .read) _ _ fun _ _ => Nat.le_refl _) fun _ =>
      Costed.bind_work_le (rankAssignments_work κ dimension config _ _) fun _ =>
        Costed.foldl_work_le (κ .visit) _ _ _ _ fun current slot _ =>
          install_work κ current slot _) ?_
  simp only [List.length_finRange, refreshRankedBound]
  omega

def rankedSlots (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    Costed (List (FeatIdx dimension)) := do
  let width ← Costed.op (κ .rankWidth) ((rankDimension dimension).capacity - 1)
  let items ← candidateList κ dimension config weights
  let chosen ← rankedBlocks κ width items
  Costed.map (κ .visit)
    (fun candidate => Costed.op (κ .hashFeature) (unitFeature dimension config candidate.unit))
    chosen

theorem rankedSlots_val (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (rankedSlots κ dimension config weights).val = Features.rankedSlots dimension config weights :=
  rfl

abbrev rankedSlotsBound (κ : Costs) (positions units : Nat) : Nat :=
  κ .rankWidth + (candidateListBound κ units + (rankedBound κ positions units +
    (Library.map.work (κ .visit) positions (κ .hashFeature))))

theorem rankedSlots_work (κ : Costs) (dimension : Dimension) (config : Features.Config)
    (weights : WeightArray (.discounted .g99) dimension) :
    (rankedSlots κ dimension config weights).work ≤
      rankedSlotsBound κ (rankDimension dimension).capacity config.units.count :=
  Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.bind_work_le_at (candidateList_work κ dimension config weights)
      (Costed.bind_work_le_at
        (Nat.le_trans (rankedRun_work κ _ _ config.units.count
          (candidateList_length dimension config weights))
          (pass_mono (Nat.sub_le _ 1) (Nat.le_refl _)))
        (Nat.le_trans (Costed.map_work_le (κ .visit) (κ .hashFeature) _ _ fun _ _ => Nat.le_refl _)
          (Library.map.work_mono (Nat.le_trans (ranked_length _ _) (Nat.sub_le _ 1))
            (Nat.le_refl _)))))

def mergedRun (κ : Costs) (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension)) :
    Costed Unit := do
  let slots ← Costed.scanVector .toList (κ .visit) ranked.slots ranked.slots.toList
  let held ← Costed.scanList .dropLast (κ .visit) slots slots.dropLast
  let filtered ← Costed.map (κ .visit)
    (fun slot => Costed.ite (slot.isSome = true)
      (Costed.scanList .contains (κ .visit + κ .compare) order
        (slot.filter fun feature => order.contains feature))
      (Costed.pure (slot.filter fun feature => order.contains feature)))
    held
  Costed.discard (Costed.filter (κ .visit)
    (fun feature => Costed.scanList .contains (κ .visit + κ .compare) held
      (!held.contains (some feature)))
    order)
  let filled ← Costed.scanList .fillVacant (κ .visit) filtered (mergeSlots held order)
  let appended ← Costed.scanList .append (κ .visit) filled (filled ++ [none])
  Costed.discard (Costed.scanList .toArray (κ .visit) appended appended.toArray)

abbrev mergedBound (κ : Costs) (positions size : Nat) : Nat :=
  Library.toList.control (κ .visit) positions +
    (Library.dropLast.control (κ .visit) positions +
      (Library.map.work (κ .visit) positions
          (Library.contains.control (κ .visit + κ .compare) size) +
        (Library.filter.work (κ .visit) size
            (Library.contains.control (κ .visit + κ .compare) positions) +
          (Library.fillVacant.control (κ .visit) positions +
            (Library.append.control (κ .visit) positions +
              Library.toArray.control (κ .visit) (positions + 1))))))

theorem mergedRun_work (κ : Costs) (ranked : RankedFeatures dimension)
    (order : List (FeatIdx dimension)) :
    (mergedRun κ ranked order).work ≤
      mergedBound κ (rankDimension dimension).capacity order.length := by
  have dropped : ranked.slots.toList.dropLast.length ≤ (rankDimension dimension).capacity := by
    simp only [List.length_dropLast, Vector.length_toList]
    omega
  have length := mergeSlots_length ranked.slots.toList.dropLast order
  have appended : (mergeSlots ranked.slots.toList.dropLast order ++ [none]).length ≤
      (rankDimension dimension).capacity + 1 := by
    simp only [List.length_append, List.length_singleton, length]
    exact Nat.add_le_add_right dropped 1
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.bind_work_le_at
      (Library.dropLast.control_mono (Nat.le_of_eq (Vector.length_toList (xs := ranked.slots))))
      (Costed.bind_work_le_at
        (Nat.le_trans (Costed.map_work_le (κ .visit)
          (Library.contains.control (κ .visit + κ .compare) order.length)
          _ _ fun _ _ => Costed.ite_work_bound _ (Nat.le_refl _) (Nat.zero_le _))
          (Library.map.work_mono dropped (Nat.le_refl _)))
        (Costed.bind_work_le_at
          (Nat.le_trans (Costed.filter_work_le (κ .visit)
            (Library.contains.control (κ .visit + κ .compare)
              ranked.slots.toList.dropLast.length) _ _
            fun _ _ => Nat.le_refl _)
            (Library.filter.work_mono (Nat.le_refl _) (Library.contains.control_mono dropped)))
          (Costed.bind_work_le_at
            (Library.fillVacant.control_mono
              (Nat.le_trans (Nat.le_of_eq (List.length_map _)) dropped))
            (Costed.bind_work_le_at
              (Library.append.control_mono (Nat.le_trans (Nat.le_of_eq length) dropped))
              (Library.toArray.control_mono appended))))))) ?_
  exact Nat.le_refl _

def rankedRerankRun (κ : Costs) (ranked : RankedFeatures dimension)
    (order : List (FeatIdx dimension)) : Costed Unit := do
  mergedRun κ ranked order
  Costed.discard (Costed.scanVector .vectorEq (κ .visit + κ .compare) ranked.slots ())
  Costed.ite (ranked.merged order = ranked.slots) (Costed.pure ())
    (Costed.discard (tabulate κ (ranked.merged order)))

def rankedRerank (κ : Costs) (ranked : RankedFeatures dimension) (order : List (FeatIdx dimension))
    (fresh : order.Nodup) : Costed (RankedFeatures dimension) :=
  Costed.via (ranked.rerank order fresh) (rankedRerankRun κ ranked order)

abbrev rankedRerankBound (κ : Costs) (capacity positions size : Nat) : Nat :=
  mergedBound κ positions size + (Library.vectorEq.control (κ .visit + κ .compare) positions +
    tabulateBound κ capacity positions)

theorem rankedRerank_work (κ : Costs) (ranked : RankedFeatures dimension)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    (rankedRerank κ ranked order fresh).work ≤
      rankedRerankBound κ dimension.capacity (rankDimension dimension).capacity order.length := by
  change (rankedRerankRun κ ranked order).work ≤ _
  unfold rankedRerankRun
  exact Costed.bind_work_le (mergedRun_work κ ranked order) fun _ =>
    Costed.bind_work_le (Nat.le_refl _) fun _ =>
      Costed.ite_work_bound _ (Nat.zero_le _) (Costed.discard_work_le (tabulate_work κ _))

def changed (κ : Costs) (before after : RankedFeatures dimension) :
    Costed (List (RankIdx dimension)) := do
  let positions ← Costed.charge (κ .rankWidth) (Costed.scanList .finRange (κ .visit)
    (List.finRange (rankDimension dimension).capacity)
    (List.finRange (rankDimension dimension).capacity))
  Costed.filter (κ .visit)
    (fun position =>
      Costed.op (κ .compare) (after.slots[position.val] != before.slots[position.val]))
    positions

theorem changed_val (κ : Costs) (before after : RankedFeatures dimension) :
    (changed κ before after).val = before.changed after := rfl

abbrev changedBound (κ : Costs) (positions : Nat) : Nat :=
  κ .rankWidth + Library.finRange.control (κ .visit) positions +
    Library.filter.work (κ .visit) positions (κ .compare)

theorem changed_work (κ : Costs) (before after : RankedFeatures dimension) :
    (changed κ before after).work ≤ changedBound κ (rankDimension dimension).capacity := by
  unfold changed
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.filter_work_le (κ .visit) (κ .compare) _ _ fun _ _ => Nat.le_refl _)) ?_
  simp only [List.length_finRange, changedBound]
  omega

theorem changed_length (before after : RankedFeatures dimension) :
    (before.changed after).length ≤ (rankDimension dimension).capacity := by
  simpa [RankedFeatures.changed] using List.length_filter_le
    (fun position : RankIdx dimension =>
      after.slots[position.val] != before.slots[position.val])
    (List.finRange (rankDimension dimension).capacity)

def forget (κ : Costs)
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity) (positions : List (RankIdx dimension)) :
    Costed (Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity) :=
  Costed.charge (κ .rankWidth) (Costed.mapFinIdx (κ .visit)
    (fun index row bound => Costed.bind
      (Costed.scanList .contains (κ .visit + κ .compare) positions ()) fun _ =>
        Costed.ite (positions.contains ⟨index, bound⟩ = true)
          (managedInitial κ _ _)
          (Costed.foldl (κ .visit)
            (fun learner position => managedApply κ learner (.retire position) trivial)
            row positions))
    rows)

theorem forget_val (κ : Costs)
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity) (positions : List (RankIdx dimension)) :
    (forget κ rows positions).val = Transition.forget rows positions := rfl

abbrev forgetBound (κ : Costs) (positions size : Nat) : Nat :=
  κ .rankWidth + Library.mapFinIdx.work (κ .visit) positions
    (Library.contains.control (κ .visit + κ .compare) size +
    (learnerInitialBound κ positions +
      Library.foldl.work (κ .visit) size
        (κ .managedEntry +
          (κ .retire + Library.findIdx.work (κ .visit) positions (κ .compare)))))

theorem forget_work (κ : Costs)
    (rows : Vector (Managed (criterion.config .demon) (rankDimension dimension))
      (rankDimension dimension).capacity) (positions : List (RankIdx dimension)) :
    (forget κ rows positions).work ≤
      forgetBound κ (rankDimension dimension).capacity positions.length :=
  Costed.charge_work_le (Costed.mapFinIdx_work_le _ _ _ _ fun _ row _ =>
    Costed.bind_work_le (Nat.le_refl _) fun _ =>
      Costed.ite_work_bound _
        (Nat.le_trans (learnerInitialRun_work κ _ _) (Nat.le_add_right _ _))
        (Nat.le_trans (Costed.foldl_work_le (κ .visit)
          (κ .managedEntry + (κ .retire + Library.findIdx.work (κ .visit)
            (rankDimension dimension).capacity (κ .compare))) _ row
          positions fun learner position _ =>
            managedApply_work κ learner (.retire position) trivial)
          (Nat.le_add_left _ _)))

def forgetColumns (κ : Costs) {count : Nat}
    (learners : Vector (Managed (criterion.config .demon) (rankDimension dimension)) count)
    (positions : List (RankIdx dimension)) :
    Costed (Vector (Managed (criterion.config .demon) (rankDimension dimension)) count) :=
  Costed.mapVector (κ .visit)
    (fun learner => Costed.foldl (κ .visit)
      (fun current position =>
        Costed.charge (κ .rankWidth) (managedApply κ current (.retire position) trivial))
      learner positions)
    learners

theorem forgetColumns_val (κ : Costs) {count : Nat}
    (learners : Vector (Managed (criterion.config .demon) (rankDimension dimension)) count)
    (positions : List (RankIdx dimension)) :
    (forgetColumns κ learners positions).val = Transition.forgetColumns learners positions := rfl

theorem forgetColumns_work (κ : Costs) {count : Nat}
    (learners : Vector (Managed (criterion.config .demon) (rankDimension dimension)) count)
    (positions : List (RankIdx dimension)) :
    (forgetColumns κ learners positions).work ≤
      Library.vectorMap.work (κ .visit) count (Library.foldl.work (κ .visit) positions.length
        (κ .rankWidth + (κ .managedEntry + (κ .retire + Library.findIdx.work (κ .visit)
          (rankDimension dimension).capacity (κ .compare))))) :=
  Costed.mapVector_work_le _ _ _ _ fun learner _ =>
    Costed.foldl_work_le (κ .visit) _ _ learner positions fun current position _ =>
      Costed.charge_work_le (managedApply_work κ current (.retire position) trivial)

def transitionRerank (κ : Costs) (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    Costed (Transition dimension criterion) := do
  let ranked ← rankedRerank κ transition.ranked order fresh
  let positions ← changed κ transition.ranked ranked
  let rows ← forget κ transition.rows positions
  let deviations ← forgetColumns κ transition.deviations positions
  Costed.pure ⟨ranked, rows, deviations⟩

theorem transitionRerank_val (κ : Costs) (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    (transitionRerank κ transition order fresh).val = transition.rerank order fresh := rfl

theorem forgetBound_mono (κ : Costs) (positions : Nat) {size limit : Nat} (fits : size ≤ limit) :
    forgetBound κ positions size ≤ forgetBound κ positions limit := by
  have tests := Library.contains.control_mono (visit := κ .visit + κ .compare) fits
  have retires := Library.foldl.work_mono (visit := κ .visit) fits
    (Nat.le_refl (κ .managedEntry + (κ .retire + Library.findIdx.work (κ .visit) positions
      (κ .compare))))
  exact Nat.add_le_add_left (Library.mapFinIdx.work_mono (Nat.le_refl _)
    (Nat.add_le_add tests (Nat.add_le_add_left retires _))) _

abbrev columnsBound (κ : Costs) (positions size : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) Acorn.FeatureConstants.metaActionCount
    (Library.foldl.work (κ .visit) size (κ .rankWidth +
      (κ .managedEntry + (κ .retire + Library.findIdx.work (κ .visit) positions (κ .compare)))))

abbrev transitionRerankBound (κ : Costs) (capacity positions size : Nat) : Nat :=
  rankedRerankBound κ capacity positions size + (changedBound κ positions +
    (forgetBound κ positions positions + (columnsBound κ positions positions + 0)))

theorem transitionRerank_work (κ : Costs) (transition : Transition dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    (transitionRerank κ transition order fresh).work ≤
      transitionRerankBound κ dimension.capacity (rankDimension dimension).capacity
        order.length :=
  Costed.bind_work_le (rankedRerank_work κ transition.ranked order fresh) fun ranked =>
    Costed.bind_work_le_at (changed_work κ transition.ranked ranked)
      (Costed.bind_work_le_at (Nat.le_trans (forget_work κ transition.rows _)
          (forgetBound_mono κ _ (changed_length transition.ranked ranked)))
        (Costed.bind_work_le (Nat.le_trans (forgetColumns_work κ transition.deviations _)
          (Library.vectorMap.work_mono (Nat.le_refl _)
            (Library.foldl.work_mono (changed_length transition.ranked ranked) (Nat.le_refl _))))
          fun _ =>
          Nat.le_refl 0))

def modelRerankRun (κ : Costs) (model : Model dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) : Costed Unit :=
  match model with
  | .discounted _ _ transition => Costed.discard (transitionRerank κ transition order fresh)
  | .differential _ _ _ transition => Costed.discard (transitionRerank κ transition order fresh)

def modelRerank (κ : Costs) (model : Model dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) : Costed (Model dimension criterion) :=
  Costed.via (model.rerank order fresh) (modelRerankRun κ model order fresh)

theorem modelRerank_work (κ : Costs) (model : Model dimension criterion)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    (modelRerank κ model order fresh).work ≤
      transitionRerankBound κ dimension.capacity (rankDimension dimension).capacity
        order.length := by
  change (modelRerankRun κ model order fresh).work ≤ _
  cases model
  · exact transitionRerank_work κ _ order fresh
  · exact transitionRerank_work κ _ order fresh

def rerankModelsRun (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    Costed Unit := do
  Costed.discard (rankedSlots κ dimension config state.lifecycle.consumers.demons.rankingWeights)
  Costed.discard (Costed.mapVector (κ .visit)
    (fun skill => modelRerank κ skill.model
      (Features.rankedSlots dimension config state.lifecycle.consumers.demons.rankingWeights)
      (rankedSlots_nodup dimension config state.lifecycle.consumers.demons.rankingWeights))
    state.lifecycle.consumers.skills)

def rerankModels (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    Costed (FreeDispatch shape actions config criterion dimension discounts payload) :=
  Costed.via state.rerankModels (rerankModelsRun κ state)

abbrev rerankModelsBound (κ : Costs) (capacity positions units : Nat) : Nat :=
  rankedSlotsBound κ positions units +
    Library.vectorMap.work (κ .visit) Acorn.FeatureConstants.skillCount
    (transitionRerankBound κ capacity positions positions)

theorem transitionRerankBound_mono (κ : Costs) (capacity positions : Nat) {size limit : Nat}
    (fits : size ≤ limit) :
    transitionRerankBound κ capacity positions size ≤
      transitionRerankBound κ capacity positions limit := by
  have kept := Library.map.work_mono (visit := κ .visit) (Nat.le_refl positions)
    (Library.contains.control_mono (visit := κ .visit + κ .compare) fits)
  have entrants := Library.filter.work_mono (visit := κ .visit) fits
    (Nat.le_refl (Library.contains.control (κ .visit + κ .compare) positions))
  simp only [transitionRerankBound, rankedRerankBound, mergedBound]
  omega

theorem rerankModels_work (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload) :
    (rerankModels κ state).work ≤
      rerankModelsBound κ dimension.capacity (rankDimension dimension).capacity
        config.units.count :=
  Costed.bind_work_le (rankedSlots_work κ dimension config _) fun _ =>
    Costed.mapVector_work_le _ _ _ _
      fun (skill : Skill actions config criterion dimension (.g99 :: discounts)) _ =>
      Nat.le_trans (modelRerank_work κ skill.model _ _)
        (transitionRerankBound_mono κ _ _ (Nat.le_trans (rankedSlots_length dimension config _)
          (Nat.sub_le _ 1)))

def refreshModels (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (assign : Bool) :
    Costed (FreeDispatch shape actions config criterion dimension discounts payload) :=
  Costed.via (state.refreshModels assign) (do
    Costed.ite (assign = true) (Costed.discard (refreshRanked κ state)) (Costed.pure ())
    Costed.discard (rerankModels κ (if assign then state.refreshRanked else state)))

abbrev refreshBound (κ : Costs) (rows capacity positions units : Nat) : Nat :=
  refreshRankedBound κ rows capacity positions units +
    rerankModelsBound κ capacity positions units

theorem refreshModels_work (κ : Costs)
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (assign : Bool) :
    (refreshModels κ state assign).work ≤
      refreshBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
        config.units.count :=
  Costed.bind_work_le (Costed.ite_work_bound _
      (Costed.discard_work_le (refreshRanked_work κ state)) (Nat.zero_le _)) fun _ =>
    Costed.discard_work_le (rerankModels_work κ _)

end AcornVerif.Resource.Twin
