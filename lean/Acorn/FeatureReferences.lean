import Acorn.FeatureConstants
import Acorn.FeatureRefresh

namespace Acorn.Features

variable {actions : Word.Count}

def eraseFeature {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature : FeatIdx dimension) : SwiftTd.ActiveSet dimension :=
  if features.indices.contains feature then
    ⟨features.indices.filter (· != feature), features.nodup.sublist List.filter_sublist⟩
  else features

theorem eraseFeature_absent {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature : FeatIdx dimension) : feature ∉ (eraseFeature features feature).indices := by
  unfold eraseFeature
  split
  · simp
  · rename_i absent
    simpa using absent

theorem eraseFeature_other {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature other : FeatIdx dimension) (different : other ≠ feature) :
    other ∈ (eraseFeature features feature).indices ↔ other ∈ features.indices := by
  unfold eraseFeature
  split
  · simp [different]
  · rfl

theorem eraseFeature_subset {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature other : FeatIdx dimension)
    (member : other ∈ (eraseFeature features feature).indices) : other ∈ features.indices := by
  unfold eraseFeature at member
  split at member
  · exact (List.mem_filter.mp member).1
  · exact member

structure RecentFeatures (dimension : Dimension) where
  frames : Vector (SwiftTd.ActiveSet dimension) Acorn.FeatureConstants.optionMaxDuration
  next : Fin Acorn.FeatureConstants.optionMaxDuration
  cursor : Fin Acorn.FeatureConstants.optionMaxDuration

def RecentFeatures.after (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    Fin Acorn.FeatureConstants.optionMaxDuration :=
  ⟨(position.val + 1) % Acorn.FeatureConstants.optionMaxDuration, Nat.mod_lt _ (by decide)⟩

def RecentFeatures.before (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    Fin Acorn.FeatureConstants.optionMaxDuration :=
  ⟨(position.val + (Acorn.FeatureConstants.optionMaxDuration - 1)) %
    Acorn.FeatureConstants.optionMaxDuration, Nat.mod_lt _ (by decide)⟩

theorem RecentFeatures.before_after (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    RecentFeatures.before (RecentFeatures.after position) = position ∧
      RecentFeatures.after (RecentFeatures.before position) = position := by
  have bound : position.val < 128 := position.isLt
  constructor <;> apply Fin.ext <;>
    simp only [RecentFeatures.before, RecentFeatures.after,
      Acorn.FeatureConstants.optionMaxDuration] <;> omega

def RecentFeatures.cold (dimension : Dimension) : RecentFeatures dimension :=
  ⟨Vector.replicate _ (SwiftTd.ActiveSet.empty dimension), ⟨0, by decide⟩, ⟨0, by decide⟩⟩

def RecentFeatures.record {dimension : Dimension} (store : RecentFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) : RecentFeatures dimension :=
  { store with
    frames := store.frames.set store.next.val features store.next.isLt
    next := RecentFeatures.after store.next }

def RecentFeatures.selected {dimension : Dimension} (store : RecentFeatures dimension) :
    SwiftTd.ActiveSet dimension := store.frames[store.cursor.val]

def RecentFeatures.advance {dimension : Dimension} (store : RecentFeatures dimension) :
    RecentFeatures dimension := { store with cursor := RecentFeatures.before store.cursor }

def RecentFeatures.retire {dimension : Dimension} (store : RecentFeatures dimension)
    (feature : FeatIdx dimension) : RecentFeatures dimension :=
  { store with frames := store.frames.map (eraseFeature · feature) }

theorem RecentFeatures.retire_absent {dimension : Dimension} (store : RecentFeatures dimension)
    (feature : FeatIdx dimension) (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    feature ∉ ((store.retire feature).frames[position.val]).indices := by
  simp only [RecentFeatures.retire, Vector.getElem_map]
  exact eraseFeature_absent _ feature

inductive PredictionCache : List Discount → Type where
  | nil : PredictionCache []
  | cons {discount : Discount} {rest : List Discount}
      (value : Prediction discount) (tail : PredictionCache rest) : PredictionCache (discount :: rest)

def PredictionCache.initial : (discounts : List Discount) → PredictionCache discounts
  | [] => .nil
  | discount :: rest => .cons (Prediction.project discount .zero) (PredictionCache.initial rest)

def PredictionCache.wordsCosted {discounts : List Discount} :
    PredictionCache discounts → Costed (List Binary32)
  | .nil => Costed.op .visit []
  | .cons value rest => Costed.charge .visit do
    let tail ← rest.wordsCosted
    Costed.op .read (value.value :: tail)

def PredictionCache.words {discounts : List Discount} (cache : PredictionCache discounts) : List Binary32 :=
  cache.wordsCosted.val

theorem PredictionCache.words_nil : (PredictionCache.nil).words = [] := rfl

theorem PredictionCache.words_cons {discount : Discount} {rest : List Discount}
    (value : Prediction discount) (tail : PredictionCache rest) :
    (PredictionCache.cons value tail).words = value.value :: tail.words := rfl

theorem PredictionCache.length {discounts : List Discount} (cache : PredictionCache discounts) :
    cache.words.length = discounts.length := by
  induction cache with
  | nil => rfl
  | cons value rest ih => simp [PredictionCache.words_cons, ih]

inductive Occupancy (activation exploration : Type) where
  | idle
  | exploring (run : exploration)
  | option (slot : Fin Acorn.FeatureConstants.skillCount) (state : activation)

def Occupancy.free {activation exploration : Type} : Occupancy activation exploration → Bool
  | .idle => true
  | .exploring _ | .option _ _ => false

structure TemporalReferences (dimension : Dimension) (discounts : List Discount)
    (activation exploration decision : Type) where
  demonPredictions : PredictionCache discounts
  demonErrors : Vector Binary32 discounts.length
  modelPredictions : Vector ModelCache Acorn.FeatureConstants.skillCount
  phase : Occupancy activation exploration
  planningSteps : UInt64
  planningErrors : Vector Binary32 Acorn.FeatureConstants.skillCount
  gapSteps : UInt8
  gapReward : Binary32
  rng : Rng.Xoshiro256
  pendingAction : Bool
  lastDecision : decision
  recent : RecentFeatures dimension

def TemporalReferences.cold {dimension : Dimension} (config : Config) (discounts : List Discount)
    {activation exploration decision : Type} (emptyDecision : decision) :
    TemporalReferences dimension discounts activation exploration decision :=
  ⟨PredictionCache.initial discounts, Vector.replicate _ .zero,
    Vector.replicate _ ModelCache.initial, .idle, 0, Vector.replicate _ .zero,
    0, .zero, Rng.Xoshiro256.seed (Rng.streamKey config.seed 0xA6E0000000000001), false, emptyDecision,
    .cold dimension⟩

structure FeatureRuntime (shape : PatchShape) (actions : Word.Count) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) (activation exploration decision : Type) where
  lifecycle : Lifecycle shape actions config criterion dimension discounts
  references : TemporalReferences dimension discounts activation exploration decision

def Ensemble.releaseAll {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (units : List (Fin config.units.count)) : Ensemble actions config criterion dimension discounts :=
  units.foldl Ensemble.release ensemble

theorem Ensemble.release_keeps {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (released unit : Fin config.units.count) (slot : Fin Acorn.FeatureConstants.skillCount)
    (absent : ensemble.skills[slot.val].interest.held.holds unit = false) :
    (ensemble.release released).skills[slot.val].interest.held.holds unit = false := by
  simp only [Ensemble.release, Vector.getElem_map]
  split
  · simp [Skill.initial, Interest.held, Assignment.holds]
  · exact absent

theorem Ensemble.releaseAll_holds {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (units : List (Fin config.units.count)) :
    ∀ (ensemble : Ensemble actions config criterion dimension discounts) (unit : Fin config.units.count),
      unit ∈ units → ∀ slot : Fin Acorn.FeatureConstants.skillCount,
        (ensemble.releaseAll units).skills[slot.val].interest.held.holds unit = false := by
  induction units with
  | nil => intro _ _ member; simp at member
  | cons head rest ih =>
    intro ensemble unit member slot
    simp only [Ensemble.releaseAll, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.mp member with same | later
    · subst same
      have gone := Ensemble.release_holds ensemble unit slot
      have keep (units : List (Fin config.units.count)) :
          ∀ (current : Ensemble actions config criterion dimension discounts),
            current.skills[slot.val].interest.held.holds unit = false →
            (units.foldl Ensemble.release current).skills[slot.val].interest.held.holds unit = false := by
        induction units with
        | nil => intro current absent; exact absent
        | cons next others inner =>
          intro current absent
          exact inner _ (Ensemble.release_keeps current next unit slot absent)
      exact keep rest _ gone
    · exact ih _ unit later slot

theorem Ensemble.releaseAll_unheld {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (units : List (Fin config.units.count)) :
    ∀ (ensemble : Ensemble actions config criterion dimension discounts),
      (∀ unit ∈ units, ensemble.holds unit = false) → ensemble.releaseAll units = ensemble := by
  induction units with
  | nil => intro _ _; rfl
  | cons head rest ih =>
    intro ensemble unheld
    simp only [Ensemble.releaseAll, List.foldl_cons] at ih ⊢
    rw [Ensemble.release_unheld ensemble head (unheld head (by simp))]
    exact ih ensemble (fun unit member => unheld unit (List.mem_cons_of_mem _ member))

def RecentFeatures.retireAll {config : Config} {dimension : Dimension}
    (store : RecentFeatures dimension) (units : List (Fin config.units.count)) :
    RecentFeatures dimension :=
  units.foldl (fun current unit => current.retire (unitFeature dimension config unit)) store

theorem RecentFeatures.retireAll_absent {config : Config} {dimension : Dimension}
    (units : List (Fin config.units.count)) :
    ∀ (store : RecentFeatures dimension) (unit : Fin config.units.count), unit ∈ units →
      ∀ position : Fin Acorn.FeatureConstants.optionMaxDuration,
        unitFeature dimension config unit ∉
          ((store.retireAll units).frames[position.val]).indices := by
  induction units with
  | nil => intro _ _ member; simp at member
  | cons head rest ih =>
    intro store unit member position
    simp only [RecentFeatures.retireAll, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.mp member with same | later
    · have keep (others : List (Fin config.units.count)) :
          ∀ current : RecentFeatures dimension,
            unitFeature dimension config unit ∉ (current.frames[position.val]).indices →
            unitFeature dimension config unit ∉ ((others.foldl (fun next other =>
              next.retire (unitFeature dimension config other)) current).frames[position.val]).indices := by
        induction others with
        | nil => intro current absent; exact absent
        | cons next more inner =>
          intro current absent
          apply inner
          simp only [RecentFeatures.retire, Vector.getElem_map]
          exact fun inside => absent (eraseFeature_subset _ _ _ inside)
      rw [← same]
      exact keep rest _ (store.retire_absent _ position)
    · exact ih _ unit later position

def FeatureRuntime.retire {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    FeatureRuntime shape actions config criterion dimension discounts activation exploration decision :=
  let tested := state.lifecycle.test state.references.phase.free active
  { state with
    lifecycle := { tested.1 with consumers := tested.1.consumers.releaseAll tested.2 }
    references := { state.references with recent := state.references.recent.retireAll tested.2 } }

theorem FeatureRuntime.retire_references {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    (state.retire active).references =
        { state.references with recent := (state.references.recent.retireAll
          (state.lifecycle.test state.references.phase.free active).2) } := rfl

theorem FeatureRuntime.retire_recent {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) (unit : Fin config.units.count)
    (replaced : unit ∈ (state.lifecycle.test state.references.phase.free active).2)
    (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    unitFeature dimension config unit ∉
      ((state.retire active).references.recent.frames[position.val]).indices :=
  RecentFeatures.retireAll_absent _ _ unit replaced position

theorem FeatureRuntime.retire_releases {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    ∀ unit ∈ (state.lifecycle.test state.references.phase.free active).2,
      ∀ slot : Fin Acorn.FeatureConstants.skillCount,
        (state.retire active).lifecycle.consumers.skills[slot.val].interest.held.holds unit = false :=
  fun unit member slot => Ensemble.releaseAll_holds
    (state.lifecycle.test state.references.phase.free active).2
    (state.lifecycle.test state.references.phase.free active).1.consumers unit member slot

theorem FeatureRuntime.retire_occupied {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) (occupied : state.references.phase.free = false) :
    state.retire active = { state with
      lifecycle := (state.lifecycle.test false active).1
      references := { state.references with recent := (state.references.recent.retireAll
        (state.lifecycle.test false active).2) } } := by
  have unheld := state.lifecycle.test_unheld active
  have holds := state.lifecycle.test_holds false active
  have kept : ∀ unit ∈ (state.lifecycle.test false active).2,
      (state.lifecycle.test false active).1.consumers.holds unit = false := by
    intro unit member
    rw [holds]
    exact unheld unit member
  unfold FeatureRuntime.retire
  simp only [occupied, Ensemble.releaseAll_unheld _ _ kept] <;> rfl

def FeatureRuntime.encodeCurrentCosted {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}
    {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    Costed (EncodingFrame dimension state.lifecycle.representation.bank words patch) :=
  EncodingFrame.computeCosted dimension state.lifecycle.representation.bank words patch

def FeatureRuntime.encodeCurrent {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    EncodingFrame dimension state.lifecycle.representation.bank words patch :=
  (state.encodeCurrentCosted words patch).val

theorem FeatureRuntime.encodeCurrent_def {shape : PatchShape} {config : Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}
    {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    state.encodeCurrent words patch =
      EncodingFrame.compute dimension state.lifecycle.representation.bank words patch := rfl

def FeatureRuntime.refreshAtFree {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension (.g99 :: discounts) activation exploration decision)
    (assign : Bool) :
    FeatureRuntime shape actions config criterion dimension (.g99 :: discounts) activation exploration decision :=
  match state.references.phase with
  | .idle =>
    let free : FreeDispatch shape actions config criterion dimension discounts Unit :=
      ⟨state.lifecycle, state.references.modelPredictions, none⟩
    let refreshed := free.refreshModels assign
    { state with
      lifecycle := refreshed.lifecycle
      references := { state.references with modelPredictions := refreshed.predictions } }
  | .option _ _ | .exploring _ => state

theorem FeatureRuntime.occupied_preserves {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension (.g99 :: discounts) activation exploration decision)
    (assign : Bool) (occupied : state.references.phase ≠ .idle) :
    state.refreshAtFree assign = state := by
  unfold FeatureRuntime.refreshAtFree
  split
  · contradiction
  · rfl
  · rfl

theorem FeatureRuntime.encodeCurrent_fresh {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    (state.encodeCurrent words patch).active = encode dimension state.lifecycle.representation.bank words patch := rfl

end Acorn.Features
