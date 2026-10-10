/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.FeatureRefresh

/-!
# Temporal references around feature retirement

The tester retains temporal predictions, active-option potential, occupancy,
planner state and the pending meta gap in the current schedule. These are not
claimed to be fresh encodings of the replacement bank. A unit held as an option
objective is replaced only at a free boundary, where every slot holding it is
released and the next free boundary's assignment refresh installs an entrant; a live
option therefore never loses its objective.
New encoding frames are constructed against the current bank. A checkpoint image stores
every reference (`Checkpoint.referencesFormat`).
Activation, exploration and decision payloads are parametric because this slice
does not interpret their later control/option algorithms.

Planning's search control keeps a bounded store of recently seen feature vectors
(Sutton, Bowling and Pilarski, *The Alberta Plan for AI Research*,
arXiv:2208.11173v3 (2023), Step 9, p. 9: search control "varying the order of state
updates"). The store holds feature vectors only, never an action, reward or
successor, so no stored transition exists to replay into a learner; it names where a
model backup is computed. A frame is recorded when its step completes, after
selection and planning, so the store holds only frames earlier than the one being
planned at. Frames are written in one direction and swept in the other, so the
sweep never follows the write position. A retired slot is erased from every stored
vector, so no backup writes a replacement unit's weight at a frame its predecessor
was active in.
-/
namespace Acorn.Features

variable {actions : Word.Count}

/-- Remove one feature slot from a frame; a frame without it is returned as is. -/
def eraseFeature {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature : FeatIdx dimension) : SwiftTd.ActiveSet dimension :=
  if features.indices.contains feature then
    ⟨features.indices.filter (· != feature), features.nodup.sublist List.filter_sublist⟩
  else features

/-- An erased slot is absent from the frame, whether or not it was there. -/
theorem eraseFeature_absent {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature : FeatIdx dimension) : feature ∉ (eraseFeature features feature).indices := by
  unfold eraseFeature
  split
  · simp
  · rename_i absent
    simpa using absent

/-- Erasing one slot keeps every other slot's membership. -/
theorem eraseFeature_other {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature other : FeatIdx dimension) (different : other ≠ feature) :
    other ∈ (eraseFeature features feature).indices ↔ other ∈ features.indices := by
  unfold eraseFeature
  split
  · simp [different]
  · rfl

/-- Erasing a slot adds no slot to a frame. -/
theorem eraseFeature_subset {dimension : Dimension} (features : SwiftTd.ActiveSet dimension)
    (feature other : FeatIdx dimension)
    (member : other ∈ (eraseFeature features feature).indices) : other ∈ features.indices := by
  unfold eraseFeature at member
  split at member
  · exact (List.mem_filter.mp member).1
  · exact member

/-- The most recent earlier feature vectors, one per action of the longest option:
at a frame where an option stops, the frame it started at is still here. A position
not yet written holds the empty feature set. -/
structure RecentFeatures (dimension : Dimension) where
  /-- Stored frames, overwritten oldest first. -/
  frames : Vector (SwiftTd.ActiveSet dimension) Acorn.FeatureConstants.optionMaxDuration
  /-- Position the next frame overwrites. -/
  next : Fin Acorn.FeatureConstants.optionMaxDuration
  /-- Position search control backs up next. -/
  cursor : Fin Acorn.FeatureConstants.optionMaxDuration

/-- The following position, wrapping at the store size. -/
def RecentFeatures.after (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    Fin Acorn.FeatureConstants.optionMaxDuration :=
  ⟨(position.val + 1) % Acorn.FeatureConstants.optionMaxDuration, Nat.mod_lt _ (by decide)⟩

/-- The preceding position, wrapping at the store size. -/
def RecentFeatures.before (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    Fin Acorn.FeatureConstants.optionMaxDuration :=
  ⟨(position.val + (Acorn.FeatureConstants.optionMaxDuration - 1)) %
    Acorn.FeatureConstants.optionMaxDuration, Nat.mod_lt _ (by decide)⟩

/-- Stepping back undoes stepping forward and conversely.
`AcornVerif.CurrentPlanning.sweep_reaches` shows that repeated steps back reach every
position within one pass over the store. -/
theorem RecentFeatures.before_after (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    RecentFeatures.before (RecentFeatures.after position) = position ∧
      RecentFeatures.after (RecentFeatures.before position) = position := by
  have bound : position.val < 128 := position.isLt
  constructor <;> apply Fin.ext <;>
    simp only [RecentFeatures.before, RecentFeatures.after,
      Acorn.FeatureConstants.optionMaxDuration] <;> omega

/-- A store that has seen no frame. -/
def RecentFeatures.cold (dimension : Dimension) : RecentFeatures dimension :=
  ⟨Vector.replicate _ (SwiftTd.ActiveSet.empty dimension), ⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- Record the current frame over the oldest one. -/
def RecentFeatures.record {dimension : Dimension} (store : RecentFeatures dimension)
    (features : SwiftTd.ActiveSet dimension) : RecentFeatures dimension :=
  { store with
    frames := store.frames.set store.next.val features store.next.isLt
    next := RecentFeatures.after store.next }

/-- The stored frame search control backs up now. -/
def RecentFeatures.selected {dimension : Dimension} (store : RecentFeatures dimension) :
    SwiftTd.ActiveSet dimension := store.frames[store.cursor.val]

/-- Move search control to the preceding position: a sweep against the write
direction, which visits every position once per store size and consumes no random
draw. Where every step is a planning boundary, the write position moves one way and
the sweep the other, so each stored frame is selected once before it is overwritten;
the two positions then close by two per step, so the ages selected share one parity. -/
def RecentFeatures.advance {dimension : Dimension} (store : RecentFeatures dimension) :
    RecentFeatures dimension := { store with cursor := RecentFeatures.before store.cursor }

/-- Erase a retired feature slot from every stored frame. -/
def RecentFeatures.retire {dimension : Dimension} (store : RecentFeatures dimension)
    (feature : FeatIdx dimension) : RecentFeatures dimension :=
  { store with frames := store.frames.map (eraseFeature · feature) }

/-- After retirement no stored frame lists the retired slot. -/
theorem RecentFeatures.retire_absent {dimension : Dimension} (store : RecentFeatures dimension)
    (feature : FeatIdx dimension) (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    feature ∉ ((store.retire feature).frames[position.val]).indices := by
  simp only [RecentFeatures.retire, Vector.getElem_map]
  exact eraseFeature_absent _ feature

/-- Prediction caches carry their immutable horizon layout at every write. -/
inductive PredictionCache : List Discount → Type where
  /-- Empty channel tail. -/
  | nil : PredictionCache []
  /-- One refined channel and its remaining layout. -/
  | cons {discount : Discount} {rest : List Discount}
      (value : Prediction discount) (tail : PredictionCache rest) : PredictionCache (discount :: rest)

/-- Cold prediction cache in its exact layout. -/
def PredictionCache.initial : (discounts : List Discount) → PredictionCache discounts
  | [] => .nil
  | discount :: rest => .cons (Prediction.project discount .zero) (PredictionCache.initial rest)

/-- Read the stored temporal words without reinterpreting them as current predictions. -/
def PredictionCache.words {discounts : List Discount} (cache : PredictionCache discounts) : List Binary32 :=
  match cache with
  | .nil => []
  | .cons value rest => value.value :: rest.words

/-- Reading preserves the complete prediction-channel count. -/
theorem PredictionCache.length {discounts : List Discount} (cache : PredictionCache discounts) :
    cache.words.length = discounts.length := by
  induction cache with
  | nil => rfl
  | cons value rest ih => simp [PredictionCache.words, ih]

/-- One exclusive dispatch occupancy; no closing owner is stored at an end-of-step boundary. -/
inductive Occupancy (activation exploration : Type) where
  /-- Free to dispatch. -/
  | idle
  /-- A committed exploratory run. -/
  | exploring (run : exploration)
  /-- One live option and its stable table slot. -/
  | option (slot : Fin Acorn.FeatureConstants.skillCount) (state : activation)

/-- A free boundary has neither a live option nor committed exploration. -/
def Occupancy.free {activation exploration : Type} : Occupancy activation exploration → Bool
  | .idle => true
  | .exploring _ | .option _ _ => false

/-- The complete process-local reference families surrounding representation storage. -/
structure TemporalReferences (dimension : Dimension) (discounts : List Discount)
    (activation exploration decision : Type) where
  /-- Prior-step demon predictions used by the next observation encoding. -/
  demonPredictions : PredictionCache discounts
  /-- Last prediction errors. -/
  demonErrors : Vector Binary32 discounts.length
  /-- Cached option-model values, refreshed before hierarchy dispatch. -/
  modelPredictions : Vector ModelCache Acorn.FeatureConstants.skillCount
  /-- The live activation payload includes its prior potential and elapsed age. -/
  phase : Occupancy activation exploration
  /-- Accumulated planning work. -/
  planningSteps : UInt64
  /-- Last planning errors. -/
  planningErrors : Vector Binary32 Acorn.FeatureConstants.skillCount
  /-- Deferred meta-controller span. -/
  gapSteps : UInt8
  /-- Deferred span reward. -/
  gapReward : Binary32
  /-- Process-local action generator. -/
  rng : Rng.Xoshiro256
  /-- Whether one action awaits its next observation. -/
  pendingAction : Bool
  /-- Last observer decision record. -/
  lastDecision : decision
  /-- Recently seen feature vectors, for planning's search control. -/
  recent : RecentFeatures dimension

/-- Cold references use the process stream's declared seed salt and no pending activation. -/
def TemporalReferences.cold {dimension : Dimension} (config : Config) (discounts : List Discount)
    {activation exploration decision : Type} (emptyDecision : decision) :
    TemporalReferences dimension discounts activation exploration decision :=
  ⟨PredictionCache.initial discounts, Vector.replicate _ .zero,
    Vector.replicate _ ModelCache.initial, .idle, 0, Vector.replicate _ .zero,
    0, .zero, Rng.Xoshiro256.seed (Rng.streamKey config.seed 0xA6E0000000000001), false, emptyDecision,
    .cold dimension⟩

/-- End-of-step receiver, after any detached closing owner has received terminal credit. -/
structure FeatureRuntime (shape : PatchShape) (actions : Word.Count) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) (activation exploration decision : Type) where
  /-- Complete representation and learner storage. -/
  lifecycle : Lifecycle shape actions config criterion dimension discounts
  /-- Current process-local references. -/
  references : TemporalReferences dimension discounts activation exploration decision

/-- Release every slot holding any of the given units. -/
def Ensemble.releaseAll {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (units : List (Fin config.units.count)) : Ensemble actions config criterion dimension discounts :=
  units.foldl Ensemble.release ensemble

/-- A slot that does not hold a unit still does not after any release. -/
theorem Ensemble.release_keeps {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (released unit : Fin config.units.count) (slot : Fin Acorn.FeatureConstants.skillCount)
    (absent : ensemble.skills[slot.val].interest.held.holds unit = false) :
    (ensemble.release released).skills[slot.val].interest.held.holds unit = false := by
  simp only [Ensemble.release, Vector.getElem_map]
  split
  · simp [Skill.initial, Interest.held, Assignment.holds]
  · exact absent

/-- After releasing a list, no slot holds any listed unit. -/
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

/-- Releasing only unheld units changes nothing. -/
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

/-- Erase the slot of every replaced unit from the stored recent frames. -/
def RecentFeatures.retireAll {config : Config} {dimension : Dimension}
    (store : RecentFeatures dimension) (units : List (Fin config.units.count)) :
    RecentFeatures dimension :=
  units.foldl (fun current unit => current.retire (unitFeature dimension config unit)) store

/-- After erasing a list of replaced units, no stored frame lists the slot of any of
them: a later erasure never restores an earlier one. -/
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

/-- The tester step at the end of a frame. A held unit is eligible only at a free
boundary, where every slot holding a replaced unit is released; the next free
boundary's assignment refresh installs an entrant when the ranking has one. Each
replaced unit's slot is erased from the stored recent frames. -/
def FeatureRuntime.retire {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    FeatureRuntime shape actions config criterion dimension discounts activation exploration decision :=
  let tested := state.lifecycle.test state.references.phase.free active
  { state with
    lifecycle := { tested.1 with consumers := tested.1.consumers.releaseAll tested.2 }
    references := { state.references with recent := state.references.recent.retireAll tested.2 } }

/-- Every temporal reference other than the stored recent frames, including live
activation potential, is retained exactly; the stored frames lose exactly the replaced
units' slots. This is a schedule-preservation claim, not a claim that all cached
numbers were recomputed. -/
theorem FeatureRuntime.retire_references {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    (state.retire active).references =
        { state.references with recent := (state.references.recent.retireAll
          (state.lifecycle.test state.references.phase.free active).2) } := rfl

/-- After a test no stored recent frame lists the slot of a replaced unit, so no
planning backup at a stored frame writes a replacement unit's weight. -/
theorem FeatureRuntime.retire_recent {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) (unit : Fin config.units.count)
    (replaced : unit ∈ (state.lifecycle.test state.references.phase.free active).2)
    (position : Fin Acorn.FeatureConstants.optionMaxDuration) :
    unitFeature dimension config unit ∉
      ((state.retire active).references.recent.frames[position.val]).indices :=
  RecentFeatures.retireAll_absent _ _ unit replaced position

/-- After a test no held assignment names a replaced unit. -/
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

/-- Release happens only at a free boundary: with a live option or committed
exploration, the test replaces only units no slot holds, and no objective, learner or
meta-controller row is released. -/
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

/-- A materialized input is indexed by this receiver's current bank and observation. -/
def FeatureRuntime.encodeCurrent {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    EncodingFrame dimension state.lifecycle.representation.bank words patch :=
  EncodingFrame.compute dimension state.lifecycle.representation.bank words patch

/-- The ranking is installed only at a free boundary. Active options and committed
exploration keep every objective. There is no detached closing owner at this
end-of-step boundary; the separate free-dispatch interface carries that owner while
terminal credit is still outstanding. -/
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

/-- Occupancy prevents every refresh mutation. -/
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

/-- Current-bank correspondence is attached to the actual materialized encoder result. -/
theorem FeatureRuntime.encodeCurrent_fresh {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape actions config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    (state.encodeCurrent words patch).active = encode dimension state.lifecycle.representation.bank words patch := rfl

end Acorn.Features
