/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.FeatureRestore

/-!
# Temporal references around feature retirement and cold restore

The tester retains temporal predictions, active-option potential, occupancy,
planner state and the pending meta gap in the current schedule. These are not
claimed to be fresh encodings of the replacement bank. A unit held as an option
objective is replaced only at a free boundary, where every slot holding it is
released and a refresh becomes pending; a live option therefore never loses its
objective.
New encoding frames are constructed against the current bank. Cold restore instead
clears process state.
Activation, exploration and decision payloads are parametric because this slice
does not interpret their later control/option algorithms.
-/
namespace Acorn.Features

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
structure TemporalReferences (discounts : List Discount) (activation exploration decision : Type) where
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

/-- Cold references use the process stream's declared seed salt and no pending activation. -/
def TemporalReferences.cold (config : Config) (discounts : List Discount)
    {activation exploration decision : Type} (emptyDecision : decision) :
    TemporalReferences discounts activation exploration decision :=
  ⟨PredictionCache.initial discounts, Vector.replicate _ .zero,
    Vector.replicate _ ModelCache.initial, .idle, 0, Vector.replicate _ .zero,
    0, .zero, Rng.Xoshiro256.seed (Rng.streamKey config.seed 0xA6E0000000000001), false, emptyDecision⟩

/-- End-of-step receiver, after any detached closing owner has received terminal credit. -/
structure FeatureRuntime (shape : PatchShape) (config : Config) (criterion : Criterion)
    (dimension : Dimension) (discounts : List Discount) (activation exploration decision : Type) where
  /-- Complete representation and learner storage. -/
  lifecycle : Lifecycle shape config criterion dimension discounts
  /-- Pending assignment-refresh work. -/
  refresh : Refresh
  /-- Current process-local references. -/
  references : TemporalReferences discounts activation exploration decision

/-- Release every slot holding any of the given units. -/
def Ensemble.releaseAll {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (units : List (Fin config.units.count)) : Ensemble config criterion dimension discounts :=
  units.foldl Ensemble.release ensemble

/-- A slot that does not hold a unit still does not after any release. -/
theorem Ensemble.release_keeps {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
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
    ∀ (ensemble : Ensemble config criterion dimension discounts) (unit : Fin config.units.count),
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
          ∀ (current : Ensemble config criterion dimension discounts),
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
    ∀ (ensemble : Ensemble config criterion dimension discounts),
      (∀ unit ∈ units, ensemble.holds unit = false) → ensemble.releaseAll units = ensemble := by
  induction units with
  | nil => intro _ _; rfl
  | cons head rest ih =>
    intro ensemble unheld
    simp only [Ensemble.releaseAll, List.foldl_cons] at ih ⊢
    rw [Ensemble.release_unheld ensemble head (unheld head (by simp))]
    exact ih ensemble (fun unit member => unheld unit (List.mem_cons_of_mem _ member))

/-- The tester step at the end of a frame. A held unit is eligible only at a free
boundary, where every slot holding a replaced unit is released and a refresh
becomes pending. -/
def FeatureRuntime.retire {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    FeatureRuntime shape config criterion dimension discounts activation exploration decision :=
  let tested := state.lifecycle.test state.references.phase.free active
  { state with
    lifecycle := { tested.1 with consumers := tested.1.consumers.releaseAll tested.2 }
    refresh := { state.refresh with
      pending := state.refresh.pending || tested.2.any tested.1.consumers.holds } }

/-- Every temporal reference, including live activation potential, and the refresh
cycle key are retained exactly. This is a schedule-preservation claim, not a claim
that all cached numbers were recomputed. -/
theorem FeatureRuntime.retire_references {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    (state.retire active).references = state.references ∧
      (state.retire active).refresh.cycle = state.refresh.cycle := ⟨rfl, rfl⟩

/-- After a test no held assignment names a replaced unit, and releasing a slot
leaves a refresh pending. -/
theorem FeatureRuntime.retire_releases {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) :
    let tested := state.lifecycle.test state.references.phase.free active
    (∀ unit ∈ tested.2, ∀ slot : Fin Acorn.FeatureConstants.skillCount,
      (state.retire active).lifecycle.consumers.skills[slot.val].interest.held.holds unit = false) ∧
      ((tested.2.any tested.1.consumers.holds) = true →
        (state.retire active).refresh.pending = true) :=
  ⟨fun unit member slot => Ensemble.releaseAll_holds
      (state.lifecycle.test state.references.phase.free active).2
      (state.lifecycle.test state.references.phase.free active).1.consumers unit member slot,
    fun released => by simp [FeatureRuntime.retire, released]⟩

/-- Release happens only at a free boundary: with a live option or committed
exploration, the test replaces only units no slot holds, and no objective, learner,
meta-controller row or refresh request is released. -/
theorem FeatureRuntime.retire_occupied {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (active : Vector Bool config.units.count) (occupied : state.references.phase.free = false) :
    state.retire active = { state with lifecycle := (state.lifecycle.test false active).1 } := by
  have unheld := state.lifecycle.test_unheld active
  have holds := state.lifecycle.test_holds false active
  have kept : ∀ unit ∈ (state.lifecycle.test false active).2,
      (state.lifecycle.test false active).1.consumers.holds unit = false := by
    intro unit member
    rw [holds]
    exact unheld unit member
  have none : ((state.lifecycle.test false active).2.any
      (state.lifecycle.test false active).1.consumers.holds) = false := by
    simpa using kept
  unfold FeatureRuntime.retire
  simp only [occupied, none, Bool.or_false,
    Ensemble.releaseAll_unheld _ _ kept] <;> rfl

/-- Cold installation resets every current process-local reference family. -/
def FeatureRuntime.restore {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (image : FeatureImage config criterion dimension discounts) (emptyDecision : decision) :
    FeatureRuntime shape config criterion dimension discounts activation exploration decision :=
  ⟨⟨Representation.restore shape image.progress,
      state.lifecycle.consumers.restore image.primary image.assignments⟩,
    Refresh.cold image.pending, TemporalReferences.cold config discounts emptyDecision⟩

/-- A materialized input is indexed by this receiver's current bank and observation. -/
def FeatureRuntime.encodeCurrent {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    EncodingFrame dimension state.lifecycle.representation.bank words patch :=
  EncodingFrame.compute dimension state.lifecycle.representation.bank words patch

/-- Pending ranking work executes only at a free boundary. Active options and
committed exploration retain the request. There is no detached closing owner at
this end-of-step boundary; the separate free-dispatch interface carries that owner
while terminal credit is still outstanding. -/
def FeatureRuntime.refreshAtFree {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension (.g99 :: discounts) activation exploration decision) :
    FeatureRuntime shape config criterion dimension (.g99 :: discounts) activation exploration decision :=
  match state.references.phase with
  | .idle =>
    let free : FreeDispatch shape config criterion dimension discounts Unit :=
      ⟨state.lifecycle, state.refresh, state.references.modelPredictions, none⟩
    let refreshed := free.refreshRanked
    { state with
      lifecycle := refreshed.lifecycle
      refresh := refreshed.refresh
      references := { state.references with modelPredictions := refreshed.predictions } }
  | .option _ _ | .exploring _ => state

/-- Occupancy prevents both refresh mutation and request acknowledgement. -/
theorem FeatureRuntime.occupied_preserves {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension (.g99 :: discounts) activation exploration decision)
    (occupied : state.references.phase ≠ .idle) : state.refreshAtFree = state := by
  unfold FeatureRuntime.refreshAtFree
  split
  · contradiction
  · rfl
  · rfl

/-- Current-bank correspondence is attached to the actual materialized encoder result. -/
theorem FeatureRuntime.encodeCurrent_fresh {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (words : List SensorWord) (patch : Patch shape) :
    (state.encodeCurrent words patch).active = encode dimension state.lifecycle.representation.bank words patch := rfl

end Acorn.Features
