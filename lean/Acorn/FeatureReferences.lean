/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.FeatureRestore

/-!
# Temporal references around feature retirement and cold restore

Retirement retains temporal predictions, active-option potential, occupancy,
planner state and the pending meta gap in the current schedule. These are not
claimed to be fresh encodings of the replacement bank. New encoding frames are
constructed against the current bank. Cold restore instead clears process state.
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

/-- Retirement either returns the exact receiver or replaces only its owned lifecycle state. -/
def FeatureRuntime.retire {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision) :
    FeatureRuntime shape config criterion dimension discounts activation exploration decision :=
  match state.lifecycle.tryRetire with
  | none => state
  | some (_, lifecycle) => { state with lifecycle }

/-- Every temporal reference, including live activation potential, is retained exactly.
This is a schedule-preservation claim, not a claim that all cached numbers were recomputed. -/
theorem FeatureRuntime.retire_references {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision) :
    state.retire.references = state.references ∧ state.retire.refresh = state.refresh := by
  unfold FeatureRuntime.retire
  split <;> exact ⟨rfl, rfl⟩

/-- Cold installation resets every current process-local reference family. -/
def FeatureRuntime.restore {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (image : FeatureImage config criterion dimension discounts) (emptyDecision : decision) :
    FeatureRuntime shape config criterion dimension discounts activation exploration decision :=
  ⟨⟨Representation.restore shape image.progress,
      state.lifecycle.consumers.restore image.primary image.assignments⟩,
    Refresh.cold image.pending, TemporalReferences.cold config discounts emptyDecision⟩

/-- Capacity refusal leaves the entire receiver, including every cache and generator, unchanged. -/
theorem FeatureRuntime.refused_identity {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {activation exploration decision : Type}
    (state : FeatureRuntime shape config criterion dimension discounts activation exploration decision)
    (refused : state.lifecycle.tryRetire = none) : state.retire = state := by
  simp [FeatureRuntime.retire, refused]

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
