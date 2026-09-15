/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.FeatureRefresh

/-!
# Feature-slice checkpoint admission and cold installation

The byte decoder supplies dimension-sized raw knowledge blocks. Feature metadata,
events and assignments are admitted together before installation. Primary
knowledge passes through each receiver's own projection; optional model storage
and process-local caches restart cold. Saved assignments are never reranked.
Complete file-format and full-agent persistence remain their separate owners.
-/
namespace Acorn.Features

/-- Exact-sized untrusted primary knowledge for one receiving learner. -/
structure KnowledgeImage (dimension : Dimension) where
  /-- Raw weight words, including exceptional inputs accepted by projection. -/
  weights : Vector Binary32 dimension.capacity
  /-- Raw log step-size words. -/
  beta : Vector Binary32 dimension.capacity

/-- Install through the actual learner's projection and transient-clear boundary. -/
def Managed.restore {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (image : KnowledgeImage dimension) : Managed config dimension :=
  learner.apply (.install image.weights.toList image.beta.toList) trivial

/-- Every primary action learner is restored; wrapper transients are cold. -/
def Controller.restore {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) (images : Vector (KnowledgeImage dimension) actions) :
    Controller config dimension actions :=
  ⟨Vector.ofFn (fun i => controller.learners[i.val].restore images[i.val]), .zero, .zero, false⟩

/-- Raw demon blocks have exactly the receiving horizon layout. -/
inductive DemonImages (dimension : Dimension) : List Discount → Type where
  /-- No remaining channel. -/
  | nil : DemonImages dimension []
  /-- One raw block and all remaining channels. -/
  | cons {discount : Discount} {rest : List Discount}
      (image : KnowledgeImage dimension) (tail : DemonImages dimension rest) :
      DemonImages dimension (discount :: rest)

/-- Restore every demon under its own immutable configuration. -/
def DemonBank.restore {dimension : Dimension} {discounts : List Discount}
    (bank : DemonBank dimension discounts) (images : DemonImages dimension discounts) :
    DemonBank dimension discounts :=
  match bank, images with
  | .nil, .nil => .nil
  | .cons learner tail, .cons image rest => .cons (learner.restore image) (tail.restore rest)

/-- Complete primary checkpoint shape; model learners are deliberately cold-only. -/
structure PrimaryImage (dimension : Dimension) (discounts : List Discount) where
  /-- Primitive-action blocks. -/
  control : Vector (KnowledgeImage dimension) Acorn.FeatureConstants.primitiveCount
  /-- Meta-action blocks. -/
  metaController : Vector (KnowledgeImage dimension) Acorn.FeatureConstants.metaActionCount
  /-- Every option-policy action block. -/
  skills : Vector (Vector (KnowledgeImage dimension) Acorn.FeatureConstants.primitiveCount)
    Acorn.FeatureConstants.skillCount
  /-- Every prediction-channel block. -/
  demons : DemonImages dimension discounts

/-- Restore the complete receiving primary state, install saved target identities,
and reset every model under its criterion-specific storage shape. -/
def Ensemble.restore {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble config criterion dimension discounts)
    (image : PrimaryImage dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    Ensemble config criterion dimension discounts :=
  ⟨ensemble.control.restore image.control, ensemble.metaController.restore image.metaController,
    Vector.ofFn (fun i => ⟨.learned assignments[i.val],
      ensemble.skills[i.val].policy.restore image.skills[i.val], Model.initial dimension criterion⟩),
    ensemble.demons.restore image.demons⟩

/-- Feature metadata received from the file decoder, before any mutation. -/
structure RawFeatureImage (dimension : Dimension) (discounts : List Discount) where
  /-- Stored feature salt. -/
  seed : UInt64
  /-- Stored sensory tiling count. -/
  tilings : UInt64
  /-- Stored bank capacity. -/
  units : UInt16
  /-- Stored feature-space capacity. -/
  capacity : UInt32
  /-- Stored criterion tag: zero discounted, one differential. -/
  criterion : UInt8
  /-- Stored saturating clock. -/
  clock : UInt64
  /-- Raw replacement sequence. -/
  events : List (UInt64 × UInt16)
  /-- Complete raw assignment image. -/
  assignments : Vector AssignmentWords Acorn.FeatureConstants.skillCount
  /-- Complete primary words. -/
  primary : PrimaryImage dimension discounts
  /-- Durable pending refresh. -/
  pending : Bool

/-- Criterion tags are exhaustive over the current immutable domain. -/
def Criterion.tag : Criterion → UInt8
  | .discounted => 0
  | .differential => 1

/-- Fully admitted feature image; no installation path accepts raw event/identity words. -/
structure FeatureImage (config : Config) (criterion : Criterion) (dimension : Dimension) (discounts : List Discount) where
  /-- Legal receiver-relative progress. -/
  progress : Progress config
  /-- Exact saved objectives. -/
  assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount
  /-- Primary values admitted by each receiving learner during installation. -/
  primary : PrimaryImage dimension discounts
  /-- Saved work request. -/
  pending : Bool

/-- Metadata and every feature identity are checked before an image exists.
The caller separately admits the full file's supported research profile. -/
def FeatureImage.admit (config : Config) (criterion : Criterion) (dimension : Dimension)
    {discounts : List Discount} (raw : RawFeatureImage dimension discounts) :
    Option (FeatureImage config criterion dimension discounts) := do
  if raw.seed != config.seed || raw.tilings != config.tilings ||
      raw.units.toNat != config.units.count || raw.capacity.toNat != dimension.capacity ||
      raw.criterion != criterion.tag then none else do
    let progress ← Progress.admit config raw.clock raw.events
    let assignments ← raw.assignments.mapM (Assignment.admit dimension config)
    some ⟨progress, assignments, raw.primary, raw.pending⟩

/-- Cold installation reconstructs the bank and clears all lifecycle-owned transient state.
No ranking function participates, so a saved bonus keeps its original identity. -/
def FreeDispatch.restore {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (image : FeatureImage config criterion dimension (.g99 :: discounts)) :
    FreeDispatch shape config criterion dimension discounts payload :=
  ⟨⟨Representation.restore shape image.progress,
      state.lifecycle.consumers.restore image.primary image.assignments⟩,
    Refresh.cold image.pending, Vector.replicate _ ModelCache.initial, none⟩

/-- Saved assignments are installed exactly, irrespective of present restored weights. -/
theorem Ensemble.restore_assignment {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble config criterion dimension discounts) (image : PrimaryImage dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (ensemble.restore image assignments).skills[slot.val].interest = .learned assignments[slot.val] := by
  simp [Ensemble.restore]

/-- Cold restore preserves pending work, resets the cycle and detaches all pending credit. -/
theorem FreeDispatch.restore_cold {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape config criterion dimension discounts payload)
    (image : FeatureImage config criterion dimension (.g99 :: discounts)) :
    (state.restore image).refresh.pending = image.pending ∧
    (state.restore image).refresh.cycle = 0 ∧ (state.restore image).closing = none ∧
    (state.restore image).predictions = Vector.replicate _ ModelCache.initial := ⟨rfl, rfl, rfl, rfl⟩

end Acorn.Features
