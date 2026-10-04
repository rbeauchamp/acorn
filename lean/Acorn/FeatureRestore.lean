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
generator and tester words and assignments are admitted together before installation. Primary
knowledge passes through each receiver's own projection; optional model storage
and process-local caches restart cold. Installation never reranks saved assignments;
the next free boundary's refresh does, keeping every unit that is still ranked. An
image whose slots repeat a selected unit is refused.
Complete file-format and full-agent persistence remain their separate owners.
-/
namespace Acorn.Features

variable {actions : Word.Count}

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
structure PrimaryImage (actions : Word.Count) (dimension : Dimension) (discounts : List Discount) where
  /-- Primitive-action blocks. -/
  control : Vector (KnowledgeImage dimension) actions.word.toNat
  /-- Meta-action blocks. -/
  metaController : Vector (KnowledgeImage dimension) Acorn.FeatureConstants.metaActionCount
  /-- Every option-policy action block. -/
  skills : Vector (Vector (KnowledgeImage dimension) actions.word.toNat)
    Acorn.FeatureConstants.skillCount
  /-- Every prediction-channel block. -/
  demons : DemonImages dimension discounts

/-- Restore the complete receiving primary state, install saved target identities,
reset every model under its criterion-specific storage shape, ask every option's
questions afresh, and link no skill to a frame from before the restore. -/
def Ensemble.restore {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (image : PrimaryImage actions dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount) :
    Ensemble actions config criterion dimension discounts :=
  ⟨ensemble.control.restore image.control, ensemble.metaController.restore image.metaController,
    Vector.ofFn (fun i => ⟨.learned assignments[i.val],
      ensemble.skills[i.val].policy.restore image.skills[i.val], Model.initial dimension criterion,
      none, OptionQuestions.initial dimension discounts⟩),
    ensemble.demons.restore image.demons⟩

/-- Every restored slot starts with no stored off-policy trajectory. -/
theorem Ensemble.restore_unlinked {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount} (ensemble : Ensemble actions config criterion dimension discounts)
    (image : PrimaryImage actions dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (ensemble.restore image assignments).skills[slot.val].following = none := by
  simp [Ensemble.restore]

/-- Every restored slot asks its questions afresh: the checkpoint stores no question. -/
theorem Ensemble.restore_questions {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts)
    (image : PrimaryImage actions dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (ensemble.restore image assignments).skills[slot.val].questions =
      OptionQuestions.initial dimension discounts := by
  simp [Ensemble.restore]

/-- Feature metadata received from the file decoder, before any mutation. -/
structure RawFeatureImage (actions : Word.Count) (dimension : Dimension) (discounts : List Discount) where
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
  /-- Raw generator and tester words. -/
  progress : ProgressWords
  /-- Complete raw assignment image. -/
  assignments : Vector AssignmentWords Acorn.FeatureConstants.skillCount
  /-- Complete primary words. -/
  primary : PrimaryImage actions dimension discounts

/-- Criterion tags are exhaustive over the current immutable domain. -/
def Criterion.tag : Criterion → UInt8
  | .discounted => 0
  | .differential => 1

/-- Fully admitted feature image; no installation path accepts raw tester or identity words. -/
structure FeatureImage (actions : Word.Count) (config : Config) (criterion : Criterion) (dimension : Dimension) (discounts : List Discount) where
  /-- Legal receiver-relative generator and tester state. -/
  progress : Progress config
  /-- Exact saved objectives. -/
  assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount
  /-- No two saved slots select the same unit. -/
  distinct : Assignment.Distinct assignments
  /-- Primary values admitted by each receiving learner during installation. -/
  primary : PrimaryImage actions dimension discounts

/-- Metadata and every feature identity are checked before an image exists.
The caller separately admits the full file's supported research profile. -/
def FeatureImage.admit (config : Config) (criterion : Criterion) (dimension : Dimension)
    {discounts : List Discount} (raw : RawFeatureImage actions dimension discounts) :
    Option (FeatureImage actions config criterion dimension discounts) := do
  if raw.seed != config.seed || raw.tilings != config.tilings ||
      raw.units.toNat != config.units.count || raw.capacity.toNat != dimension.capacity ||
      raw.criterion != criterion.tag then none else do
    let progress ← Progress.admit config raw.clock raw.progress
    let assignments ← raw.assignments.mapM (Assignment.admit dimension config)
    if distinct : Assignment.distinct assignments then
      some ⟨progress, assignments, (Assignment.distinct_iff assignments).mp distinct,
        raw.primary⟩
    else none

/-- Cold installation reconstructs the bank and clears all lifecycle-owned transient state.
No ranking function participates, so a saved objective keeps its unit and held bonus. -/
def FreeDispatch.restore {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (image : FeatureImage actions config criterion dimension (.g99 :: discounts)) :
    FreeDispatch shape actions config criterion dimension discounts payload :=
  ⟨⟨Representation.restore shape image.progress,
      state.lifecycle.consumers.restore image.primary image.assignments⟩,
    Vector.replicate _ ModelCache.initial, none⟩

/-- Saved assignments are installed exactly, irrespective of present restored weights. -/
theorem Ensemble.restore_assignment {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts) (image : PrimaryImage actions dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (ensemble.restore image assignments).skills[slot.val].interest = .learned assignments[slot.val] := by
  simp [Ensemble.restore]

/-- Restoring distinct saved objectives keeps distinct held units. -/
theorem Ensemble.restore_distinct {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts) (image : PrimaryImage actions dimension discounts)
    (assignments : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (distinct : Assignment.Distinct assignments) : (ensemble.restore image assignments).Distinct := by
  apply Assignment.Distinct.mono distinct
  intro slot unit named
  simpa [Ensemble.restore, Interest.held] using named

/-- Cold restore detaches all pending credit and clears every cached model prediction. -/
theorem FreeDispatch.restore_cold {shape : PatchShape} {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {payload : Type}
    (state : FreeDispatch shape actions config criterion dimension discounts payload)
    (image : FeatureImage actions config criterion dimension (.g99 :: discounts)) :
    (state.restore image).closing = none ∧
    (state.restore image).predictions = Vector.replicate _ ModelCache.initial := ⟨rfl, rfl⟩

end Acorn.Features
