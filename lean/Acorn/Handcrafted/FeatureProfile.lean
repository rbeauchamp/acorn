/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.Handcrafted.Observation
import Acorn.FeatureRestore

/-!
# Declared feature-profile composition

These are the current profile discriminants inspected by feature construction,
refresh and persistence. Their control/exploration dynamics have separate
owners. Historical profiles retain their explicit choices and are refused by
the resumable feature-image boundary.
-/
namespace Acorn.Handcrafted
open Features

/-- Complete current evaluator-mode discriminants. -/
inductive EvaluationMode where
  /-- Full hierarchical learning. -/
  | final
  /-- Frozen learning, with the same declared observation interface. -/
  | frozen
  /-- Hierarchy with the reach relation omitted. -/
  | withoutReachRelation
  /-- Primitive-only learning. -/
  | primitiveOnly
  deriving DecidableEq

/-- Current primitive-credit discriminants, independent of their transient payload. -/
inductive ControlCredit where
  /-- Credit each primitive step. -/
  | perStep
  /-- Historical deferred span credit. -/
  | smdpCatchUp
  /-- Historical omission of span credit. -/
  | noSpanCredit
  deriving DecidableEq

/-- Current rate-source discriminants; schedule state belongs to the exploration owner. -/
inductive RatePolicy where
  /-- Each learner supplies its own rate. -/
  | perLearner
  /-- Share the primitive controller's derived rate. -/
  | shared
  /-- Historical declared annealing schedule. -/
  | annealed
  deriving DecidableEq

/-- Current subtask-construction alternatives. -/
inductive SubtaskPolicy where
  /-- Rank learned bank units. -/
  | learned
  /-- Use declared spatial potentials. -/
  | spatial
  deriving DecidableEq

/-- Exactly the immutable discriminants relevant to feature lifecycle behavior. -/
structure FeatureProfile where
  /-- Observation and hierarchy mode. -/
  mode : EvaluationMode
  /-- Primitive credit choice. -/
  credit : ControlCredit
  /-- Rate-source choice. -/
  rate : RatePolicy
  /-- Subtask source. -/
  subtasks : SubtaskPolicy
  deriving DecidableEq

/-- Only the relation-ablation profile changes task-word construction. -/
def FeatureProfile.taskMode (profile : FeatureProfile) : TaskFeatureMode :=
  if profile.mode == .withoutReachRelation then .withoutReachRelation else .complete

/-- Primitive-only mode has no hierarchy to refresh. -/
def FeatureProfile.usesHierarchy (profile : FeatureProfile) : Bool := profile.mode != .primitiveOnly

/-- Only full clock-free learned profiles have a resumable current image. -/
def FeatureProfile.checkpointSupported (profile : FeatureProfile) : Bool :=
  profile.mode == .final && profile.credit == .perStep &&
    profile.rate == .perLearner && profile.subtasks == .learned

/-- Profile refusal is derived from all four discriminants. -/
theorem FeatureProfile.checkpoint_iff (profile : FeatureProfile) :
    profile.checkpointSupported = true ↔ profile.mode = .final ∧ profile.credit = .perStep ∧
      profile.rate = .perLearner ∧ profile.subtasks = .learned := by
  simp [FeatureProfile.checkpointSupported, and_assoc]

/-- Initial objective identities preserve the declared current construction order. -/
def FeatureProfile.interests (profile : FeatureProfile) (config : Features.Config) :
    Vector (Interest config) Acorn.FeatureConstants.skillCount :=
  Vector.ofFn fun slot => match profile.subtasks with
    | .learned => .learned .neutral
    | .spatial => .declared .spatialPotentials slot

/-- Attempt events request ranking exactly when a learned hierarchy uses it. -/
def FeatureProfile.request (profile : FeatureProfile) (refresh : Refresh)
    (cycle : UInt64) (achieved : Bool) : Refresh :=
  if profile.subtasks == .learned && profile.usesHierarchy then refresh.request cycle achieved else refresh

/-- The full current observation adapter derives its mode from the immutable profile. -/
def FeatureProfile.encode (profile : FeatureProfile) (dimension : Dimension)
    {config : Features.Config} (bank : Bank Host.patchShape config) (observation : Host.Observation)
    (predictions : Predictions) : SwiftTd.ActiveSet dimension :=
  encodeObservation dimension bank observation predictions profile.taskMode

/-- Profile admission precedes all feature-image admission and installation. -/
def FeatureProfile.admit (profile : FeatureProfile) (config : Features.Config) (criterion : Criterion)
    (dimension : Dimension) {discounts : List Discount} (raw : RawFeatureImage dimension discounts) :
    Option (FeatureImage config criterion dimension discounts) :=
  if profile.checkpointSupported then FeatureImage.admit config criterion dimension raw else none

/-- Unsupported profiles cannot install a structurally legal image by bypassing their mode. -/
theorem FeatureProfile.unsupported_refuses (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) {discounts : List Discount}
    (raw : RawFeatureImage dimension discounts) (unsupported : profile.checkpointSupported = false) :
    profile.admit config criterion dimension raw = none := by
  simp [FeatureProfile.admit, unsupported]

end Acorn.Handcrafted
