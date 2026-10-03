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
refresh and persistence, and the D7 tester schedule every profile uses. Their
control/exploration dynamics have separate owners. Historical profiles retain
their explicit choices and are refused by the resumable feature-image boundary.
-/
namespace Acorn.Handcrafted
open Features

/-- D7: the declared generate-and-test schedule. Replacement rate ρ = 10⁻⁴,
maturity threshold m = 1000 steps and utility decay η = 0.99, the example
settings of continual backpropagation with Adam (Dohare, Hernandez-Garcia,
Rahman, Mahmood & Sutton, *Maintaining Plasticity in Deep Continual Learning*,
arXiv:2306.13812v3 (2024), Algorithm 3, p. 44; ρ and η also in Algorithm 1,
p. 23). The rate accrues per eligible unit, as in the authors' released
implementation. The decay word is the binary32 word nearest 0.99 and the
complement the word nearest 0.01. -/
def declaredTester : Features.Tester where
  period := 10000
  positive := by decide
  bounded := by decide
  maturity := 1000
  decay := ⟨0x3f7d70a4⟩
  complement := ⟨0x3c23d70a⟩

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
  /-- Every consumer uses the declared D6 rate. -/
  | declared
  /-- Each learner supplies its own PAR-10 derived rate. -/
  | perLearner
  /-- Share the primitive controller's PAR-10 derived rate. -/
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

/-- Only the full learned profile with the declared, clock-free rate has a
resumable current image. The image stores no rate. -/
def FeatureProfile.checkpointSupported (profile : FeatureProfile) : Bool :=
  profile.mode == .final && profile.credit == .perStep &&
    profile.rate == .declared && profile.subtasks == .learned

/-- Profile refusal is derived from all four discriminants. -/
theorem FeatureProfile.checkpoint_iff (profile : FeatureProfile) :
    profile.checkpointSupported = true ↔ profile.mode = .final ∧ profile.credit = .perStep ∧
      profile.rate = .declared ∧ profile.subtasks = .learned := by
  simp [FeatureProfile.checkpointSupported, and_assoc]

/-- Initial objective identities preserve the declared current construction order. -/
def FeatureProfile.interests (profile : FeatureProfile) (config : Features.Config) :
    Vector (Interest config) Acorn.FeatureConstants.skillCount :=
  Vector.ofFn fun slot => match profile.subtasks with
    | .learned => .learned .neutral
    | .spatial => .declared .spatialPotentials slot

/-- The ranking assigns the subtasks exactly when they are learned; declared subtasks
keep their declaration. Assignment happens at a free dispatch, which
`TemporalControl.selectWithOperations` reaches only after its primitive-only branch has
returned. A primitive-only profile draws no meta decision
(`TemporalControl.primitive_undrawn`). -/
def FeatureProfile.ranksSubtasks (profile : FeatureProfile) : Bool := profile.subtasks == .learned

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
