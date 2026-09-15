/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConsumers

/-!
# One-way learner diagnostics

Every diagnostic reads the current managed learner. Shapes follow the same
controller, skill and horizon indices as storage. These observations do not
recompute predictions, update eligibility or feed action selection.
-/
namespace Acorn.Host
open Features

/-- Current numeric observations of one physically stored learner. -/
structure LearnerDiagnostic where
  /-- Mean step size of the currently adapted coordinates. -/
  activeAlpha : Binary32
  /-- Current eligibility cardinality, without machine-integer truncation. -/
  eligible : Nat

/-- Read the actual scheduled learner's existing diagnostic owners. -/
def learnerDiagnostic {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) : LearnerDiagnostic :=
  ⟨learner.state.activeAlpha, learner.state.eligibleCount⟩

/-- Canonical absent model component in the telemetry contract. -/
def LearnerDiagnostic.absent : LearnerDiagnostic := ⟨.zero, 0⟩

/-- Model telemetry is reward, continuation, duration; an absent duration is zero.
The reset-reader traversal has different aliasing semantics and is not used here. -/
def modelDiagnostics {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : Vector LearnerDiagnostic 3 :=
  match model with
  | .discounted reward continuation =>
    #v[learnerDiagnostic reward, learnerDiagnostic continuation, .absent]
  | .differential reward continuation duration =>
    #v[learnerDiagnostic reward, learnerDiagnostic continuation, learnerDiagnostic duration]

/-- Discounted models have no duration learner, for every admitted model state. -/
theorem modelDiagnostics_discounted_duration {dimension : Dimension}
    (model : Model dimension .discounted) :
    (modelDiagnostics model).get 2 = LearnerDiagnostic.absent := by
  cases model
  rfl

/-- Horizon-indexed traversal preserves each actual demon learner's position. -/
def demonDiagnostics {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) : Vector LearnerDiagnostic discounts.length :=
  match demons with
  | .nil => #v[]
  | .cons learner rest =>
    (#v[learnerDiagnostic learner] ++ demonDiagnostics rest).cast (by simp [Nat.add_comm])

/-- All observer shapes derive from the composition's storage dimensions. -/
structure EnsembleDiagnostics (discounts : List Discount) where
  /-- Primitive-action learners in action order. -/
  control : Vector LearnerDiagnostic Acorn.FeatureConstants.primitiveCount
  /-- Meta-action learners in action order. -/
  metaController : Vector LearnerDiagnostic Acorn.FeatureConstants.metaActionCount
  /-- Skill-major option-action learners. -/
  options : Vector (Vector LearnerDiagnostic Acorn.FeatureConstants.primitiveCount)
    Acorn.FeatureConstants.skillCount
  /-- Skill-major reward, continuation and duration learners. -/
  models : Vector (Vector LearnerDiagnostic 3) Acorn.FeatureConstants.skillCount
  /-- Prediction learners in the declared horizon layout. -/
  demons : Vector LearnerDiagnostic discounts.length

/-- Read every family directly from its immutable owner. -/
def ensembleDiagnostics {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Ensemble config criterion dimension discounts) : EnsembleDiagnostics discounts :=
  ⟨state.control.learners.map learnerDiagnostic,
    state.metaController.learners.map learnerDiagnostic,
    state.skills.map (fun skill => skill.policy.learners.map learnerDiagnostic),
    state.skills.map (fun skill => modelDiagnostics skill.model), demonDiagnostics state.demons⟩

end Acorn.Host
