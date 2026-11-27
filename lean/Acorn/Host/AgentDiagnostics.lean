import Acorn.Handcrafted.GridWorld

namespace Acorn.Host
open Features

structure LearnerDiagnostic where
  activeAlpha : Binary32
  eligible : Nat

def learnerDiagnostic {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) : LearnerDiagnostic :=
  ⟨learner.state.activeAlpha, learner.state.eligibleCount⟩

def LearnerDiagnostic.absent : LearnerDiagnostic := ⟨.zero, 0⟩

def modelDiagnostics {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : Vector LearnerDiagnostic 3 :=
  match model with
  | .discounted reward continuation _ =>
    #v[learnerDiagnostic reward, learnerDiagnostic continuation, .absent]
  | .differential reward continuation duration _ =>
    #v[learnerDiagnostic reward, learnerDiagnostic continuation, learnerDiagnostic duration]

theorem modelDiagnostics_discounted_duration {dimension : Dimension}
    (model : Model dimension .discounted) :
    (modelDiagnostics model).get 2 = LearnerDiagnostic.absent := by
  cases model
  rfl

def demonDiagnostics {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) : Vector LearnerDiagnostic discounts.length :=
  match demons with
  | .nil => #v[]
  | .cons learner rest =>
    (#v[learnerDiagnostic learner] ++ demonDiagnostics rest).cast (by simp [Nat.add_comm])

structure EnsembleDiagnostics (discounts : List Discount) where
  control : Vector LearnerDiagnostic Acorn.FeatureConstants.primitiveCount
  metaController : Vector LearnerDiagnostic Acorn.FeatureConstants.metaActionCount
  options : Vector (Vector LearnerDiagnostic Acorn.FeatureConstants.primitiveCount)
    Acorn.FeatureConstants.skillCount
  models : Vector (Vector LearnerDiagnostic 3) Acorn.FeatureConstants.skillCount
  demons : Vector LearnerDiagnostic discounts.length

def ensembleDiagnostics {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (state : Ensemble Handcrafted.Grid.actions config criterion dimension discounts) :
    EnsembleDiagnostics discounts :=
  ⟨state.control.learners.map learnerDiagnostic,
    state.metaController.learners.map learnerDiagnostic,
    state.skills.map (fun skill => skill.policy.learners.map learnerDiagnostic),
    state.skills.map (fun skill => modelDiagnostics skill.model), demonDiagnostics state.demons⟩

end Acorn.Host
