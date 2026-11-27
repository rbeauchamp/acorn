import Acorn.Handcrafted.StepParts
import AcornVerif.CurrentPlanning

namespace AcornVerif.CurrentColdStart
open Acorn Acorn.Features Acorn.Handcrafted

def reached (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection)
    (order : StepOrder) (percepts : List (Percept interface)) :
    Agent interface profile config criterion dimension planning :=
  percepts.foldl (fun state percept => (state.actOrdered order percept).1)
    (Agent.initial interface profile config criterion dimension planning)

theorem reached_predictions_finite (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension)
    (planning : PlanningSelection) (order : StepOrder) (percepts : List (Percept interface))
    (slot : Fin Acorn.FeatureConstants.skillCount) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    let model := ((reached interface profile config criterion dimension planning order
      percepts).control.runtime.lifecycle.consumers.skills.get slot).model
    (model.predict value features age).continuation.Finite ∧
      (model.predict value features age).duration.value.Finite :=
  CurrentPlanning.model_predictions_finite _ value features age

end AcornVerif.CurrentColdStart
