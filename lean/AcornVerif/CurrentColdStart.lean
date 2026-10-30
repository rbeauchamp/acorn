/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.StepParts
import AcornVerif.CurrentPlanning

/-!
# What a cold-started agent reaches

`reached` is the agent after a list of percepts, from cold initialization, under one step order.
An option model's continuation and duration predictions are finite on every such state
(`reached_predictions_finite`). The fact holds of every model state
(`CurrentPlanning.model_predictions_finite`), reached or not, so it rests on no invariant of the
run: this is its instance at the executed agent's options, for every interface, profile, value
function, frame and age.
-/

namespace AcornVerif.CurrentColdStart
open Acorn Acorn.Features Acorn.Handcrafted

/-- The agent after a list of percepts, from cold initialization, under one step order. -/
def reached (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection)
    (order : StepOrder) (percepts : List (Percept interface)) :
    Agent interface profile config criterion dimension planning :=
  percepts.foldl (fun state percept => (state.actOrdered order percept).1)
    (Agent.initial interface profile config criterion dimension planning)

/-- On every state a cold-started agent reaches, each option model's continuation and duration
predictions are finite. -/
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
