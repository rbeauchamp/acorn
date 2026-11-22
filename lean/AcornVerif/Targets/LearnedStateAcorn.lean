/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission
import AcornVerif.Kernel
import AcornVerif.Targets.LearnedState

namespace AcornVerif.LearnedState.Acorn
open _root_.Acorn _root_.Acorn.Handcrafted _root_.Acorn.Features

structure Configuration where
  criterion : Criterion
  /-- The planning selection. -/
  planning : PlanningSelection
  /-- The order of the two parts of a step. -/
  order : StepOrder

def Configuration.selection (configuration : Configuration) : Host.AgentSelection :=
  ⟨.primitive, configuration.criterion⟩

/-- The standard construction of a configuration at a seed. -/
def Configuration.construction (configuration : Configuration) (seed : UInt64) :
    AgentConstruction :=
  AgentConstruction.standard seed configuration.selection configuration.planning
    configuration.order

structure Shown where
  /-- The action of the step's decision. -/
  action : Kernel.Act Grid.interface
  /-- The prediction words the agent stored at the step, in the order of its questions. -/
  predictions : List Binary32

/-! ## The base agent -/

namespace Base

/-- The state of the base agent of a construction. -/
abbrev State (construction : AgentConstruction) : Type :=
  Handcrafted.Agent Grid.interface construction.profile construction.config
    construction.criterion construction.dimension construction.planning

/-- The cold construction of the base agent. -/
def cold (construction : AgentConstruction) : State construction :=
  Handcrafted.Agent.initial _ _ _ _ _ _

/-- The step of the base agent: the whole step of the construction's step order, which is its
first part and then its second part on what the first returned. -/
def step {construction : AgentConstruction} (state : State construction)
    (percept : Percept Grid.interface) :
    State construction × TemporalDecision Grid.interface.actions :=
  state.actOrdered construction.order percept

/-- The prediction words the base agent stored. -/
def predictions {construction : AgentConstruction} (state : State construction) : List Binary32 :=
  state.control.runtime.references.demonPredictions.words

/-- A state with its demon bank overwritten. -/
def putDemons {construction : AgentConstruction} (state : State construction)
    (demons : DemonBank construction.dimension Grid.interface.layout) : State construction :=
  { control := { state.control with runtime := { state.control.runtime with
      lifecycle := { state.control.runtime.lifecycle with
        consumers := { state.control.runtime.lifecycle.consumers with demons := demons } } } }
    aligned := state.aligned
    episodes := state.episodes }

/-- A state with its primitive controller and its meta controller overwritten. -/
def putControllers {construction : AgentConstruction} (state : State construction)
    (primitive : Controller (construction.criterion.config .control) construction.dimension
      Grid.interface.actions.word.toNat)
    (chooser : Controller (construction.criterion.config .control) construction.dimension
      Acorn.FeatureConstants.metaActionCount) : State construction :=
  { control := { state.control with runtime := { state.control.runtime with
      lifecycle := { state.control.runtime.lifecycle with
        consumers := { state.control.runtime.lifecycle.consumers with
          control := primitive, metaController := chooser } } } }
    aligned := state.aligned
    episodes := state.episodes }

end Base

/-- The base agent, from its cold construction at each seed. Its state carries the seed, since
the type of an agent's state depends on it. -/
def base (configuration : Configuration) :
    Agent UInt64 (Percept Grid.interface) (Emitted Shown) where
  State := Σ seed : UInt64, Base.State (configuration.construction seed)
  cold seed := ⟨seed, Base.cold (configuration.construction seed)⟩
  step state percept :=
    (⟨⟨(Base.step state.2 percept).2.action, Base.predictions (Base.step state.2 percept).1⟩,
        (Base.step state.2 percept).2.explored⟩,
      ⟨state.1, (Base.step state.2 percept).1⟩)

/-- A percept with a mechanism's words appended to its frame's words. Words that would overfill
the frame, or that use a prediction feedback channel, are not appended. -/
def extend (percept : Percept Grid.interface) (words : List SensorWord) :
    Percept Grid.interface :=
  if fits : (percept.frame.words ++ words).length ≤ Grid.interface.words ∧
      ∀ word ∈ percept.frame.words ++ words, Grid.interface.reserved word.channel = false then
    { percept with frame := { percept.frame with
        words := percept.frame.words ++ words, bounded := fits.1, clear := fits.2 } }
  else percept

/-- The prediction learners' store: the demon bank. -/
abbrev Demons (configuration : Configuration) : Type :=
  DemonBank (configuration.construction 0).dimension Grid.interface.layout

/-- The control learners' store: the primitive controller and the meta controller. -/
abbrev Controllers (configuration : Configuration) : Type :=
  Controller ((configuration.construction 0).criterion.config .control)
      (configuration.construction 0).dimension Grid.interface.actions.word.toNat ×
    Controller ((configuration.construction 0).criterion.config .control)
      (configuration.construction 0).dimension Acorn.FeatureConstants.metaActionCount

/-- The setting of a configuration. -/
def setting (configuration : Configuration) : Setting where
  Seed := UInt64
  seeded := ⟨0⟩
  Percept := Percept Grid.interface
  Action := Kernel.Act Grid.interface
  Shown := Shown
  action := Shown.action
  base := base configuration
  Extra := List SensorWord
  extend := extend
  Predictor := Demons configuration
  Controller := Controllers configuration
  predictor state := state.2.control.runtime.lifecycle.consumers.demons
  controller state := (state.2.control.runtime.lifecycle.consumers.control,
    state.2.control.runtime.lifecycle.consumers.metaController)
  setPredictor state demons := ⟨state.1, Base.putDemons state.2 demons⟩
  setController state controllers :=
    ⟨state.1, Base.putControllers state.2 controllers.1 controllers.2⟩
  predictor_same _ := rfl
  controller_same _ := rfl

/-- A world of the interaction kernel over the grid interface, from a start state, as a world
of the frame. -/
def ofKernel (world : Kernel.World Grid.interface) (start : world.State) :
    World (Percept Grid.interface) (Kernel.Act Grid.interface) where
  State := world.State
  start := start
  step := world.step
  percept := world.percept

/-- **A complete result on Acorn's agent**: the seven necessary conditions, at Acorn's
setting. -/
def Complete (configuration : Configuration) (mechanism : Mechanism (setting configuration))
    (task : Task (setting configuration)) : Prop :=
  Result (setting configuration) mechanism task

end AcornVerif.LearnedState.Acorn
