import Acorn.Host.AgentAdmission
import AcornVerif.Kernel
import AcornVerif.Targets.LearnedState

namespace AcornVerif.LearnedState.Acorn
open _root_.Acorn _root_.Acorn.Handcrafted _root_.Acorn.Features

structure Configuration where
  selection : Host.AgentSelection
  planning : PlanningSelection
  order : StepOrder

def Configuration.construction (configuration : Configuration) (seed : UInt64) :
    AgentConstruction :=
  AgentConstruction.standard seed configuration.selection configuration.planning
    configuration.order

structure Emitted where
  action : Kernel.Act Grid.interface
  predictions : List Binary32

namespace Base

abbrev State (construction : AgentConstruction) : Type :=
  Handcrafted.Agent Grid.interface construction.profile construction.config
    construction.criterion construction.dimension construction.planning

def cold (construction : AgentConstruction) : State construction :=
  Handcrafted.Agent.initial _ _ _ _ _ _

def step {construction : AgentConstruction} (state : State construction)
    (percept : Percept Grid.interface) :
    State construction × TemporalDecision Grid.interface.actions :=
  state.actOrdered construction.order percept

def predictions {construction : AgentConstruction} (state : State construction) : List Binary32 :=
  state.control.runtime.references.demonPredictions.words

def putDemons {construction : AgentConstruction} (state : State construction)
    (demons : DemonBank construction.dimension Grid.interface.layout) : State construction :=
  { control := { state.control with runtime := { state.control.runtime with
      lifecycle := { state.control.runtime.lifecycle with
        consumers := { state.control.runtime.lifecycle.consumers with demons := demons } } } }
    aligned := state.aligned
    episodes := state.episodes }

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

def base (configuration : Configuration) : Agent UInt64 (Percept Grid.interface) Emitted where
  State := Σ seed : UInt64, Base.State (configuration.construction seed)
  cold seed := ⟨seed, Base.cold (configuration.construction seed)⟩
  step state percept :=
    (⟨(Base.step state.2 percept).2.action, Base.predictions (Base.step state.2 percept).1⟩,
      ⟨state.1, (Base.step state.2 percept).1⟩)

def extend (percept : Percept Grid.interface) (words : List SensorWord) :
    Percept Grid.interface :=
  if fits : (percept.frame.words ++ words).length ≤ Grid.interface.words ∧
      ∀ word ∈ percept.frame.words ++ words, Grid.interface.reserved word.channel = false then
    { percept with frame := { percept.frame with
        words := percept.frame.words ++ words, bounded := fits.1, clear := fits.2 } }
  else percept

abbrev Demons (configuration : Configuration) : Type :=
  DemonBank (configuration.construction 0).dimension Grid.interface.layout

abbrev Controllers (configuration : Configuration) : Type :=
  Controller ((configuration.construction 0).criterion.config .control)
      (configuration.construction 0).dimension Grid.interface.actions.word.toNat ×
    Controller ((configuration.construction 0).criterion.config .control)
      (configuration.construction 0).dimension Acorn.FeatureConstants.metaActionCount

def setting (configuration : Configuration) : Setting where
  Seed := UInt64
  seeded := ⟨0⟩
  Percept := Percept Grid.interface
  Action := Kernel.Act Grid.interface
  Output := Emitted
  action := Emitted.action
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

def ofKernel (world : Kernel.World Grid.interface) (start : world.State) :
    World (Percept Grid.interface) (Kernel.Act Grid.interface) where
  State := world.State
  start := start
  step := world.step
  percept := world.percept

def Complete (configuration : Configuration) (mechanism : Mechanism (setting configuration))
    (task : Task (setting configuration)) : Prop :=
  Result (setting configuration) mechanism task

end AcornVerif.LearnedState.Acorn
