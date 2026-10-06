/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Provenance
import AcornVerif.Kernel

/-!
# The OaK picture as a signature

Oak Lab's mission page (https://oaklab.ai/mission.html, figure `assets/Oak.svg`, read on
2026-10-06) draws the OaK architecture as five boxes and seven edges:

* experience, joined to state features;
* state features define subproblems to attain features;
* subproblems define options and values that solve (sub)problems;
* options and values define models of options;
* planning runs from models of options to options and values;
* options and values use features, and models use features.

`Oak` states the picture as a type over the executing interface of `Acorn.Interface`. A
box is a carrier and an edge is a function, an arrow, whose arguments are what the
picture lets it read. `plan` takes models, options and values and a feature vector, and
no percept, reward or extra arrow is among its arguments. An arrow reads its own box as
well, because each box is state that persists.

The signature does not bound what a feature vector carries. `perceive` reads the whole
percept, and the carrier `Feature` is any type, so an instance can pass any part of a
percept on as a feature. What the signature guarantees is `Oak.step_congr`: a step reads
a percept through what `perceive` returns for it, its reward and its extra arrows. That
the features are features is a claim of the instance.

The picture draws options and values as one box, and its edge to the models leaves that
box, so the signature has one carrier for both, `Solution`. Three things an agent needs
are not drawn, and the signature states how it reads each.

* The reward of a transition is part of experience and is no feature. The two arrows that
  learn from a transition, `solve` and `model`, take it as an argument.
* An agent acts. `act` reads the options and values and a feature vector.
* The construction of state features keeps state from percept to percept. That state is
  the carrier `Perception`, which `perceive` alone reads and writes.

An `Oak.Extra` is an arrow outside the picture: a value that `solve` reads from each
percept beside the features and the reward. An extra arrow holds a `Acorn.Provenance`
declaration for its carrier and names a registered departure, and `registered` states
that the two agree, so no extra arrow exists without a departure. The declaration is not
checked against what the arrow reads: as for every `Provenance` declaration, review
checks it against the producing code. No other arrow takes an extra.

`Oak.toAgent` composes the arrows into an agent of `AcornVerif.Kernel`, each arrow once
per percept: perceive, pose, solve, model, plan, act. `Oak.step_congr` shows that such
an agent reads a percept through its features, its reward and its extra arrows only.

`Oak.Conforms` is the form of a conformance statement: under a map of memories, an
agent takes the action of the composed arrows on every percept and keeps the image of
its memory. `Oak.Conforms.actions` shows that a conforming agent and the composed
arrows take the same actions in every world from every start state. Every agent
conforms to the instance whose perception holds its whole memory
(`Oak.conforms_coarse`), so a conformance statement is as strong as the carriers and
arrows of its instance and no stronger. `Oak.Realizes` is
the same statement for one arrow and one operation of an agent, through an `Oak.View`
of the agent's memory: the operation reads the memory through one function, applies the
arrow, and writes the arrow's value into the view. `Oak.Realizes.restores` shows that
such an operation changes nothing outside the view, and `Oak.Realizes.reads` that it
reads nothing but the arrow's input.

This module defines the picture and proves nothing of the executed agent.
`AcornVerif.CurrentOak` states which arrows the executed definitions realize. The order
of `Oak.toAgent` is one reading of the picture as a step: learn from the transition,
plan, then act. The executed step is not in that order. At a free boundary it plans
first, then draws an action, and credits the transition into the frame after the draw;
under the discounted criterion it also credits an ending option before it plans. So the
executed agent is not shown to conform to an instance with separate arrows.
-/

namespace AcornVerif
open Acorn Acorn.Features AcornVerif.Kernel

variable {interface : Interface}

/-! ## Arrows outside the picture -/

/-- An arrow outside the picture: a value that the options and values read from each
percept beside its features and its reward. It holds a provenance declaration for its
carrier and names a registered departure, and the two agree. Nothing here checks the
declaration against the value the arrow reads. -/
structure Oak.Extra (interface : Interface) where
  /-- What the arrow carries. -/
  Carrier : Type
  /-- The declared origin of the carrier. -/
  [provenance : Provenance Carrier]
  /-- The registered departure the arrow belongs to. -/
  departure : Departure
  /-- The carrier's declared origin is that departure. -/
  registered : Provenance.origin (α := Carrier) = some departure
  /-- The value the arrow reads from a percept. -/
  read : Percept interface → Carrier

/-- The values of a list of extra arrows, one for each arrow in order. -/
def Oak.Extra.Values : List (Oak.Extra interface) → Type
  | [] => Unit
  | extra :: rest => extra.Carrier × Oak.Extra.Values rest

/-- The value of every extra arrow of a list at one percept. -/
def Oak.Extra.readAll :
    (extras : List (Oak.Extra interface)) → Percept interface → Oak.Extra.Values extras
  | [], _ => ()
  | extra :: rest, percept => (extra.read percept, Oak.Extra.readAll rest percept)

/-! ## The signature -/

/-- The OaK picture over an interface: a carrier for each box and an arrow for each
edge, with the arrows outside the picture listed. -/
structure Oak (interface : Interface) where
  /-- What the construction of state features keeps between percepts. -/
  Perception : Type
  /-- The state features of one percept. -/
  Feature : Type
  /-- The subproblems posed. -/
  Subproblem : Type
  /-- The options and values that solve the subproblems and the main problem. -/
  Solution : Type
  /-- The models of the options. -/
  Model : Type
  /-- The arrows outside the picture, each with its registered departure. -/
  extras : List (Oak.Extra interface)
  /-- Experience produces state features. -/
  perceive : Perception → Percept interface → Perception × Feature
  /-- State features define subproblems to attain features. -/
  pose : Feature → Subproblem → Subproblem
  /-- Subproblems define options and values, which use features. They learn from the
  reward of the transition and read the extra arrows. -/
  solve : Subproblem → Solution → Feature → Binary32 → Oak.Extra.Values extras → Solution
  /-- Options and values define models of options, which use features. They learn from
  the reward of the transition. -/
  model : Solution → Model → Feature → Binary32 → Model
  /-- Planning runs from models of options to options and values, at a feature vector.
  No percept, reward or extra arrow is among its arguments. -/
  plan : Model → Solution → Feature → Solution
  /-- Options and values use features to choose an action. -/
  act : Solution → Feature → Act interface

/-- Everything an agent of the picture retains between percepts: one value for each box
that persists. -/
structure Oak.Memory (oak : Oak interface) where
  /-- The state of the feature construction. -/
  perception : oak.Perception
  /-- The subproblems posed. -/
  subproblems : oak.Subproblem
  /-- The options and values. -/
  solutions : oak.Solution
  /-- The models of the options. -/
  models : oak.Model

/-- One step of the picture: perceive, pose, solve, model, plan, then act on the planned
options and values. -/
def Oak.step (oak : Oak interface) (memory : oak.Memory) (percept : Percept interface) :
    Act interface × oak.Memory :=
  let perceived := oak.perceive memory.perception percept
  let subproblems := oak.pose perceived.2 memory.subproblems
  let solved := oak.solve subproblems memory.solutions perceived.2 percept.reward
    (Oak.Extra.readAll oak.extras percept)
  let models := oak.model solved memory.models perceived.2 percept.reward
  let planned := oak.plan models solved perceived.2
  (oak.act planned perceived.2, ⟨perceived.1, subproblems, planned, models⟩)

/-- The arrows composed into an agent of the interface, from an initial memory. -/
def Oak.toAgent (oak : Oak interface) (initial : oak.Memory) : Agent interface where
  Memory := oak.Memory
  initial := initial
  act := oak.step

/-- A step of the picture reads a percept through its features, its reward and its
extra arrows only. -/
theorem Oak.step_congr (oak : Oak interface) (memory : oak.Memory)
    (first second : Percept interface)
    (perceived : oak.perceive memory.perception first = oak.perceive memory.perception second)
    (reward : first.reward = second.reward)
    (extras : Oak.Extra.readAll oak.extras first = Oak.Extra.readAll oak.extras second) :
    oak.step memory first = oak.step memory second := by
  simp only [Oak.step, perceived, reward, extras]

/-! ## Conformance of an agent -/

/-- The form of a conformance statement: under a map of memories, the composed arrows
take the agent's action on every percept and keep the image of the agent's next
memory. -/
def Oak.Conforms (agent : Agent interface) (oak : Oak interface) : Prop :=
  ∃ view : agent.Memory → oak.Memory, ∀ memory percept,
    oak.step (view memory) percept =
      ((agent.act memory percept).1, view (agent.act memory percept).2)

/-- Under a conformance map, the closed loop of the composed arrows holds the agent's
world state and the image of the agent's memory at every time. -/
theorem Oak.loop_view {agent : Agent interface} {oak : Oak interface}
    (view : agent.Memory → oak.Memory)
    (same : ∀ memory percept, oak.step (view memory) percept =
      ((agent.act memory percept).1, view (agent.act memory percept).2))
    (world : World interface) (start : world.State) (time : ℕ) :
    loop world (oak.toAgent (view agent.initial)) start time =
      ((loop world agent start time).1, view (loop world agent start time).2) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change interact world (oak.toAgent (view agent.initial))
      (loop world (oak.toAgent (view agent.initial)) start time) = _
    rw [ih]
    change (world.step _ (oak.step (view _) _).1, (oak.step (view _) _).2) = _
    rw [same]
    rfl

/-- A conforming agent and the composed arrows take the same actions in every world,
from every start state, at every time. -/
theorem Oak.Conforms.actions {agent : Agent interface} {oak : Oak interface}
    (conforms : Oak.Conforms agent oak) :
    ∃ initial : oak.Memory, ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world (oak.toAgent initial) start time = actionAt world agent start time := by
  obtain ⟨view, same⟩ := conforms
  refine ⟨view agent.initial, fun world start time => ?_⟩
  have held := Oak.loop_view view same world start time
  change ((oak.toAgent (view agent.initial)).act
    (loop world (oak.toAgent (view agent.initial)) start time).2
    (world.percept (loop world (oak.toAgent (view agent.initial)) start time).1)).1 = _
  rw [held]
  exact congrArg Prod.fst (same _ _)

/-- The coarsest instance of an agent: perception holds the agent's whole memory and
takes its decision, the feature of a percept is the chosen action, and no other arrow
does anything. -/
def Oak.coarse (agent : Agent interface) : Oak interface where
  Perception := agent.Memory
  Feature := Act interface
  Subproblem := Unit
  Solution := Unit
  Model := Unit
  extras := []
  perceive memory percept := ((agent.act memory percept).2, (agent.act memory percept).1)
  pose _ subproblems := subproblems
  solve _ solutions _ _ _ := solutions
  model _ models _ _ := models
  plan _ solutions _ := solutions
  act _ feature := feature

/-- Every agent conforms to its coarsest instance. So conformance to some instance is no
claim about an agent: a conformance statement says what the types of its instance's
arrows say, and no more. -/
theorem Oak.conforms_coarse (agent : Agent interface) : Oak.Conforms agent (Oak.coarse agent) :=
  ⟨fun memory => ⟨memory, (), (), ()⟩, fun _ _ => rfl⟩

/-! ## Conformance of one arrow -/

/-- A view of a memory: the part one box holds, with the way to write the part back. -/
structure Oak.View (Memory Part : Type) where
  /-- The part of a memory. -/
  get : Memory → Part
  /-- A memory with the part replaced. -/
  put : Memory → Part → Memory
  /-- Writing a memory's own part changes nothing. -/
  restore : ∀ memory, put memory (get memory) = memory
  /-- A second write replaces the first. -/
  replace : ∀ memory first second, put (put memory first) second = put memory second

/-- An operation on a memory realizes an arrow when it reads the memory through `read`,
applies the arrow, and writes the arrow's value into a view. -/
def Oak.Realizes {Memory Part Input : Type} (operation : Memory → Memory)
    (read : Memory → Input) (arrow : Input → Part) (view : Oak.View Memory Part) : Prop :=
  ∀ memory, operation memory = view.put memory (arrow (read memory))

/-- An operation that realizes an arrow changes nothing outside the arrow's view: writing
the old part back gives the old memory. -/
theorem Oak.Realizes.restores {Memory Part Input : Type} {operation : Memory → Memory}
    {read : Memory → Input} {arrow : Input → Part} {view : Oak.View Memory Part}
    (realized : Oak.Realizes operation read arrow view) (memory : Memory) :
    view.put (operation memory) (view.get memory) = memory := by
  rw [realized memory, view.replace, view.restore]

/-- An operation that realizes an arrow reads its memory through the arrow's input only:
two memories with the same input have the same part written. -/
theorem Oak.Realizes.reads {Memory Part Input : Type} {operation : Memory → Memory}
    {read : Memory → Input} {arrow : Input → Part} {view : Oak.View Memory Part}
    (realized : Oak.Realizes operation read arrow view) (first second : Memory)
    (same : read first = read second) :
    ∃ part, operation first = view.put first part ∧ operation second = view.put second part :=
  ⟨arrow (read first), realized first, by rw [realized second, same]⟩

end AcornVerif
