/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentGridWorld

/-!
# The two-part step in the closed loop

The executed step is two functions: `Agent.choose` selects, and `Chosen.learn`
completes the step from the value `Agent.choose` returned
(`Acorn.Handcrafted.Agent.act_parts`). A host declares when it releases the selected
action to the world: after both parts, or between them (`Acorn.StepOrder`). This
module states what that declaration changes in a closed loop.

A `TwoPart` agent is a kernel agent whose decision is given as those two functions.
`executedParts` is the executed agent in that form, and `executedParts_agent` proves it
equal to `CurrentGridWorld.executedAgent`, so both have one closed loop in every world.

The loop of the kernel has no order: its world takes one transition for each action
and waits for it. `memory_parts` restates the kernel's causality law for a two-part
agent, and `actionAt_chosen` and `memoryAt_learn` unfold the loop.

A `Moving` world also changes while the agent computes, and there the order is a
parameter. `Moving.interact` is the definition of one interaction under an order: it
places the work of the second part before the world's transition under learn-then-act
and after it under act-then-learn. `Moving.landing_learn`, `Moving.interact_landing`
and `Moving.interact_memory` unfold that definition for one interaction from one
state and memory: the action and the memory kept are the same in both orders, and the
state the action lands on is not. Over a run the two orders can therefore diverge in
every later state, percept, memory and action.

The derived statements are about the loop. `Moving.loop_memory`: under either order,
for every assignment of work, the memory before a time is the fold of the first part
followed by the second over that order's own percepts before the time, in order. So
each percept is learned exactly once and in order, in both orders, whether the world
moves or waits. `Moving.loop_waits`: when the world waits, the loop under either order
is the loop of the kernel, so the order changes no state, percept, memory or action.
`Moving.interact_commutes`: one interaction is the same in both orders when the
world's own change commutes with its transitions.

The `Moving` world is a model. No executing world implements it: the grid world waits
for the agent (`Acorn.Handcrafted.Grid.timing`, a declaration that nothing links to
`Moving.Waits`). The work of each part is an arbitrary function here, so the
statements hold for every assignment of work; none is a measurement, and no theorem
here bounds the work of the executed parts.
-/

namespace AcornVerif.Kernel
open Acorn Acorn.Features

variable {interface : Interface}

/-- An agent over an interface whose step has two parts. -/
structure TwoPart (interface : Interface) where
  /-- Everything the agent retains between percepts. -/
  Memory : Type
  /-- What the agent holds between the two parts of one step. -/
  Chosen : Type
  /-- The memory before the first percept. -/
  initial : Memory
  /-- First part: select from the memory and one percept. -/
  choose : Memory → Percept interface → Chosen
  /-- The action the first part selected. -/
  action : Chosen → Act interface
  /-- Second part: the memory kept after the percept, from the value the first part
  returned. It has no other input. -/
  learn : Chosen → Memory

/-- Both parts as one decision: the kernel agent of a two-part agent. -/
def TwoPart.agent (parts : TwoPart interface) : Agent interface where
  Memory := parts.Memory
  initial := parts.initial
  act := fun memory percept =>
    (parts.action (parts.choose memory percept), parts.learn (parts.choose memory percept))

/-- The value the first part returns at a time. -/
def chosenAt (parts : TwoPart interface) (world : World interface) (start : world.State)
    (time : ℕ) : parts.Chosen :=
  parts.choose (memoryAt world parts.agent start time) (perceptAt world parts.agent start time)

/-! ## A world that waits -/

/-- The action at a time is the action of the value the first part returned at that
time. The second part of that time's percept is no input of it. -/
theorem actionAt_chosen (parts : TwoPart interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    actionAt world parts.agent start time = parts.action (chosenAt parts world start time) :=
  rfl

/-- The memory before the next time is the second part of the value the first part
returned at this time. -/
theorem memoryAt_learn (parts : TwoPart interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    memoryAt world parts.agent start (time + 1) = parts.learn (chosenAt parts world start time) :=
  rfl

/-- The kernel's causality law for a two-part agent: the memory before a time is the
fold of the first part followed by the second over the percepts before that time, in
the order the world delivered them. `Moving.loop_memory` states it under a declared
order. -/
theorem memory_parts (parts : TwoPart interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    memoryAt world parts.agent start time =
      (List.range time).foldl
        (fun memory index =>
          parts.learn (parts.choose memory (perceptAt world parts.agent start index)))
        parts.initial :=
  memory_causal world parts.agent start time

/-! ## A world that moves while the agent computes -/

/-- A world that also changes while the agent computes. `elapse` is its change during
one unit of agent work. -/
structure Moving (interface : Interface) extends World interface where
  /-- The change of the world during one unit of agent work. -/
  elapse : State → State

/-- The world after a number of units of agent work. -/
def Moving.elapsed (world : Moving interface) : ℕ → world.State → world.State
  | 0, state => state
  | units + 1, state => world.elapsed units (world.elapse state)

/-- The world waits for the agent: agent work changes nothing. This is the
agent-synchronized discipline of `Acorn.Timing`. -/
def Moving.Waits (world : Moving interface) : Prop :=
  ∀ state, world.elapse state = state

/-- Work of each part of a step, in the units of `Moving.elapse`, for every memory,
percept and chosen value. -/
structure TwoPart.Work (parts : TwoPart interface) where
  /-- Units of work of the first part. -/
  choose : parts.Memory → Percept interface → ℕ
  /-- Units of work of the second part. -/
  learn : parts.Chosen → ℕ

/-- The world state on which the action of one interaction lands. The world moves
during the first part in both orders, and during the second part as well under
learn-then-act. -/
def Moving.landing (world : Moving interface) (parts : TwoPart interface) (work : parts.Work)
    (order : StepOrder) (pair : world.State × parts.Memory) : world.State :=
  let percept := world.percept pair.1
  let chosen := parts.choose pair.2 percept
  let reacted := world.elapsed (work.choose pair.2 percept) pair.1
  match order with
  | .learnThenAct => world.elapsed (work.learn chosen) reacted
  | .actThenLearn => reacted

/-- One interaction under a declared order. The world delivers the percept of its state
and moves during the first part. Under learn-then-act it moves during the second part
and then takes its transition on the action. Under act-then-learn it takes its
transition on the action and then moves during the second part. -/
def Moving.interact (world : Moving interface) (parts : TwoPart interface) (work : parts.Work)
    (order : StepOrder) (pair : world.State × parts.Memory) : world.State × parts.Memory :=
  let percept := world.percept pair.1
  let chosen := parts.choose pair.2 percept
  let reacted := world.elapsed (work.choose pair.2 percept) pair.1
  match order with
  | .learnThenAct =>
    (world.step (world.elapsed (work.learn chosen) reacted) (parts.action chosen),
      parts.learn chosen)
  | .actThenLearn =>
    (world.elapsed (work.learn chosen) (world.step reacted (parts.action chosen)),
      parts.learn chosen)

/-- The closed loop of a moving world and a two-part agent under a declared order, as
the world state and the agent's memory before each interaction. -/
def Moving.loop (world : Moving interface) (parts : TwoPart interface) (work : parts.Work)
    (order : StepOrder) (start : world.State) : ℕ → world.State × parts.Memory
  | 0 => (start, parts.initial)
  | time + 1 => world.interact parts work order (world.loop parts work order start time)

/-- A world that waits is unchanged by any amount of agent work. -/
theorem Moving.elapsed_waits (world : Moving interface) (waits : world.Waits) (units : ℕ)
    (state : world.State) : world.elapsed units state = state := by
  induction units generalizing state with
  | zero => rfl
  | succ units ih => exact (congrArg (world.elapsed units) (waits state)).trans (ih state)

/-- When the world's own change commutes with its transitions, so does any amount of
it. -/
theorem Moving.elapsed_step (world : Moving interface)
    (commutes : ∀ state action,
      world.elapse (world.step state action) = world.step (world.elapse state) action)
    (units : ℕ) (state : world.State) (action : Act interface) :
    world.elapsed units (world.step state action) =
      world.step (world.elapsed units state) action := by
  induction units generalizing state with
  | zero => rfl
  | succ units ih =>
    exact (congrArg (world.elapsed units) (commutes state action)).trans
      (ih (world.elapse state))

/-- The definition of `Moving.landing`, for one interaction from one world state and
memory: under learn-then-act the action lands on the state the world reaches, from
where act-then-learn's action lands, during the work of the second part. -/
theorem Moving.landing_learn (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (pair : world.State × parts.Memory) :
    world.landing parts work .learnThenAct pair =
      world.elapsed (work.learn (parts.choose pair.2 (world.percept pair.1)))
        (world.landing parts work .actThenLearn pair) :=
  rfl

/-- **Where the two orders differ.** The definition of `Moving.interact`, for one
interaction from one world state and memory: in both orders the world's transition is
taken with the action of the value the first part returned, on the landing state of
that order; under act-then-learn the world then moves during the work of the second
part. -/
theorem Moving.interact_landing (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (pair : world.State × parts.Memory) :
    (world.interact parts work .learnThenAct pair).1 =
        world.step (world.landing parts work .learnThenAct pair)
          (parts.action (parts.choose pair.2 (world.percept pair.1))) ∧
      (world.interact parts work .actThenLearn pair).1 =
        world.elapsed (work.learn (parts.choose pair.2 (world.percept pair.1)))
          (world.step (world.landing parts work .actThenLearn pair)
            (parts.action (parts.choose pair.2 (world.percept pair.1)))) :=
  ⟨rfl, rfl⟩

/-- The memory one interaction keeps, from one world state and memory, is the second
part of the value the first part returned, in both orders and for every assignment of
work. -/
theorem Moving.interact_memory (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (order : StepOrder) (pair : world.State × parts.Memory) :
    (world.interact parts work order pair).2 =
      parts.learn (parts.choose pair.2 (world.percept pair.1)) := by
  cases order <;> rfl

/-- In a world that waits for the agent, one interaction under either order is the
interaction of the kernel, for every assignment of work. -/
theorem Moving.interact_waits (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (waits : world.Waits) (order : StepOrder)
    (pair : world.State × parts.Memory) :
    world.interact parts work order pair = Kernel.interact world.toWorld parts.agent pair := by
  cases order <;>
    simp only [Moving.interact, Moving.elapsed_waits world waits] <;> rfl

/-- When the world's own change commutes with its transitions, the two orders give one
interaction, for every assignment of work. -/
theorem Moving.interact_commutes (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work)
    (commutes : ∀ state action,
      world.elapse (world.step state action) = world.step (world.elapse state) action)
    (pair : world.State × parts.Memory) :
    world.interact parts work .actThenLearn pair =
      world.interact parts work .learnThenAct pair := by
  simp only [Moving.interact, Moving.elapsed_step world commutes]

/-- **Each percept is learned once, in order, under either order.** For every moving
world, assignment of work, declared order and start state, the memory before a time is
the fold of the first part followed by the second over the percepts that order's loop
delivered before the time, in order. Every percept before the time enters exactly one
learning part, and no later percept enters any. -/
theorem Moving.loop_memory (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (order : StepOrder) (start : world.State) (time : ℕ) :
    (world.loop parts work order start time).2 =
      (List.range time).foldl
        (fun memory index => parts.learn (parts.choose memory
          (world.percept (world.loop parts work order start index).1)))
        parts.initial := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [List.range_succ, List.foldl_append]
    exact (world.interact_memory parts work order _).trans
      (congrArg (fun memory => parts.learn (parts.choose memory
        (world.percept (world.loop parts work order start time).1))) ih)

/-- **In a world that waits, the order changes nothing.** For every assignment of work
and start state, the loop under either order is the closed loop of the kernel: the
same world state and memory before every interaction, hence the same percepts and
actions. -/
theorem Moving.loop_waits (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (waits : world.Waits) (order : StepOrder) (start : world.State)
    (time : ℕ) :
    world.loop parts work order start time =
      Kernel.loop world.toWorld parts.agent start time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    exact (congrArg (world.interact parts work order) ih).trans
      (world.interact_waits parts work waits order _)

end AcornVerif.Kernel

namespace AcornVerif.StepParts
open Acorn Acorn.Features Acorn.Handcrafted AcornVerif.Kernel

variable {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- The executed agent's two parts from a given agent state, as a two-part agent over
the agent's own interface. -/
def executedParts (state : Agent interface profile features criterion dimension planning) :
    TwoPart interface where
  Memory := Agent interface profile features criterion dimension planning
  Chosen := Chosen interface profile features criterion dimension planning
  initial := state
  choose := Agent.choose
  action := fun chosen => chosen.decision.action
  learn := Chosen.learn

/-- **One closed loop.** The executed agent in two parts is the executed agent of
`CurrentGridWorld.executedAgent`. Every statement about that agent's closed loop,
in every world, is a statement about the two parts. -/
theorem executedParts_agent
    (state : Agent interface profile features criterion dimension planning) :
    (executedParts state).agent = CurrentGridWorld.executedAgent state := by
  have same : (fun (memory : Agent interface profile features criterion dimension planning)
        (percept : Percept interface) =>
        ((memory.choose percept).decision.action, (memory.choose percept).learn)) =
      fun memory percept => ((memory.act percept).2.action, (memory.act percept).1) := by
    funext memory percept
    exact (Prod.ext (congrArg (fun step => step.2.action) (memory.act_parts percept))
      (congrArg Prod.fst (memory.act_parts percept))).symm
  exact congrArg (fun act => (⟨Agent interface profile features criterion dimension planning,
    state, act⟩ : Kernel.Agent interface)) same

end AcornVerif.StepParts
