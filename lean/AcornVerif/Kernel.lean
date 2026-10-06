/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Interface
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Embedding.Basic

/-!
# The interaction kernel

The kernel states what a world and an agent are over the executing interface of
`Acorn.Interface`, and what their closed loop is. It restates no interface: an action
is an index below the interface's declared count, the type of the executed decision's
action, and a percept is the executed `Percept`, a frame and the reward word of the
preceding transition.

A `World` is deterministic given its state. Randomness, the clock, the installed task
and the result of the last transition live in the state, so the percept is a function
of the state. An `Agent` is indexed by the interface and not by a world, and carries
its initial memory, so one agent can meet every world of a class. Its `act` has the
shape of the executed `Acorn.Handcrafted.Agent.act`: from a memory and one percept, an
action and the next memory.

`loop` is the closed loop from a start state. `stateAt_eq_path` shows that its world
states are the path driven by the agent's own actions, and `memory_causal` that the
memory at a time is a fold over the percepts before it. `path_congr` shows that a path
depends on the actions before its time only.

Three classes of agents are defined. An `ExperienceFree` agent's memory advances
without reading percepts. An `OpenLoop` agent's action ignores the percept as well, so
its action sequence is the same in every world from every start
(`openLoop_actions`). A `Reactive` agent's action is a function of the latest percept
alone. `MemoryWithin` is the memory axis of a resource envelope: the memory embeds in
bit strings of a given width.

Transitions are deterministic and a percept carries a raw reward word, so no theorem
here concerns a return, a stochastic kernel or the time an agent takes to act. The
work an agent does per step has no axis here.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-- The actions of an interface: the indices below its declared count. This is the
type of the executed decision's action, `TemporalDecision.action`. -/
abbrev Act (interface : Interface) : Type := Action interface.actions.word.toNat

/-- A world over an interface: a deterministic state machine that answers each action
with a successor state and delivers one percept at each state. -/
structure World (interface : Interface) where
  /-- Everything the next percept and the next transition depend on. -/
  State : Type
  /-- The deterministic transition. -/
  step : State → Act interface → State
  /-- The percept the world delivers at a state: the frame, and the reward word of the
  transition that produced the state. -/
  percept : State → Percept interface

/-- An agent over an interface: a causal transducer that turns its memory and one
percept into an action and its next memory. -/
structure Agent (interface : Interface) where
  /-- Everything the agent retains between percepts. -/
  Memory : Type
  /-- The memory before the first percept. -/
  initial : Memory
  /-- One decision: the action taken on a percept and the memory kept after it. -/
  act : Memory → Percept interface → Act interface × Memory

/-- One interaction: the world delivers the percept of its state, the agent acts on it,
and the world steps on that action. -/
def interact (world : World interface) (agent : Agent interface)
    (pair : world.State × agent.Memory) : world.State × agent.Memory :=
  (world.step pair.1 (agent.act pair.2 (world.percept pair.1)).1,
    (agent.act pair.2 (world.percept pair.1)).2)

/-- The closed loop of a world and an agent from a start state, as the world state and
the agent's memory before each interaction. -/
def loop (world : World interface) (agent : Agent interface) (start : world.State) :
    ℕ → world.State × agent.Memory
  | 0 => (start, agent.initial)
  | time + 1 => interact world agent (loop world agent start time)

/-- The world state before the interaction at a time. -/
def stateAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : world.State :=
  (loop world agent start time).1

/-- The agent's memory before the interaction at a time. -/
def memoryAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : agent.Memory :=
  (loop world agent start time).2

/-- The percept the agent receives at a time. -/
def perceptAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : Percept interface :=
  world.percept (stateAt world agent start time)

/-- The action the agent takes at a time. -/
def actionAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : Act interface :=
  (agent.act (memoryAt world agent start time) (perceptAt world agent start time)).1

/-- The state an action sequence drives a world to from a start state. -/
def path (world : World interface) (start : world.State) (actions : ℕ → Act interface) :
    ℕ → world.State
  | 0 => start
  | time + 1 => world.step (path world start actions time) (actions time)

/-! ## The closed loop -/

/-- The memory at a time is the fold of single decisions over the percepts before it,
so no agent's memory depends on a later percept. -/
theorem memory_causal (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) :
    memoryAt world agent start time =
      (List.range time).foldl
        (fun memory index => (agent.act memory (perceptAt world agent start index)).2)
        agent.initial := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [List.range_succ, List.foldl_append]
    exact congrArg
      (fun memory => (agent.act memory (perceptAt world agent start time)).2) ih

/-- The closed loop's world states are the path driven by the agent's own actions. -/
theorem stateAt_eq_path (world : World interface) (agent : Agent interface)
    (start : world.State) (time : ℕ) :
    stateAt world agent start time = path world start (actionAt world agent start) time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    exact congrArg (fun state => world.step state (actionAt world agent start time)) ih

/-! ## Action-driven paths -/

/-- A path depends on the actions before its time only. -/
theorem path_congr (world : World interface) (start : world.State)
    (first second : ℕ → Act interface) (time : ℕ)
    (agree : ∀ index, index < time → first index = second index) :
    path world start first time = path world start second time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have earlier := ih (fun index before => agree index (Nat.lt_succ_of_lt before))
    have last := agree time (Nat.lt_succ_self time)
    exact (congrArg (fun state => world.step state (first time)) earlier).trans
      (congrArg (fun action => world.step (path world start second time) action) last)

/-- A path of one more step is the path of the remaining actions from the successor of
the start. -/
theorem path_shift (world : World interface) (start : world.State)
    (actions : ℕ → Act interface) (time : ℕ) :
    path world start actions (time + 1) =
      path world (world.step start (actions 0)) (fun index => actions (index + 1)) time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    exact congrArg (fun state => world.step state (actions (time + 1))) ih

/-- A path is the fold of the world's transition over its first actions. -/
theorem path_eq_foldl (world : World interface) (start : world.State)
    (actions : ℕ → Act interface) (time : ℕ) :
    path world start actions time = ((List.range time).map actions).foldl world.step start := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    exact congrArg (fun state => world.step state (actions time)) ih

/-- The fold of the world's transition over a list of actions is the path of the
sequence that reads the list. -/
theorem path_list (world : World interface) (start : world.State)
    (actions : List (Act interface)) (fallback : Act interface) :
    path world start (fun index => actions.getD index fallback) actions.length =
      actions.foldl world.step start := by
  induction actions generalizing start with
  | nil => rfl
  | cons head rest ih =>
    rw [List.length_cons, path_shift]
    exact ih (world.step start head)

/-- The states a world can enter from a start state under some action sequence. -/
inductive Reachable (world : World interface) (start : world.State) : world.State → Prop where
  /-- The start state is reachable. -/
  | here : Reachable world start start
  /-- Every action from a reachable state leads to a reachable state. -/
  | next {state : world.State} (earlier : Reachable world start state) (action : Act interface) :
      Reachable world start (world.step state action)

/-- Every state of a path is reachable. -/
theorem path_reachable (world : World interface) (start : world.State)
    (actions : ℕ → Act interface) (time : ℕ) :
    Reachable world start (path world start actions time) := by
  induction time with
  | zero => exact .here
  | succ time ih => exact .next ih (actions time)

/-- Every state the closed loop visits is reachable. -/
theorem stateAt_reachable (world : World interface) (agent : Agent interface)
    (start : world.State) (time : ℕ) : Reachable world start (stateAt world agent start time) := by
  rw [stateAt_eq_path]
  exact path_reachable world start _ time

/-! ## Agent classes -/

/-- An agent whose memory advances without reading percepts. Its action may still
read the current percept. -/
def ExperienceFree (agent : Agent interface) : Prop :=
  ∃ advance : agent.Memory → agent.Memory,
    ∀ memory percept, (agent.act memory percept).2 = advance memory

/-- An agent that reads no percept: its action and its next memory are functions of its
memory alone. -/
def OpenLoop (agent : Agent interface) : Prop :=
  ∃ (advance : agent.Memory → agent.Memory) (choose : agent.Memory → Act interface),
    ∀ memory percept, agent.act memory percept = (choose memory, advance memory)

/-- An agent whose action is a function of the latest percept alone, whatever its
memory. -/
def Reactive (agent : Agent interface) : Prop :=
  ∃ rule : Percept interface → Act interface,
    ∀ memory percept, (agent.act memory percept).1 = rule percept

/-- An open-loop agent is experience-free. -/
theorem OpenLoop.experienceFree {agent : Agent interface} (blind : OpenLoop agent) :
    ExperienceFree agent := by
  obtain ⟨advance, choose, law⟩ := blind
  exact ⟨advance, fun memory percept => congrArg Prod.snd (law memory percept)⟩

/-- A memory advanced a number of times without reading a percept. -/
def advanced {Memory : Type} (advance : Memory → Memory) (initial : Memory) : ℕ → Memory
  | 0 => initial
  | time + 1 => advance (advanced advance initial time)

/-- An open-loop agent's action sequence is fixed before any world is consulted: it is
the same in every world, from every start state. -/
theorem openLoop_actions {agent : Agent interface} (blind : OpenLoop agent) :
    ∃ actions : ℕ → Act interface, ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world agent start time = actions time := by
  obtain ⟨advance, choose, law⟩ := blind
  refine ⟨fun time => choose (advanced advance agent.initial time), ?_⟩
  intro world start time
  have drift : ∀ count, memoryAt world agent start count =
      advanced advance agent.initial count := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih =>
      exact (congrArg Prod.snd
        (law (memoryAt world agent start count) (perceptAt world agent start count))).trans
        (congrArg advance ih)
  exact (congrArg Prod.fst
    (law (memoryAt world agent start time) (perceptAt world agent start time))).trans
    (congrArg choose (drift time))

/-- The memory axis of a resource envelope: the agent's memory embeds in the bit
strings of the given width, so it has at most `2 ^ bits` distinguishable values. -/
def MemoryWithin (agent : Agent interface) (bits : ℕ) : Prop :=
  Nonempty (agent.Memory ↪ Fin (2 ^ bits))

end AcornVerif.Kernel
