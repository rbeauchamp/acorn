import Acorn.Interface
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Embedding.Basic

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

abbrev Act (interface : Interface) : Type := Action interface.actions.word.toNat

structure World (interface : Interface) where
  State : Type
  step : State → Act interface → State
  percept : State → Percept interface

structure Agent (interface : Interface) where
  Memory : Type
  initial : Memory
  act : Memory → Percept interface → Act interface × Memory

def interact (world : World interface) (agent : Agent interface)
    (pair : world.State × agent.Memory) : world.State × agent.Memory :=
  (world.step pair.1 (agent.act pair.2 (world.percept pair.1)).1,
    (agent.act pair.2 (world.percept pair.1)).2)

def loop (world : World interface) (agent : Agent interface) (start : world.State) :
    ℕ → world.State × agent.Memory
  | 0 => (start, agent.initial)
  | time + 1 => interact world agent (loop world agent start time)

def stateAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : world.State :=
  (loop world agent start time).1

def memoryAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : agent.Memory :=
  (loop world agent start time).2

def perceptAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : Percept interface :=
  world.percept (stateAt world agent start time)

def actionAt (world : World interface) (agent : Agent interface) (start : world.State)
    (time : ℕ) : Act interface :=
  (agent.act (memoryAt world agent start time) (perceptAt world agent start time)).1

def path (world : World interface) (start : world.State) (actions : ℕ → Act interface) :
    ℕ → world.State
  | 0 => start
  | time + 1 => world.step (path world start actions time) (actions time)

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

theorem stateAt_eq_path (world : World interface) (agent : Agent interface)
    (start : world.State) (time : ℕ) :
    stateAt world agent start time = path world start (actionAt world agent start) time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    exact congrArg (fun state => world.step state (actionAt world agent start time)) ih

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

theorem path_shift (world : World interface) (start : world.State)
    (actions : ℕ → Act interface) (time : ℕ) :
    path world start actions (time + 1) =
      path world (world.step start (actions 0)) (fun index => actions (index + 1)) time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    exact congrArg (fun state => world.step state (actions (time + 1))) ih

theorem path_eq_foldl (world : World interface) (start : world.State)
    (actions : ℕ → Act interface) (time : ℕ) :
    path world start actions time = ((List.range time).map actions).foldl world.step start := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    exact congrArg (fun state => world.step state (actions time)) ih

theorem path_list (world : World interface) (start : world.State)
    (actions : List (Act interface)) (fallback : Act interface) :
    path world start (fun index => actions.getD index fallback) actions.length =
      actions.foldl world.step start := by
  induction actions generalizing start with
  | nil => rfl
  | cons head rest ih =>
    rw [List.length_cons, path_shift]
    exact ih (world.step start head)

inductive Reachable (world : World interface) (start : world.State) : world.State → Prop where
  | here : Reachable world start start
  | next {state : world.State} (earlier : Reachable world start state) (action : Act interface) :
      Reachable world start (world.step state action)

theorem path_reachable (world : World interface) (start : world.State)
    (actions : ℕ → Act interface) (time : ℕ) :
    Reachable world start (path world start actions time) := by
  induction time with
  | zero => exact .here
  | succ time ih => exact .next ih (actions time)

theorem stateAt_reachable (world : World interface) (agent : Agent interface)
    (start : world.State) (time : ℕ) : Reachable world start (stateAt world agent start time) := by
  rw [stateAt_eq_path]
  exact path_reachable world start _ time

def ExperienceFree (agent : Agent interface) : Prop :=
  ∃ advance : agent.Memory → agent.Memory,
    ∀ memory percept, (agent.act memory percept).2 = advance memory

def OpenLoop (agent : Agent interface) : Prop :=
  ∃ (advance : agent.Memory → agent.Memory) (choose : agent.Memory → Act interface),
    ∀ memory percept, agent.act memory percept = (choose memory, advance memory)

def Reactive (agent : Agent interface) : Prop :=
  ∃ rule : Percept interface → Act interface,
    ∀ memory percept, (agent.act memory percept).1 = rule percept

theorem OpenLoop.experienceFree {agent : Agent interface} (blind : OpenLoop agent) :
    ExperienceFree agent := by
  obtain ⟨advance, choose, law⟩ := blind
  exact ⟨advance, fun memory percept => congrArg Prod.snd (law memory percept)⟩

def advanced {Memory : Type} (advance : Memory → Memory) (initial : Memory) : ℕ → Memory
  | 0 => initial
  | time + 1 => advance (advanced advance initial time)

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

def MemoryWithin (agent : Agent interface) (bits : ℕ) : Prop :=
  Nonempty (agent.Memory ↪ Fin (2 ^ bits))

end AcornVerif.Kernel
