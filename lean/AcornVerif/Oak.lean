import Acorn.Provenance
import AcornVerif.Kernel

namespace AcornVerif
open Acorn Acorn.Features AcornVerif.Kernel

variable {interface : Interface}

structure Oak.Extra (interface : Interface) where
  Carrier : Type
  departure : Departure
  read : Percept interface → Carrier

def Oak.Extra.Values : List (Oak.Extra interface) → Type
  | [] => Unit
  | extra :: rest => extra.Carrier × Oak.Extra.Values rest

def Oak.Extra.readAll :
    (extras : List (Oak.Extra interface)) → Percept interface → Oak.Extra.Values extras
  | [], _ => ()
  | extra :: rest, percept => (extra.read percept, Oak.Extra.readAll rest percept)

structure Oak (interface : Interface) where
  Perception : Type
  Feature : Type
  Subproblem : Type
  Solution : Type
  Model : Type
  extras : List (Oak.Extra interface)
  perceive : Perception → Percept interface → Perception × Feature
  pose : Feature → Subproblem → Subproblem
  solve : Subproblem → Solution → Feature → Binary32 → Oak.Extra.Values extras → Solution
  model : Solution → Model → Feature → Binary32 → Model
  plan : Model → Solution → Feature → Solution
  act : Solution → Feature → Act interface

structure Oak.Memory (oak : Oak interface) where
  perception : oak.Perception
  subproblems : oak.Subproblem
  solutions : oak.Solution
  models : oak.Model

def Oak.step (oak : Oak interface) (memory : oak.Memory) (percept : Percept interface) :
    Act interface × oak.Memory :=
  let perceived := oak.perceive memory.perception percept
  let subproblems := oak.pose perceived.2 memory.subproblems
  let solved := oak.solve subproblems memory.solutions perceived.2 percept.reward
    (Oak.Extra.readAll oak.extras percept)
  let models := oak.model solved memory.models perceived.2 percept.reward
  let planned := oak.plan models solved perceived.2
  (oak.act planned perceived.2, ⟨perceived.1, subproblems, planned, models⟩)

def Oak.toAgent (oak : Oak interface) (initial : oak.Memory) : Agent interface where
  Memory := oak.Memory
  initial := initial
  act := oak.step

theorem Oak.step_congr (oak : Oak interface) (memory : oak.Memory)
    (first second : Percept interface)
    (perceived : oak.perceive memory.perception first = oak.perceive memory.perception second)
    (reward : first.reward = second.reward)
    (extras : Oak.Extra.readAll oak.extras first = Oak.Extra.readAll oak.extras second) :
    oak.step memory first = oak.step memory second := by
  simp only [Oak.step, perceived, reward, extras]

theorem related_actions {first second : Agent interface}
    (related : first.Memory → second.Memory → Prop)
    (initial : related first.initial second.initial)
    (kept : ∀ left right percept, related left right →
      (first.act left percept).1 = (second.act right percept).1 ∧
        related (first.act left percept).2 (second.act right percept).2)
    (world : World interface) (start : world.State) (time : ℕ) :
    actionAt world first start time = actionAt world second start time := by
  have held : ∀ count,
      (loop world first start count).1 = (loop world second start count).1 ∧
        related (loop world first start count).2 (loop world second start count).2 := by
    intro count
    induction count with
    | zero => exact ⟨rfl, initial⟩
    | succ count ih =>
      have decided := kept _ _ (world.percept (loop world first start count).1) ih.2
      change world.step (loop world first start count).1
            (first.act (loop world first start count).2
              (world.percept (loop world first start count).1)).1 =
          world.step (loop world second start count).1
            (second.act (loop world second start count).2
              (world.percept (loop world second start count).1)).1 ∧
        related
          (first.act (loop world first start count).2
            (world.percept (loop world first start count).1)).2
          (second.act (loop world second start count).2
            (world.percept (loop world second start count).1)).2
      rw [← ih.1]
      exact ⟨congrArg _ decided.1, decided.2⟩
  have decided := kept _ _ (world.percept (loop world first start time).1) (held time).2
  change (first.act (loop world first start time).2
      (world.percept (loop world first start time).1)).1 =
    (second.act (loop world second start time).2
      (world.percept (loop world second start time).1)).1
  rw [← (held time).1]
  exact decided.1

def Oak.Conforms (agent : Agent interface) (oak : Oak interface) : Prop :=
  ∃ view : agent.Memory → oak.Memory, ∀ memory percept,
    oak.step (view memory) percept =
      ((agent.act memory percept).1, view (agent.act memory percept).2)

theorem Oak.Conforms.actions {agent : Agent interface} {oak : Oak interface}
    (conforms : Oak.Conforms agent oak) :
    ∃ initial : oak.Memory, ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world (oak.toAgent initial) start time = actionAt world agent start time := by
  obtain ⟨view, same⟩ := conforms
  refine ⟨view agent.initial, related_actions (first := oak.toAgent (view agent.initial))
    (second := agent) (fun (left : oak.Memory) right => left = view right) rfl ?_⟩
  intro left right percept held
  subst held
  exact ⟨congrArg Prod.fst (same right percept), congrArg Prod.snd (same right percept)⟩

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

theorem Oak.conforms_coarse (agent : Agent interface) : Oak.Conforms agent (Oak.coarse agent) :=
  ⟨fun memory => ⟨memory, (), (), ()⟩, fun _ _ => rfl⟩

structure Oak.View (Memory Part : Type) where
  get : Memory → Part
  put : Memory → Part → Memory
  restore : ∀ memory, put memory (get memory) = memory
  replace : ∀ memory first second, put (put memory first) second = put memory second
  written : ∀ memory part, get (put memory part) = part

def Oak.Realizes {Memory Part Input : Type} (operation : Memory → Memory)
    (read : Memory → Input) (arrow : Input → Part) (view : Oak.View Memory Part) : Prop :=
  ∀ memory, operation memory = view.put memory (arrow (read memory))

theorem Oak.Realizes.restores {Memory Part Input : Type} {operation : Memory → Memory}
    {read : Memory → Input} {arrow : Input → Part} {view : Oak.View Memory Part}
    (realized : Oak.Realizes operation read arrow view) (memory : Memory) :
    view.put (operation memory) (view.get memory) = memory := by
  rw [realized memory, view.replace, view.restore]

theorem Oak.Realizes.writes {Memory Part Input : Type} {operation : Memory → Memory}
    {read : Memory → Input} {arrow : Input → Part} {view : Oak.View Memory Part}
    (realized : Oak.Realizes operation read arrow view) (memory : Memory) :
    view.get (operation memory) = arrow (read memory) := by
  rw [realized memory, view.written]

theorem Oak.Realizes.reads {Memory Part Input : Type} {operation : Memory → Memory}
    {read : Memory → Input} {arrow : Input → Part} {view : Oak.View Memory Part}
    (realized : Oak.Realizes operation read arrow view) (first second : Memory)
    (same : read first = read second) :
    view.get (operation first) = view.get (operation second) := by
  rw [realized.writes first, realized.writes second, same]

end AcornVerif
