import AcornVerif.CurrentGridWorld

namespace AcornVerif.Kernel
open Acorn Acorn.Features

variable {interface : Interface}

structure TwoPart (interface : Interface) where
  Memory : Type
  Chosen : Type
  initial : Memory
  choose : Memory → Percept interface → Chosen
  action : Chosen → Act interface
  learn : Chosen → Memory

def TwoPart.agent (parts : TwoPart interface) : Agent interface where
  Memory := parts.Memory
  initial := parts.initial
  act := fun memory percept =>
    (parts.action (parts.choose memory percept), parts.learn (parts.choose memory percept))

def chosenAt (parts : TwoPart interface) (world : World interface) (start : world.State)
    (time : ℕ) : parts.Chosen :=
  parts.choose (memoryAt world parts.agent start time) (perceptAt world parts.agent start time)

theorem actionAt_chosen (parts : TwoPart interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    actionAt world parts.agent start time = parts.action (chosenAt parts world start time) :=
  rfl

theorem memoryAt_learn (parts : TwoPart interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    memoryAt world parts.agent start (time + 1) = parts.learn (chosenAt parts world start time) :=
  rfl

theorem memory_parts (parts : TwoPart interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    memoryAt world parts.agent start time =
      (List.range time).foldl
        (fun memory index =>
          parts.learn (parts.choose memory (perceptAt world parts.agent start index)))
        parts.initial :=
  memory_causal world parts.agent start time

inductive Position where
  | afterParts
  | betweenParts

structure Moving (interface : Interface) extends World interface where
  elapse : State → State

def Moving.elapsed (world : Moving interface) : ℕ → world.State → world.State
  | 0, state => state
  | units + 1, state => world.elapsed units (world.elapse state)

def Moving.Waits (world : Moving interface) : Prop :=
  ∀ state, world.elapse state = state

structure TwoPart.Work (parts : TwoPart interface) where
  choose : parts.Memory → Percept interface → ℕ
  learn : parts.Chosen → ℕ

def Moving.landing (world : Moving interface) (parts : TwoPart interface) (work : parts.Work)
    (position : Position) (pair : world.State × parts.Memory) : world.State :=
  let percept := world.percept pair.1
  let chosen := parts.choose pair.2 percept
  let reacted := world.elapsed (work.choose pair.2 percept) pair.1
  match position with
  | .afterParts => world.elapsed (work.learn chosen) reacted
  | .betweenParts => reacted

def Moving.interact (world : Moving interface) (parts : TwoPart interface) (work : parts.Work)
    (position : Position) (pair : world.State × parts.Memory) : world.State × parts.Memory :=
  let percept := world.percept pair.1
  let chosen := parts.choose pair.2 percept
  let reacted := world.elapsed (work.choose pair.2 percept) pair.1
  match position with
  | .afterParts =>
    (world.step (world.elapsed (work.learn chosen) reacted) (parts.action chosen),
      parts.learn chosen)
  | .betweenParts =>
    (world.elapsed (work.learn chosen) (world.step reacted (parts.action chosen)),
      parts.learn chosen)

def Moving.loop (world : Moving interface) (parts : TwoPart interface) (work : parts.Work)
    (position : Position) (start : world.State) : ℕ → world.State × parts.Memory
  | 0 => (start, parts.initial)
  | time + 1 => world.interact parts work position (world.loop parts work position start time)

theorem Moving.elapsed_waits (world : Moving interface) (waits : world.Waits) (units : ℕ)
    (state : world.State) : world.elapsed units state = state := by
  induction units generalizing state with
  | zero => rfl
  | succ units ih => exact (congrArg (world.elapsed units) (waits state)).trans (ih state)

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

theorem Moving.landing_learn (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (pair : world.State × parts.Memory) :
    world.landing parts work .afterParts pair =
      world.elapsed (work.learn (parts.choose pair.2 (world.percept pair.1)))
        (world.landing parts work .betweenParts pair) :=
  rfl

theorem Moving.interact_landing (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (pair : world.State × parts.Memory) :
    (world.interact parts work .afterParts pair).1 =
        world.step (world.landing parts work .afterParts pair)
          (parts.action (parts.choose pair.2 (world.percept pair.1))) ∧
      (world.interact parts work .betweenParts pair).1 =
        world.elapsed (work.learn (parts.choose pair.2 (world.percept pair.1)))
          (world.step (world.landing parts work .betweenParts pair)
            (parts.action (parts.choose pair.2 (world.percept pair.1)))) :=
  ⟨rfl, rfl⟩

theorem Moving.interact_memory (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (position : Position) (pair : world.State × parts.Memory) :
    (world.interact parts work position pair).2 =
      parts.learn (parts.choose pair.2 (world.percept pair.1)) := by
  cases position <;> rfl

theorem Moving.interact_waits (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (waits : world.Waits) (position : Position)
    (pair : world.State × parts.Memory) :
    world.interact parts work position pair = Kernel.interact world.toWorld parts.agent pair := by
  cases position <;>
    simp only [Moving.interact, Moving.elapsed_waits world waits] <;> rfl

theorem Moving.interact_commutes (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work)
    (commutes : ∀ state action,
      world.elapse (world.step state action) = world.step (world.elapse state) action)
    (pair : world.State × parts.Memory) :
    world.interact parts work .betweenParts pair =
      world.interact parts work .afterParts pair := by
  simp only [Moving.interact, Moving.elapsed_step world commutes]

theorem Moving.loop_memory (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (position : Position) (start : world.State) (time : ℕ) :
    (world.loop parts work position start time).2 =
      (List.range time).foldl
        (fun memory index => parts.learn (parts.choose memory
          (world.percept (world.loop parts work position start index).1)))
        parts.initial := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [List.range_succ, List.foldl_append]
    exact (world.interact_memory parts work position _).trans
      (congrArg (fun memory => parts.learn (parts.choose memory
        (world.percept (world.loop parts work position start time).1))) ih)

theorem Moving.loop_waits (world : Moving interface) (parts : TwoPart interface)
    (work : parts.Work) (waits : world.Waits) (position : Position) (start : world.State)
    (time : ℕ) :
    world.loop parts work position start time =
      Kernel.loop world.toWorld parts.agent start time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    exact (congrArg (world.interact parts work position) ih).trans
      (world.interact_waits parts work waits position _)

end AcornVerif.Kernel

namespace AcornVerif.StepParts
open Acorn Acorn.Features Acorn.Handcrafted AcornVerif.Kernel

variable {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

def executedParts (order : StepOrder)
    (state : Agent interface profile features criterion dimension planning) :
    TwoPart interface where
  Memory := Agent interface profile features criterion dimension planning
  Chosen := Chosen interface profile features criterion dimension planning
  initial := state
  choose := fun memory percept => memory.choose order percept
  action := fun chosen => chosen.decision.action
  learn := Chosen.learn

theorem executedParts_agent
    (state : Agent interface profile features criterion dimension planning) :
    (executedParts .learnThenAct state).agent = CurrentGridWorld.executedAgent state := by
  have same : (fun (memory : Agent interface profile features criterion dimension planning)
        (percept : Percept interface) =>
        ((memory.choose .learnThenAct percept).decision.action,
          (memory.choose .learnThenAct percept).learn)) =
      fun memory percept => ((memory.act percept).2.action, (memory.act percept).1) := by
    funext memory percept
    exact (Prod.ext (congrArg (fun step => step.2.action) (memory.act_parts percept))
      (congrArg Prod.fst (memory.act_parts percept))).symm
  exact congrArg (fun act => (⟨Agent interface profile features criterion dimension planning,
    state, act⟩ : Kernel.Agent interface)) same

theorem executedParts_unplanned
    (state : Agent interface profile features criterion dimension .none) :
    (executedParts .planAfterAct state).agent = (executedParts .learnThenAct state).agent := by
  have same : (fun (memory : Agent interface profile features criterion dimension .none)
        (percept : Percept interface) =>
        ((memory.choose .planAfterAct percept).decision.action,
          (memory.choose .planAfterAct percept).learn)) =
      fun memory percept =>
        ((memory.choose .learnThenAct percept).decision.action,
          (memory.choose .learnThenAct percept).learn) := by
    funext memory percept
    exact Prod.ext (congrArg (fun step => step.2.action) (memory.actOrdered_unplanned percept))
      (congrArg Prod.fst (memory.actOrdered_unplanned percept))
  exact congrArg (fun act => (⟨Agent interface profile features criterion dimension .none,
    state, act⟩ : Kernel.Agent interface)) same

theorem loop_unplanned (state : Agent interface profile features criterion dimension .none)
    (world : World interface) (start : world.State) (time : ℕ) :
    loop world (executedParts .planAfterAct state).agent start time =
      loop world (executedParts .learnThenAct state).agent start time := by
  have same : HEq (loop world (executedParts .planAfterAct state).agent start time)
      (loop world (executedParts .learnThenAct state).agent start time) := by
    rw [executedParts_unplanned]
  exact eq_of_heq same

end AcornVerif.StepParts
