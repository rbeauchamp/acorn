/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Concealment
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Find

/-!
# Visits

`visits world start length` is a world in visits of a length: from the start state it takes
`length` steps of the world, delivers one more percept at the visit's last state, and then
returns to the start state whatever the action. A visit takes `length + 1` decisions, and
every visit begins in the start state (`visits_period`). Within a visit the closed loop is
the world's own (`visits_loop`). An agent's later decisions are the decisions of the agent
resumed from its memory (`loop_add`), so a member is solved on a visit exactly when the agent,
resumed from its memory at the start of that visit, solves it in the member's world within
one visit's length (`solvesOnVisit_iff`).

For a class that conceals its goals, with a covering bound for one visit's length:

- **Need on every visit.** An experience-free agent's memory at a time is its initial memory
  advanced that many times (`experienceFree_memoryAt`), and every visit begins at the same
  time in every member. So on each visit it is one agent for the whole class, and it solves
  at most the covering bound of members on that visit (`visits_need`).
- **First success, for every agent.** Before a member's goal is first met, every agent keeps
  in that member's visits the memory it keeps in the reference's visits
  (`Conceals.visits_memory`). So the members an agent solves on a visit and on no earlier one
  number at most the covering bound (`visits_first_success`), on its first visit it solves at
  most that many (`visits_first`), and over its first `count` visits at most `count` times
  that many (`visits_ever`).

The return to a state that does not depend on the member is what bounds the later visits of
an experience-free agent. In a world that persists between attempts, `park_keeps` shows an
experience-free agent keeping every goal it has met. `AcornVerif.Replay` shows an agent that
uses its experience solving, on every later visit, every member it has solved once.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-! ## Resuming an agent -/

/-- An agent with another initial memory: the same decisions, from that memory. -/
def Agent.resume (agent : Agent interface) (memory : agent.Memory) : Agent interface :=
  { agent with initial := memory }

/-- The closed loop after a time is the closed loop of the agent resumed from its memory at
that time, from the state at that time. -/
theorem loop_add (world : World interface) (agent : Agent interface) (start : world.State)
    (time later : ℕ) :
    loop world agent start (time + later) =
      loop world (agent.resume (memoryAt world agent start time))
        (stateAt world agent start time) later := by
  induction later with
  | zero => rfl
  | succ later ih => exact congrArg (interact world agent) ih

/-- The state after a time is the state of the agent resumed from its memory at that time. -/
theorem stateAt_add (world : World interface) (agent : Agent interface) (start : world.State)
    (time later : ℕ) :
    stateAt world agent start (time + later) =
      stateAt world (agent.resume (memoryAt world agent start time))
        (stateAt world agent start time) later :=
  congrArg Prod.fst (loop_add world agent start time later)

/-- The memory after a time is the memory of the agent resumed from its memory at that
time. -/
theorem memoryAt_add (world : World interface) (agent : Agent interface) (start : world.State)
    (time later : ℕ) :
    memoryAt world agent start (time + later) =
      memoryAt world (agent.resume (memoryAt world agent start time))
        (stateAt world agent start time) later :=
  congrArg Prod.snd (loop_add world agent start time later)

/-- An experience-free agent's memory at a time is its initial memory advanced that many
times, in every world from every start state. -/
theorem experienceFree_memoryAt {agent : Agent interface} {advance : agent.Memory → agent.Memory}
    (law : ∀ memory percept, (agent.act memory percept).2 = advance memory)
    (world : World interface) (start : world.State) (time : ℕ) :
    memoryAt world agent start time = advanced advance agent.initial time := by
  induction time with
  | zero => rfl
  | succ time ih => exact (law _ _).trans (congrArg advance ih)

/-! ## A world in visits -/

/-- A world in visits of a length. From the start state the world takes `length` steps,
delivers one more percept at the visit's last state, and then returns to the start state
whatever the action. The counter is the number of steps taken in the current visit. -/
def visits (world : World interface) (start : world.State) (length : ℕ) : World interface where
  State := world.State × Fin (length + 1)
  step := fun state action =>
    if within : state.2.val < length then
      (world.step state.1 action, ⟨state.2.val + 1, by omega⟩)
    else (start, ⟨0, Nat.succ_pos length⟩)
  percept := fun state => world.percept state.1

/-- The first state of every visit: the start state, with no step taken. -/
def visitStart (world : World interface) (start : world.State) (length : ℕ) :
    (visits world start length).State :=
  (start, ⟨0, Nat.succ_pos length⟩)

/-- Within a visit the closed loop is the world's own: after at most `length` decisions from
the start of a visit, the state is the world's state with the count of steps taken, and the
memory is the memory the agent keeps in the world. -/
theorem visits_loop (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (time : ℕ) (within : time ≤ length) :
    loop (visits world start length) agent (visitStart world start length) time =
      (((loop world agent start time).1, ⟨time, Nat.lt_succ_of_le within⟩),
        (loop world agent start time).2) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have short : time < length := Nat.lt_of_succ_le within
    show interact (visits world start length) agent
        (loop (visits world start length) agent (visitStart world start length) time) = _
    rw [earlier]
    simp only [interact, visits, dif_pos short]
    rfl

/-- After a whole visit, `length + 1` decisions from the start of a visit, the world is again
at the start of a visit, whatever the agent. -/
theorem visits_return (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) :
    stateAt (visits world start length) agent (visitStart world start length) (length + 1) =
      visitStart world start length := by
  have last : stateAt (visits world start length) agent (visitStart world start length) length =
      ((loop world agent start length).1, ⟨length, Nat.lt_succ_self length⟩) :=
    congrArg Prod.fst (visits_loop world start length agent length (Nat.le_refl length))
  show (visits world start length).step
      (stateAt (visits world start length) agent (visitStart world start length) length)
      (actionAt (visits world start length) agent (visitStart world start length) length) = _
  rw [last]
  simp only [visits, dif_neg (Nat.lt_irrefl length)]
  rfl

/-- Every visit begins at the start of a visit: after each multiple of `length + 1`
decisions. -/
theorem visits_period (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count : ℕ) :
    stateAt (visits world start length) agent (visitStart world start length)
        (count * (length + 1)) =
      visitStart world start length := by
  induction count with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ count ih =>
    rw [Nat.add_mul, Nat.one_mul, stateAt_add, ih]
    exact visits_return world start length _

/-! ## Solving on a visit -/

/-- The goal of each member with its step cap replaced by a visit's length. -/
def visitGoals {family : WorldClass interface} (goals : family.Goals) (length : ℕ) :
    family.Goals :=
  fun index => ⟨(goals index).satisfied, length⟩

/-- An agent solves a member of a class on a visit when, in that member's world in visits
from its start state, some state of that visit after one to `length` steps satisfies the
member's goal. Visit 0 is the first. -/
def SolvesOnVisit (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (agent : Agent interface) (count : ℕ) (index : family.Index) : Prop :=
  ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
    (stateAt (visits (family.world index) (family.start index) length) agent
      (visitStart (family.world index) (family.start index) length)
      (count * (length + 1) + step)).1

/-- An agent solves a member on a visit exactly when the agent, resumed from its memory at the
start of that visit, solves the member in its own world within one visit's length. -/
theorem solvesOnVisit_iff (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (agent : Agent interface) (count : ℕ) (index : family.Index) :
    SolvesOnVisit family goals length agent count index ↔
      Solves family (visitGoals goals length)
        (agent.resume (memoryAt (visits (family.world index) (family.start index) length) agent
          (visitStart (family.world index) (family.start index) length)
          (count * (length + 1))))
        index := by
  have inner : ∀ step, step ≤ length →
      (stateAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length)
        (count * (length + 1) + step)).1 =
      stateAt (family.world index)
        (agent.resume (memoryAt (visits (family.world index) (family.start index) length) agent
          (visitStart (family.world index) (family.start index) length)
          (count * (length + 1))))
        (family.start index) step := by
    intro step within
    rw [stateAt_add, visits_period]
    exact congrArg (fun pair => pair.1.1)
      (visits_loop (family.world index) (family.start index) length _ step within)
  constructor
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    show (goals index).satisfied _
    rw [← inner step high]
    exact met
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    rw [inner step high]
    exact met

/-! ## Need on every visit -/

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

/-- A class that conceals its goals conceals them with every step cap. -/
theorem Conceals.withLength (hidden : Conceals family goals reference origin) (length : ℕ) :
    Conceals family (visitGoals goals length) reference origin :=
  hidden

/-- Need on every visit. In a class that conceals its goals, if one action sequence meets the
goal of at most `bound` members within one visit's length, every experience-free agent solves
at most `bound` members on each visit. -/
theorem visits_need (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound)
    {agent : Agent interface} (free : ExperienceFree agent) (count : ℕ)
    (solved : Finset family.Index)
    (each : ∀ index ∈ solved, SolvesOnVisit family goals length agent count index) :
    solved.card ≤ bound := by
  obtain ⟨advance, law⟩ := free
  refine (hidden.withLength length).need covered
    (agent.resume (advanced advance agent.initial (count * (length + 1)))) trivial solved
    (fun index member => ?_)
  have solves := (solvesOnVisit_iff family goals length agent count index).mp (each index member)
  rwa [experienceFree_memoryAt law] at solves

/-! ## First success -/

/-- Over one visit in which a member's goal is not met, every agent that starts the visit in
the member and in the reference with one memory ends it with one memory. -/
theorem Conceals.visit_memory (hidden : Conceals family goals reference origin) (length : ℕ)
    (agent : Agent interface) (index : family.Index)
    (unmet : ∀ step, 1 ≤ step → step ≤ length → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) step)) :
    memoryAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) (length + 1) =
      memoryAt (visits reference origin length) agent (visitStart reference origin length)
        (length + 1) := by
  obtain ⟨memory, actions⟩ := hidden.agree agent index length unmet
  have percept := hidden.perceptAt_eq agent index length unmet
    (fun step before => actions step (Nat.le_of_lt before))
  have member := visits_loop (family.world index) (family.start index) length agent length
    (Nat.le_refl length)
  have base := visits_loop reference origin length agent length (Nat.le_refl length)
  have memberMemory : memoryAt (visits (family.world index) (family.start index) length) agent
      (visitStart (family.world index) (family.start index) length) length =
        memoryAt (family.world index) agent (family.start index) length :=
    congrArg Prod.snd member
  have memberPercept : perceptAt (visits (family.world index) (family.start index) length) agent
      (visitStart (family.world index) (family.start index) length) length =
        perceptAt (family.world index) agent (family.start index) length :=
    congrArg (fun pair => (family.world index).percept pair.1.1) member
  have baseMemory : memoryAt (visits reference origin length) agent
      (visitStart reference origin length) length = memoryAt reference agent origin length :=
    congrArg Prod.snd base
  have basePercept : perceptAt (visits reference origin length) agent
      (visitStart reference origin length) length = perceptAt reference agent origin length :=
    congrArg (fun pair => reference.percept pair.1.1) base
  show (agent.act
      (memoryAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) length)
      (perceptAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) length)).2 =
    (agent.act
      (memoryAt (visits reference origin length) agent (visitStart reference origin length) length)
      (perceptAt (visits reference origin length) agent (visitStart reference origin length)
        length)).2
  rw [memberMemory, memberPercept, baseMemory, basePercept, memory, percept]

/-- Before a member's goal is first met, every agent keeps in that member's visits the memory
it keeps in the reference's visits: at the start of each visit up to the first on which it
solves the member, its memory is its memory in the reference. -/
theorem Conceals.visits_memory (hidden : Conceals family goals reference origin) (length : ℕ)
    (agent : Agent interface) (index : family.Index) (count : ℕ)
    (unsolved : ∀ earlier, earlier < count →
      ¬ SolvesOnVisit family goals length agent earlier index) :
    memoryAt (visits (family.world index) (family.start index) length) agent
        (visitStart (family.world index) (family.start index) length) (count * (length + 1)) =
      memoryAt (visits reference origin length) agent (visitStart reference origin length)
        (count * (length + 1)) := by
  induction count with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ count ih =>
    have same := ih (fun earlier before => unsolved earlier (Nat.lt_succ_of_lt before))
    have missed := unsolved count (Nat.lt_succ_self count)
    rw [solvesOnVisit_iff] at missed
    have memberSplit := memoryAt_add (visits (family.world index) (family.start index) length)
      agent (visitStart (family.world index) (family.start index) length)
      (count * (length + 1)) (length + 1)
    have baseSplit := memoryAt_add (visits reference origin length) agent
      (visitStart reference origin length) (count * (length + 1)) (length + 1)
    rw [visits_period] at memberSplit baseSplit
    rw [Nat.add_mul, Nat.one_mul, memberSplit, baseSplit]
    rw [same] at missed ⊢
    exact hidden.visit_memory length _ index (fun step low high met =>
      missed ⟨step, low, high, met⟩)

/-- First success, for every agent. In a class that conceals its goals, if one action
sequence meets the goal of at most `bound` members within one visit's length, then for every
agent and every visit, the members it solves on that visit and on no earlier one number at
most `bound`. -/
theorem visits_first_success (hidden : Conceals family goals reference origin)
    {length bound : ℕ} (covered : Covered family (visitGoals goals length) bound)
    (agent : Agent interface) (count : ℕ) (solved : Finset family.Index)
    (each : ∀ index ∈ solved, SolvesOnVisit family goals length agent count index ∧
      ∀ earlier, earlier < count → ¬ SolvesOnVisit family goals length agent earlier index) :
    solved.card ≤ bound := by
  refine (hidden.withLength length).need covered
    (agent.resume (memoryAt (visits reference origin length) agent
      (visitStart reference origin length) (count * (length + 1)))) trivial solved
    (fun index member => ?_)
  have solves := (solvesOnVisit_iff family goals length agent count index).mp
    (each index member).1
  rwa [hidden.visits_memory length agent index count (each index member).2] at solves

/-- The first-visit bound in visits: on its first visit every agent solves at most `bound`
members. -/
theorem visits_first (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound) (agent : Agent interface)
    (solved : Finset family.Index)
    (each : ∀ index ∈ solved, SolvesOnVisit family goals length agent 0 index) :
    solved.card ≤ bound :=
  visits_first_success hidden covered agent 0 solved
    (fun index member => ⟨each index member, fun _ before => absurd before (Nat.not_lt_zero _)⟩)

/-- Over its first `count` visits every agent solves at most `count` times `bound` members:
each member it solves is solved first on one of those visits. -/
theorem visits_ever (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound) (agent : Agent interface)
    (count : ℕ) (solved : Finset family.Index)
    (each : ∀ index ∈ solved, ∃ earlier, earlier < count ∧
      SolvesOnVisit family goals length agent earlier index) :
    solved.card ≤ count * bound := by
  classical
  let first : family.Index → ℕ := fun index =>
    if once : ∃ earlier, SolvesOnVisit family goals length agent earlier index then
      Nat.find once else count
  have firstOf : ∀ index (once : ∃ earlier, SolvesOnVisit family goals length agent earlier index),
      first index = Nat.find once := fun index once => dif_pos once
  have cover : solved ⊆ (Finset.range count).biUnion
      (fun visit => solved.filter (fun index => first index = visit)) := by
    intro index member
    obtain ⟨earlier, before, solves⟩ := each index member
    have least : Nat.find ⟨earlier, solves⟩ ≤ earlier := Nat.find_min' ⟨earlier, solves⟩ solves
    rw [Finset.mem_biUnion]
    refine ⟨first index, ?_, Finset.mem_filter.mpr ⟨member, rfl⟩⟩
    rw [Finset.mem_range, firstOf index ⟨earlier, solves⟩]
    omega
  calc solved.card
      ≤ ((Finset.range count).biUnion
          (fun visit => solved.filter (fun index => first index = visit))).card :=
        Finset.card_le_card cover
    _ ≤ ∑ visit ∈ Finset.range count, (solved.filter (fun index => first index = visit)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _visit ∈ Finset.range count, bound := by
        apply Finset.sum_le_sum
        intro visit _
        apply visits_first_success hidden covered agent visit
        intro index member
        obtain ⟨inSolved, isFirst⟩ := Finset.mem_filter.mp member
        obtain ⟨earlier, _, solves⟩ := each index inSolved
        have once : ∃ earlier, SolvesOnVisit family goals length agent earlier index :=
          ⟨earlier, solves⟩
        have found : Nat.find once = visit := (firstOf index once).symm.trans isFirst
        refine ⟨?_, fun sooner before => Nat.find_min once (by rw [found]; exact before)⟩
        rw [← found]
        exact Nat.find_spec once
    _ = count * bound := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end AcornVerif.Kernel
