/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Kernel
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Log

/-!
# World classes, attempt goals and need

An `AttemptGoal` is a predicate on a world's states with a step cap: it is met when
some state reached at step 1 to the cap satisfies it. `Feasible` says some action
sequence meets it from a start state, and `Achieves` that an agent's closed loop does.

## One world

`script` is the clocked script: an agent whose memory is a step counter and whose
action at a count is the corresponding action of a fixed sequence. It reads no percept
(`script_openLoop`), and its counter fits ⌈log₂ (cap + 1)⌉ bits (`script_memory_clog`).
`feasible_iff_script` shows that a goal is feasible exactly when the script of some
sequence achieves it. So in one fixed world, from one start state, no admitted agent
achieving a goal is equivalent to the goal being infeasible, for every class of agents
that admits the clocked scripts (`need_iff_infeasible`). The experience-free agents
within a memory width with room for the counter are such a class
(`experienceFree_iff_infeasible`). A frozen clocked script takes one action throughout
(`script_frozen_constant`), so a class of `Frozen` agents admits only constant scripts
and the equivalence does not apply to it.

## A class of worlds

A `WorldClass` is a family of worlds over one interface with a start state each.
`Need` bounds the members of a class in which an admitted agent achieves its goal, and
`Covered` bounds the members in which one fixed action sequence meets it. An agent is
`Blind` on a class when its actions do not depend on the member until that member's
goal is met; every open-loop agent is blind on every class (`openLoop_blind`). A
covering bound is a need bound for blind agents (`need_of_covered`), and it is exactly
the need bound for open-loop agents (`covered_iff_need`). `need_single_iff_infeasible`
restates the one-world equivalence as a need of zero in the class of one world.

These theorems hold for every world and class over the interface. They say nothing
about an agent whose actions read which member it is in: for such an agent a covering
bound gives no need bound.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-! ## Attempt goals -/

/-- A goal of one attempt: a predicate on states and a step cap. -/
structure AttemptGoal (world : World interface) where
  /-- The states that satisfy the goal. -/
  satisfied : world.State → Prop
  /-- The most steps an attempt takes. -/
  cap : ℕ

variable {world : World interface}

/-- An action sequence meets a goal from a start state when some state it reaches at
step 1 to the cap satisfies the goal. -/
def AttemptGoal.MetBy (goal : AttemptGoal world) (start : world.State)
    (actions : ℕ → Act interface) : Prop :=
  ∃ time, 1 ≤ time ∧ time ≤ goal.cap ∧ goal.satisfied (path world start actions time)

/-- A goal is feasible from a start state when some action sequence meets it. -/
def Feasible (goal : AttemptGoal world) (start : world.State) : Prop :=
  ∃ actions : ℕ → Act interface, goal.MetBy start actions

/-- An agent achieves a goal from a start state when some state of its closed loop at
step 1 to the cap satisfies the goal. -/
def Achieves (agent : Agent interface) (goal : AttemptGoal world) (start : world.State) : Prop :=
  ∃ time, 1 ≤ time ∧ time ≤ goal.cap ∧ goal.satisfied (stateAt world agent start time)

/-- An agent achieves a goal exactly when its own action sequence meets it. -/
theorem achieves_iff_metBy (agent : Agent interface) (goal : AttemptGoal world)
    (start : world.State) :
    Achieves agent goal start ↔ goal.MetBy start (actionAt world agent start) := by
  constructor
  · rintro ⟨time, low, high, met⟩
    rw [stateAt_eq_path] at met
    exact ⟨time, low, high, met⟩
  · rintro ⟨time, low, high, met⟩
    rw [← stateAt_eq_path] at met
    exact ⟨time, low, high, met⟩

/-- A goal some agent achieves is feasible. -/
theorem Achieves.feasible {agent : Agent interface} {goal : AttemptGoal world}
    {start : world.State} (achieved : Achieves agent goal start) : Feasible goal start :=
  ⟨actionAt world agent start, (achieves_iff_metBy agent goal start).mp achieved⟩

/-- A goal is feasible exactly when the world's transition, folded over some list of
one to cap actions, ends in a satisfying state. -/
theorem feasible_iff_list (goal : AttemptGoal world) (start : world.State) :
    Feasible goal start ↔ ∃ actions : List (Act interface),
      1 ≤ actions.length ∧ actions.length ≤ goal.cap ∧
        goal.satisfied (actions.foldl world.step start) := by
  constructor
  · rintro ⟨actions, time, low, high, met⟩
    refine ⟨(List.range time).map actions, ?_, ?_, ?_⟩
    · rw [List.length_map, List.length_range]
      exact low
    · rw [List.length_map, List.length_range]
      exact high
    · rw [← path_eq_foldl]
      exact met
  · rintro ⟨actions, low, high, met⟩
    refine ⟨fun index => actions.getD index ⟨0, interface.actions.positive⟩, actions.length,
      low, high, ?_⟩
    rw [path_list]
    exact met

/-! ## The clocked script -/

/-- A step counter that stops at the cap. -/
def tick (cap : ℕ) (count : Fin (cap + 1)) : Fin (cap + 1) :=
  ⟨min (count.val + 1) cap, by omega⟩

/-- The clocked script of an action sequence: its memory is a step counter, and its
action at a count is the sequence's action there. It reads no percept. -/
def script (interface : Interface) (cap : ℕ) (actions : ℕ → Act interface) : Agent interface where
  Memory := Fin (cap + 1)
  initial := ⟨0, Nat.succ_pos cap⟩
  act := fun count _ => (actions count.val, tick cap count)

/-- A clocked script reads no percept. -/
theorem script_openLoop (cap : ℕ) (actions : ℕ → Act interface) :
    OpenLoop (script interface cap actions) :=
  ⟨tick cap, fun (count : Fin (cap + 1)) => actions count.val, fun _ _ => rfl⟩

/-- A clocked script's memory advances without reading percepts. -/
theorem script_experienceFree (cap : ℕ) (actions : ℕ → Act interface) :
    ExperienceFree (script interface cap actions) :=
  (script_openLoop cap actions).experienceFree

/-- A clocked script's counter fits every width with room for the cap. -/
theorem script_memoryWithin (cap bits : ℕ) (actions : ℕ → Act interface)
    (room : cap + 1 ≤ 2 ^ bits) : MemoryWithin (script interface cap actions) bits := by
  refine ⟨⟨fun (count : Fin (cap + 1)) => Fin.castLE room count, fun first second same => ?_⟩⟩
  have values := congrArg Fin.val same
  exact Fin.ext values

/-- A clocked script's counter fits ⌈log₂ (cap + 1)⌉ bits. -/
theorem script_memory_clog (cap : ℕ) (actions : ℕ → Act interface) :
    MemoryWithin (script interface cap actions) (Nat.clog 2 (cap + 1)) :=
  script_memoryWithin cap _ actions (Nat.le_pow_clog Nat.one_lt_two _)

/-- Up to the cap, a clocked script's counter reads the time. -/
theorem script_memoryAt (world : World interface) (start : world.State) (cap : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) (within : time ≤ cap) :
    (memoryAt world (script interface cap actions) start time).val = time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have counted : (memoryAt world (script interface cap actions) start (time + 1)).val =
        min ((memoryAt world (script interface cap actions) start time).val + 1) cap := rfl
    rw [counted, earlier]
    exact Nat.min_eq_left within

/-- Below the cap, a clocked script takes its sequence's actions. -/
theorem script_actionAt (world : World interface) (start : world.State) (cap : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) (within : time < cap) :
    actionAt world (script interface cap actions) start time = actions time :=
  congrArg actions (script_memoryAt world start cap actions time (Nat.le_of_lt within))

/-- Up to the cap, a clocked script's closed loop follows its sequence's path. -/
theorem script_stateAt (world : World interface) (start : world.State) (cap : ℕ)
    (actions : ℕ → Act interface) (time : ℕ) (within : time ≤ cap) :
    stateAt world (script interface cap actions) start time = path world start actions time := by
  rw [stateAt_eq_path]
  exact path_congr world start _ actions time (fun index before =>
    script_actionAt world start cap actions index (Nat.lt_of_lt_of_le before within))

/-- The clocked script of a sequence that meets a goal achieves it, for every counter
at least as long as the goal's cap. -/
theorem script_achieves {goal : AttemptGoal world} {start : world.State}
    {actions : ℕ → Act interface} {cap : ℕ} (long : goal.cap ≤ cap)
    (met : goal.MetBy start actions) : Achieves (script interface cap actions) goal start := by
  obtain ⟨time, low, high, satisfied⟩ := met
  refine ⟨time, low, high, ?_⟩
  rw [script_stateAt world start cap actions time (Nat.le_trans high long)]
  exact satisfied

/-- The script theorem. A goal is feasible from a start state exactly when the clocked
script of some action sequence achieves it. -/
theorem feasible_iff_script (goal : AttemptGoal world) (start : world.State) :
    Feasible goal start ↔
      ∃ actions : ℕ → Act interface, Achieves (script interface goal.cap actions) goal start :=
  ⟨fun ⟨actions, met⟩ => ⟨actions, script_achieves (Nat.le_refl _) met⟩,
    fun ⟨_, achieved⟩ => achieved.feasible⟩

/-- In one world, need is infeasibility. For every class of agents that admits the
clocked scripts of a goal's cap, no admitted agent achieves the goal from a start state
exactly when the goal is infeasible from it. -/
theorem need_iff_infeasible (goal : AttemptGoal world) (start : world.State)
    (admits : Agent interface → Prop)
    (scripts : ∀ actions : ℕ → Act interface, admits (script interface goal.cap actions)) :
    (∀ agent, admits agent → ¬ Achieves agent goal start) ↔ ¬ Feasible goal start := by
  constructor
  · intro fails feasible
    obtain ⟨actions, achieved⟩ := (feasible_iff_script goal start).mp feasible
    exact fails _ (scripts actions) achieved
  · intro infeasible agent _ achieved
    exact infeasible achieved.feasible

/-- Against experience-free agents within a memory width with room for the cap's
counter, need is infeasibility: no such agent achieves a goal from a start state exactly
when the goal is infeasible from it. -/
theorem experienceFree_iff_infeasible (goal : AttemptGoal world) (start : world.State)
    (bits : ℕ) (room : goal.cap + 1 ≤ 2 ^ bits) :
    (∀ agent : Agent interface, ExperienceFree agent → MemoryWithin agent bits →
      ¬ Achieves agent goal start) ↔ ¬ Feasible goal start := by
  refine Iff.trans ?_ (need_iff_infeasible goal start
    (fun agent => ExperienceFree agent ∧ MemoryWithin agent bits)
    (fun actions => ⟨script_experienceFree goal.cap actions,
      script_memoryWithin goal.cap bits actions room⟩))
  exact ⟨fun fails agent admitted => fails agent admitted.1 admitted.2,
    fun fails agent free fits => fails agent ⟨free, fits⟩⟩

/-- A frozen clocked script takes one action at every count up to its cap, where the
interface has a percept. A class of frozen agents therefore admits only such scripts. -/
theorem script_frozen_constant (cap : ℕ) (actions : ℕ → Act interface)
    (frozen : Frozen (script interface cap actions)) (percept : Percept interface)
    (first second : ℕ) (low : first ≤ cap) (high : second ≤ cap) :
    actions first = actions second := by
  obtain ⟨rule, law⟩ := frozen
  have early : actions first = rule percept :=
    law (⟨first, Nat.lt_succ_of_le low⟩ : Fin (cap + 1)) percept
  have late : actions second = rule percept :=
    law (⟨second, Nat.lt_succ_of_le high⟩ : Fin (cap + 1)) percept
  exact early.trans late.symm

/-! ## Classes of worlds -/

/-- A family of worlds over one interface, with a start state each. -/
structure WorldClass (interface : Interface) where
  /-- What distinguishes the members: a seed, a target, a configuration. -/
  Index : Type
  /-- The world of each member. -/
  world : Index → World interface
  /-- The start state of each member. -/
  start : (index : Index) → (world index).State

/-- The class of one world and one start state. -/
def WorldClass.single (world : World interface) (start : world.State) : WorldClass interface :=
  ⟨Unit, fun _ => world, fun _ => start⟩

/-- One attempt goal for each member of a class. -/
abbrev WorldClass.Goals (family : WorldClass interface) : Type :=
  (index : family.Index) → AttemptGoal (family.world index)

variable {family : WorldClass interface}

/-- An agent solves a member of a class when it achieves that member's goal from that
member's start state. -/
def Solves (family : WorldClass interface) (goals : family.Goals) (agent : Agent interface)
    (index : family.Index) : Prop :=
  Achieves agent (goals index) (family.start index)

/-- A need bound: every admitted agent solves at most `bound` members of the class. -/
def Need (family : WorldClass interface) (goals : family.Goals)
    (admits : Agent interface → Prop) (bound : ℕ) : Prop :=
  ∀ agent, admits agent → ∀ solved : Finset family.Index,
    (∀ index ∈ solved, Solves family goals agent index) → solved.card ≤ bound

/-- A covering bound: every single action sequence meets the goal of at most `bound`
members of the class. -/
def Covered (family : WorldClass interface) (goals : family.Goals) (bound : ℕ) : Prop :=
  ∀ (actions : ℕ → Act interface) (solved : Finset family.Index),
    (∀ index ∈ solved, (goals index).MetBy (family.start index) actions) → solved.card ≤ bound

/-- An agent is blind on a class when one action sequence gives its action in every
member at every time before that member's goal is first satisfied. -/
def Blind (family : WorldClass interface) (goals : family.Goals) (agent : Agent interface) :
    Prop :=
  ∃ actions : ℕ → Act interface, ∀ index time,
    (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (stateAt (family.world index) agent (family.start index) earlier)) →
    actionAt (family.world index) agent (family.start index) time = actions time

/-- An open-loop agent is blind on every class. -/
theorem openLoop_blind (family : WorldClass interface) (goals : family.Goals)
    {agent : Agent interface} (blind : OpenLoop agent) : Blind family goals agent := by
  obtain ⟨actions, law⟩ := openLoop_actions blind
  exact ⟨actions, fun index time _ => law (family.world index) (family.start index) time⟩

/-- A member a blind agent solves is a member its action sequence meets. -/
theorem blind_metBy {goals : family.Goals} {agent : Agent interface}
    {actions : ℕ → Act interface}
    (law : ∀ index time,
      (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
        (stateAt (family.world index) agent (family.start index) earlier)) →
      actionAt (family.world index) agent (family.start index) time = actions time)
    (index : family.Index) (solved : Solves family goals agent index) :
    (goals index).MetBy (family.start index) actions := by
  have first : ∀ time, 1 ≤ time → time ≤ (goals index).cap →
      (goals index).satisfied (stateAt (family.world index) agent (family.start index) time) →
      (goals index).MetBy (family.start index) actions := by
    intro time
    induction time using Nat.strongRecOn with
    | _ time ih =>
      intro low high met
      by_cases sooner : ∃ earlier, 1 ≤ earlier ∧ earlier < time ∧ (goals index).satisfied
          (stateAt (family.world index) agent (family.start index) earlier)
      · obtain ⟨earlier, lowEarlier, before, metEarlier⟩ := sooner
        exact ih earlier before lowEarlier (Nat.le_trans (Nat.le_of_lt before) high) metEarlier
      · have agree : ∀ step, step < time →
            actionAt (family.world index) agent (family.start index) step = actions step := by
          intro step before
          apply law index step
          intro earlier lowEarlier within reached
          exact sooner ⟨earlier, lowEarlier, Nat.lt_of_le_of_lt within before, reached⟩
        have same : stateAt (family.world index) agent (family.start index) time =
            path (family.world index) (family.start index) actions time :=
          (stateAt_eq_path _ _ _ time).trans (path_congr _ _ _ actions time agree)
        rw [same] at met
        exact ⟨time, low, high, met⟩
  obtain ⟨time, low, high, met⟩ := solved
  exact first time low high met

/-- A covering bound is a need bound for blind agents. -/
theorem need_of_covered {goals : family.Goals} {bound : ℕ} (covered : Covered family goals bound) :
    Need family goals (Blind family goals) bound := by
  intro agent blind solved each
  obtain ⟨actions, law⟩ := blind
  exact covered actions solved (fun index member => blind_metBy law index (each index member))

/-- Against open-loop agents, need is coverage: every open-loop agent solves at most
`bound` members exactly when every action sequence meets the goal of at most `bound`
members. -/
theorem covered_iff_need (goals : family.Goals) (bound : ℕ) :
    Covered family goals bound ↔ Need family goals OpenLoop bound := by
  constructor
  · intro covered agent blind
    exact need_of_covered covered agent (openLoop_blind family goals blind)
  · intro need actions solved each
    exact need (script interface (solved.sup fun index => (goals index).cap) actions)
      (script_openLoop _ actions) solved (fun index member =>
        script_achieves (Finset.le_sup (f := fun index => (goals index).cap) member)
          (each index member))

/-- A need bound leaves at least the rest of every finite set of members unsolved. -/
theorem Need.unsolved [DecidableEq family.Index] {goals : family.Goals}
    {admits : Agent interface → Prop} {bound : ℕ} (need : Need family goals admits bound)
    {agent : Agent interface} (admitted : admits agent) (members solved : Finset family.Index)
    (inside : solved ⊆ members) (each : ∀ index ∈ solved, Solves family goals agent index) :
    members.card - bound ≤ (members \ solved).card := by
  have few := need agent admitted solved each
  have split := Finset.card_sdiff_add_card_eq_card inside
  omega

/-- In the class of one world, a need of zero says that no admitted agent achieves the
goal. -/
theorem need_single (goal : AttemptGoal world) (start : world.State)
    (admits : Agent interface → Prop) :
    Need (WorldClass.single world start) (fun _ => goal) admits 0 ↔
      ∀ agent, admits agent → ¬ Achieves agent goal start := by
  constructor
  · intro need agent admitted achieved
    have one : ({()} : Finset Unit).card ≤ 0 := need agent admitted {()} (fun _ _ => achieved)
    rw [Finset.card_singleton] at one
    exact absurd one (by decide)
  · intro fails agent admitted solved each
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro index member
    exact fails agent admitted (each index member)

/-- In the class of one world, a need of zero is infeasibility, for every class of
agents that admits the clocked scripts of the goal's cap. -/
theorem need_single_iff_infeasible (goal : AttemptGoal world) (start : world.State)
    (admits : Agent interface → Prop)
    (scripts : ∀ actions : ℕ → Act interface, admits (script interface goal.cap actions)) :
    Need (WorldClass.single world start) (fun _ => goal) admits 0 ↔ ¬ Feasible goal start :=
  (need_single goal start admits).trans (need_iff_infeasible goal start admits scripts)

end AcornVerif.Kernel
