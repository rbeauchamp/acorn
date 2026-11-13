/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Visits
import Mathlib.Algebra.Order.Field.Rat

/-!
# Separation, retention and the failing fraction of runs

The postcondition of `docs/mission-contract.md` is proved, on a class of worlds in visits, through
two statements about attempt goals, which this module defines over the kernel's
`AcornVerif.Kernel.SolvesOnVisit`:

- `Separates`: on one visit the agent solves more of the counted members than a bound. With a
  covering bound of a class that conceals its goals, no agent that keeps nothing of its experience
  does so on any visit (`visits_need`).
- `Retains`: a member the agent has solved on one visit it solves on every later visit.

`Finds` is the part of separation that is exploration: each of more than the bound's number of
counted members is solved on some visit, each on a visit of its own. An agent that finds and retains
separates (`separates_of_finds`): it solves on the latest of those visits every member it has found.
So the obligation to separate splits into finding, which concerns how the agent explores, and
retaining, which concerns what it learns.

These statements read an agent only through the states its closed loops reach, so two agents that
take the same action at every time in every world find, retain and separate alike
(`solvesOnVisit_of_actions`, `Finds.of_actions`, `Retains.of_actions`).

`AllBut` counts the runs of a finite family of which a guarantee fails: it holds of every run but a
set holding at most a stated fraction of the family. Fractions add when two guarantees are joined
(`AllBut.and`), and a fraction of zero is every run (`allBut_zero`). It is the counting part of
fork F4 of the mission contract, under which a guarantee about an agent that explores with random
draws holds of all but a fraction of runs when the draws are ideal: the family is then to hold one
run for each sequence of the draws the guarantee reads, each as likely as any other. Two things
this module does not supply, and obligation 15 of `docs/mission-contract.md` owns:

- a model of an agent's draws, with the hypothesis that the generator's outputs may stand in for
  ideal ones. No theorem here has that hypothesis, because none reads a draw: the family is a
  parameter.
- a number of visits. A finite family of draw sequences exists only for a guarantee that reads
  finitely many draws. `Finds` and `Retains` name no last visit, so for an agent that draws at
  every decision they are not such guarantees, and `Retains` asks every later visit: an agent that
  goes on exploring at a rate that can miss a visit fails it on almost every run (argued, not
  proved here). rbeauchamp/acorn#248 decides how retention is asked.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-- **Separation.** On one visit the agent solves each member of a set of more than `bound` of the
counted members. This is postcondition (i) of `docs/mission-contract.md` for a class in visits, with
the members the comparison counts named. -/
def Separates (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (agent : Agent interface) : Prop :=
  ∃ (visit : ℕ) (solved : Finset family.Index), bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧ SolvesOnVisit family goals length agent visit index

/-- **Retention.** A member the agent has solved on one visit it solves on every later visit. This
is postcondition (ii) of `docs/mission-contract.md` for a class in visits, where every visit of a
member starts from the same state. -/
def Retains (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (agent : Agent interface) : Prop :=
  ∀ index visit later, visit < later → SolvesOnVisit family goals length agent visit index →
    SolvesOnVisit family goals length agent later index

/-- **First successes.** The agent solves each member of a set of more than `bound` of the counted
members on some visit, each on a visit of its own. -/
def Finds (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (agent : Agent interface) : Prop :=
  ∃ solved : Finset family.Index, bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧
      ∃ visit, SolvesOnVisit family goals length agent visit index

variable {family : WorldClass interface} {goals : family.Goals} {length : ℕ}
  {agent : Agent interface}

/-- An agent that retains solves, on one common visit, every member of a finite set each of whose
members it has solved on some visit. -/
theorem Retains.common (retains : Retains family goals length agent)
    (solved : Finset family.Index)
    (each : ∀ index ∈ solved, ∃ visit, SolvesOnVisit family goals length agent visit index) :
    ∃ visit, ∀ index ∈ solved, SolvesOnVisit family goals length agent visit index := by
  classical
  induction solved using Finset.induction_on with
  | empty => exact ⟨0, fun _ inside => absurd inside (Finset.notMem_empty _)⟩
  | insert added rest fresh ih =>
    obtain ⟨common, all⟩ := ih (fun index inside => each index (Finset.mem_insert_of_mem inside))
    obtain ⟨own, once⟩ := each added (Finset.mem_insert_self added rest)
    refine ⟨max common own, fun index inside => ?_⟩
    rcases Finset.mem_insert.mp inside with rfl | older
    · rcases Nat.lt_or_eq_of_le (Nat.le_max_right common own) with sooner | same
      · exact retains _ own _ sooner once
      · rw [← same]
        exact once
    · rcases Nat.lt_or_eq_of_le (Nat.le_max_left common own) with sooner | same
      · exact retains _ common _ sooner (all index older)
      · rw [← same]
        exact all index older

/-- **An agent that finds and retains separates.** It solves, on one common visit, every member it
has found. -/
theorem separates_of_finds {bound : ℕ} {counted : List family.Index}
    (finds : Finds family goals length bound counted agent)
    (retains : Retains family goals length agent) :
    Separates family goals length bound counted agent := by
  obtain ⟨solved, many, each⟩ := finds
  obtain ⟨visit, all⟩ := retains.common solved (fun index inside => (each index inside).2)
  exact ⟨visit, solved, many, fun index inside => ⟨(each index inside).1, all index inside⟩⟩

/-- An agent that finds more counted members than a bound has more counted members than the
bound to find. -/
theorem Finds.many {bound : ℕ} {counted : List family.Index}
    (finds : Finds family goals length bound counted agent) : bound < counted.length := by
  classical
  obtain ⟨solved, many, each⟩ := finds
  have inside : solved ⊆ counted.toFinset :=
    fun index member => List.mem_toFinset.mpr (each index member).1
  exact Nat.lt_of_lt_of_le many
    (le_trans (Finset.card_le_card inside) (List.toFinset_card_le counted))

/-! ## Agents that act alike -/

/-- Two agents that take the same action at every time in every world are in the same state at
every time in every world. -/
theorem stateAt_of_actions {first second : Agent interface}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (world : World interface) (start : world.State) (time : ℕ) :
    stateAt world first start time = stateAt world second start time := by
  rw [stateAt_eq_path, stateAt_eq_path]
  exact path_congr world start _ _ time (fun index _ => same world start index)

/-- Two agents that take the same action at every time in every world solve the same members on
the same visits. -/
theorem solvesOnVisit_of_actions {first second : Agent interface}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (visit : ℕ) (index : family.Index) :
    SolvesOnVisit family goals length first visit index ↔
      SolvesOnVisit family goals length second visit index := by
  constructor
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    rw [← stateAt_of_actions same]
    exact met
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    rw [stateAt_of_actions same]
    exact met

/-- An agent that takes the actions of an agent that finds, finds. -/
theorem Finds.of_actions {first second : Agent interface} {bound : ℕ}
    {counted : List family.Index}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (finds : Finds family goals length bound counted second) :
    Finds family goals length bound counted first := by
  obtain ⟨solved, many, each⟩ := finds
  refine ⟨solved, many, fun index member => ⟨(each index member).1, ?_⟩⟩
  obtain ⟨visit, once⟩ := (each index member).2
  exact ⟨visit, (solvesOnVisit_of_actions same visit index).mpr once⟩

/-- An agent that takes the actions of an agent that retains, retains. -/
theorem Retains.of_actions {first second : Agent interface}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (retains : Retains family goals length second) : Retains family goals length first :=
  fun index visit later after solved =>
    (solvesOnVisit_of_actions same later index).mpr
      (retains index visit later after ((solvesOnVisit_of_actions same visit index).mp solved))

/-! ## All but a fraction of runs -/

/-- **All but a fraction of the runs.** The guarantee `holds` is met by every run of the finite
family `runs` but a set holding at most the fraction `fraction` of the family. Under fork F4 of
`docs/mission-contract.md` the family is to hold one run for each sequence of the ideal draws the
guarantee reads, so the form serves a guarantee that reads finitely many draws. -/
def AllBut (fraction : ℚ) {Run : Type} (runs : Finset Run) (holds : Run → Prop) : Prop :=
  ∃ failing : Finset Run, failing ⊆ runs ∧ (failing.card : ℚ) ≤ fraction * runs.card ∧
    ∀ run ∈ runs, run ∉ failing → holds run

variable {Run : Type} {runs : Finset Run}

/-- A guarantee that follows, run by run, from one met by all but a fraction of the runs is met by
all but that fraction. -/
theorem AllBut.mono {fraction : ℚ} {first second : Run → Prop}
    (most : AllBut fraction runs first) (follows : ∀ run ∈ runs, first run → second run) :
    AllBut fraction runs second := by
  obtain ⟨failing, inside, few, rest⟩ := most
  exact ⟨failing, inside, few, fun run member spared => follows run member (rest run member spared)⟩

/-- Fractions add: two guarantees, each met by all but a fraction of the runs, are met together by
all but the sum of the fractions. -/
theorem AllBut.and {left right : ℚ} {first second : Run → Prop}
    (most : AllBut left runs first) (also : AllBut right runs second) :
    AllBut (left + right) runs (fun run => first run ∧ second run) := by
  classical
  obtain ⟨failing, inside, few, rest⟩ := most
  obtain ⟨failing', inside', few', rest'⟩ := also
  refine ⟨failing ∪ failing', Finset.union_subset inside inside', ?_, fun run member spared => ?_⟩
  · have joined : ((failing ∪ failing').card : ℚ) ≤ failing.card + failing'.card := by
      exact_mod_cast Finset.card_union_le failing failing'
    rw [add_mul]
    exact le_trans joined (add_le_add few few')
  · rw [Finset.mem_union, not_or] at spared
    exact ⟨rest run member spared.1, rest' run member spared.2⟩

/-- A fraction of zero is every run. -/
theorem allBut_zero {holds : Run → Prop} :
    AllBut 0 runs holds ↔ ∀ run ∈ runs, holds run := by
  constructor
  · rintro ⟨failing, -, few, rest⟩ run member
    rw [zero_mul] at few
    have none : failing.card = 0 := by
      have : failing.card ≤ 0 := by exact_mod_cast few
      omega
    rw [Finset.card_eq_zero] at none
    exact rest run member (by rw [none]; exact Finset.notMem_empty run)
  · intro all
    exact ⟨∅, Finset.empty_subset runs, by simp, fun run member _ => all run member⟩

end AcornVerif.Kernel
