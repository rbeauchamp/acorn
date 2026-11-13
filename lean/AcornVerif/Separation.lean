/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Retrace
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

`AllBut` is the form in which a failing fraction of runs enters under fork F4 of the mission
contract. A guarantee about an agent that explores with random draws is stated of a finite family of
runs, one for each sequence of the draws the guarantee reads, each as likely as any other under the
assumption that the draws are ideal: the guarantee holds of every run of the family but a set
holding at most the stated fraction of it. Fractions add when two guarantees are joined
(`AllBut.and`), and a fraction of zero is every run (`allBut_zero`). How the fraction depends on the
class and on the number of visits is obligation 15 of `docs/mission-contract.md`; that the
generator's outputs may stand in for ideal draws is the assumption F4 names, and no theorem here
discharges it.

The retracing agent retains (`retrace_retains`), and it finds every counted member whose goal one of
its exploring walks meets (`retrace_finds`).
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

/-! ## All but a fraction of runs -/

/-- **All but a fraction of the runs.** The guarantee `holds` is met by every run of the finite
family `runs` but a set holding at most the fraction `fraction` of the family. Under fork F4 of
`docs/mission-contract.md` the family has one run for each sequence of the ideal draws the
guarantee reads. -/
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

/-! ## The retracing agent -/

/-- The retracing agent retains, in a class whose members' percepts after every step show the
signal exactly when that step satisfies the member's goal. -/
theorem retrace_retains (family : WorldClass interface) (goals : family.Goals) (length last : ℕ)
    (signal : Percept interface → Bool) (explore : ℕ → ℕ → Act interface)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action)) :
    Retains family goals length (retrace interface length last signal explore) :=
  fun index visit later after solved =>
    retrace_solves family goals length last signal explore index (decodes index) visit later
      after solved

/-- The retracing agent finds every counted member whose goal one of its exploring walks meets
from the member's start within a visit: where that holds of each of more than `bound` counted
members, it finds more than `bound`. -/
theorem retrace_finds (family : WorldClass interface) (goals : family.Goals)
    (length last bound : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Act interface)
    (decodes : ∀ index state action,
      signal ((family.world index).percept ((family.world index).step state action)) = true ↔
        (goals index).satisfied ((family.world index).step state action))
    (counted : List family.Index) (distinct : counted.Nodup) (many : bound < counted.length)
    (explored : ∀ index ∈ counted, ∃ visit, visit ≤ last ∧
      ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
        (path (family.world index) (family.start index) (explore visit) step)) :
    Finds family goals length bound counted (retrace interface length last signal explore) := by
  classical
  refine ⟨counted.toFinset, by rwa [List.toFinset_card_of_nodup distinct],
    fun index inside => ?_⟩
  have listed := List.mem_toFinset.mp inside
  obtain ⟨visit, exploring, meets⟩ := explored index listed
  exact ⟨listed, visit, retrace_solves_explored family goals length last signal explore index
    (decodes index) visit visit exploring (Nat.le_refl visit) meets⟩

end AcornVerif.Kernel
