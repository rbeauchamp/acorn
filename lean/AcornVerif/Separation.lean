import AcornVerif.Visits
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Interval.Finset.Nat

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

def Separates (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (agent : Agent interface) : Prop :=
  ∃ (visit : ℕ) (solved : Finset family.Index), bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧ SolvesOnVisit family goals length agent visit index

def SeparatesBy (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (limit : ℕ) (agent : Agent interface) : Prop :=
  ∃ (visit : ℕ) (solved : Finset family.Index), visit < limit ∧ bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧ SolvesOnVisit family goals length agent visit index

def Retains (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (agent : Agent interface) : Prop :=
  ∀ index visit later, visit < later → SolvesOnVisit family goals length agent visit index →
    SolvesOnVisit family goals length agent later index

def Finds (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (agent : Agent interface) : Prop :=
  ∃ solved : Finset family.Index, bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧
      ∃ visit, SolvesOnVisit family goals length agent visit index

def FindsBy (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (last : ℕ) (agent : Agent interface) : Prop :=
  ∃ solved : Finset family.Index, bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧
      ∃ visit, visit < last ∧ SolvesOnVisit family goals length agent visit index

def RetainsOn (family : WorldClass interface) (goals : family.Goals) (length horizon : ℕ)
    (admits : family.Index → ℕ → Prop) (agent : Agent interface) : Prop :=
  ∀ index visit later, visit < later → later < horizon →
    SolvesOnVisit family goals length agent visit index → admits index later →
      SolvesOnVisit family goals length agent later index

def RetainsBut (family : WorldClass interface) (goals : family.Goals)
    (length horizon lapses : ℕ) (agent : Agent interface) : Prop :=
  ∀ index, ∃ lapsed : Finset ℕ, lapsed.card ≤ lapses ∧
    ∀ visit later, visit < later → later < horizon →
      SolvesOnVisit family goals length agent visit index → later ∉ lapsed →
        SolvesOnVisit family goals length agent later index

def AdmitsBut {ι : Type} (admits : ι → ℕ → Prop) (horizon lapses : ℕ) : Prop :=
  ∀ index, ∃ restless : Finset ℕ, restless.card ≤ lapses ∧
    ∀ visit, visit < horizon → visit ∉ restless → admits index visit

def AdmitsOnce {ι : Type} (admits : ι → ℕ → Prop) (counted : List ι)
    (last limit spare : ℕ) : Prop :=
  ∃ common, last ≤ common ∧ common < limit ∧ ∃ restless : Finset ι, restless.card ≤ spare ∧
    ∀ index ∈ counted, index ∉ restless → admits index common

variable {family : WorldClass interface} {goals : family.Goals} {length : ℕ}
  {agent : Agent interface}

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

theorem separates_of_finds {bound : ℕ} {counted : List family.Index}
    (finds : Finds family goals length bound counted agent)
    (retains : Retains family goals length agent) :
    Separates family goals length bound counted agent := by
  obtain ⟨solved, many, each⟩ := finds
  obtain ⟨visit, all⟩ := retains.common solved (fun index inside => (each index inside).2)
  exact ⟨visit, solved, many, fun index inside => ⟨(each index inside).1, all index inside⟩⟩

theorem Finds.many {bound : ℕ} {counted : List family.Index}
    (finds : Finds family goals length bound counted agent) : bound < counted.length := by
  classical
  obtain ⟨solved, many, each⟩ := finds
  have inside : solved ⊆ counted.toFinset :=
    fun index member => List.mem_toFinset.mpr (each index member).1
  exact Nat.lt_of_lt_of_le many
    (le_trans (Finset.card_le_card inside) (List.toFinset_card_le counted))

theorem Separates.finds {bound : ℕ} {counted : List family.Index}
    (separates : Separates family goals length bound counted agent) :
    Finds family goals length bound counted agent := by
  obtain ⟨visit, solved, many, each⟩ := separates
  exact ⟨solved, many, fun index member => ⟨(each index member).1, visit, (each index member).2⟩⟩

theorem FindsBy.finds {bound last : ℕ} {counted : List family.Index}
    (finds : FindsBy family goals length bound counted last agent) :
    Finds family goals length bound counted agent := by
  obtain ⟨solved, many, each⟩ := finds
  refine ⟨solved, many, fun index member => ⟨(each index member).1, ?_⟩⟩
  obtain ⟨visit, -, once⟩ := (each index member).2
  exact ⟨visit, once⟩

theorem findsBy_of_each {bound last : ℕ} {counted : List family.Index} (distinct : counted.Nodup)
    (many : bound < counted.length)
    (each : ∀ index ∈ counted, ∃ visit, visit < last ∧
      SolvesOnVisit family goals length agent visit index) :
    FindsBy family goals length bound counted last agent := by
  classical
  refine ⟨counted.toFinset, ?_, fun index member =>
    ⟨List.mem_toFinset.mp member, each index (List.mem_toFinset.mp member)⟩⟩
  rw [List.toFinset_card_of_nodup distinct]
  exact many

theorem SeparatesBy.separates {bound limit : ℕ} {counted : List family.Index}
    (separates : SeparatesBy family goals length bound counted limit agent) :
    Separates family goals length bound counted agent := by
  obtain ⟨visit, solved, -, many, each⟩ := separates
  exact ⟨visit, solved, many, each⟩

theorem Retains.on (retains : Retains family goals length agent) (horizon : ℕ)
    (admits : family.Index → ℕ → Prop) : RetainsOn family goals length horizon admits agent :=
  fun index visit later after _ solved _ => retains index visit later after solved

theorem retainsOn_true :
    (∀ horizon, RetainsOn family goals length horizon (fun _ _ => True) agent) ↔
      Retains family goals length agent :=
  ⟨fun core index visit later after solved =>
      core (later + 1) index visit later after (Nat.lt_succ_self later) solved trivial,
    fun retains horizon => retains.on horizon _⟩

theorem Retains.but (retains : Retains family goals length agent) (horizon : ℕ) :
    RetainsBut family goals length horizon 0 agent :=
  fun index => ⟨∅, Nat.le_of_eq Finset.card_empty,
    fun visit later after _ solved _ => retains index visit later after solved⟩

theorem RetainsOn.but {admits : family.Index → ℕ → Prop} {horizon lapses : ℕ}
    (core : RetainsOn family goals length horizon admits agent)
    (few : AdmitsBut admits horizon lapses) :
    RetainsBut family goals length horizon lapses agent := fun index => by
  obtain ⟨restless, count, admitted⟩ := few index
  exact ⟨restless, count, fun visit later after before solved out =>
    core index visit later after before solved (admitted later before out)⟩

theorem RetainsBut.again {horizon lapses : ℕ}
    (retains : RetainsBut family goals length horizon lapses agent) (index : family.Index)
    (visit since : ℕ) (earlier : visit ≤ since) (room : since + lapses < horizon)
    (solved : SolvesOnVisit family goals length agent visit index) :
    ∃ later, since ≤ later ∧ later ≤ since + lapses ∧
      SolvesOnVisit family goals length agent later index := by
  obtain ⟨lapsed, count, keeps⟩ := retains index
  have more : lapsed.card < (Finset.Icc since (since + lapses)).card := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨later, inside, out⟩ := Finset.exists_mem_notMem_of_card_lt_card more
  obtain ⟨low, high⟩ := Finset.mem_Icc.mp inside
  refine ⟨later, low, high, ?_⟩
  rcases Nat.lt_or_eq_of_le (Nat.le_trans earlier low) with after | same
  · exact keeps visit later after (by omega) solved out
  · rw [← same]
    exact solved

theorem retainsBut_of_lapses (family : WorldClass interface) (goals : family.Goals)
    (length : ℕ) {horizon lapses : ℕ} (agent : Agent interface)
    (covered : horizon ≤ lapses + 1) : RetainsBut family goals length horizon lapses agent := by
  intro index
  refine ⟨Finset.Icc 1 (horizon - 1), ?_, ?_⟩
  · rw [Nat.card_Icc]
    omega
  · intro visit later after before _ out
    exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) out

theorem separatesBy_of_finds_on {bound last limit horizon spare : ℕ}
    {counted : List family.Index} {admits : family.Index → ℕ → Prop}
    (finds : FindsBy family goals length (bound + spare) counted last agent)
    (core : RetainsOn family goals length horizon admits agent)
    (once : AdmitsOnce admits counted last limit spare) (within : limit ≤ horizon) :
    SeparatesBy family goals length bound counted limit agent := by
  classical
  obtain ⟨solved, many, each⟩ := finds
  obtain ⟨common, late, early, restless, few, admitted⟩ := once
  refine ⟨common, solved \ restless, early, ?_, fun index member => ?_⟩
  · have left := Finset.le_card_sdiff restless solved
    omega
  · obtain ⟨inside, out⟩ := Finset.mem_sdiff.mp member
    refine ⟨(each index inside).1, ?_⟩
    obtain ⟨visit, before, found⟩ := (each index inside).2
    exact core index visit common (Nat.lt_of_lt_of_le before late)
      (Nat.lt_of_lt_of_le early within) found (admitted index (each index inside).1 out)

theorem separatesBy_of_findsBy {bound last : ℕ} {counted : List family.Index}
    (finds : FindsBy family goals length bound counted last agent)
    (retains : Retains family goals length agent) :
    SeparatesBy family goals length bound counted last agent := by
  obtain ⟨solved, many, each⟩ := finds
  have positive : 0 < last := by
    obtain ⟨index, member⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) many)
    obtain ⟨visit, before, -⟩ := (each index member).2
    omega
  refine ⟨last - 1, solved, by omega, many, fun index member => ⟨(each index member).1, ?_⟩⟩
  obtain ⟨visit, before, found⟩ := (each index member).2
  rcases Nat.lt_or_eq_of_le (show visit ≤ last - 1 by omega) with sooner | same
  · exact retains index visit (last - 1) sooner found
  · rw [← same]
    exact found

theorem Conceals.finds_iff {reference : World interface} {origin : reference.State}
    (hidden : Conceals family goals reference origin) (bound : ℕ)
    (counted : List family.Index) :
    Finds family goals length bound counted agent ↔
      ∃ solved : Finset family.Index, bound < solved.card ∧
        ∀ index ∈ solved, index ∈ counted ∧
          ∃ visit, (visitGoals goals length index).MetBy (family.start index)
            (visitActions reference origin length agent visit) := by
  constructor
  · rintro ⟨solved, many, each⟩
    exact ⟨solved, many, fun index member =>
      ⟨(each index member).1, (hidden.found_iff length agent index).mp (each index member).2⟩⟩
  · rintro ⟨solved, many, each⟩
    exact ⟨solved, many, fun index member =>
      ⟨(each index member).1, (hidden.found_iff length agent index).mpr (each index member).2⟩⟩

theorem stateAt_of_actions {first second : Agent interface}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (world : World interface) (start : world.State) (time : ℕ) :
    stateAt world first start time = stateAt world second start time := by
  rw [stateAt_eq_path, stateAt_eq_path]
  exact path_congr world start _ _ time (fun index _ => same world start index)

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

theorem Retains.of_actions {first second : Agent interface}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (retains : Retains family goals length second) : Retains family goals length first :=
  fun index visit later after solved =>
    (solvesOnVisit_of_actions same later index).mpr
      (retains index visit later after ((solvesOnVisit_of_actions same visit index).mp solved))

theorem FindsBy.of_actions {first second : Agent interface} {bound last : ℕ}
    {counted : List family.Index}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (finds : FindsBy family goals length bound counted last second) :
    FindsBy family goals length bound counted last first := by
  obtain ⟨solved, many, each⟩ := finds
  refine ⟨solved, many, fun index member => ⟨(each index member).1, ?_⟩⟩
  obtain ⟨visit, before, once⟩ := (each index member).2
  exact ⟨visit, before, (solvesOnVisit_of_actions same visit index).mpr once⟩

theorem RetainsOn.of_actions {first second : Agent interface} {horizon : ℕ}
    {admits : family.Index → ℕ → Prop}
    (same : ∀ (world : World interface) (start : world.State) (time : ℕ),
      actionAt world first start time = actionAt world second start time)
    (core : RetainsOn family goals length horizon admits second) :
    RetainsOn family goals length horizon admits first :=
  fun index visit later after before solved admitted =>
    (solvesOnVisit_of_actions same later index).mpr
      (core index visit later after before
        ((solvesOnVisit_of_actions same visit index).mp solved) admitted)

def AllBut (fraction : ℚ) {Run : Type} (runs : Finset Run) (holds : Run → Prop) : Prop :=
  ∃ failing : Finset Run, failing ⊆ runs ∧ (failing.card : ℚ) ≤ fraction * runs.card ∧
    ∀ run ∈ runs, run ∉ failing → holds run

variable {Run : Type} {runs : Finset Run}

theorem AllBut.mono {fraction : ℚ} {first second : Run → Prop}
    (most : AllBut fraction runs first) (follows : ∀ run ∈ runs, first run → second run) :
    AllBut fraction runs second := by
  obtain ⟨failing, inside, few, rest⟩ := most
  exact ⟨failing, inside, few, fun run member spared => follows run member (rest run member spared)⟩

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
