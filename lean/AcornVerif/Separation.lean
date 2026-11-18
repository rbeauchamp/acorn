/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Visits
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Interval.Finset.Nat

/-!
# Separation, retention and the failing fraction of runs

The postcondition of `docs/mission-contract.md` is proved, on a class of worlds in visits, through
statements about attempt goals, which this module defines over the kernel's
`AcornVerif.Kernel.SolvesOnVisit`:

- `Separates`: on one visit the agent solves more of the counted members than a bound. With a
  covering bound of a class that conceals its goals, no agent that keeps nothing of its experience
  does so on any visit (`visits_need`). `SeparatesBy` names a visit before which it does.
- `Retains`: a member the agent has solved on one visit it solves on every later visit.
- `RetainsBut`: the same before a stated visit, the horizon, but for at most a stated number of
  each member's visits, its lapses. `Retains` gives it with no lapse (`Retains.but`).

The postcondition asks `SeparatesBy` and `RetainsBut` together. The owner decided on 2026-11-17
(rbeauchamp/acorn#248) that the advantage is read before the horizon as well, early enough that
the promise of solving again still applies to it; the postcondition's record reads that, on the
owner's behalf, as a visit that leaves more later visits than the lapses before the horizon, so
each member solved on it is solved again (`RetainsBut.again`). A horizon that leaves no such room
asks no retention (`retainsBut_of_lapses`).

`Finds` is the part of separation that is exploration: each of more than the bound's number of
counted members is solved on some visit, each on a visit of its own. An agent that finds and retains
separates (`separates_of_finds`): it solves on the latest of those visits every member it has found.
So the obligation to separate splits into finding, which concerns how the agent explores, and
retaining, which concerns what it learns. In a class that conceals its goals behind a reference,
finding is a property of the agent's one run in the reference (`Conceals.finds_iff`); where the
reference pays no reward, as that of the concealed targets does, that run is the agent's
exploration before any reward.

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
  finitely many draws. `Finds`, `Separates` and `Retains` name no last visit, so for an agent that
  draws at every decision they are not such guarantees, and `Retains` asks every later visit: an
  agent that goes on exploring at a rate that can miss a visit fails it on almost every run
  (argued, not proved here). `FindsBy`, `SeparatesBy`, `RetainsOn` and `RetainsBut` each name a
  visit before which they are read.

**An agent that goes on exploring.** Retention is asked of it in two parts. `RetainsOn` is the
first: before the horizon, a member solved on one visit is solved on every later visit that a
predicate admits. It is a statement about one run and counts nothing. The second counts: the
predicate admits every visit before the horizon but for at most `lapses` of each member's
(`AdmitsBut`). Together they give `RetainsBut` (`RetainsOn.but`), under which a member solved once
is solved again within the lapses (`RetainsBut.again`). Separation needs one visit on which the
agent solves more counted members than the bound, so it needs the predicate to admit one visit
for enough members at once: with finding, by a stated visit, of `spare` members more than the
bound asks, and one later visit before a stated visit that the predicate admits for all but
`spare` of the counted members (`AdmitsOnce`), the first part gives separation before that visit
(`separatesBy_of_finds_on`). The predicate is a parameter: the one to read is that the agent
takes no exploratory action on that visit of that member's run, which
`AcornVerif.CurrentConcealedTargetMission.ExecutedCalm` defines for the executed agent.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-- **Separation.** On one visit the agent solves each member of a set of more than `bound` of the
counted members, with the members the comparison counts named. It names no visit: `SeparatesBy` is
the form postcondition (i) of `docs/mission-contract.md` takes. -/
def Separates (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (agent : Agent interface) : Prop :=
  ∃ (visit : ℕ) (solved : Finset family.Index), bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧ SolvesOnVisit family goals length agent visit index

/-- **Separation before a stated visit.** On one visit before the visit `limit` the agent solves
each member of a set of more than `bound` of the counted members. This is postcondition (i) of
`docs/mission-contract.md` for a class in visits, read before the class's horizon as the owner
decided on 2026-11-17 (rbeauchamp/acorn#248). -/
def SeparatesBy (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (limit : ℕ) (agent : Agent interface) : Prop :=
  ∃ (visit : ℕ) (solved : Finset family.Index), visit < limit ∧ bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧ SolvesOnVisit family goals length agent visit index

/-- **Retention on every later visit.** A member the agent has solved on one visit it solves on
every later visit. It names no horizon and allows no lapse: `RetainsBut` is the form postcondition
(ii) of `docs/mission-contract.md` takes, and this gives it at every horizon (`Retains.but`). -/
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

/-- **First successes by a stated visit.** The agent solves each member of a set of more than
`bound` of the counted members on some visit before the visit `last`. -/
def FindsBy (family : WorldClass interface) (goals : family.Goals) (length bound : ℕ)
    (counted : List family.Index) (last : ℕ) (agent : Agent interface) : Prop :=
  ∃ solved : Finset family.Index, bound < solved.card ∧
    ∀ index ∈ solved, index ∈ counted ∧
      ∃ visit, visit < last ∧ SolvesOnVisit family goals length agent visit index

/-- **Retention on the visits a predicate admits, before a horizon.** A member the agent has
solved on one visit it solves on every later visit before the visit `horizon` that the predicate
`admits` holds of for that member. `Retains` gives it for every predicate and horizon
(`Retains.on`). For an agent that goes on exploring, the predicate to read is that the agent
takes no exploratory action on that visit of that member's run. No definition here says so: every
theorem below holds of every predicate. -/
def RetainsOn (family : WorldClass interface) (goals : family.Goals) (length horizon : ℕ)
    (admits : family.Index → ℕ → Prop) (agent : Agent interface) : Prop :=
  ∀ index visit later, visit < later → later < horizon →
    SolvesOnVisit family goals length agent visit index → admits index later →
      SolvesOnVisit family goals length agent later index

/-- **Retention before a horizon, but for a number of lapses.** For each member there are at most
`lapses` visits outside which the agent solves the member on every visit before the visit
`horizon` that is later than one on which it solved it. This is postcondition (ii) of
`docs/mission-contract.md` for a class in visits, where every visit of a member starts from the
same state, as the owner decided it on 2026-11-17 (rbeauchamp/acorn#248). -/
def RetainsBut (family : WorldClass interface) (goals : family.Goals)
    (length horizon lapses : ℕ) (agent : Agent interface) : Prop :=
  ∀ index, ∃ lapsed : Finset ℕ, lapsed.card ≤ lapses ∧
    ∀ visit later, visit < later → later < horizon →
      SolvesOnVisit family goals length agent visit index → later ∉ lapsed →
        SolvesOnVisit family goals length agent later index

/-- **Admitted but for a number of visits.** For each member, the predicate admits every visit
before the visit `horizon` outside a set of at most `lapses` visits. -/
def AdmitsBut {ι : Type} (admits : ι → ℕ → Prop) (horizon lapses : ℕ) : Prop :=
  ∀ index, ∃ restless : Finset ℕ, restless.card ≤ lapses ∧
    ∀ visit, visit < horizon → visit ∉ restless → admits index visit

/-- **Admitted together once, but for a number of members.** Some visit from the visit `last` on
and before the visit `limit` is admitted for every counted member outside a set of at most `spare`
members. -/
def AdmitsOnce {ι : Type} (admits : ι → ℕ → Prop) (counted : List ι)
    (last limit spare : ℕ) : Prop :=
  ∃ common, last ≤ common ∧ common < limit ∧ ∃ restless : Finset ι, restless.card ≤ spare ∧
    ∀ index ∈ counted, index ∉ restless → admits index common

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

/-- An agent that separates finds: the members it solves on one visit it has each solved on a
visit. -/
theorem Separates.finds {bound : ℕ} {counted : List family.Index}
    (separates : Separates family goals length bound counted agent) :
    Finds family goals length bound counted agent := by
  obtain ⟨visit, solved, many, each⟩ := separates
  exact ⟨solved, many, fun index member => ⟨(each index member).1, visit, (each index member).2⟩⟩

/-- An agent that finds by a stated visit finds. -/
theorem FindsBy.finds {bound last : ℕ} {counted : List family.Index}
    (finds : FindsBy family goals length bound counted last agent) :
    Finds family goals length bound counted agent := by
  obtain ⟨solved, many, each⟩ := finds
  refine ⟨solved, many, fun index member => ⟨(each index member).1, ?_⟩⟩
  obtain ⟨visit, -, once⟩ := (each index member).2
  exact ⟨visit, once⟩

/-- Distinct counted members, more of them than the bound, each solved before one visit, are
found by that visit. -/
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

/-- An agent that separates before a stated visit separates. -/
theorem SeparatesBy.separates {bound limit : ℕ} {counted : List family.Index}
    (separates : SeparatesBy family goals length bound counted limit agent) :
    Separates family goals length bound counted agent := by
  obtain ⟨visit, solved, -, many, each⟩ := separates
  exact ⟨visit, solved, many, each⟩

/-! ## Retention for an agent that goes on exploring -/

/-- An agent that retains on every later visit retains, before every horizon, on the visits any
predicate admits. -/
theorem Retains.on (retains : Retains family goals length agent) (horizon : ℕ)
    (admits : family.Index → ℕ → Prop) : RetainsOn family goals length horizon admits agent :=
  fun index visit later after _ solved _ => retains index visit later after solved

/-- Retention before every horizon on the visits of a predicate that admits every visit is
retention on every later visit. -/
theorem retainsOn_true :
    (∀ horizon, RetainsOn family goals length horizon (fun _ _ => True) agent) ↔
      Retains family goals length agent :=
  ⟨fun core index visit later after solved =>
      core (later + 1) index visit later after (Nat.lt_succ_self later) solved trivial,
    fun retains horizon => retains.on horizon _⟩

/-- An agent that retains on every later visit has no lapse before any horizon. -/
theorem Retains.but (retains : Retains family goals length agent) (horizon : ℕ) :
    RetainsBut family goals length horizon 0 agent :=
  fun index => ⟨∅, Nat.le_of_eq Finset.card_empty,
    fun visit later after _ solved _ => retains index visit later after solved⟩

/-- **The two parts give retention but for the lapses.** An agent that retains, before the
horizon, on the visits a predicate admits, where the predicate admits every visit before the
horizon but for at most `lapses` of each member's, retains before that horizon but for that many
lapses. The first part is a statement about one run with no count in it; the second counts visits
and reads no solving. -/
theorem RetainsOn.but {admits : family.Index → ℕ → Prop} {horizon lapses : ℕ}
    (core : RetainsOn family goals length horizon admits agent)
    (few : AdmitsBut admits horizon lapses) :
    RetainsBut family goals length horizon lapses agent := fun index => by
  obtain ⟨restless, count, admitted⟩ := few index
  exact ⟨restless, count, fun visit later after before solved out =>
    core index visit later after before solved (admitted later before out)⟩

/-- **A member solved once is solved again within the lapses.** Under retention but for `lapses`
lapses, among the `lapses + 1` visits from any visit on, where all come before the horizon, the
agent solves on one of them a member it solved on that visit or earlier. -/
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

/-- **A horizon within one visit of the lapses asks no retention.** Where the lapses number at
least the visits before the horizon, less one, every agent retains before that horizon but for
those lapses: every visit before the horizon but the first may be a lapse, and the first visit is
later than none. -/
theorem retainsBut_of_lapses (family : WorldClass interface) (goals : family.Goals)
    (length : ℕ) {horizon lapses : ℕ} (agent : Agent interface)
    (covered : horizon ≤ lapses + 1) : RetainsBut family goals length horizon lapses agent := by
  intro index
  refine ⟨Finset.Icc 1 (horizon - 1), ?_, ?_⟩
  · rw [Nat.card_Icc]
    omega
  · intro visit later after before _ out
    exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) out

/-- **An agent that finds by a visit and retains on admitted visits separates before a stated
visit**, where it finds `spare` members more than the bound asks and the predicate admits some
visit from that one on, before the stated visit, for all but `spare` of the counted members: on
that visit it solves every member it has found for which the visit is admitted, and those are
more than the bound. The stated visit is no later than the horizon of the retention. -/
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

/-- **An agent that finds by a visit and retains on every later visit separates before that
visit**: on the visit before `last` it solves every member it has found before `last`. -/
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

/-- **Finding is a property of the run in the reference.** In a class that conceals its goals
behind a reference, an agent finds exactly when the actions of its run in the reference's visits
meet, each on some visit, the goals of more counted members than the bound. The reference is one
world for the whole class, so finding reads one run of the agent and nothing a member shows
it. -/
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

/-- An agent that takes the actions of an agent that finds by a stated visit, finds by it. -/
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

/-- An agent that takes the actions of an agent that retains, before a horizon, on the visits a
predicate admits, retains on them before it. -/
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
