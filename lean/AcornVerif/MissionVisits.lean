/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.MissionTheorem
import AcornVerif.Replay
import AcornVerif.Separation
import AcornVerif.VisitsClass
import Mathlib.Tactic.NormNum

/-!
# The mission theorem's statement on a class of worlds in visits

`AcornVerif.Intent.MissionTheorem.Mission` is the mission theorem's statement for one class of
worlds, in the terms of the four intent records. This module reads a class of the kernel's worlds,
run in visits, as such a class, and proves the statement of it from named premises about the class
and about the agent. After it, the way the mission theorem on a class in visits depends on its
obligations is a Lean theorem, `visits_mission`, whose hypotheses are the work that remains.

## The class as the records read it

`visitsRung` is the rung of a class `family` with visits of `length` steps and an agent:

- a member is that member's world in visits (`visitMember`). Its observation is the kernel's
  percept, and its reward is `pay`, the class's reading of the percept as a number. Its goal is met
  at a state that at least one step of a visit has reached and that satisfies the member's goal,
  as `AcornVerif.Kernel.SolvesOnVisit` counts it;
- an attempt is a visit: its `length + 1` decisions;
- an attempt's rewards are aggregated by `untilPaid`: they are summed up to and including the first
  step that pays, so an attempt is over, for the count of reward, when its goal is first met;
- the agent is the kernel's agent, given the percept as its observation (`recordAgent`). An agent of
  the records over percepts and actions is a kernel agent in turn (`kernelAgent`), and the run the
  records compute with is the kernel's closed loop (`run_eq_loop`). So an agent solves a member on
  an attempt, as the records count it, exactly when the kernel says it solves that member on that
  visit (`solves_iff`), and the agents that keep nothing of their experience are experience-free
  (`keepsNothing_experienceFree`).

## What the class states about its reward

`PaysAtGoals` is what fork F-A of `docs/mission-contract.md` asks a class to state: its whole reward
function. The reward read from the percept after a step is one when that step satisfies the member's
goal and zero when it does not, and it is zero at a visit's start. With it and `untilPaid`, every
agent earns on every attempt, across the counted members, exactly the number of them it solves
(`classReward_eq`). That is the class's reward lemma, obligation 16 of the mission contract, and it
holds of every agent, not only of the agents compared.

Why the aggregate is not the plain sum: a reward paid at every step that satisfies the goal pays an
agent again for each step it rests where the goal is satisfied, so two agents that solve the same
members can earn different sums, and the sum does not order agents as the count of members does.
`untilPaid` is the choice made here on the owner's behalf; the owner can overrule it.

## Contract 2 and the postcondition

For a class that conceals its goals, with a covering bound below the count of the counted members,
feasible goals and `PaysAtGoals`, the class in visits meets the record of contract 2 (`visits_big`).
Concealment is carried across visits by `AcornVerif.Kernel.Conceals.inVisits`. Success shows in the
reward: the reading that says whether the goal is met is whether the reward is one.

For an agent that separates and retains (`AcornVerif.Kernel.Separates`,
`AcornVerif.Kernel.Retains`), the class in visits meets the record of the postcondition
(`visits_achieves`).

## The mission from premises

`visits_mission` proves `Mission` of the rung from: the class's conditions above; `Finds` and
`Retains` of the agent; and contract 3's record of the agent's run in each member. `Finds` and
`Retains` are what remains of obligation 9, and are what the goal-information and exploration
premises of obligation 4 must deliver for an agent. Contract 3's record splits into the premises
`AcornVerif.Intent.MissionTheorem.MemoryBounded`, `WorkBounded`, `LearnsOnArrival` and
`KeepsDiscipline`, which name obligations 6 and 7. `visits_mission_allBut` is the statement under
fork F4, for a family of runs: where finding fails on at most one fraction of the runs and retaining
on at most another, the mission's statement holds of all but the sum of the fractions.

`retrace_mission` discharges every premise for the retracing agent with the reward as its signal,
on every such class whose counted members its exploring walks meet. So the statement is satisfiable
with fixed memory and the invariants of contract 3, on the kernel's own worlds. The agent's reports
to contract 3 are its own declaration, stated at `retraceRung`; that they describe its step is
argued there, not proved.
-/

namespace AcornVerif.MissionVisits
open Acorn.Features AcornVerif.Kernel
open AcornVerif.Intent AcornVerif.Intent.MissionTheorem

variable {interface : Interface}

/-! ## Reward and its aggregate -/

/-- The rewards of one attempt, summed up to and including the first step that pays. -/
def untilPaid : List ℚ → ℚ
  | [] => 0
  | reward :: rest => if 0 < reward then reward else reward + untilPaid rest

/-- Of rewards that are one at the steps a condition marks and zero elsewhere, the aggregate is one
when some step is marked and zero when none is. -/
theorem untilPaid_indicator {Time : Type} (times : List Time) (hit : Time → Bool) :
    untilPaid (times.map fun time => if hit time then (1 : ℚ) else 0) =
      if times.any hit then 1 else 0 := by
  induction times with
  | nil => rfl
  | cons head rest ih =>
    cases reached : hit head with
    | false => simp [untilPaid, reached, ih]
    | true => simp [untilPaid, reached]

/-- A sum of ones over the items a condition marks is the number of items it marks. -/
theorem sum_indicator {Item : Type} (items : List Item) (hit : Item → Bool) :
    (items.map fun item => if hit item then (1 : ℚ) else 0).sum =
      ((items.filter hit).length : ℚ) := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    cases reached : hit head with
    | false => simp [reached, ih]
    | true => simp [reached, ih, add_comm]

/-! ## Agents -/

/-- A kernel agent as an agent of the records: it is given the percept as its observation, with the
reward read from it, and answers as the kernel agent answers that percept. -/
def recordAgent (agent : Agent interface) :
    WorldInterface.Agent (Percept interface) (Act interface) where
  Memory := agent.Memory
  initial := agent.initial
  act := fun memory given => agent.act memory given.1

/-- An agent of the records over percepts and actions as a kernel agent: on a percept it answers as
it answers that percept with the reward `pay` reads from it. -/
def kernelAgent (pay : Percept interface → ℚ)
    (other : WorldInterface.Agent (Percept interface) (Act interface)) : Agent interface where
  Memory := other.Memory
  initial := other.initial
  act := fun memory percept => other.act memory (percept, pay percept)

/-- A kernel agent read as an agent of the records and back is itself. -/
theorem kernelAgent_recordAgent (pay : Percept interface → ℚ) (agent : Agent interface) :
    kernelAgent pay (recordAgent agent) = agent := rfl

/-- An agent of the records that keeps nothing of its experience is, as a kernel agent,
experience-free. -/
theorem keepsNothing_experienceFree (pay : Percept interface → ℚ)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (frozen : Postcondition.KeepsNothing other) : ExperienceFree (kernelAgent pay other) := by
  by_cases some : Nonempty (Percept interface)
  · obtain ⟨shown⟩ := some
    exact ⟨fun memory => (other.act memory (shown, pay shown)).2,
      fun memory percept => frozen memory _ _⟩
  · exact ⟨id, fun _ percept => absurd ⟨percept⟩ some⟩

/-! ## A member in visits -/

/-- A member of a class in visits, as the records read it: the member's world in visits of `length`
steps, with the percept as its observation and `pay` of the percept as its reward, and with its goal
met at a state that at least one step of a visit has reached and that `met` marks. -/
def visitMember (world : World interface) (start : world.State) (length : ℕ)
    (pay : Percept interface → ℚ) (met : world.State → Bool) :
    Postcondition.Member (Percept interface) (Act interface) where
  State := world.State × Fin (length + 1)
  start := visitStart world start length
  observe := fun state => world.percept state.1
  reward := fun state => pay (world.percept state.1)
  step := (visits world start length).step
  goal := fun state => decide (1 ≤ state.2.val) && met state.1

/-- The run the records compute with is the kernel's closed loop: an agent of the records in a
member in visits, and that agent as a kernel agent in the member's world in visits, are in the same
state with the same memory at every time. -/
theorem run_eq_loop (world : World interface) (start : world.State) (length : ℕ)
    (pay : Percept interface → ℚ) (met : world.State → Bool)
    (other : WorldInterface.Agent (Percept interface) (Act interface)) (time : ℕ) :
    (visitMember world start length pay met).run other time =
      loop (visits world start length) (kernelAgent pay other) (visitStart world start length)
        time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    exact congrArg (interact (visits world start length) (kernelAgent pay other)) ih

/-- What a member in visits gives an agent of the records at a time: the percept of the kernel's
closed loop at that time, with the reward read from it. -/
theorem given_eq (world : World interface) (start : world.State) (length : ℕ)
    (pay : Percept interface → ℚ) (met : world.State → Bool)
    (other : WorldInterface.Agent (Percept interface) (Act interface)) (time : ℕ) :
    BigClass.given (visitMember world start length pay met) other time =
      (perceptAt (visits world start length) (kernelAgent pay other)
          (visitStart world start length) time,
        pay (perceptAt (visits world start length) (kernelAgent pay other)
          (visitStart world start length) time)) := by
  unfold BigClass.given
  rw [run_eq_loop]
  rfl

/-! ## The class -/

/-- What a class states about its reward, as fork F-A of `docs/mission-contract.md` asks: `met`
marks the states that satisfy each member's goal; the reward `pay` reads from the percept after a
step is one when that step satisfies the member's goal and zero when it does not; and it is zero at
each member's start. -/
structure PaysAtGoals (family : WorldClass interface) (goals : family.Goals)
    (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool) : Prop where
  /-- `met` marks the states that satisfy a member's goal. -/
  reads : ∀ index state, met index state = true ↔ (goals index).satisfied state
  /-- After a step, the reward is one when the step satisfies the goal and zero when not. -/
  pays : ∀ index state action,
    pay ((family.world index).percept ((family.world index).step state action)) =
      if met index ((family.world index).step state action) then 1 else 0
  /-- At a member's start, the reward is zero. -/
  quiet : ∀ index, pay ((family.world index).percept (family.start index)) = 0

/-- A class of worlds in visits with one agent, as the records read it: each member in visits of
`length` steps, the members the comparison counts, attempts of a visit's `length + 1` decisions, the
rewards of an attempt aggregated by `untilPaid`, and the agent. -/
def visitsTrial (family : WorldClass interface) (length : ℕ) (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index) (agent : Agent interface) : Postcondition.Trial where
  Obs := Percept interface
  Act := Act interface
  Index := family.Index
  member := fun index =>
    visitMember (family.world index) (family.start index) length pay (met index)
  counted := counted
  length := length + 1
  total := untilPaid
  agent := recordAgent agent

section trial

variable (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
  (pay : Percept interface → ℚ)
  (met : (index : family.Index) → (family.world index).State → Bool)
  (counted : List family.Index) (agent : Agent interface)

/-- The state of an agent of the records' run in a member of the class is the state of the kernel's
closed loop of that agent in the member's world in visits. -/
theorem stateAt_eq (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (time : ℕ) :
    (visitsTrial family length pay met counted agent).stateAt other index time =
      stateAt (visits (family.world index) (family.start index) length) (kernelAgent pay other)
        (visitStart (family.world index) (family.start index) length) time :=
  congrArg Prod.fst
    (run_eq_loop (family.world index) (family.start index) length pay (met index) other time)

/-- Whether a member's goal is met at a time of a run, in the kernel's terms. -/
theorem goal_eq (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (time : ℕ) :
    ((visitsTrial family length pay met counted agent).member index).goal
        ((visitsTrial family length pay met counted agent).stateAt other index time) =
      (decide (1 ≤ (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) time).2.val) &&
        met index (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) time).1) :=
  congrArg
    (fun state : (family.world index).State × Fin (length + 1) =>
      decide (1 ≤ state.2.val) && met index state.1)
    (stateAt_eq family length pay met counted agent other index time)

/-- At step `step` of attempt `attempt`, a member's goal is met exactly when at least one step of
the visit has been taken and the state satisfies the member's goal. -/
theorem goal_iff (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (attempt step : ℕ) (within : step ≤ length) :
    ((visitsTrial family length pay met counted agent).member index).goal
        ((visitsTrial family length pay met counted agent).stateAt other index
          ((length + 1) * attempt + step)) = true ↔
      1 ≤ step ∧ (goals index).satisfied
        (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length)
          (attempt * (length + 1) + step)).1 := by
  rw [goal_eq, Nat.mul_comm, Bool.and_eq_true, decide_eq_true_iff,
    visits_counter _ _ _ _ attempt step within, stated.reads]

/-- **Solving, as the records count it, is solving on a visit.** An agent of the records solves a
member on an attempt exactly when, as a kernel agent, it solves that member on that visit. -/
theorem solves_iff (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (attempt : ℕ) :
    (visitsTrial family length pay met counted agent).solves other index attempt = true ↔
      SolvesOnVisit family goals length (kernelAgent pay other) attempt index := by
  unfold Postcondition.Trial.solves Postcondition.Trial.attemptTimes
  rw [List.any_eq_true]
  constructor
  · rintro ⟨time, listed, reached⟩
    obtain ⟨step, below, rfl⟩ := List.mem_map.mp listed
    have within : step ≤ length := Nat.le_of_lt_succ (List.mem_range.mp below)
    obtain ⟨low, satisfied⟩ :=
      (goal_iff family goals length pay met counted agent stated other index attempt step
        within).mp reached
    exact ⟨step, low, within, satisfied⟩
  · rintro ⟨step, low, high, satisfied⟩
    exact ⟨(length + 1) * attempt + step,
      List.mem_map.mpr ⟨step, List.mem_range.mpr (Nat.lt_succ_of_le high), rfl⟩,
      (goal_iff family goals length pay met counted agent stated other index attempt step
        high).mpr ⟨low, satisfied⟩⟩

/-! ## The reward lemma -/

/-- At every time of every run, a member's reward is one when its goal is met and zero when not. -/
theorem reward_eq (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (time : ℕ) :
    ((visitsTrial family length pay met counted agent).member index).reward
        ((visitsTrial family length pay met counted agent).stateAt other index time) =
      if ((visitsTrial family length pay met counted agent).member index).goal
        ((visitsTrial family length pay met counted agent).stateAt other index time)
      then 1 else 0 := by
  rw [goal_eq]
  have paid : ((visitsTrial family length pay met counted agent).member index).reward
        ((visitsTrial family length pay met counted agent).stateAt other index time) =
      pay ((family.world index).percept
        (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) time).1) :=
    congrArg (fun state : (family.world index).State × Fin (length + 1) =>
        pay ((family.world index).percept state.1))
      (stateAt_eq family length pay met counted agent other index time)
  rw [paid]
  rcases visits_shape (family.world index) (family.start index) length (kernelAgent pay other)
      time with ⟨zero, atStart⟩ | ⟨positive, before, action, stepped⟩
  · rw [atStart, stated.quiet, zero]
    rfl
  · rw [stepped, stated.pays, decide_eq_true positive, Bool.true_and]

/-- On every attempt, every agent earns in a member one when it solves the member on that attempt
and nothing when it does not. -/
theorem earned_eq (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (attempt : ℕ) :
    (visitsTrial family length pay met counted agent).earned other index attempt =
      if (visitsTrial family length pay met counted agent).solves other index attempt
      then 1 else 0 := by
  have rewards :
      (fun time => ((visitsTrial family length pay met counted agent).member index).reward
        ((visitsTrial family length pay met counted agent).stateAt other index time)) =
      fun time => if ((visitsTrial family length pay met counted agent).member index).goal
        ((visitsTrial family length pay met counted agent).stateAt other index time)
        then (1 : ℚ) else 0 :=
    funext (reward_eq family goals length pay met counted agent stated other index)
  unfold Postcondition.Trial.earned Postcondition.Trial.solves
  rw [rewards]
  exact untilPaid_indicator _ _

/-- **The class's reward lemma.** On every attempt, every agent earns across the counted members
exactly the number of them it solves on that attempt. So one agent earns more than another exactly
when it solves more members, for every two agents and every two attempts. -/
theorem classReward_eq (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface)) (attempt : ℕ) :
    (visitsTrial family length pay met counted agent).classReward other attempt =
      ((visitsTrial family length pay met counted agent).solvedCount other attempt : ℚ) := by
  have each :
      (fun index => (visitsTrial family length pay met counted agent).earned other index
        attempt) =
      fun index => if (visitsTrial family length pay met counted agent).solves other index
        attempt then (1 : ℚ) else 0 :=
    funext fun index =>
      earned_eq family goals length pay met counted agent stated other index attempt
  unfold Postcondition.Trial.classReward Postcondition.Trial.solvedCount
  rw [each]
  exact sum_indicator _ _

/-! ## Counting members solved -/

variable {reference : World interface} {origin : reference.State} {bound : ℕ}

/-- In a class that conceals its goals, with a covering bound for one visit's length, an agent that
keeps nothing of its experience solves at most the bound of the counted members on every
attempt. -/
theorem frozen_bound (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound) (distinct : counted.Nodup)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (frozen : Postcondition.KeepsNothing other) (attempt : ℕ) :
    (visitsTrial family length pay met counted agent).solvedCount other attempt ≤ bound := by
  classical
  have each : ∀ index ∈ (counted.filter fun index =>
        (visitsTrial family length pay met counted agent).solves other index attempt).toFinset,
      SolvesOnVisit family goals length (kernelAgent pay other) attempt index :=
    fun index inside =>
      (solves_iff family goals length pay met counted agent stated other index attempt).mp
        (List.mem_filter.mp (List.mem_toFinset.mp inside)).2
  have few := visits_need hidden covered (keepsNothing_experienceFree pay other frozen) attempt _
    each
  have card := List.toFinset_card_of_nodup (distinct.filter fun index : family.Index =>
    (visitsTrial family length pay met counted agent).solves other index attempt)
  exact le_trans (le_of_eq card.symm) few

/-- An agent that separates solves, on some attempt, more of the counted members than the bound. -/
theorem count_of_separates (stated : PaysAtGoals family goals pay met)
    (separates : Separates family goals length bound counted agent) :
    ∃ attempt, bound <
      (visitsTrial family length pay met counted agent).solvedCount (recordAgent agent)
        attempt := by
  classical
  obtain ⟨visit, solved, many, each⟩ := separates
  refine ⟨visit, Nat.lt_of_lt_of_le many ?_⟩
  have inside : solved ⊆ (counted.filter fun index =>
      (visitsTrial family length pay met counted agent).solves (recordAgent agent) index
        visit).toFinset :=
    fun index member => List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(each index member).1,
      (solves_iff family goals length pay met counted agent stated (recordAgent agent) index
        visit).mpr (each index member).2⟩)
  exact le_trans (Finset.card_le_card inside) (List.toFinset_card_le _)

/-! ## Contract 2 -/

/-- Every attempt of every agent's run in a member starts from the start of a visit. -/
theorem visits_attemptsRecur :
    BigClass.attemptsRecur.holds (visitsTrial family length pay met counted agent) :=
  fun (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) attempt => by
    change (visitsTrial family length pay met counted agent).stateAt other index
      ((length + 1) * attempt) = visitStart (family.world index) (family.start index) length
    rw [stateAt_eq, Nat.mul_comm]
    exact visits_period _ _ _ _ attempt

/-- Condition (a): where every member's goal is feasible within a visit, it can be reached within
an attempt from the state every attempt starts in. -/
theorem visits_goalsReachable (stated : PaysAtGoals family goals pay met)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index)) :
    BigClass.goalsReachable.holds (visitsTrial family length pay met counted agent) :=
  fun (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) attempt => by
    obtain ⟨actions, low, high, reached⟩ := (feasible_iff_list _ _).mp (feasible index)
    have fits : actions.length ≤ length := high
    refine ⟨actions, Nat.lt_succ_of_le fits, ?_⟩
    rw [visits_attemptsRecur family length pay met counted agent other index attempt]
    change (decide (1 ≤ (actions.foldl
        (visits (family.world index) (family.start index) length).step
        (family.start index, (⟨0, Nat.succ_pos length⟩ : Fin (length + 1)))).2.val) &&
      met index (actions.foldl (visits (family.world index) (family.start index) length).step
        (family.start index, (⟨0, Nat.succ_pos length⟩ : Fin (length + 1)))).1) = true
    rw [visits_foldl (family.world index) (family.start index) length actions (family.start index)
      ⟨0, Nat.succ_pos length⟩ (by rw [Nat.zero_add]; exact fits),
      Bool.and_eq_true, decide_eq_true_iff, stated.reads]
    refine ⟨?_, reached⟩
    change 1 ≤ 0 + actions.length
    omega

/-- Condition (b): a class that conceals its goals behind a reference world gives every agent, in
every member, what the reference world in visits gives it, until that member's goal is first met on
any attempt. -/
theorem visits_goalsConcealed (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin) :
    BigClass.goalsConcealed.holds (visitsTrial family length pay met counted agent) := by
  refine ⟨visitMember reference origin length pay (fun _ => false),
    fun (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) time unmet => ?_⟩
  have never : ∀ earlier, 1 ≤ earlier → earlier ≤ time →
      ¬ (visitsGoals goals length index).satisfied
        (stateAt ((family.inVisits length).world index) (kernelAgent pay other)
          ((family.inVisits length).start index) earlier) := by
    intro earlier _ within reached
    have off := unmet earlier within
    rw [goal_eq] at off
    have on : (decide (1 ≤ (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) earlier).2.val) &&
        met index (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) earlier).1) = true := by
      rw [Bool.and_eq_true, decide_eq_true_iff, stated.reads]
      exact reached
    rw [on] at off
    exact Bool.noConfusion off
  have percept := (hidden.inVisits length).perceptAt_eq (kernelAgent pay other) index time never
    ((hidden.inVisits length).agree_before (kernelAgent pay other) index time never).2
  change BigClass.given
      (visitMember (family.world index) (family.start index) length pay (met index)) other time =
    BigClass.given (visitMember reference origin length pay fun _ => false) other time
  rw [given_eq, given_eq]
  exact congrArg (fun shown => (shown, pay shown)) percept

/-- Condition (c): in a class that conceals its goals, with a covering bound below the count of the
counted members, an agent that keeps nothing of its experience solves at most the bound of them on
every attempt. -/
theorem visits_frozenShareSmall (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound) (distinct : counted.Nodup)
    (many : bound < counted.length) :
    BigClass.frozenShareSmall.holds (visitsTrial family length pay met counted agent) :=
  ⟨bound, many, fun (other : WorldInterface.Agent (Percept interface) (Act interface)) frozen
      attempt =>
    frozen_bound family goals length pay met counted agent stated hidden covered distinct other
      frozen attempt⟩

/-- Success shows in the reward: at every time of every run, the reward a member gives is one
exactly when its goal is met then. -/
theorem visits_successShows (stated : PaysAtGoals family goals pay met) :
    BigClass.successShows.holds (visitsTrial family length pay met counted agent) := by
  refine ⟨fun given => decide (given.2 = 1),
    fun (other : WorldInterface.Agent (Percept interface) (Act interface))
      (index : family.Index) time => ?_⟩
  change decide (((visitsTrial family length pay met counted agent).member index).reward
      ((visitsTrial family length pay met counted agent).stateAt other index time) = 1) =
    ((visitsTrial family length pay met counted agent).member index).goal
      ((visitsTrial family length pay met counted agent).stateAt other index time)
  rw [reward_eq family goals length pay met counted agent stated other index time]
  cases ((visitsTrial family length pay met counted agent).member index).goal
    ((visitsTrial family length pay met counted agent).stateAt other index time) <;> simp

/-- **A class in visits is big, as contract 2's record says.** A class that conceals its goals, with
a covering bound for one visit's length below the count of its counted members, goals feasible
within a visit and a reward that pays at its goals, meets the record of contract 2 when it is run in
visits, with every agent. -/
theorem visits_big (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) (many : bound < counted.length) :
    BigClass.bigClass.Meets (visitsTrial family length pay met counted agent) :=
  BigClass.bigClass_meets.mpr
    ⟨visits_goalsReachable family goals length pay met counted agent stated feasible,
      visits_goalsConcealed family goals length pay met counted agent stated hidden,
      visits_frozenShareSmall family goals length pay met counted agent stated hidden covered
        distinct many,
      visits_successShows family goals length pay met counted agent stated,
      visits_attemptsRecur family length pay met counted agent⟩

/-! ## The postcondition -/

/-- **An agent that separates and retains achieves goals, as the postcondition's record says.** In a
class that conceals its goals, with a covering bound for one visit's length and a reward that pays
at its goals, the class in visits with an agent that separates from that bound and retains meets the
record of the postcondition. -/
theorem visits_achieves (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound) (distinct : counted.Nodup)
    (separates : Separates family goals length bound counted agent)
    (retains : Retains family goals length agent) :
    Postcondition.postcondition.Meets (visitsTrial family length pay met counted agent) := by
  have kept : ∀ index attempt later, attempt ≤ later →
      (visitsTrial family length pay met counted agent).solves (recordAgent agent) index
        attempt = true →
      (visitsTrial family length pay met counted agent).solves (recordAgent agent) index
        later = true := by
    intro index attempt later order solved
    rcases Nat.lt_or_eq_of_le order with sooner | same
    · exact (solves_iff family goals length pay met counted agent stated (recordAgent agent)
        index later).mpr (retains index attempt later sooner
          ((solves_iff family goals length pay met counted agent stated (recordAgent agent)
            index attempt).mp solved))
    · rw [← same]
      exact solved
  refine Postcondition.postcondition_meets.mpr
    ⟨fun (first second : WorldInterface.Agent (Percept interface) (Act interface)) _ _ attempt
        other => ?_, ?_,
      fun (index : family.Index) attempt later order _ solved =>
        kept index attempt later order solved,
      fun (index : family.Index) attempt later order _ solved =>
        ⟨later, Nat.le_refl later, kept index attempt later order solved⟩⟩
  · rw [classReward_eq family goals length pay met counted agent stated,
      classReward_eq family goals length pay met counted agent stated]
    exact Nat.cast_lt
  · obtain ⟨attempt, more⟩ :=
      count_of_separates family goals length pay met counted agent stated separates
    refine ⟨attempt, fun (other : WorldInterface.Agent (Percept interface) (Act interface))
      frozen later => ?_⟩
    change (visitsTrial family length pay met counted agent).classReward other later <
      (visitsTrial family length pay met counted agent).classReward (recordAgent agent) attempt
    rw [classReward_eq family goals length pay met counted agent stated,
      classReward_eq family goals length pay met counted agent stated]
    exact Nat.cast_lt.mpr (Nat.lt_of_le_of_lt
      (frozen_bound family goals length pay met counted agent stated hidden covered distinct
        other frozen later) more)

end trial

/-! ## The mission from premises -/

/-- The rung of a class of worlds in visits and an agent, with what the agent reports of its own
steps. -/
def visitsRung (family : WorldClass interface) (length : ℕ) (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index) (agent : Agent interface)
    (updates : agent.Memory → Percept interface × ℚ → List OneStream.Update)
    (work : agent.Memory → Percept interface × ℚ → ℕ) (resume : agent.Memory → agent.Memory) :
    Rung where
  toTrial := visitsTrial family length pay met counted agent
  updates := updates
  work := work
  resume := resume

section mission

variable {family : WorldClass interface} {goals : family.Goals} {length bound : ℕ}
  {pay : Percept interface → ℚ}
  {met : (index : family.Index) → (family.world index).State → Bool}
  {counted : List family.Index} {reference : World interface} {origin : reference.State}

/-- **The mission theorem on a class in visits, from its premises.** Take a class that conceals its
goals, with a covering bound for one visit's length below the count of its counted members, goals
feasible within a visit and a reward that pays at its goals. An agent that finds more of the counted
members than the bound and retains what it has solved, and whose run in every member meets contract
3's record under its reports, achieves goals over the class in visits: the mission's statement holds
of the rung. -/
theorem visits_mission (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) (many : bound < counted.length) {agent : Agent interface}
    {updates : agent.Memory → Percept interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept interface × ℚ → ℕ} {resume : agent.Memory → agent.Memory}
    (finds : Finds family goals length bound counted agent)
    (retains : Retains family goals length agent)
    (stream : ∀ index, OneStream.oneStream.Meets
      ((visitsRung family length pay met counted agent updates work resume).learner index)) :
    Mission (visitsRung family length pay met counted agent updates work resume) :=
  Mission.of_records
    (visits_big family goals length pay met counted agent stated hidden covered feasible distinct
      many)
    stream
    (visits_achieves family goals length pay met counted agent stated hidden covered distinct
      (separates_of_finds finds retains) retains)

/-- **The mission theorem on a class in visits, for all but a fraction of runs.** For a family of
runs, each with its agent and that agent's reports, on a class as in `visits_mission`: where the
agents of all but a fraction `left` of the runs find, the agents of all but a fraction `right`
retain, and every run's agent meets contract 3's record in every member, the mission's statement
holds of all but the fraction `left + right` of the runs. This is the form the statement takes under
fork F4 of `docs/mission-contract.md`. -/
theorem visits_mission_allBut (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) (many : bound < counted.length) {Run : Type}
    (runs : Finset Run) (agent : Run → Agent interface)
    (updates : (run : Run) → (agent run).Memory → Percept interface × ℚ → List OneStream.Update)
    (work : (run : Run) → (agent run).Memory → Percept interface × ℚ → ℕ)
    (resume : (run : Run) → (agent run).Memory → (agent run).Memory) (left right : ℚ)
    (finds : AllBut left runs fun run => Finds family goals length bound counted (agent run))
    (retains : AllBut right runs fun run => Retains family goals length (agent run))
    (stream : ∀ run ∈ runs, ∀ index, OneStream.oneStream.Meets
      ((visitsRung family length pay met counted (agent run) (updates run) (work run)
        (resume run)).learner index)) :
    AllBut (left + right) runs fun run =>
      Mission (visitsRung family length pay met counted (agent run) (updates run) (work run)
        (resume run)) :=
  (finds.and retains).mono fun run member both =>
    visits_mission stated hidden covered feasible distinct many both.1 both.2 (stream run member)

/-! ## The retracing agent meets the statement -/

/-- The reward as a signal: whether the reward read from a percept is one. -/
def paid (pay : Percept interface → ℚ) (percept : Percept interface) : Bool :=
  decide (pay percept = 1)

/-- In a class whose reward pays at its goals, the percept after every step shows the reward's
signal exactly when that step satisfies the member's goal. -/
theorem paid_decodes (stated : PaysAtGoals family goals pay met) (index : family.Index)
    (state : (family.world index).State) (action : Act interface) :
    paid pay ((family.world index).percept ((family.world index).step state action)) = true ↔
      (goals index).satisfied ((family.world index).step state action) := by
  unfold paid
  rw [decide_eq_true_iff, stated.pays, ← stated.reads]
  cases met index ((family.world index).step state action) <;> simp

/-- The rung of a class in visits and the retracing agent with the reward as its signal. The agent
reports, at every step, one learning update on the experience the step was given, one other update,
and two units of work, and it resumes with the memory it held.

That the reports describe its step is argued, not proved. Its step reads the reward of the percept
it is given and, the first time that reward shows the goal met, keeps the count of the walk it is
on: a learning update on the experience of that step, which uses its count of visits beside it. It
then advances its two counts: one other update. It plans with no model. It sets no part of its
memory back to its first value except the count of a visit's steps, which is a cyclic count and
discards nothing. -/
def retraceRung (family : WorldClass interface) (length last : ℕ) (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index) (explore : ℕ → ℕ → Act interface) : Rung :=
  visitsRung family length pay met counted (retrace interface length last (paid pay) explore)
    (fun _ _ => [.learn (.stream 0), .other]) (fun _ _ => 2) id

/-- **The mission's statement is satisfiable on a class in visits.** Take a class that conceals its
goals, with a covering bound for one visit's length below the count of its counted members, goals
feasible within a visit and a reward that pays at its goals. If, for each counted member, one of the
exploring walks of the visits up to `last` meets that member's goal from its start within a visit,
the retracing agent with the reward as its signal achieves goals over the class: the mission's
statement holds of its rung, with every premise discharged. -/
theorem retrace_mission (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) (many : bound < counted.length) (last : ℕ)
    (explore : ℕ → ℕ → Act interface)
    (explored : ∀ index ∈ counted, ∃ visit, visit ≤ last ∧
      ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
        (path (family.world index) (family.start index) (explore visit) step)) :
    Mission (retraceRung family length last pay met counted explore) :=
  visits_mission stated hidden covered feasible distinct many
    (retrace_finds family goals length last bound (paid pay) explore (paid_decodes stated) counted
      distinct many explored)
    (retrace_retains family goals length last (paid pay) explore (paid_decodes stated))
    (fun _ => OneStream.learner_meets _ _ _ _ _
      (fun _ _ datum listed => by
        rcases List.mem_cons.mp listed with first | second
        · exact OneStream.Update.learn.inj first
        · exact nomatch List.mem_singleton.mp second)
      ⟨2, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ (retraceMemory_finite length last)
      (.inl fun _ _ => ⟨_, List.mem_cons_self⟩)
      (.inr fun _ _ listed => by
        rcases List.mem_cons.mp listed with first | second
        · exact nomatch first
        · exact nomatch List.mem_singleton.mp second)
      (fun _ _ listed => by
        rcases List.mem_cons.mp listed with first | second
        · exact nomatch first
        · exact nomatch List.mem_singleton.mp second)
      fun _ => rfl)

end mission

end AcornVerif.MissionVisits
