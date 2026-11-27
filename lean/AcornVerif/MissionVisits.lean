import AcornVerif.Intent.MissionTheorem
import AcornVerif.Retrace
import AcornVerif.VisitsClass
import Mathlib.Tactic.NormNum

namespace AcornVerif.MissionVisits
open Acorn.Features AcornVerif.Kernel
open AcornVerif.Intent AcornVerif.Intent.MissionTheorem

variable {interface : Interface}

def untilPaid : List ℚ → ℚ
  | [] => 0
  | reward :: rest => if 0 < reward then reward else reward + untilPaid rest

theorem untilPaid_indicator {Time : Type} (times : List Time) (hit : Time → Bool) :
    untilPaid (times.map fun time => if hit time then (1 : ℚ) else 0) =
      if times.any hit then 1 else 0 := by
  induction times with
  | nil => rfl
  | cons head rest ih =>
    cases reached : hit head with
    | false => simp [untilPaid, reached, ih]
    | true => simp [untilPaid, reached]

theorem sum_indicator {Item : Type} (items : List Item) (hit : Item → Bool) :
    (items.map fun item => if hit item then (1 : ℚ) else 0).sum =
      ((items.filter hit).length : ℚ) := by
  induction items with
  | nil => simp
  | cons head rest ih =>
    cases reached : hit head with
    | false => simp [reached, ih]
    | true => simp [reached, ih, add_comm]

def recordAgent (agent : Agent interface) :
    WorldInterface.Agent (Percept interface) (Act interface) where
  Memory := agent.Memory
  initial := agent.initial
  act := fun memory given => agent.act memory given.1

def kernelAgent (pay : Percept interface → ℚ)
    (other : WorldInterface.Agent (Percept interface) (Act interface)) : Agent interface where
  Memory := other.Memory
  initial := other.initial
  act := fun memory percept => other.act memory (percept, pay percept)

theorem kernelAgent_recordAgent (pay : Percept interface → ℚ) (agent : Agent interface) :
    kernelAgent pay (recordAgent agent) = agent := rfl

theorem keepsNothing_experienceFree (pay : Percept interface → ℚ)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (frozen : Postcondition.KeepsNothing other) : ExperienceFree (kernelAgent pay other) := by
  by_cases some : Nonempty (Percept interface)
  · obtain ⟨shown⟩ := some
    exact ⟨fun memory => (other.act memory (shown, pay shown)).2,
      fun memory percept => frozen memory _ _⟩
  · exact ⟨id, fun _ percept => absurd ⟨percept⟩ some⟩

def visitMember (world : World interface) (start : world.State) (length : ℕ)
    (pay : Percept interface → ℚ) (met : world.State → Bool) :
    Postcondition.Member (Percept interface) (Act interface) where
  State := world.State × Fin (length + 1)
  start := visitStart world start length
  observe := fun state => world.percept state.1
  reward := fun state => pay (world.percept state.1)
  step := (visits world start length).step
  goal := fun state => decide (1 ≤ state.2.val) && met state.1

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

structure PaysAtGoals (family : WorldClass interface) (goals : family.Goals)
    (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool) : Prop where
  reads : ∀ index state, met index state = true ↔ (goals index).satisfied state
  pays : ∀ index state action,
    pay ((family.world index).percept ((family.world index).step state action)) =
      if met index ((family.world index).step state action) then 1 else 0
  quiet : ∀ index, pay ((family.world index).percept (family.start index)) = 0

def visitsTrial (family : WorldClass interface) (length horizon lapses : ℕ)
    (pay : Percept interface → ℚ)
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
  horizon := horizon
  lapses := lapses
  agent := recordAgent agent

section trial

variable (family : WorldClass interface) (goals : family.Goals) (length horizon lapses : ℕ)
  (pay : Percept interface → ℚ)
  (met : (index : family.Index) → (family.world index).State → Bool)
  (counted : List family.Index) (agent : Agent interface)

theorem stateAt_eq (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (time : ℕ) :
    (visitsTrial family length horizon lapses pay met counted agent).stateAt other index time =
      stateAt (visits (family.world index) (family.start index) length) (kernelAgent pay other)
        (visitStart (family.world index) (family.start index) length) time :=
  congrArg Prod.fst
    (run_eq_loop (family.world index) (family.start index) length pay (met index) other time)

theorem goal_eq (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (time : ℕ) :
    ((visitsTrial family length horizon lapses pay met counted agent).member index).goal
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
            time) =
      (decide (1 ≤ (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) time).2.val) &&
        met index (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) time).1) :=
  congrArg
    (fun state : (family.world index).State × Fin (length + 1) =>
      decide (1 ≤ state.2.val) && met index state.1)
    (stateAt_eq family length horizon lapses pay met counted agent other index time)

theorem goal_iff (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (attempt step : ℕ) (within : step ≤ length) :
    ((visitsTrial family length horizon lapses pay met counted agent).member index).goal
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
          ((length + 1) * attempt + step)) = true ↔
      1 ≤ step ∧ (goals index).satisfied
        (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length)
          (attempt * (length + 1) + step)).1 := by
  rw [goal_eq, Nat.mul_comm, Bool.and_eq_true, decide_eq_true_iff,
    visits_counter _ _ _ _ attempt step within, stated.reads]

theorem solves_iff (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (attempt : ℕ) :
    (visitsTrial family length horizon lapses pay met counted agent).solves other index attempt =
        true ↔
      SolvesOnVisit family goals length (kernelAgent pay other) attempt index := by
  unfold Postcondition.Trial.solves Postcondition.Trial.attemptTimes
  rw [List.any_eq_true]
  constructor
  · rintro ⟨time, listed, reached⟩
    obtain ⟨step, below, rfl⟩ := List.mem_map.mp listed
    have within : step ≤ length := Nat.le_of_lt_succ (List.mem_range.mp below)
    obtain ⟨low, satisfied⟩ :=
      (goal_iff family goals length horizon lapses pay met counted agent stated other index attempt
          step
        within).mp reached
    exact ⟨step, low, within, satisfied⟩
  · rintro ⟨step, low, high, satisfied⟩
    exact ⟨(length + 1) * attempt + step,
      List.mem_map.mpr ⟨step, List.mem_range.mpr (Nat.lt_succ_of_le high), rfl⟩,
      (goal_iff family goals length horizon lapses pay met counted agent stated other index attempt
          step
        high).mpr ⟨low, satisfied⟩⟩

theorem reward_eq (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (time : ℕ) :
    ((visitsTrial family length horizon lapses pay met counted agent).member index).reward
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
            time) =
      if ((visitsTrial family length horizon lapses pay met counted agent).member index).goal
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index time)
      then 1 else 0 := by
  rw [goal_eq]
  have paid : ((visitsTrial family length horizon lapses pay met counted agent).member index).reward
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
            time) =
      pay ((family.world index).percept
        (stateAt (visits (family.world index) (family.start index) length)
          (kernelAgent pay other)
          (visitStart (family.world index) (family.start index) length) time).1) :=
    congrArg (fun state : (family.world index).State × Fin (length + 1) =>
        pay ((family.world index).percept state.1))
      (stateAt_eq family length horizon lapses pay met counted agent other index time)
  rw [paid]
  rcases visits_shape (family.world index) (family.start index) length (kernelAgent pay other)
      time with ⟨zero, atStart⟩ | ⟨positive, before, action, stepped⟩
  · rw [atStart, stated.quiet, zero]
    rfl
  · rw [stepped, stated.pays, decide_eq_true positive, Bool.true_and]

theorem earned_eq (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (attempt : ℕ) :
    (visitsTrial family length horizon lapses pay met counted agent).earned other index attempt =
      if (visitsTrial family length horizon lapses pay met counted agent).solves other index attempt
      then 1 else 0 := by
  have rewards :
      (fun time => ((visitsTrial family length horizon lapses pay met counted agent).member
          index).reward
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
            time)) =
      fun time => if ((visitsTrial family length horizon lapses pay met counted agent).member
          index).goal
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index time)
        then (1 : ℚ) else 0 :=
    funext (reward_eq family goals length horizon lapses pay met counted agent stated other index)
  unfold Postcondition.Trial.earned Postcondition.Trial.solves
  rw [rewards]
  exact untilPaid_indicator _ _

theorem classReward_eq (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface)) (attempt : ℕ) :
    (visitsTrial family length horizon lapses pay met counted agent).classReward other attempt =
      ((visitsTrial family length horizon lapses pay met counted agent).solvedCount other attempt :
          ℚ) := by
  have each :
      (fun index => (visitsTrial family length horizon lapses pay met counted agent).earned other
          index
        attempt) =
      fun index => if (visitsTrial family length horizon lapses pay met counted agent).solves other
          index
        attempt then (1 : ℚ) else 0 :=
    funext fun index =>
      earned_eq family goals length horizon lapses pay met counted agent stated other index attempt
  unfold Postcondition.Trial.classReward Postcondition.Trial.solvedCount
  rw [each]
  exact sum_indicator _ _

theorem rewards_sum (stated : PaysAtGoals family goals pay met)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) (attempt : ℕ) :
    (((visitsTrial family length horizon lapses pay met counted agent).attemptTimes attempt).map
        fun time =>
        ((visitsTrial family length horizon lapses pay met counted agent).member index).reward
          ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
              time)).sum =
      ((((visitsTrial family length horizon lapses pay met counted agent).attemptTimes
          attempt).filter
        fun time => ((visitsTrial family length horizon lapses pay met counted agent).member
            index).goal
          ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
              time)).length :
        ℚ) := by
  have rewards :
      (fun time => ((visitsTrial family length horizon lapses pay met counted agent).member
          index).reward
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index
            time)) =
      fun time => if ((visitsTrial family length horizon lapses pay met counted agent).member
          index).goal
        ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index time)
        then (1 : ℚ) else 0 :=
    funext (reward_eq family goals length horizon lapses pay met counted agent stated other index)
  rw [rewards]
  exact sum_indicator _ _

variable {reference : World interface} {origin : reference.State} {bound : ℕ}

theorem frozen_bound (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound) (distinct : counted.Nodup)
    (other : WorldInterface.Agent (Percept interface) (Act interface))
    (frozen : Postcondition.KeepsNothing other) (attempt : ℕ) :
    (visitsTrial family length horizon lapses pay met counted agent).solvedCount other attempt ≤
        bound := by
  classical
  have each : ∀ index ∈ (counted.filter fun index =>
        (visitsTrial family length horizon lapses pay met counted agent).solves other index
            attempt).toFinset,
      SolvesOnVisit family goals length (kernelAgent pay other) attempt index :=
    fun index inside =>
      (solves_iff family goals length horizon lapses pay met counted agent stated other index
          attempt).mp
        (List.mem_filter.mp (List.mem_toFinset.mp inside)).2
  have few := visits_need hidden covered (keepsNothing_experienceFree pay other frozen) attempt _
    each
  have card := List.toFinset_card_of_nodup (distinct.filter fun index : family.Index =>
    (visitsTrial family length horizon lapses pay met counted agent).solves other index attempt)
  exact le_trans (le_of_eq card.symm) few

theorem count_of_separates (stated : PaysAtGoals family goals pay met) {limit : ℕ}
    (separates : SeparatesBy family goals length bound counted limit agent) :
    ∃ attempt, attempt < limit ∧ bound <
      (visitsTrial family length horizon lapses pay met counted agent).solvedCount (recordAgent
          agent)
        attempt := by
  classical
  obtain ⟨visit, solved, early, many, each⟩ := separates
  refine ⟨visit, early, Nat.lt_of_lt_of_le many ?_⟩
  have inside : solved ⊆ (counted.filter fun index =>
      (visitsTrial family length horizon lapses pay met counted agent).solves (recordAgent agent)
          index
        visit).toFinset :=
    fun index member => List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(each index member).1,
      (solves_iff family goals length horizon lapses pay met counted agent stated (recordAgent
          agent) index
        visit).mpr (each index member).2⟩)
  exact le_trans (Finset.card_le_card inside) (List.toFinset_card_le _)

theorem visits_attemptsRecur :
    BigClass.attemptsRecur.holds (visitsTrial family length horizon lapses pay met counted agent) :=
  fun (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) attempt => by
    change (visitsTrial family length horizon lapses pay met counted agent).stateAt other index
      ((length + 1) * attempt) = visitStart (family.world index) (family.start index) length
    rw [stateAt_eq, Nat.mul_comm]
    exact visits_period _ _ _ _ attempt

theorem visits_goalsReachable (stated : PaysAtGoals family goals pay met)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index)) :
    BigClass.goalsReachable.holds (visitsTrial family length horizon lapses pay met counted
        agent) :=
  fun (other : WorldInterface.Agent (Percept interface) (Act interface))
    (index : family.Index) attempt => by
    obtain ⟨actions, low, high, reached⟩ := (feasible_iff_list _ _).mp (feasible index)
    have fits : actions.length ≤ length := high
    refine ⟨actions, Nat.lt_succ_of_le fits, ?_⟩
    rw [visits_attemptsRecur family length horizon lapses pay met counted agent other index attempt]
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

theorem visits_goalsConcealed (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin) :
    BigClass.goalsConcealed.holds (visitsTrial family length horizon lapses pay met counted
        agent) := by
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

theorem visits_frozenShareSmall (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound) (distinct : counted.Nodup)
    (many : bound < counted.length) :
    BigClass.frozenShareSmall.holds (visitsTrial family length horizon lapses pay met counted
        agent) :=
  ⟨bound, many, fun (other : WorldInterface.Agent (Percept interface) (Act interface)) frozen
      attempt =>
    frozen_bound family goals length horizon lapses pay met counted agent stated hidden covered
        distinct other
      frozen attempt⟩

theorem visits_successShows (stated : PaysAtGoals family goals pay met) :
    BigClass.successShows.holds (visitsTrial family length horizon lapses pay met counted
        agent) := by
  refine ⟨fun given => decide (given.2 = 1),
    fun (other : WorldInterface.Agent (Percept interface) (Act interface))
      (index : family.Index) time => ?_⟩
  change decide (((visitsTrial family length horizon lapses pay met counted agent).member
      index).reward
      ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index time) =
          1) =
    ((visitsTrial family length horizon lapses pay met counted agent).member index).goal
      ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index time)
  rw [reward_eq family goals length horizon lapses pay met counted agent stated other index time]
  cases ((visitsTrial family length horizon lapses pay met counted agent).member index).goal
    ((visitsTrial family length horizon lapses pay met counted agent).stateAt other index time) <;>
        simp

theorem visits_big (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) (many : bound < counted.length) :
    BigClass.bigClass.Meets (visitsTrial family length horizon lapses pay met counted agent) :=
  BigClass.bigClass_meets.mpr
    ⟨visits_goalsReachable family goals length horizon lapses pay met counted agent stated feasible,
      visits_goalsConcealed family goals length horizon lapses pay met counted agent stated hidden,
      visits_frozenShareSmall family goals length horizon lapses pay met counted agent stated hidden
          covered
        distinct many,
      visits_successShows family goals length horizon lapses pay met counted agent stated,
      visits_attemptsRecur family length horizon lapses pay met counted agent⟩

theorem visits_achieves (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound) (distinct : counted.Nodup)
    {limit : ℕ} (separates : SeparatesBy family goals length bound counted limit agent)
    (room : limit + lapses < horizon)
    (retains : RetainsBut family goals length horizon lapses agent) :
    Postcondition.postcondition.Meets
      (visitsTrial family length horizon lapses pay met counted agent) := by
  refine Postcondition.postcondition_meets.mpr
    ⟨fun (first second : WorldInterface.Agent (Percept interface) (Act interface)) _ _ attempt
        other => ?_, ?_,
      fun (index : family.Index) => ?_,
      fun (index : family.Index) attempt later order room _ solved => ?_⟩
  · rw [classReward_eq family goals length horizon lapses pay met counted agent stated,
      classReward_eq family goals length horizon lapses pay met counted agent stated]
    exact Nat.cast_lt
  · obtain ⟨attempt, early, more⟩ :=
      count_of_separates family goals length horizon lapses pay met counted agent stated separates
    refine ⟨attempt, show attempt + lapses + 1 < horizon by omega,
      fun (other : WorldInterface.Agent (Percept interface) (Act interface)) frozen later => ?_⟩
    change (visitsTrial family length horizon lapses pay met counted agent).classReward other
        later <
      (visitsTrial family length horizon lapses pay met counted agent).classReward (recordAgent
          agent) attempt
    rw [classReward_eq family goals length horizon lapses pay met counted agent stated,
      classReward_eq family goals length horizon lapses pay met counted agent stated]
    exact Nat.cast_lt.mpr (Nat.lt_of_le_of_lt
      (frozen_bound family goals length horizon lapses pay met counted agent stated hidden
        covered distinct other frozen later) more)
  · obtain ⟨lapsed, count, keeps⟩ := retains index
    refine ⟨lapsed.toList, by rw [Finset.length_toList]; exact count,
      fun attempt later order before _ solved out => ?_⟩
    rcases Nat.lt_or_eq_of_le order with sooner | same
    · exact (solves_iff family goals length horizon lapses pay met counted agent stated
        (recordAgent agent) index later).mpr (keeps attempt later sooner before
          ((solves_iff family goals length horizon lapses pay met counted agent stated
            (recordAgent agent) index attempt).mp solved)
          (fun inside => out (Finset.mem_toList.mpr inside)))
    · rw [← same]
      exact solved
  · obtain ⟨again, low, high, once⟩ := retains.again index attempt later order room
      ((solves_iff family goals length horizon lapses pay met counted agent stated
        (recordAgent agent) index attempt).mp solved)
    exact ⟨again, low, high,
      (solves_iff family goals length horizon lapses pay met counted agent stated
        (recordAgent agent) index again).mpr once⟩

end trial

def visitsRung (family : WorldClass interface) (length horizon lapses : ℕ)
    (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index) (agent : Agent interface)
    (updates : agent.Memory → Percept interface × ℚ → List OneStream.Update)
    (work : agent.Memory → Percept interface × ℚ → ℕ) (resume : agent.Memory → agent.Memory) :
    Rung where
  toTrial := visitsTrial family length horizon lapses pay met counted agent
  updates := updates
  work := work
  resume := resume

section mission

variable {family : WorldClass interface} {goals : family.Goals}
  {length horizon lapses bound : ℕ} {pay : Percept interface → ℚ}
  {met : (index : family.Index) → (family.world index).State → Bool}
  {counted : List family.Index} {reference : World interface} {origin : reference.State}

theorem visits_mission (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) {agent : Agent interface}
    {updates : agent.Memory → Percept interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept interface × ℚ → ℕ} {resume : agent.Memory → agent.Memory}
    {limit : ℕ} (separates : SeparatesBy family goals length bound counted limit agent)
    (room : limit + lapses < horizon)
    (retains : RetainsBut family goals length horizon lapses agent)
    (stream : ∀ index, OneStream.oneStream.Meets
      ((visitsRung family length horizon lapses pay met counted agent updates work
        resume).learner index)) :
    Mission (visitsRung family length horizon lapses pay met counted agent updates work resume) :=
  Mission.of_records
    (visits_big family goals length horizon lapses pay met counted agent stated hidden covered
      feasible distinct separates.separates.finds.many)
    stream
    (visits_achieves family goals length horizon lapses pay met counted agent stated hidden
      covered distinct separates room retains)

theorem visits_mission_allBut (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) {Run : Type}
    (runs : Finset Run) (agent : Run → Agent interface)
    (updates : (run : Run) → (agent run).Memory → Percept interface × ℚ → List OneStream.Update)
    (work : (run : Run) → (agent run).Memory → Percept interface × ℚ → ℕ)
    (resume : (run : Run) → (agent run).Memory → (agent run).Memory) (left right : ℚ)
    {limit : ℕ} (room : limit + lapses < horizon)
    (separates : AllBut left runs fun run =>
      SeparatesBy family goals length bound counted limit (agent run))
    (retains : AllBut right runs fun run =>
      RetainsBut family goals length horizon lapses (agent run))
    (stream : ∀ run ∈ runs, ∀ index, OneStream.oneStream.Meets
      ((visitsRung family length horizon lapses pay met counted (agent run) (updates run)
        (work run) (resume run)).learner index)) :
    AllBut (left + right) runs fun run =>
      Mission (visitsRung family length horizon lapses pay met counted (agent run) (updates run)
        (work run) (resume run)) :=
  (separates.and retains).mono fun run member both =>
    visits_mission stated hidden covered feasible distinct both.1 room both.2 (stream run member)

def paid (pay : Percept interface → ℚ) (percept : Percept interface) : Bool :=
  decide (pay percept = 1)

theorem paid_decodes (stated : PaysAtGoals family goals pay met) (index : family.Index)
    (state : (family.world index).State) (action : Act interface) :
    paid pay ((family.world index).percept ((family.world index).step state action)) = true ↔
      (goals index).satisfied ((family.world index).step state action) := by
  unfold paid
  rw [decide_eq_true_iff, stated.pays, ← stated.reads]
  cases met index ((family.world index).step state action) <;> simp

def retraceRung (family : WorldClass interface) (length horizon last : ℕ)
    (pay : Percept interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index) (explore : ℕ → ℕ → Act interface) : Rung :=
  visitsRung family length horizon 0 pay met counted
    (retrace interface length last (paid pay) explore)
    (fun _ _ => [.learn (.stream 0), .other]) (fun _ _ => 2) id

theorem retrace_mission (stated : PaysAtGoals family goals pay met)
    (hidden : Conceals family goals reference origin)
    (covered : Covered family (visitGoals goals length) bound)
    (feasible : ∀ index, Feasible (visitGoals goals length index) (family.start index))
    (distinct : counted.Nodup) (many : bound < counted.length) (last : ℕ)
    (late : last + 1 < horizon) (explore : ℕ → ℕ → Act interface)
    (explored : ∀ index ∈ counted, ∃ visit, visit ≤ last ∧
      ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
        (path (family.world index) (family.start index) (explore visit) step)) :
    Mission (retraceRung family length horizon last pay met counted explore) :=
  visits_mission stated hidden covered feasible distinct
    (separatesBy_of_findsBy
      (retrace_finds family goals length last bound (paid pay) explore (paid_decodes stated)
        counted distinct many explored)
      (retrace_retains family goals length last (paid pay) explore (paid_decodes stated)))
    (show last + 1 + 0 < horizon by omega)
    ((retrace_retains family goals length last (paid pay) explore (paid_decodes stated)).but
      horizon)
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
