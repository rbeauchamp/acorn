/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Blindness
import AcornVerif.Campaign
import AcornVerif.Replay

/-!
# Visits that start in one of two situations

In `AcornVerif.Kernel.visits` every visit of a member starts from one state, so what an agent
perceives along a visit is decided by its own earlier actions and by whether its goal has been
met. This module states the class in which that is not so. A `TurnClass` gives each member two
start states, its two *situations*. `turns` is a member's world in visits under an *order*, a
function that names the situation of each visit: the world takes `length` steps from the start
of the visit's situation, delivers one more percept, and then moves to the start of the next
visit's situation whatever the action. The order is no part of what the world shows. A class
has a member for every order, so no agent can hold the order in advance.

Within a visit the closed loop is the member's own from the situation's start (`turns_loop`),
and every visit begins at the start of its situation (`turns_period`). So an agent solves a
member on a visit exactly when, resumed from its memory at that visit's start, it solves the
member from the situation's start within one visit (`solvesTurn_iff`). That memory is decided by
the order of the earlier visits alone (`turnMemory_congr`): the situation of a visit reaches the
agent through that visit's percepts and through nothing else.

Two promises are stated over such a class.

- `MastersBy`: under one order and on one visit before a stated visit, the agent solves each
  member of a set of more than `bound` members whichever situation that visit brings. The
  members are counted by a key, which the set does not repeat.
- `KeepsBut`: under every order, a member solved on a visit is solved again on every later
  visit before the horizon that brings the same situation, but for at most `lapses` visits of
  that member.

What the class forces, for a class in which no single action sequence meets a member's goal from
both of its starts (`Apart`):

- **Every agent that masters reads the visit's percepts.** Where an agent solves a member on a
  visit in both situations, it takes different actions at some step of that visit in the two
  runs, from one memory at the visit's start (`turn_differs`, `turnMemory_sides`).
- **No feedback-driven agent masters.** Where the two situations give one feedback until the
  goal is met (`Mute`), an agent whose actions depend on its clock and its feedback solves no
  member on any visit in both situations (`FeedbackDriven.turn`), so it masters at no bound
  (`FeedbackDriven.masters`), and of the two sides of the members of any finite set it solves at
  most as many as the set has members (`FeedbackDriven.sides`). The same holds of every agent
  whose closed loops in the class are those of a feedback-driven agent
  (`MastersBy.of_states`).
- **No agent that keeps nothing masters above a covering bound.** Where the first situation's
  class conceals its goals and one action sequence meets the goals of at most `bound` members
  with different keys, an experience-free agent does not master at that bound (`turns_need`).

The promises are satisfiable. `switch` runs one agent for each situation and reads the situation
from the first percept of each visit. Where that percept shows the situation, it solves a member
on a visit exactly when the situation's agent solves it, in the situation's class in visits, on
the visit of that situation's own count (`switch_turn`). So where each situation's agent solves
again whatever it has solved, the switch keeps with no lapse (`switch_keeps`).

A world in turns is a kernel world built from a member's own transition and percept. No host
loop in the tree runs one, and no theorem here relates it to a host's run.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-! ## A world in turns -/

/-- A world in visits of a length under an order of two situations. From the start state of the
visit's situation the world takes `length` steps, delivers one more percept at the visit's last
state, and then moves to the start state of the next visit's situation whatever the action. The
state holds the visit's number and the steps taken in it. -/
def turns (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length : ℕ) : World interface where
  State := world.State × ℕ × Fin (length + 1)
  step := fun state action =>
    if within : state.2.2.val < length then
      (world.step state.1 action, state.2.1, ⟨state.2.2.val + 1, by omega⟩)
    else (start (order (state.2.1 + 1)), state.2.1 + 1, ⟨0, Nat.succ_pos length⟩)
  percept := fun state => world.percept state.1

/-- The first state of a visit: the start state of its situation, with no step taken. -/
def turnStart (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length visit : ℕ) : (turns world start order length).State :=
  (start (order visit), visit, ⟨0, Nat.succ_pos length⟩)

/-- Within a visit the closed loop is the world's own from the start of the visit's
situation. -/
theorem turns_loop (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length visit : ℕ) (agent : Agent interface) (time : ℕ) (within : time ≤ length) :
    loop (turns world start order length) agent (turnStart world start order length visit)
        time =
      (((loop world agent (start (order visit)) time).1, visit,
          ⟨time, Nat.lt_succ_of_le within⟩),
        (loop world agent (start (order visit)) time).2) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have short : time < length := Nat.lt_of_succ_le within
    change interact (turns world start order length) agent
        (loop (turns world start order length) agent
          (turnStart world start order length visit) time) = _
    rw [earlier]
    simp only [interact, turns, dite_eq_left short]
    rfl

/-- The memory an agent holds after one whole visit from a start state, entered with a
memory. -/
def visitMemory (agent : Agent interface) (world : World interface) (origin : world.State)
    (length : ℕ) (memory : agent.Memory) : agent.Memory :=
  (agent.act (memoryAt world (agent.resume memory) origin length)
    (perceptAt world (agent.resume memory) origin length)).2

/-- A visit's last decision moves the world in turns to the start of the next visit, and leaves
the agent the memory of one whole visit from the situation's start. -/
theorem turns_return (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length visit : ℕ) (agent : Agent interface) (memory : agent.Memory) :
    loop (turns world start order length) (agent.resume memory)
        (turnStart world start order length visit) (length + 1) =
      (turnStart world start order length (visit + 1),
        visitMemory agent world (start (order visit)) length memory) := by
  have last := turns_loop world start order length visit (agent.resume memory) length
    (Nat.le_refl length)
  change interact (turns world start order length) (agent.resume memory)
    (loop (turns world start order length) (agent.resume memory)
      (turnStart world start order length visit) length) = _
  rw [last]
  simp only [interact, turns, dite_eq_right (Nat.lt_irrefl length)]
  rfl

/-- Every visit begins at the start of its situation: after each multiple of `length + 1`
decisions. -/
theorem turns_period (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length : ℕ) (agent : Agent interface) (visit : ℕ) :
    stateAt (turns world start order length) agent (turnStart world start order length 0)
        (visit * (length + 1)) =
      turnStart world start order length visit := by
  induction visit with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ visit ih =>
    rw [Nat.add_mul, Nat.one_mul, stateAt_add, ih]
    exact congrArg Prod.fst (turns_return world start order length visit agent
      (memoryAt (turns world start order length) agent (turnStart world start order length 0)
        (visit * (length + 1))))

/-- An agent's memory at the start of a visit of a world in turns. -/
def turnMemory (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length : ℕ) (agent : Agent interface) (visit : ℕ) : agent.Memory :=
  memoryAt (turns world start order length) agent (turnStart world start order length 0)
    (visit * (length + 1))

/-- The memory at the start of the next visit is the memory of one whole visit from the start of
this visit's situation, entered with the memory at this visit's start. -/
theorem turnMemory_succ (world : World interface) (start : Bool → world.State)
    (order : ℕ → Bool) (length : ℕ) (agent : Agent interface) (visit : ℕ) :
    turnMemory world start order length agent (visit + 1) =
      visitMemory agent world (start (order visit)) length
        (turnMemory world start order length agent visit) := by
  unfold turnMemory
  rw [Nat.add_mul, Nat.one_mul, memoryAt_add, turns_period]
  exact congrArg Prod.snd (turns_return world start order length visit agent
    (memoryAt (turns world start order length) agent (turnStart world start order length 0)
      (visit * (length + 1))))

/-- **The memory at a visit's start is decided by the order of the earlier visits.** Under two
orders that name one situation for every earlier visit, an agent holds one memory at the start
of a visit. -/
theorem turnMemory_congr (world : World interface) (start : Bool → world.State)
    (first second : ℕ → Bool) (length : ℕ) (agent : Agent interface) (visit : ℕ)
    (same : ∀ earlier, earlier < visit → first earlier = second earlier) :
    turnMemory world start first length agent visit =
      turnMemory world start second length agent visit := by
  induction visit with
  | zero =>
    unfold turnMemory
    rw [Nat.zero_mul]
    rfl
  | succ visit ih =>
    rw [turnMemory_succ, turnMemory_succ,
      ih (fun earlier before => same earlier (Nat.lt_succ_of_lt before)),
      same visit (Nat.lt_succ_self visit)]

/-- Within a visit, the world's state is the state that the agent resumed from its memory at the
visit's start reaches in the world itself from the start of the visit's situation. -/
theorem turns_state (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length : ℕ) (agent : Agent interface) (visit step : ℕ) (within : step ≤ length) :
    (stateAt (turns world start order length) agent (turnStart world start order length 0)
        (visit * (length + 1) + step)).1 =
      stateAt world (agent.resume (turnMemory world start order length agent visit))
        (start (order visit)) step := by
  rw [stateAt_add, turns_period]
  exact congrArg Prod.fst
    (congrArg Prod.fst (turns_loop world start order length visit _ step within))

/-- Within a visit, the agent's action is the action of the agent resumed from its memory at the
visit's start, in the world itself from the start of the visit's situation. -/
theorem turns_action (world : World interface) (start : Bool → world.State) (order : ℕ → Bool)
    (length : ℕ) (agent : Agent interface) (visit step : ℕ) (within : step ≤ length) :
    actionAt (turns world start order length) agent (turnStart world start order length 0)
        (visit * (length + 1) + step) =
      actionAt world (agent.resume (turnMemory world start order length agent visit))
        (start (order visit)) step := by
  have split := loop_add (turns world start order length) agent
    (turnStart world start order length 0) (visit * (length + 1)) step
  rw [turns_period] at split
  have inner := turns_loop world start order length visit
    (agent.resume (turnMemory world start order length agent visit)) step within
  change (agent.act (loop (turns world start order length) agent
      (turnStart world start order length 0) (visit * (length + 1) + step)).2
    ((turns world start order length).percept (loop (turns world start order length) agent
      (turnStart world start order length 0) (visit * (length + 1) + step)).1)).1 = _
  rw [split]
  change (agent.act (loop (turns world start order length)
      (agent.resume (turnMemory world start order length agent visit))
      (turnStart world start order length visit) step).2
    ((turns world start order length).percept (loop (turns world start order length)
      (agent.resume (turnMemory world start order length agent visit))
      (turnStart world start order length visit) step).1)).1 = _
  rw [inner]
  rfl

/-! ## A class in turns -/

/-- A class of worlds each visit of which starts in one of two situations: each member has a
world and, for each situation, a start state. -/
structure TurnClass (interface : Interface) where
  /-- The members. -/
  Index : Type
  /-- A member's world. -/
  world : Index → World interface
  /-- A member's start state in each situation. -/
  start : (index : Index) → Bool → (world index).State

/-- One goal for each member, read in both of its situations. -/
abbrev TurnClass.Goals (family : TurnClass interface) : Type :=
  (index : family.Index) → AttemptGoal (family.world index)

/-- The class of one situation: every member, started in that situation. -/
abbrev TurnClass.side (family : TurnClass interface) (situation : Bool) :
    WorldClass interface where
  Index := family.Index
  world := family.world
  start := fun index => family.start index situation

variable {family : TurnClass interface} {goals : family.Goals} {length : ℕ}

/-- A member's goal with a visit's length as its step cap. -/
def turnGoal (goals : family.Goals) (length : ℕ) (index : family.Index) :
    AttemptGoal (family.world index) :=
  ⟨(goals index).satisfied, length⟩

/-- An agent solves a member on a visit under an order when, in that member's world in turns,
some state of that visit after one to `length` steps satisfies the member's goal. Visit 0 is the
first. -/
def SolvesTurn (family : TurnClass interface) (goals : family.Goals) (length : ℕ)
    (order : ℕ → Bool) (agent : Agent interface) (visit : ℕ) (index : family.Index) : Prop :=
  ∃ step, 1 ≤ step ∧ step ≤ length ∧ (goals index).satisfied
    (stateAt (turns (family.world index) (family.start index) order length) agent
      (turnStart (family.world index) (family.start index) order length 0)
      (visit * (length + 1) + step)).1

/-- An agent solves a member on a visit exactly when, resumed from its memory at the visit's
start, it achieves the member's goal from the start of the visit's situation within one visit's
length. -/
theorem solvesTurn_iff (family : TurnClass interface) (goals : family.Goals) (length : ℕ)
    (order : ℕ → Bool) (agent : Agent interface) (visit : ℕ) (index : family.Index) :
    SolvesTurn family goals length order agent visit index ↔
      Achieves
        (agent.resume
          (turnMemory (family.world index) (family.start index) order length agent visit))
        (turnGoal goals length index) (family.start index (order visit)) := by
  have inner := turns_state (family.world index) (family.start index) order length agent visit
  constructor
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    change (goals index).satisfied _
    rw [← inner step high]
    exact met
  · rintro ⟨step, low, high, met⟩
    refine ⟨step, low, high, ?_⟩
    rw [inner step high]
    exact met

/-- The memory at a visit's start does not read that visit's situation. -/
theorem turnMemory_sides (world : World interface) (start : Bool → world.State)
    (order : ℕ → Bool) (length : ℕ) (agent : Agent interface) (visit : ℕ) (situation : Bool) :
    turnMemory world start (Function.update order visit situation) length agent visit =
      turnMemory world start order length agent visit :=
  turnMemory_congr world start _ _ length agent visit
    (fun _ before => Function.update_of_ne (Nat.ne_of_lt before) situation order)

/-- An agent solves a member on a visit, with that visit's situation set, exactly when,
resumed from its memory at the visit's start under the order as it was, it achieves the member's
goal from that situation's start. -/
theorem solvesTurn_side (family : TurnClass interface) (goals : family.Goals) (length : ℕ)
    (order : ℕ → Bool) (agent : Agent interface) (visit : ℕ) (index : family.Index)
    (situation : Bool) :
    SolvesTurn family goals length (Function.update order visit situation) agent visit
        index ↔
      Achieves
        (agent.resume
          (turnMemory (family.world index) (family.start index) order length agent visit))
        (turnGoal goals length index) (family.start index situation) := by
  rw [solvesTurn_iff, turnMemory_sides, Function.update_self]

/-- Two agents in one state at every time of every member's world in turns solve the same
members on the same visits under the same orders. -/
theorem solvesTurn_of_states {first second : Agent interface}
    (same : ∀ (index : family.Index) (order : ℕ → Bool) (time : ℕ),
      stateAt (turns (family.world index) (family.start index) order length) first
          (turnStart (family.world index) (family.start index) order length 0) time =
        stateAt (turns (family.world index) (family.start index) order length) second
          (turnStart (family.world index) (family.start index) order length 0) time)
    (order : ℕ → Bool) (visit : ℕ) (index : family.Index) :
    SolvesTurn family goals length order first visit index ↔
      SolvesTurn family goals length order second visit index := by
  unfold SolvesTurn
  simp only [same]

/-! ## The two promises -/

/-- **Mastery before a stated visit.** Under one order, on one visit before the visit `limit`,
the agent solves each member of a set of more than `bound` members in both situations: under the
order with that visit's situation set to the one and to the other. No two members of the set
have one key.

This is a draft of the successor mission's promise, under revision, and no definition of the
mission contract. It has a witness on the day-and-night class and a failing example in every
feedback-driven agent (`FeedbackDriven.masters`). -/
def MastersBy (family : TurnClass interface) (goals : family.Goals) (length bound : ℕ)
    {κ : Type} (key : family.Index → κ) (limit : ℕ) (agent : Agent interface) : Prop :=
  ∃ (order : ℕ → Bool) (visit : ℕ) (solved : Finset family.Index),
    visit < limit ∧ bound < solved.card ∧
    (∀ first ∈ solved, ∀ second ∈ solved, key first = key second → first = second) ∧
    ∀ index ∈ solved, ∀ situation : Bool,
      SolvesTurn family goals length (Function.update order visit situation) agent visit index

/-- **Keeping what is solved, situation by situation, but for a number of lapses.** For each
member and each order there are at most `lapses` visits outside which the agent solves the member
on every visit before the visit `horizon` that is later than one on which it solved it and that
brings the same situation.

This is a draft of the successor mission's promise, under revision, and no definition of the
mission contract. It has a witness on the day-and-night class and no failing example. -/
def KeepsBut (family : TurnClass interface) (goals : family.Goals)
    (length horizon lapses : ℕ) (agent : Agent interface) : Prop :=
  ∀ (index : family.Index) (order : ℕ → Bool), ∃ lapsed : Finset ℕ, lapsed.card ≤ lapses ∧
    ∀ visit later, visit < later → later < horizon → order later = order visit →
      SolvesTurn family goals length order agent visit index → later ∉ lapsed →
        SolvesTurn family goals length order agent later index

/-- An agent that masters before a visit masters before every later one. -/
theorem MastersBy.mono {bound limit later : ℕ} {κ : Type} {key : family.Index → κ}
    {agent : Agent interface} (within : limit ≤ later)
    (masters : MastersBy family goals length bound key limit agent) :
    MastersBy family goals length bound key later agent := by
  obtain ⟨order, visit, solved, before, many, distinct, each⟩ := masters
  exact ⟨order, visit, solved, Nat.lt_of_lt_of_le before within, many, distinct, each⟩

/-- An agent that keeps but for a number of lapses keeps but for every greater number. -/
theorem KeepsBut.mono {horizon lapses more : ℕ} {agent : Agent interface}
    (within : lapses ≤ more) (keeps : KeepsBut family goals length horizon lapses agent) :
    KeepsBut family goals length horizon more agent := fun index order => by
  obtain ⟨lapsed, count, kept⟩ := keeps index order
  exact ⟨lapsed, Nat.le_trans count within, kept⟩

/-- An agent in the states of an agent that masters, masters. -/
theorem MastersBy.of_states {first second : Agent interface}
    (same : ∀ (index : family.Index) (order : ℕ → Bool) (time : ℕ),
      stateAt (turns (family.world index) (family.start index) order length) first
          (turnStart (family.world index) (family.start index) order length 0) time =
        stateAt (turns (family.world index) (family.start index) order length) second
          (turnStart (family.world index) (family.start index) order length 0) time)
    {bound limit : ℕ} {κ : Type} {key : family.Index → κ}
    (masters : MastersBy family goals length bound key limit first) :
    MastersBy family goals length bound key limit second := by
  obtain ⟨order, visit, solved, before, many, distinct, each⟩ := masters
  exact ⟨order, visit, solved, before, many, distinct, fun index member situation =>
    (solvesTurn_of_states same _ visit index).mp (each index member situation)⟩

/-! ## What a class with forks forces -/

variable {Φ : Type}

/-- **Every member is a fork.** No single action sequence meets a member's goal, within one
visit's length, from both of its starts. -/
def Apart (family : TurnClass interface) (goals : family.Goals) (length : ℕ) : Prop :=
  ∀ (index : family.Index) (actions : ℕ → Act interface),
    ¬ ((turnGoal goals length index).MetBy (family.start index false) actions ∧
      (turnGoal goals length index).MetBy (family.start index true) actions)

/-- **The situations give one feedback until the goal is met.** Along every action sequence,
from a member's two starts, the percepts have one feedback at every time before which the goal
has been met from neither. -/
def Mute (feedback : Percept interface → Φ) (family : TurnClass interface)
    (goals : family.Goals) : Prop :=
  ∀ (index : family.Index) (actions : ℕ → Act interface) (time : ℕ),
    (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (path (family.world index) (family.start index false) actions earlier)) →
    (∀ earlier, 1 ≤ earlier → earlier ≤ time → ¬ (goals index).satisfied
      (path (family.world index) (family.start index true) actions earlier)) →
    feedback ((family.world index).percept
        (path (family.world index) (family.start index false) actions time)) =
      feedback ((family.world index).percept
        (path (family.world index) (family.start index true) actions time))

/-- Within a visit whose situation is set, the agent's action is the action of the agent resumed
from its memory at the visit's start under the order as it was, from that situation's start. -/
theorem turns_action_side (world : World interface) (start : Bool → world.State)
    (order : ℕ → Bool) (length : ℕ) (agent : Agent interface) (visit step : ℕ)
    (within : step ≤ length) (situation : Bool) :
    actionAt (turns world start (Function.update order visit situation) length) agent
        (turnStart world start (Function.update order visit situation) length 0)
        (visit * (length + 1) + step) =
      actionAt world (agent.resume (turnMemory world start order length agent visit))
        (start situation) step := by
  rw [turns_action world start _ length agent visit step within, turnMemory_sides,
    Function.update_self]

/-- **An agent that solves a member in both situations reads that visit's percepts.** In a class
whose members are forks, where an agent solves a member on a visit under an order with that
visit's situation set to the one and to the other, its actions at some step of that visit differ
between the two runs. Its memory at the visit's start is the same in both
(`turnMemory_sides`), so the difference comes from what it perceives during the visit. -/
theorem turn_differs (apart : Apart family goals length) (order : ℕ → Bool)
    (agent : Agent interface) (visit : ℕ) (index : family.Index)
    (solved : ∀ situation : Bool, SolvesTurn family goals length
      (Function.update order visit situation) agent visit index) :
    ∃ step, step < length ∧
      actionAt (turns (family.world index) (family.start index)
            (Function.update order visit false) length) agent
          (turnStart (family.world index) (family.start index)
            (Function.update order visit false) length 0) (visit * (length + 1) + step) ≠
        actionAt (turns (family.world index) (family.start index)
            (Function.update order visit true) length) agent
          (turnStart (family.world index) (family.start index)
            (Function.update order visit true) length 0) (visit * (length + 1) + step) := by
  by_contra none
  have same : ∀ step, step < length →
      actionAt (family.world index)
          (agent.resume (turnMemory (family.world index) (family.start index) order length
            agent visit)) (family.start index false) step =
        actionAt (family.world index)
          (agent.resume (turnMemory (family.world index) (family.start index) order length
            agent visit)) (family.start index true) step := by
    intro step short
    rw [← turns_action_side (family.world index) (family.start index) order length agent visit
        step (Nat.le_of_lt short) false,
      ← turns_action_side (family.world index) (family.start index) order length agent visit
        step (Nat.le_of_lt short) true]
    exact Classical.not_not.mp (fun differ => none ⟨step, short, differ⟩)
  have first := (achieves_iff_metBy _ _ _).mp
    ((solvesTurn_side family goals length order agent visit index false).mp (solved false))
  obtain ⟨time, low, high, met⟩ := (achieves_iff_metBy _ _ _).mp
    ((solvesTurn_side family goals length order agent visit index true).mp (solved true))
  refine apart index _ ⟨first, time, low, high, ?_⟩
  have within : time ≤ length := high
  rw [path_congr (family.world index) (family.start index true) _
    (actionAt (family.world index)
      (agent.resume (turnMemory (family.world index) (family.start index) order length
        agent visit)) (family.start index true)) time
    (fun step before => same step (Nat.lt_of_lt_of_le before within))]
  exact met

/-- **A fork in turns defeats every feedback-driven agent.** In a class whose members are forks
and whose situations give one feedback until the goal is met, an agent whose actions depend on
its clock and its feedback solves no member, on any visit under any order, in both situations of
that visit. -/
theorem FeedbackDriven.turn {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (mute : Mute feedback family goals)
    (apart : Apart family goals length) (order : ℕ → Bool) (visit : ℕ)
    (index : family.Index) :
    ¬ ∀ situation : Bool, SolvesTurn family goals length
      (Function.update order visit situation) agent visit index := by
  intro solved
  have first := (solvesTurn_side family goals length order agent visit index false).mp
    (solved false)
  have second := (solvesTurn_side family goals length order agent visit index true).mp
    (solved true)
  have resumed : FeedbackDriven feedback (agent.resume
      (turnMemory (family.world index) (family.start index) order length agent visit)) := by
    unfold turnMemory
    rw [memoryAt_driven]
    exact blind.resume _ _
  exact resumed.fork (family.start index false) (family.start index true)
    (turnGoal goals length index) (turnGoal goals length index)
    (fun actions time unmetFirst unmetSecond => mute index actions time unmetFirst unmetSecond)
    (apart index) ⟨first, second⟩

/-- **No feedback-driven agent masters**, at any bound, key and limit, in a class whose members
are forks and whose situations give one feedback until the goal is met. -/
theorem FeedbackDriven.masters {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (mute : Mute feedback family goals)
    (apart : Apart family goals length) (bound limit : ℕ) {κ : Type}
    (key : family.Index → κ) : ¬ MastersBy family goals length bound key limit agent := by
  rintro ⟨order, visit, solved, -, many, -, each⟩
  obtain ⟨index, member⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le bound) many)
  exact blind.turn mute apart order visit index (each index member)

/-- **A feedback-driven agent serves at most one side of each fork.** Take any order and visit,
and any finite set of sides, a member with a situation for that visit, each of which the agent
solves on that visit. Then no two of them are sides of one member: the set has as many sides as
members. So of the two sides of each of `n` members it solves at most `n`. -/
theorem FeedbackDriven.sides {feedback : Percept interface → Φ} {agent : Agent interface}
    (blind : FeedbackDriven feedback agent) (mute : Mute feedback family goals)
    (apart : Apart family goals length) (order : ℕ → Bool) (visit : ℕ)
    [DecidableEq family.Index] (sides : Finset (family.Index × Bool))
    (each : ∀ side ∈ sides, SolvesTurn family goals length
      (Function.update order visit side.2) agent visit side.1) :
    sides.card = (sides.image Prod.fst).card := by
  refine (Finset.card_image_of_injOn ?_).symm
  rintro ⟨index, situation⟩ member ⟨other, twin⟩ also (same : index = other)
  subst same
  refine Prod.ext rfl ?_
  by_contra differ
  refine blind.turn mute apart order visit index (fun wanted => ?_)
  have options : wanted = situation ∨ wanted = twin := by
    revert differ
    cases wanted <;> cases situation <;> cases twin <;> simp
  rcases options with rfl | rfl
  · exact each _ member
  · exact each _ also

/-- **No agent that keeps nothing masters above a covering bound.** Take a class in turns whose
first situation's class conceals its goals behind a reference, and a bound such that one action
sequence meets, from their first starts within a visit, the goals of at most `bound` members no
two of which have one key. Then no experience-free agent masters at that bound. -/
theorem turns_need {reference : World interface} {origin : reference.State}
    (hidden : Conceals (family.side false) goals reference origin) {κ : Type}
    (key : family.Index → κ) {bound : ℕ}
    (covered : ∀ (actions : ℕ → Act interface) (solved : Finset family.Index),
      (∀ first ∈ solved, ∀ second ∈ solved, key first = key second → first = second) →
      (∀ index ∈ solved,
        (turnGoal goals length index).MetBy (family.start index false) actions) →
      solved.card ≤ bound)
    {agent : Agent interface} (free : ExperienceFree agent) (limit : ℕ) :
    ¬ MastersBy family goals length bound key limit agent := by
  rintro ⟨order, visit, solved, -, many, distinct, each⟩
  obtain ⟨advance, law⟩ := free
  refine absurd (covered (actionAt reference
    (agent.resume (advanced advance agent.initial (visit * (length + 1)))) origin) solved
    distinct (fun index member => ?_)) (Nat.not_le_of_lt many)
  have solves := (solvesTurn_side family goals length order agent visit index false).mp
    (each index member false)
  unfold turnMemory at solves
  rw [experienceFree_memoryAt law] at solves
  exact ((hidden.withLength length).solves_iff _ index).mp solves

/-! ## One agent for each situation -/

/-- The agent that runs one agent for each situation. At the first percept of each visit it
reads the situation from the percept; through the visit it gives every percept to that
situation's agent and takes its action, while the other agent's memory rests. Its own memory
holds the situation it read and the steps taken in the visit. -/
def switch (side : Percept interface → Bool) (length : ℕ) (agents : Bool → Agent interface) :
    Agent interface where
  Memory := (Bool × Fin (length + 1)) × ((situation : Bool) → (agents situation).Memory)
  initial := ((false, ⟨0, Nat.succ_pos length⟩), fun situation => (agents situation).initial)
  act := fun memory percept =>
    (((agents (if memory.1.2.val = 0 then side percept else memory.1.1)).act
        (memory.2 (if memory.1.2.val = 0 then side percept else memory.1.1)) percept).1,
      ((if memory.1.2.val = 0 then side percept else memory.1.1,
          if within : memory.1.2.val < length then ⟨memory.1.2.val + 1, by omega⟩
          else ⟨0, Nat.succ_pos length⟩),
        Function.update memory.2 (if memory.1.2.val = 0 then side percept else memory.1.1)
          ((agents (if memory.1.2.val = 0 then side percept else memory.1.1)).act
            (memory.2 (if memory.1.2.val = 0 then side percept else memory.1.1)) percept).2))

/-- One decision of the switch, where the situation it reads or holds is known. -/
theorem switch_act (side : Percept interface → Bool) (length : ℕ)
    (agents : Bool → Agent interface) (flag : Bool) (count : Fin (length + 1))
    (memories : (situation : Bool) → (agents situation).Memory) (percept : Percept interface)
    (situation : Bool) (reads : (if count.val = 0 then side percept else flag) = situation) :
    (switch side length agents).act ((flag, count), memories) percept =
      (((agents situation).act (memories situation) percept).1,
        ((situation, if within : count.val < length then ⟨count.val + 1, by omega⟩
            else ⟨0, Nat.succ_pos length⟩),
          Function.update memories situation
            ((agents situation).act (memories situation) percept).2)) := by
  subst reads
  rfl

/-- **Within a visit the switch is its situation's agent.** From a start state whose percept
shows a situation, entered with its step count at zero, the switch's closed loop for one visit's
length has the states of that situation's agent resumed from its own memory, and holds that
agent's memory in that situation's place and the other memories as they were. -/
theorem switch_loop (side : Percept interface → Bool) (length : ℕ)
    (agents : Bool → Agent interface) (world : World interface) (origin : world.State)
    (situation : Bool) (reads : side (world.percept origin) = situation) (flag : Bool)
    (memories : (situation : Bool) → (agents situation).Memory) (time : ℕ)
    (within : time ≤ length) :
    loop world ((switch side length agents).resume
        ((flag, ⟨0, Nat.succ_pos length⟩), memories)) origin time =
      ((loop world ((agents situation).resume (memories situation)) origin time).1,
        ((if time = 0 then flag else situation, ⟨time, Nat.lt_succ_of_le within⟩),
          Function.update memories situation
            (loop world ((agents situation).resume (memories situation)) origin time).2)) := by
  induction time with
  | zero =>
    change (origin, ((flag, _), memories)) =
      (origin, ((flag, _), Function.update memories situation (memories situation)))
    rw [Function.update_eq_self]
  | succ time ih =>
    have earlier := ih (Nat.le_of_succ_le within)
    have short : time < length := Nat.lt_of_succ_le within
    have told : (if time = 0 then
          side (world.percept
            (loop world ((agents situation).resume (memories situation)) origin time).1)
        else (if time = 0 then flag else situation)) = situation := by
      cases time with
      | zero => exact reads
      | succ before => rfl
    have decided := switch_act side length agents (if time = 0 then flag else situation)
      ⟨time, Nat.lt_succ_of_le (Nat.le_of_succ_le within)⟩
      (Function.update memories situation
        (loop world ((agents situation).resume (memories situation)) origin time).2)
      (world.percept (loop world ((agents situation).resume (memories situation)) origin time).1)
      situation told
    change interact world ((switch side length agents).resume
        ((flag, ⟨0, Nat.succ_pos length⟩), memories))
      (loop world ((switch side length agents).resume
        ((flag, ⟨0, Nat.succ_pos length⟩), memories)) origin time) = _
    rw [earlier]
    change (world.step _ ((switch side length agents).act _ _).1,
      ((switch side length agents).act _ _).2) = _
    rw [decided]
    refine Prod.ext ?_ (Prod.ext (Prod.ext rfl ?_) ?_)
    · exact congrArg (fun memory => world.step
        (loop world ((agents situation).resume (memories situation)) origin time).1
        ((agents situation).act memory (world.percept
          (loop world ((agents situation).resume (memories situation)) origin time).1)).1)
        (Function.update_self situation _ memories)
    · exact dite_eq_left short
    · exact (Function.update_idem _ _ _).trans (congrArg (Function.update memories situation)
        (congrArg (fun memory => ((agents situation).act memory (world.percept
          (loop world ((agents situation).resume (memories situation)) origin time).1)).2)
          (Function.update_self situation _ memories)))

/-- **One visit of the switch is one visit of its situation's agent.** The memory the switch
holds after a whole visit from a start state whose percept shows a situation holds, in that
situation's place, the memory that situation's agent holds after the visit, and the other
memories as they were. -/
theorem switch_visitMemory (side : Percept interface → Bool) (length : ℕ)
    (agents : Bool → Agent interface) (world : World interface) (origin : world.State)
    (situation : Bool) (reads : side (world.percept origin) = situation) (flag : Bool)
    (memories : (situation : Bool) → (agents situation).Memory) :
    visitMemory (switch side length agents) world origin length
        ((flag, ⟨0, Nat.succ_pos length⟩), memories) =
      ((situation, ⟨0, Nat.succ_pos length⟩),
        Function.update memories situation
          (visitMemory (agents situation) world origin length (memories situation))) := by
  have last := switch_loop side length agents world origin situation reads flag memories length
    (Nat.le_refl length)
  have told : (if length = 0 then
        side (world.percept
          (loop world ((agents situation).resume (memories situation)) origin length).1)
      else (if length = 0 then flag else situation)) = situation := by
    cases length with
    | zero => exact reads
    | succ before => rfl
  have decided := switch_act side length agents (if length = 0 then flag else situation)
    ⟨length, Nat.lt_succ_self length⟩
    (Function.update memories situation
      (loop world ((agents situation).resume (memories situation)) origin length).2)
    (world.percept (loop world ((agents situation).resume (memories situation)) origin length).1)
    situation told
  change ((switch side length agents).act
    (loop world ((switch side length agents).resume
      ((flag, ⟨0, Nat.succ_pos length⟩), memories)) origin length).2
    (world.percept (loop world ((switch side length agents).resume
      ((flag, ⟨0, Nat.succ_pos length⟩), memories)) origin length).1)).2 = _
  rw [last, decided]
  refine Prod.ext (Prod.ext rfl (dite_eq_right (Nat.lt_irrefl length))) ?_
  exact (Function.update_idem _ _ _).trans (congrArg (Function.update memories situation)
    (congrArg (fun memory => ((agents situation).act memory (world.percept
      (loop world ((agents situation).resume (memories situation)) origin length).1)).2)
      (Function.update_self situation _ memories)))

/-- The memory after one more visit of a world in visits is the memory of one whole visit from
the start, entered with the memory at this visit's start. -/
theorem visits_memory_succ (world : World interface) (start : world.State) (length : ℕ)
    (agent : Agent interface) (count : ℕ) :
    memoryAt (visits world start length) agent (visitStart world start length)
        ((count + 1) * (length + 1)) =
      visitMemory agent world start length
        (memoryAt (visits world start length) agent (visitStart world start length)
          (count * (length + 1))) := by
  rw [Nat.add_mul, Nat.one_mul, memoryAt_add, visits_period]
  have inner := visits_loop world start length
    (agent.resume (memoryAt (visits world start length) agent (visitStart world start length)
      (count * (length + 1)))) length (Nat.le_refl length)
  change (agent.act
    (loop (visits world start length)
      (agent.resume (memoryAt (visits world start length) agent (visitStart world start length)
        (count * (length + 1)))) (visitStart world start length) length).2
    ((visits world start length).percept (loop (visits world start length)
      (agent.resume (memoryAt (visits world start length) agent (visitStart world start length)
        (count * (length + 1)))) (visitStart world start length) length).1)).2 = _
  rw [inner]
  rfl

/-- The visits before a visit to which an order gives a situation. -/
def seen (order : ℕ → Bool) (situation : Bool) : ℕ → ℕ
  | 0 => 0
  | visit + 1 => seen order situation visit + if order visit = situation then 1 else 0

/-- The count of a situation's visits does not fall. -/
theorem seen_mono (order : ℕ → Bool) (situation : Bool) {visit later : ℕ}
    (after : visit ≤ later) : seen order situation visit ≤ seen order situation later := by
  induction later with
  | zero =>
    rw [Nat.le_zero.mp after]
  | succ later ih =>
    rcases Nat.lt_or_eq_of_le after with sooner | same
    · exact Nat.le_trans (ih (Nat.le_of_lt_succ sooner)) (Nat.le_add_right _ _)
    · rw [same]

/-- A later visit of one situation has a greater count of that situation's visits. -/
theorem seen_lt (order : ℕ → Bool) {visit later : ℕ} (after : visit < later) :
    seen order (order visit) visit < seen order (order visit) later := by
  have next : seen order (order visit) (visit + 1) = seen order (order visit) visit + 1 := by
    change seen order (order visit) visit + (if order visit = order visit then 1 else 0) = _
    rw [ite_eq_left rfl]
  have rest := seen_mono order (order visit) (show visit + 1 ≤ later from after)
  omega

/-- The count of a situation's visits before a visit reads the order of the earlier visits
only. -/
theorem seen_congr (first second : ℕ → Bool) (situation : Bool) (visit : ℕ)
    (same : ∀ earlier, earlier < visit → first earlier = second earlier) :
    seen first situation visit = seen second situation visit := by
  induction visit with
  | zero => rfl
  | succ visit ih =>
    change seen first situation visit + (if first visit = situation then 1 else 0) =
      seen second situation visit + (if second visit = situation then 1 else 0)
    rw [ih (fun earlier before => same earlier (Nat.lt_succ_of_lt before)),
      same visit (Nat.lt_succ_self visit)]

/-- **At the start of each visit the switch holds each situation's agent as that agent stands
after its own visits.** Where the percept of each situation's start shows the situation, the
switch's memory at the start of a visit of a world in turns holds, for each situation, the
memory that situation's agent holds in that situation's world in visits after as many visits as
the order has given the situation. -/
theorem switch_memory (side : Percept interface → Bool) (length : ℕ)
    (agents : Bool → Agent interface) (world : World interface) (start : Bool → world.State)
    (reads : ∀ situation, side (world.percept (start situation)) = situation)
    (order : ℕ → Bool) (visit : ℕ) :
    ∃ flag, turnMemory world start order length (switch side length agents) visit =
      ((flag, ⟨0, Nat.succ_pos length⟩), fun situation =>
        memoryAt (visits world (start situation) length) (agents situation)
          (visitStart world (start situation) length)
          (seen order situation visit * (length + 1))) := by
  induction visit with
  | zero =>
    refine ⟨false, ?_⟩
    unfold turnMemory
    rw [Nat.zero_mul]
    refine Prod.ext rfl (funext fun situation => ?_)
    change (agents situation).initial = memoryAt (visits world (start situation) length)
      (agents situation) (visitStart world (start situation) length) (0 * (length + 1))
    rw [Nat.zero_mul]
    rfl
  | succ visit ih =>
    obtain ⟨flag, held⟩ := ih
    refine ⟨order visit, ?_⟩
    rw [turnMemory_succ, held, switch_visitMemory side length agents world (start (order visit))
      (order visit) (reads (order visit))]
    refine congrArg (Prod.mk _) (funext fun situation => ?_)
    by_cases here : situation = order visit
    · subst here
      refine (Function.update_self (β := fun situation => (agents situation).Memory)
        (order visit) _ _).trans ?_
      change _ = memoryAt (visits world (start (order visit)) length) (agents (order visit))
        (visitStart world (start (order visit)) length)
        ((seen order (order visit) visit + (if order visit = order visit then 1 else 0)) *
          (length + 1))
      rw [ite_eq_left rfl, visits_memory_succ]
    · refine (Function.update_of_ne (β := fun situation => (agents situation).Memory) here
        _ _).trans ?_
      change _ = memoryAt (visits world (start situation) length) (agents situation)
        (visitStart world (start situation) length)
        ((seen order situation visit + (if order visit = situation then 1 else 0)) *
          (length + 1))
      rw [ite_eq_right (fun same => here same.symm)]
      rfl

/-- **The switch solves what its situation's agent solves.** Where the percept of each of a
member's starts shows the situation, the switch solves the member on a visit under an order
exactly when the agent of that visit's situation solves it, in that situation's class in visits,
on the visit whose number is the count of that situation's earlier visits. -/
theorem switch_turn (family : TurnClass interface) (goals : family.Goals) (length : ℕ)
    (side : Percept interface → Bool) (agents : Bool → Agent interface) (order : ℕ → Bool)
    (visit : ℕ) (index : family.Index)
    (reads : ∀ situation,
      side ((family.world index).percept (family.start index situation)) = situation) :
    SolvesTurn family goals length order (switch side length agents) visit index ↔
      SolvesOnVisit (family.side (order visit)) goals length (agents (order visit))
        (seen order (order visit) visit) index := by
  obtain ⟨flag, held⟩ := switch_memory side length agents (family.world index)
    (family.start index) reads order visit
  have states : ∀ time, time ≤ length →
      stateAt (family.world index)
          ((switch side length agents).resume
            (turnMemory (family.world index) (family.start index) order length
              (switch side length agents) visit))
          (family.start index (order visit)) time =
        stateAt (family.world index)
          ((agents (order visit)).resume
            (memoryAt (visits (family.world index) (family.start index (order visit)) length)
              (agents (order visit))
              (visitStart (family.world index) (family.start index (order visit)) length)
              (seen order (order visit) visit * (length + 1))))
          (family.start index (order visit)) time := by
    intro time within
    rw [held]
    exact congrArg Prod.fst (switch_loop side length agents (family.world index)
      (family.start index (order visit)) (order visit) (reads (order visit)) flag _ time within)
  rw [solvesTurn_iff, solvesOnVisit_iff]
  constructor
  · rintro ⟨time, low, high, met⟩
    refine ⟨time, low, high, ?_⟩
    have within : time ≤ length := high
    change (goals index).satisfied _
    rw [← states time within]
    exact met
  · rintro ⟨time, low, high, met⟩
    refine ⟨time, low, high, ?_⟩
    have within : time ≤ length := high
    change (goals index).satisfied _
    rw [states time within]
    exact met

/-- **The switch keeps what its agents retain.** Where the percept of each start shows the
situation and each situation's agent, in that situation's class in visits, solves on every later
visit a member it has solved, the switch keeps with no lapse, before every horizon. -/
theorem switch_keeps (family : TurnClass interface) (goals : family.Goals) (length : ℕ)
    (side : Percept interface → Bool) (agents : Bool → Agent interface)
    (reads : ∀ index situation,
      side ((family.world index).percept (family.start index situation)) = situation)
    (retains : ∀ situation,
      Retains (family.side situation) goals length (agents situation)) (horizon : ℕ) :
    KeepsBut family goals length horizon 0 (switch side length agents) := by
  intro index order
  refine ⟨∅, Nat.le_of_eq Finset.card_empty, fun visit later after _ same solved _ => ?_⟩
  rw [switch_turn family goals length side agents order later index (reads index), same]
  rw [switch_turn family goals length side agents order visit index (reads index)] at solved
  exact retains (order visit) index _ _ (seen_lt order after) solved

/-! ## An agent that differs only where the class never looks -/

variable {E Core V : Type}

/-- **An agent that is feedback-driven on everything a class shows it does not master.** Take a
chooser whose preference and memory read the percept through a feedback alone, made aloof on a
set of percepts: on those it holds a resting preference. Over every sequence of percepts it need
then not be driven by the feedback; whether it is depends on the set, and with an empty set it is
the chooser itself. If no member of the class delivers a percept of the set, it does not master,
at any bound, key and limit: in every member's world in turns its closed loop is the chooser's
own (`aloof_loop`), and the chooser is feedback-driven (`chooser_stepped`). -/
theorem aloof_masters {feedback : Percept interface → Φ} (select : E → V → Act interface × E)
    (core : Core) (seed : E) (prefer : Core → Φ → V)
    (advance : Core → Φ → Act interface → Core)
    (alien : Percept interface → Prop) [DecidablePred alien] (rest : V)
    (never : ∀ (index : family.Index) (state : (family.world index).State),
      ¬ alien ((family.world index).percept state))
    (mute : Mute feedback family goals) (apart : Apart family goals length)
    (bound limit : ℕ) {κ : Type} (key : family.Index → κ) :
    ¬ MastersBy family goals length bound key limit
      (chooser select core seed
        (aloof alien rest (fun inner percept => prefer inner (feedback percept)))
        (fun inner percept action => advance inner (feedback percept) action)) := by
  intro masters
  refine (chooser_stepped feedback select core seed prefer advance).feedbackDriven.masters
    mute apart bound limit key (masters.of_states (fun index order time => ?_))
  exact congrArg Prod.fst (aloof_loop select core seed _ _ alien rest
    (turns (family.world index) (family.start index) order length) _
    (fun state => never index state.1) time)

/-! ## What keeping asks -/

/-- **A member solved in a situation is solved again among any more visits of that situation
than the lapses.** Under keeping but for `lapses` lapses, take a visit on which the agent solved
a member and a set of more than `lapses` later visits before the horizon that bring the same
situation. The agent solves the member on one of them. -/
theorem KeepsBut.again {horizon lapses : ℕ} {agent : Agent interface}
    (keeps : KeepsBut family goals length horizon lapses agent) (index : family.Index)
    (order : ℕ → Bool) (visit : ℕ)
    (solved : SolvesTurn family goals length order agent visit index) (later : Finset ℕ)
    (each : ∀ other ∈ later, visit < other ∧ other < horizon ∧ order other = order visit)
    (many : lapses < later.card) :
    ∃ other ∈ later, SolvesTurn family goals length order agent other index := by
  obtain ⟨lapsed, count, kept⟩ := keeps index order
  obtain ⟨other, inside, out⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (Nat.lt_of_le_of_lt count many)
  obtain ⟨after, before, same⟩ := each other inside
  exact ⟨other, inside, kept visit other after before same solved out⟩

/-- **A horizon within one visit of the lapses asks no keeping.** Where the lapses number at
least the visits before the horizon, less one, every agent keeps. -/
theorem keepsBut_of_lapses (family : TurnClass interface) (goals : family.Goals) (length : ℕ)
    {horizon lapses : ℕ} (agent : Agent interface) (covered : horizon ≤ lapses + 1) :
    KeepsBut family goals length horizon lapses agent := by
  intro index order
  refine ⟨Finset.Icc 1 (horizon - 1), ?_, ?_⟩
  · rw [Nat.card_Icc]
    omega
  · intro visit later after before _ _ out
    exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) out

end AcornVerif.Kernel
