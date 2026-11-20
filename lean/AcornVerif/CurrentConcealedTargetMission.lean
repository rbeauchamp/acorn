/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentArithmetic
import AcornVerif.CurrentConcealedTarget
import AcornVerif.MissionVisits

/-!
# The mission theorem's statement on the concealed targets of the executed grid world

The first class of the mission's ladder is the concealed targets of one grid world, run in visits
(`docs/mission-contract.md`, section "The mission theorem and its ladder"). This module states the
mission theorem on it, in the terms of the four intent records
(`AcornVerif.Intent.MissionTheorem.Mission`), proves the statement for a reference agent, and
proves it for the executed agent from named premises. The statement meant is the Lean one,
`Mission`: it keeps the comparison of 2026-11-03, read before the horizon as decided on 2026-11-17,
and is not the postcondition as the owner confirmed it on 2026-11-20;
`lean/AcornVerif/Intent/MissionTheorem.lean` sets out the difference under what the proposition does
not say.

## The class

`findRung` is the rung of the feasible concealed targets of a host world
(`AcornVerif.CurrentConcealedTarget.feasibleFind`), in visits of `length` steps, with a list of
counted members and an agent. What the class states about its reward, as fork F-A of the mission
contract asks:

- its reward function is the executed one. The reward of a percept is the number its reward word
  reads as (`reward`). After every step of the grid world that number is one when the step
  satisfies the installed goal and zero when it does not, the refused state included
  (`reward_step`): the host's only nonzero reward is exactly one on completion
  (`Acorn.Host.StepResult.reward`). At a visit's start it is the reward word the host world
  carries, which the class requires to be zero;
- an attempt is a visit, of `length + 1` decisions;
- an attempt's rewards are summed up to and including the first step that pays
  (`AcornVerif.MissionVisits.untilPaid`).

So the class's reward pays at its goals (`find_pays`), and with the concealment, the covering bound
`49 + 7 length` and the feasibility that `AcornVerif.CurrentConcealedTarget` proves, every premise
of `AcornVerif.MissionVisits.visits_mission` about the class holds. The reward lemma, obligation 16
of the mission contract, is discharged for this class by
`AcornVerif.MissionVisits.classReward_eq`, under the aggregate named above.

## A reference agent meets the statement

`witness_mission`: in the witness world (seed 1, side 64, visits of seven steps), with the 147
concealed targets of `AcornVerif.CurrentConcealedTarget.witness_explored` counted and the covering
bound 98, the retracing agent with the reward as its signal and the witness's three walks as its
exploration meets the mission's statement, with every premise discharged, with no lapse and at
every horizon of at least four visits. So the statement is
satisfiable on the executed grid world, by an agent that holds one of 96 memories (eight counts of
a visit's steps, three counts of visits and four values of the walk found) and stores no action and
no percept. This is a reference: it shows that the four contracts can be met together on this
class, and it is not a result about Acorn's agent. Its exploration is built for this world.

## The executed agent, from named premises

`executed_mission` proves the mission's statement from premises about the executed agent, from a
state of it, for every profile, feature configuration, criterion, dimension and planning
selection. The executed agent here is the executed decision function at the default step order
(`AcornVerif.CurrentGridWorld.executedAgent`). The statement is of any agent that takes the
executed agent's action at every time in every world (`ActsAsExecuted`), with that agent's own
memory and reports:

- `ExecutedFindsBy` and `ExecutedRetainsOn`, of the executed agent: what remains of obligation
  9, and what the goal-information and exploration premises of obligation 4 must deliver. The
  first says that the agent solves each of more counted members than the covering bound before
  a stated visit. For the cold agent of a profile with no hierarchy under the declared rate,
  over a host world that carries the zero reward word, what it gives without the visit
  (`ExecutedFinds`) is equivalent to a statement that reads one action sequence and no learner
  (`AcornVerif.CurrentConcealedTargetFinding.cold_finds_iff`), and it is proved on the first
  rung (`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds`). The second says that the
  agent solves again what it has solved on every later visit before the horizon that a
  predicate admits;
- `AcornVerif.Kernel.AdmitsBut` and `AcornVerif.Kernel.AdmitsOnce`, of that predicate alone: it
  admits every visit before the horizon but for at most the stated lapses of each member, and
  it admits one visit, from the visit of the finds on and before a visit that leaves more later
  visits than the lapses before the horizon, for all but a stated number of the counted
  members, where the agent has found that many more than the covering bound asks. They read no
  solving. The predicate is a parameter of the theorem; the one the first rung reads is
  `ExecutedCalm`, that the executed step reports no exploration at any decision of the visit
  that the world takes;
- `AcornVerif.Intent.MissionTheorem.MemoryBounded`, obligation 6, of the agent's memory. It is
  proved, for a construction of the default step order and from the agent of a state a host runs,
  of the executed agent itself, whose memory is its whole state
  (`AcornVerif.CurrentKernelMemory.find_memory_bounded`);
- `AcornVerif.Intent.MissionTheorem.WorkBounded` and
  `AcornVerif.Intent.MissionTheorem.LearnsOnArrival`, obligation 7, of its reports;
- `AcornVerif.Intent.MissionTheorem.KeepsDiscipline`, the clauses of contract 3's record that no
  numbered obligation states.

Why the statement is not of the executed agent's whole state alone. As a kernel agent the executed
agent's memory is its whole state, which holds its evaluator's session. The executing resumption
starts a new session (`AcornVerif.CurrentCheckpoint.resume_saved`), so it does not return the
memory the agent held, and `KeepsDiscipline` cannot hold of that memory with the resumption the
code performs. Resumption does return every learned field. So contract 3's record can hold of the
executed agent only as an agent whose memory is what its decisions read, or once the evaluator's
session is no part of the agent's state, or under a changed record. The owner decided on
2026-11-18 that it is the first (rbeauchamp/acorn#249): contract 3 is read of an agent whose memory
is the executed agent's learned state, without the evaluator's session. The theorem takes the agent
as a parameter, so it applies to that agent once the fifth step of rbeauchamp/acorn#215 constructs
it and proves `ActsAsExecuted` of it, which is not done; the executed agent itself is one agent the
parameter admits (`executedAgent_actsAs`).

How the promises are asked. The owner decided on 2026-11-17 (rbeauchamp/acorn#248) that the
postcondition's record reads its promises before a visit the class states, its horizon. The
agent solves again what it has solved on every later visit before the horizon but for a number
of each member's visits that the class states, its lapses
(`AcornVerif.Intent.Postcondition.keepsSolving`), and its advantage comes on a visit that leaves
more later visits than the lapses before the horizon
(`AcornVerif.Intent.Postcondition.earnsMoreInTime`). The executed agent is asked the first in two
parts: on a later visit in which it takes no exploratory action it solves the member again, and
a count of the visits in which it explores. The premises above are those parts. From them the
agent separates before the stated visit, on the one visit that is admitted for enough of the
members it has found (`AcornVerif.Kernel.separatesBy_of_finds_on`), and retains before the
horizon but for the lapses (`AcornVerif.Kernel.RetainsOn.but`). The reason is that the executed
agent explores at a constant rate at every decision that serves no run (departure D6 of
`docs/learned-only-binding.md`): where an exploring run can make a visit miss, the agent as
built does not solve a member on every later visit, under ideal draws on almost every run
(argued, not proved).

No premise states obligation 4. No premise about the class that suffices for this agent's
retention is known; its finding on the first rung needs none, since its actions up to a first
reward are a function of its seed (`AcornVerif.CurrentExplorer`).

Obligation 15 enters through the two premises on the predicate. They are statements about the
agent's one run in each member, with no fraction of runs and no hypothesis on the draws: the
executed agent's generator is part of its state, so one state has one run. Every premise about
solving and about the predicate reads the visits before the horizon and no other, so those
premises read finitely many decisions of each run. Proving the two for `ExecutedCalm` needs
the generator's state along the agent's run after a first reward. Each decision's flag is a
function of the generator's state at that decision
(`AcornVerif.TemporalSupport.select_declared`), and the tree follows that state up to a first
reward (`AcornVerif.CurrentExplorer.Explorer`) and at the one decision after it, and no
further. For a family of states, which is a family of seeds, the count is the exact one of
obligation 12, and for a family of ideal draw sequences it is the fraction obligation 15 asks
for.

What these theorems leave open, beside their premises:

- The class constants. The theorems hold for every host world whose carried reward is zero, every
  visit length, every list of distinct counted members, and every horizon and number of lapses
  that leave room after the visit by which the agent separates.
  `AcornVerif.CurrentConcealedTargetRung` fixes the world, the visit length and the agent of the
  first rung, and names the theorems its world and its visit length rest on. The counted members
  are those the executed agent finds; on the first rung 102 are listed
  (`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds`).
- The agent's reports. What the agent's step reports of its internal updates and its work, and how
  it resumes, are parameters. Defining them from the executing code and proving the premises about
  them is the fifth step of rbeauchamp/acorn#215.
- The link to a host's run. A rung's run is contract 1's faithful run by how it is built, which is
  not a theorem about a host. That the host's loop of visits is the kernel's world in visits, with
  the same learners at each step order, is `AcornVerif.CurrentVisits.executed_visits_closed_loop`;
  no theorem ties the native entry `acorn-core visits` to that loop.
-/

namespace AcornVerif.CurrentConcealedTargetMission
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.MissionVisits AcornVerif.Intent AcornVerif.Intent.MissionTheorem

variable {config : Host.WorldConfig}

/-! ## The class's reward -/

/-- The grid world's reward as a number: the number the reward word of a percept reads as. -/
def reward (percept : Percept Grid.interface) : ℚ :=
  numerical32 percept.reward

/-- Whether a state of the grid world reports its installed goal satisfied. The refused state
reports none. -/
def goalMet : Option (Live config) → Bool
  | some live => live.world.goalSatisfied
  | none => false

/-- `goalMet` marks the states that satisfy the installed goal's completion. -/
theorem goalMet_iff (mode : TaskFeatureMode) (cap : ℕ) (state : Option (Live config)) :
    goalMet state = true ↔ (completion config mode cap).satisfied state := by
  cases state with
  | none =>
    exact ⟨fun shown => absurd shown Bool.false_ne_true, fun ⟨_, never, _⟩ => nomatch never⟩
  | some live =>
    exact ⟨fun met => ⟨live, rfl, met⟩, fun ⟨found, same, met⟩ => by cases same; exact met⟩

/-- **The grid world's reward word.** After every step of the grid world the reward word is the
word one when the step satisfies the installed goal and the zero word when it does not: a step
the host refuses, and every step from the refused state, pays nothing. -/
theorem reward_word_step (mode : TaskFeatureMode) (state : Option (Live config))
    (action : Kernel.Act Grid.interface) :
    ((gridWorld config mode).percept ((gridWorld config mode).step state action)).reward =
      if goalMet ((gridWorld config mode).step state action) then Binary32.one
      else Binary32.zero := by
  cases state with
  | none => rfl
  | some live =>
    change ((gridWorld config mode).percept (advance live action)).reward =
      if goalMet (advance live action) then Binary32.one else Binary32.zero
    cases stepped : advance live action with
    | none => rfl
    | some next =>
      obtain ⟨events, moved, carried⟩ := advance_some live next action stepped
      have done := Host.World.step_completion _ _ _ _ moved
      change next.carried.reward = if next.world.goalSatisfied then Binary32.one else Binary32.zero
      rw [carried, ← done]
      change events.reward = _
      unfold Host.StepResult.reward
      cases events.done <;> rfl

/-- **The grid world's whole reward function.** After every step of the grid world, the reward is
one when the step satisfies the installed goal and zero when it does not: a step the host refuses,
and every step from the refused state, pays nothing. -/
theorem reward_step (mode : TaskFeatureMode) (state : Option (Live config))
    (action : Kernel.Act Grid.interface) :
    reward ((gridWorld config mode).percept ((gridWorld config mode).step state action)) =
      if goalMet ((gridWorld config mode).step state action) then 1 else 0 := by
  have zero : numerical32 Binary32.zero = 0 := by decide
  have one : numerical32 Binary32.one = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  change numerical32 ((gridWorld config mode).percept
    ((gridWorld config mode).step state action)).reward = _
  rw [reward_word_step]
  cases goalMet ((gridWorld config mode).step state action)
  · exact zero
  · exact one

/-- **The class's reward pays at its goals.** Over a host world that carries a reward of zero, the
feasible concealed targets have a reward that is one after each step that satisfies the member's
goal, zero after every other step, and zero at each member's start. -/
theorem find_pays (mode : TaskFeatureMode) (live : Live config) (length : ℕ)
    (fresh : live.carried.reward = ⟨0⟩) :
    PaysAtGoals (feasibleFind config mode live length) (fun _ => completion config mode length)
      reward (fun _ => goalMet) where
  reads := fun _ state => goalMet_iff mode length state
  pays := fun _ state action => reward_step mode state action
  quiet := fun _ => by
    change numerical32 live.carried.reward = 0
    rw [fresh]
    decide

/-! ## The rung -/

/-- The rung of the feasible concealed targets of a host world in visits of `length` steps, with
the visit before which its promises are read and the number of lapses its promise of solving
again allows, the members the comparison counts, an agent, and what the agent reports of its own
steps. -/
def findRung (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (length horizon lapses : ℕ) (counted : List (feasibleFind config mode live length).Index)
    (agent : Kernel.Agent Grid.interface)
    (updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update)
    (work : agent.Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : agent.Memory → agent.Memory) : Rung :=
  visitsRung (feasibleFind config mode live length) length horizon lapses reward
    (fun _ => goalMet) counted agent updates work resume

/-- **The mission theorem on the concealed targets, from its premises about the agent.** Over a
host world that carries a reward of zero, with a list of distinct counted members: an agent that
solves more counted members than the covering bound `49 + 7 length` on one visit before the visit
`limit`, where `limit` leaves more later visits than the lapses before the horizon, that solves
again what it has solved on every later visit before the horizon but for at most the stated
lapses of each member, and whose run in every member meets contract 3's record under its reports,
achieves goals over the class. Every premise about the class is discharged. The statement meant is
the Lean one, `Mission`: it keeps the comparison of 2026-11-03, read before the horizon as decided
on 2026-11-17, and is not the postcondition as the owner confirmed it on 2026-11-20;
`lean/AcornVerif/Intent/MissionTheorem.lean` sets out the difference under what the proposition does
not say. -/
theorem find_mission (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (length horizon lapses limit : ℕ) (fresh : live.carried.reward = ⟨0⟩)
    (counted : List (feasibleFind config mode live length).Index) (distinct : counted.Nodup)
    {agent : Kernel.Agent Grid.interface}
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    (separates : Kernel.SeparatesBy (feasibleFind config mode live length)
      (fun _ => completion config mode length) length (49 + 7 * length) counted limit agent)
    (room : limit + lapses < horizon)
    (retains : Kernel.RetainsBut (feasibleFind config mode live length)
      (fun _ => completion config mode length) length horizon lapses agent)
    (stream : ∀ target, OneStream.oneStream.Meets
      ((findRung config mode live length horizon lapses counted agent updates work
        resume).learner target)) :
    Mission (findRung config mode live length horizon lapses counted agent updates work resume) :=
  visits_mission (find_pays mode live length fresh) (feasibleFind_conceals mode live length length)
    (feasibleFind_covered config mode live length) (fun target => target.2) distinct separates
    room retains stream

/-! ## A reference agent meets the statement -/

/-- **The mission's statement is satisfiable on the executed grid world.** In the witness world,
with visits of seven steps and the covering bound 98, there is a list of 147 distinct feasible
concealed targets such that the retracing agent, with the reward as its signal and the witness's
three walks as its exploration, achieves goals over the class with those targets counted: the
mission's statement holds of its rung, with every premise discharged, with no lapse and at every
horizon of at least four visits: the agent solves every counted member on its third visit, the
last of its exploring ones, and the horizon leaves a visit after it. The statement meant is the Lean
one, `Mission`: it keeps the comparison of 2026-11-03, read before the horizon as decided on
2026-11-17, and is not the postcondition as the owner confirmed it on 2026-11-20;
`lean/AcornVerif/Intent/MissionTheorem.lean` sets out the difference under what the proposition does
not say. -/
theorem witness_mission (mode : TaskFeatureMode) :
    ∃ counted : List (feasibleFind witnessConfig mode witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 147 ∧
        ∀ horizon, 3 < horizon →
          Mission (retraceRung (feasibleFind witnessConfig mode witnessLive 7) 7 horizon 2 reward
            (fun _ => goalMet) counted witnessExplore) := by
  classical
  obtain ⟨members, count, explored⟩ := witness_explored mode
  have feasible : ∀ target ∈ members,
      Kernel.Feasible (completion witnessConfig mode 7) (member witnessLive target.1) := by
    intro target chosen
    obtain ⟨visit, -, step, low, high, met⟩ := explored target chosen
    exact ⟨witnessExplore visit, step, low, high, met⟩
  let admitted : { target // target ∈ members } →
      (feasibleFind witnessConfig mode witnessLive 7).Index :=
    fun target => ⟨target.1, feasible target.1 target.2⟩
  have injective : Function.Injective admitted := by
    intro first second same
    exact Subtype.ext (congrArg
      (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => target.1) same)
  have size : (members.attach.map ⟨admitted, injective⟩).toList.length = 147 := by
    rw [Finset.length_toList, Finset.card_map, Finset.card_attach, count]
  refine ⟨(members.attach.map ⟨admitted, injective⟩).toList, Finset.nodup_toList _, size,
    fun horizon late => ?_⟩
  refine retrace_mission (find_pays mode witnessLive 7 rfl)
    (feasibleFind_conceals mode witnessLive 7 7) (feasibleFind_covered witnessConfig mode
      witnessLive 7) (fun target => target.2) (Finset.nodup_toList _) (by rw [size]; decide) 2
    late witnessExplore (fun index listed => ?_)
  obtain ⟨target, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_toList.mp listed)
  exact explored target.1 target.2

/-! ## The executed agent, from named premises -/

section executed

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {planning : PlanningSelection}

/-- An agent takes the executed agent's actions, from a state of the executed agent: in every world
of the grid's interface, from every start, at every time. The executed agent itself is one; an
agent whose memory is only what the executed decisions read would be another. -/
def ActsAsExecuted (state : Agent Grid.interface profile features criterion dimension planning)
    (agent : Kernel.Agent Grid.interface) : Prop :=
  ∀ (world : Kernel.World Grid.interface) (start : world.State) (time : ℕ),
    Kernel.actionAt world agent start time = Kernel.actionAt world (executedAgent state) start time

/-- The executed agent takes its own actions. -/
theorem executedAgent_actsAs
    (state : Agent Grid.interface profile features criterion dimension planning) :
    ActsAsExecuted state (executedAgent state) :=
  fun _ _ _ => rfl

/-- **Obligation 9, first successes; what obligation 4's exploration premise must deliver**
(rbeauchamp/acorn#230, decided in rbeauchamp/acorn#232 with rbeauchamp/acorn#170). The executed
agent, from the given state, solves each of more than `49 + 7 length` counted members on some
visit. For the cold agent of a profile with no hierarchy under the declared rate it is a property
of one action sequence (`AcornVerif.CurrentConcealedTargetFinding.cold_finds_iff`). The premise
of `executed_mission` is `ExecutedFindsBy`, which names a visit and gives this
(`ExecutedFindsBy.finds`). -/
def ExecutedFinds (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (counted : List (feasibleFind config profile.taskMode live length).Index) : Prop :=
  Kernel.Finds (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length (49 + 7 * length) counted
    (executedAgent state)

/-- **Obligation 9, first successes by a stated visit.** The executed agent, from the given state,
solves each of more than `49 + 7 length + spare` counted members on some visit before the visit
`last`: `spare` members more than the covering bound asks, which separation can then do without
on the visit it names. On the first rung it is proved with `last` at 72 and `spare` at 3
(`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds`). -/
def ExecutedFindsBy (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (counted : List (feasibleFind config profile.taskMode live length).Index)
    (last spare : ℕ) : Prop :=
  Kernel.FindsBy (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length (49 + 7 * length + spare) counted
    last (executedAgent state)

/-- An executed agent that finds by a stated visit finds. -/
theorem ExecutedFindsBy.finds
    {state : Agent Grid.interface profile features criterion dimension planning}
    {live : Live config} {length last spare : ℕ}
    {counted : List (feasibleFind config profile.taskMode live length).Index}
    (finds : ExecutedFindsBy state config live length counted last spare) :
    ExecutedFinds state config live length counted := by
  obtain ⟨solved, many, each⟩ := Kernel.FindsBy.finds finds
  exact ⟨solved, by omega, each⟩

/-- **Obligation 9, retention, its first part** (rbeauchamp/acorn#230, decided in
rbeauchamp/acorn#232 with rbeauchamp/acorn#171; asked in this form by the owner's decision of
2026-11-17 on rbeauchamp/acorn#248). The executed agent, from the given state, solves on every
later visit before the horizon that the predicate `admits` holds of for a member, each member it
has solved on one visit. It is a statement about the agent's one run in each member and counts
nothing. The predicate is a parameter, and `executed_mission` holds of every predicate. The
owner's decision names the visits in which the agent takes no exploratory action; `ExecutedCalm`
is the reading of that on the first rung. Open: no theorem says the agent learns a route from
its first reward. -/
def ExecutedRetainsOn
    (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length horizon : ℕ)
    (admits : (feasibleFind config profile.taskMode live length).Index → ℕ → Prop) : Prop :=
  Kernel.RetainsOn (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length horizon admits
    (executedAgent state)

/-- **A visit on which the executed agent explores at no decision the world takes.** In the
executed agent's run in a member's visits, from the given state, the executed step reports no
exploration at any of the visit's first `length` decisions, the ones whose actions the member's
world takes. The visit's last decision is not read: the world returns to its start whatever that
action is (`AcornVerif.Kernel.visits`), after every state that solving the member on this visit
reads.

What "reports no exploration" means. The step's decision carries the flag
`Acorn.Features.TemporalDecision.explored`. A decision is a served step of a run the agent had
committed to, or the outcome of one persistent draw, whose flag is the draw's branch
(`AcornVerif.CurrentTemporal.select_persistent`); under the declared rate that branch is a
function of one word of the generator (`AcornVerif.TemporalSupport.select_declared`). The step
that serves a committed run sets the flag as well
(`AcornVerif.CurrentTemporal.serve_explored`); that the selection returns that step's decision
when it serves is its definition, and no theorem states the two together. So a calm visit holds,
among the decisions it reads, neither the start of an exploratory run nor a step of one.

Four things in this reading were chosen on the owner's behalf, and the owner can overrule each.
The flag is taken as the meaning of an exploratory action. The visit's last decision is not
read, for the reason above. A greedy choice among several candidates draws on the generator as
well (`Acorn.Features.PolicySnapshot.greedy_def`); it sets no flag and is not exploration here,
so a calm visit can still hold a choice drawn at random among actions whose values are tied. And
under a profile with a hierarchy the meta-controller's own exploring branch is not that flag and
is not read. -/
def ExecutedCalm (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (index : (feasibleFind config profile.taskMode live length).Index) (visit : ℕ) : Prop :=
  ∀ step, step < length →
    ((Kernel.memoryAt
        (Kernel.visits ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (executedAgent state)
        (Kernel.visitStart ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (visit * (length + 1) + step)).act
      (Kernel.perceptAt
        (Kernel.visits ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (executedAgent state)
        (Kernel.visitStart ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (visit * (length + 1) + step))).2.explored = false

/-- **The executed agent achieves goals over the concealed targets, from named premises.** Over a
host world that carries a reward of zero, with a list of distinct counted members, take a
predicate `admits` on a member's visits, and a visit `limit` that leaves more later visits than
the lapses before the horizon. If the executed agent finds by the visit `last`,
`spare` members more than the covering bound asks (`ExecutedFindsBy`), and solves again, on
every later visit before the horizon that the predicate admits, what it has solved
(`ExecutedRetainsOn`), and the predicate admits every visit before the horizon but for at most
`lapses` of each member's (`AcornVerif.Kernel.AdmitsBut`) and admits one visit from `last` on and
before `limit` for all but `spare` of the counted members (`AcornVerif.Kernel.AdmitsOnce`), then
every agent that takes its actions, and whose own memory and reports meet the four premises of
contract 3, achieves goals over the class with that horizon and that number of lapses. The
mission's statement holds of that agent's rung. Every premise about solving and about the
predicate reads the visits before the horizon and no other. Two premises are proved:
`MemoryBounded`, where the agent is the executed agent itself from the agent of a state a host
runs, under a construction of the default step order
(`AcornVerif.CurrentKernelMemory.find_memory_bounded`), and `ExecutedFindsBy` on the first rung
(`AcornVerif.CurrentConcealedTargetRungFinds.rung_finds`). Each premise names the obligation, or
the step of the issue, that owns it; the two on the predicate alone read no solving, and
obligation 15 owns them for an agent that explores with random draws. The theorem holds of every
predicate; the first rung reads `ExecutedCalm`. The statement meant is the Lean one, `Mission`: it
keeps the comparison of 2026-11-03, read before the horizon as decided on 2026-11-17, and is not the
postcondition as the owner confirmed it on 2026-11-20; `lean/AcornVerif/Intent/MissionTheorem.lean`
sets out the difference under what the proposition does not say. -/
theorem executed_mission
    (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config)
    (length horizon lapses last limit spare : ℕ) (fresh : live.carried.reward = ⟨0⟩)
    (counted : List (feasibleFind config profile.taskMode live length).Index)
    (distinct : counted.Nodup) {agent : Kernel.Agent Grid.interface}
    (acts : ActsAsExecuted state agent)
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    {admits : (feasibleFind config profile.taskMode live length).Index → ℕ → Prop}
    (finds : ExecutedFindsBy state config live length counted last spare)
    (retains : ExecutedRetainsOn state config live length horizon admits)
    (few : Kernel.AdmitsBut admits horizon lapses)
    (once : Kernel.AdmitsOnce admits counted last limit spare)
    (room : limit + lapses < horizon)
    (memory : MemoryBounded (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume))
    (bounded : WorkBounded (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume))
    (arrival : LearnsOnArrival (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume))
    (discipline : KeepsDiscipline (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume)) :
    Mission (findRung config profile.taskMode live length horizon lapses counted agent updates
      work resume) :=
  find_mission config profile.taskMode live length horizon lapses limit fresh counted distinct
    (Kernel.separatesBy_of_finds_on (Kernel.FindsBy.of_actions acts finds)
      (Kernel.RetainsOn.of_actions acts retains) once (by omega))
    room ((Kernel.RetainsOn.of_actions acts retains).but few)
    (Rung.stream_met memory bounded arrival discipline)

end executed

end AcornVerif.CurrentConcealedTargetMission
