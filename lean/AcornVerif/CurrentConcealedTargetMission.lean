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
proves it for the executed agent from named premises.

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

`witness_mission`: in the witness world (seed 5, side 64, visits of seven steps), with the 147
concealed targets of `AcornVerif.CurrentConcealedTarget.witness_explored` counted and the covering
bound 98, the retracing agent with the reward as its signal and the witness's three walks as its
exploration meets the mission's statement, with every premise discharged. So the statement is
satisfiable on the executed grid world, by an agent that holds one of 96 memories and stores no
action and no percept. This is a reference: it shows that the four contracts can be met together on
this class, and it is not a result about Acorn's agent. Its exploration is built for this world.

## The executed agent, from named premises

`executed_mission` proves the mission's statement of the executed agent, from every state of it and
at every construction, from premises that each name an open obligation of the mission contract:

- `ExecutedFinds` and `ExecutedRetains`: what remains of obligation 9, and what the
  goal-information and exploration premises of obligation 4 must deliver for this agent;
- `AcornVerif.Intent.MissionTheorem.MemoryBounded`, obligation 6;
- `AcornVerif.Intent.MissionTheorem.WorkBounded` and
  `AcornVerif.Intent.MissionTheorem.LearnsOnce`, obligation 7;
- `AcornVerif.Intent.MissionTheorem.KeepsDiscipline`, the rest of contract 3's record.

`executed_mission_allBut` is the statement under fork F4, obligation 15: for a finite family of
states of the agent, where finding fails on at most one fraction of the family and retaining on at
most another, the mission's statement holds of all but the sum of the fractions.

What these theorems leave open, beside their premises:

- The class constants. The theorems hold for every host world whose carried reward is zero, every
  visit length and every list of distinct counted members longer than the covering bound. Which
  world, visit length and counted members the executed agent's rung fixes is not decided here: the
  witness's constants suit the reference agent, and a visit length near the horizon over which the
  executed agent's credit reaches may suit that agent.
- The agent's reports. What the executed agent's step reports of its internal updates and its work,
  and how it resumes, are parameters. Defining them from the executing code and proving the four
  premises about them is the fifth step of rbeauchamp/acorn#215.
- The family of runs under F4. It is a parameter. Under F4 it is to hold one state for each sequence
  of the ideal draws a guarantee reads, which needs a model of the agent's draws; with one state for
  each seed of the generator it is the exact count of obligation 12.
- The research profile. The theorems hold for every construction; the first to be assembled is the
  primitive profile.
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

/-- **The grid world's whole reward function.** After every step of the grid world, the reward is
one when the step satisfies the installed goal and zero when it does not: a step the host refuses,
and every step from the refused state, pays nothing. -/
theorem reward_step (mode : TaskFeatureMode) (state : Option (Live config))
    (action : Kernel.Act Grid.interface) :
    reward ((gridWorld config mode).percept ((gridWorld config mode).step state action)) =
      if goalMet ((gridWorld config mode).step state action) then 1 else 0 := by
  have zero : numerical32 (Binary32.mk 0) = 0 := by decide
  have one : numerical32 (Binary32.mk 0x3f800000) = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  have refused : reward ((gridWorld config mode).percept none) =
      if goalMet (none : Option (Live config)) then 1 else 0 := zero
  cases state with
  | none => exact refused
  | some live =>
    change reward ((gridWorld config mode).percept (advance live action)) =
      if goalMet (advance live action) then 1 else 0
    cases stepped : live.world.step (Host.Action.fromIndex action.val) with
    | error refusal =>
      have gone : advance live action = none := by simp only [advance, stepped]
      rw [gone]
      exact refused
    | ok pair =>
      obtain ⟨world, events⟩ := pair
      rw [advance_ok live action world events stepped]
      have done := Host.World.step_completion _ _ _ _ stepped
      change numerical32 events.reward = if world.goalSatisfied then 1 else 0
      rw [← done]
      unfold Host.StepResult.reward
      cases events.done
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
the members the comparison counts, an agent, and what the agent reports of its own steps. -/
def findRung (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (length : ℕ) (counted : List (feasibleFind config mode live length).Index)
    (agent : Kernel.Agent Grid.interface)
    (updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update)
    (work : agent.Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : agent.Memory → agent.Memory) : Rung :=
  visitsRung (feasibleFind config mode live length) length reward (fun _ => goalMet) counted
    agent updates work resume

/-- **The mission theorem on the concealed targets, from its premises about the agent.** Over a
host world that carries a reward of zero, with a list of distinct counted members longer than the
covering bound `49 + 7 length`: an agent that finds more counted members than the bound and retains
what it has solved, and whose run in every member meets contract 3's record under its reports,
achieves goals over the class. Every premise about the class is discharged. -/
theorem find_mission (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (length : ℕ) (fresh : live.carried.reward = ⟨0⟩)
    (counted : List (feasibleFind config mode live length).Index) (distinct : counted.Nodup)
    (many : 49 + 7 * length < counted.length) {agent : Kernel.Agent Grid.interface}
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    (finds : Kernel.Finds (feasibleFind config mode live length)
      (fun _ => completion config mode length) length (49 + 7 * length) counted agent)
    (retains : Kernel.Retains (feasibleFind config mode live length)
      (fun _ => completion config mode length) length agent)
    (stream : ∀ target, OneStream.oneStream.Meets
      ((findRung config mode live length counted agent updates work resume).learner target)) :
    Mission (findRung config mode live length counted agent updates work resume) :=
  visits_mission (find_pays mode live length fresh) (feasibleFind_conceals mode live length length)
    (feasibleFind_covered config mode live length) (fun target => target.2) distinct many finds
    retains stream

/-! ## A reference agent meets the statement -/

/-- **The mission's statement is satisfiable on the executed grid world.** In the witness world,
with visits of seven steps and the covering bound 98, there is a list of 147 distinct feasible
concealed targets such that the retracing agent, with the reward as its signal and the witness's
three walks as its exploration, achieves goals over the class with those targets counted: the
mission's statement holds of its rung, with every premise discharged. -/
theorem witness_mission (mode : TaskFeatureMode) :
    ∃ counted : List (feasibleFind witnessConfig mode witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 147 ∧
        Mission (retraceRung (feasibleFind witnessConfig mode witnessLive 7) 7 2 reward
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
  refine ⟨(members.attach.map ⟨admitted, injective⟩).toList, Finset.nodup_toList _, size, ?_⟩
  refine retrace_mission (find_pays mode witnessLive 7 rfl)
    (feasibleFind_conceals mode witnessLive 7 7) (feasibleFind_covered witnessConfig mode
      witnessLive 7) (fun target => target.2) (Finset.nodup_toList _) (by rw [size]; decide) 2
    witnessExplore (fun index listed => ?_)
  obtain ⟨target, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_toList.mp listed)
  exact explored target.1 target.2

/-! ## The executed agent, from named premises -/

section executed

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {planning : PlanningSelection}

/-- The rung of the executed agent from a state of it, on the feasible concealed targets of a host
world in visits. The agent's reports of its own steps are parameters. -/
def executedRung (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (counted : List (feasibleFind config profile.taskMode live length).Index)
    (updates : Agent Grid.interface profile features criterion dimension planning →
      Percept Grid.interface × ℚ → List OneStream.Update)
    (work : Agent Grid.interface profile features criterion dimension planning →
      Percept Grid.interface × ℚ → ℕ)
    (resume : Agent Grid.interface profile features criterion dimension planning →
      Agent Grid.interface profile features criterion dimension planning) : Rung :=
  findRung config profile.taskMode live length counted (executedAgent state) updates work resume

/-- **Obligation 9, first successes; what obligation 4's exploration premise must deliver**
(rbeauchamp/acorn#232, with rbeauchamp/acorn#170). The executed agent, from the given state, solves
each of more than `49 + 7 length` counted members on some visit. Open: no theorem says its
exploration meets a concealed target. -/
def ExecutedFinds (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (counted : List (feasibleFind config profile.taskMode live length).Index) : Prop :=
  Kernel.Finds (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length (49 + 7 * length) counted
    (executedAgent state)

/-- **Obligation 9, retention** (rbeauchamp/acorn#232, with rbeauchamp/acorn#171). The executed
agent, from the given state, solves on every later visit each member it has solved on one visit.
Open: no theorem says the agent learns a route from its first reward. -/
def ExecutedRetains (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ) : Prop :=
  Kernel.Retains (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length (executedAgent state)

/-- **The executed agent achieves goals over the concealed targets, from named premises.** Over a
host world that carries a reward of zero, with a list of distinct counted members longer than the
covering bound: if the executed agent finds and retains, and its reports meet the four premises of
contract 3, the mission's statement holds of its rung. Each premise names an open obligation of
`docs/mission-contract.md`; none is proved. -/
theorem executed_mission
    (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (fresh : live.carried.reward = ⟨0⟩)
    (counted : List (feasibleFind config profile.taskMode live length).Index)
    (distinct : counted.Nodup) (many : 49 + 7 * length < counted.length)
    (updates : Agent Grid.interface profile features criterion dimension planning →
      Percept Grid.interface × ℚ → List OneStream.Update)
    (work : Agent Grid.interface profile features criterion dimension planning →
      Percept Grid.interface × ℚ → ℕ)
    (resume : Agent Grid.interface profile features criterion dimension planning →
      Agent Grid.interface profile features criterion dimension planning)
    (finds : ExecutedFinds state config live length counted)
    (retains : ExecutedRetains state config live length)
    (memory : MemoryBounded (executedRung state config live length counted updates work resume))
    (bounded : WorkBounded (executedRung state config live length counted updates work resume))
    (once : LearnsOnce (executedRung state config live length counted updates work resume))
    (discipline :
      KeepsDiscipline (executedRung state config live length counted updates work resume)) :
    Mission (executedRung state config live length counted updates work resume) :=
  find_mission config profile.taskMode live length fresh counted distinct many finds retains
    (Rung.stream_met memory bounded once discipline)

/-- **The executed agent's statement for all but a fraction of runs.** For a finite family of states
of the executed agent, over a class as in `executed_mission`: where the agent finds from all but a
fraction `left` of the states and retains from all but a fraction `right`, and its reports meet the
four premises of contract 3 from every state of the family, the mission's statement holds from all
but the fraction `left + right` of the states. This is the form of the statement under fork F4;
how the fractions depend on the class and the number of visits is obligation 15. -/
theorem executed_mission_allBut {Run : Type} (runs : Finset Run)
    (state : Run → Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (fresh : live.carried.reward = ⟨0⟩)
    (counted : List (feasibleFind config profile.taskMode live length).Index)
    (distinct : counted.Nodup) (many : 49 + 7 * length < counted.length)
    (updates : Agent Grid.interface profile features criterion dimension planning →
      Percept Grid.interface × ℚ → List OneStream.Update)
    (work : Agent Grid.interface profile features criterion dimension planning →
      Percept Grid.interface × ℚ → ℕ)
    (resume : Agent Grid.interface profile features criterion dimension planning →
      Agent Grid.interface profile features criterion dimension planning)
    (left right : ℚ)
    (finds : Kernel.AllBut left runs fun run =>
      ExecutedFinds (state run) config live length counted)
    (retains : Kernel.AllBut right runs fun run => ExecutedRetains (state run) config live length)
    (invariants : ∀ run ∈ runs,
      MemoryBounded (executedRung (state run) config live length counted updates work resume) ∧
      WorkBounded (executedRung (state run) config live length counted updates work resume) ∧
      LearnsOnce (executedRung (state run) config live length counted updates work resume) ∧
      KeepsDiscipline
        (executedRung (state run) config live length counted updates work resume)) :
    Kernel.AllBut (left + right) runs fun run =>
      Mission (executedRung (state run) config live length counted updates work resume) :=
  (finds.and retains).mono fun run member both =>
    executed_mission (state run) config live length fresh counted distinct many updates work
      resume both.1 both.2 (invariants run member).1 (invariants run member).2.1
      (invariants run member).2.2.1 (invariants run member).2.2.2

end executed

end AcornVerif.CurrentConcealedTargetMission
