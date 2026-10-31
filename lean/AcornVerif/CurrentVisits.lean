/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Visits
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentConcealedTarget
import AcornVerif.CurrentAccounting
import AcornVerif.CurrentHostLoop

/-!
# Every decision of a run of visits is the kernel's

`Host.VisitRun.decide` is one decision of a run of visits, `Host.VisitRun.after` their fold and
`Host.runVisitDecisions` the native loop. These statements relate them to the kernel's world in
visits (`Kernel.visits`) of the grid world, from the run's held start, with the agent of the
construction's step order (`CurrentHostLoop.orderedAgent`).

- `executed_visits_closed_loop`: after every number of decisions a run reached, the kernel's state
  holds the run's world, carried result and step count, the kernel's memory and the run's agent have
  the same learners, and the action of the next decision that observes successfully, whether the
  world takes it, refuses it or does not receive it, decodes the kernel's action at that time.
- `executed_visits_solved`: a run of a member of the class of concealed targets has completed one
  visit for every `cap + 1` decisions, and reports a completed visit solved exactly when
  `Kernel.SolvesOnVisit` holds.
- `runVisitDecisions_complete`: a value the native loop returned agrees with the fold.
- `executed_runs_first_success` and `comparator_runs_need`: the kernel's two bounds, for one visit
  index fixed for all members, over values the native loop returned.
- `visits_resumed`: the account of a crash.

Hypotheses and limits. A refused observation produces no action, so nothing is said of one. That a
world never refuses, that the loop returns, that any agent learns or solves anything are not stated.
The native loop is read as a function on the world token through the tree's `Host.returned_bind`,
`Host.returned_lazyPure` and `Host.returned_pure`; that the compiled code computes these definitions
is assumed, as for every executing definition. No theorem relates the native entry
`acorn-core visits` to the loop: that it starts the loop from the admitted world and target rests on
reading it.

A crash is a loop that did not return, so `runVisitDecisions_complete` says nothing of one. The loop
writes a checkpoint only at a visit's boundary, so a crash leaves the last completed save or none.
`visits_resumed` takes a run at a boundary, bytes a save of its agent wrote and the state resumed
from those bytes, and does not say that the bytes a later process loads are the bytes this run saved
(a file is not authenticated) or that the later process was given the same start and cap (the
checkpoint holds neither). It also takes as given that a completed save survives the crash and a
partial one leaves the old file: `Acorn.Host.Checkpoint.IO` states what a saved report establishes
on each platform, and where a sync stops at the drive a power loss can lose this save and the image
it replaced. Beyond the learners nothing about the agent is claimed: resuming begins a new session,
so the evaluator's session statistics and pending records restart, and the host's report, action
fingerprint and checkpoint schedule are not saved.
-/

namespace AcornVerif.CurrentVisits
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentAccounting AcornVerif.CurrentHostLoop
open AcornVerif.CurrentConcealedTarget

variable {order : StepOrder} {config : Host.WorldConfig} {α β : Type} {goal : Host.Goal}
  {cap : UInt64}

/-- The kernel's world in visits of a run: the grid world from the run's held start, in visits of
the run's cap. -/
abbrev visitWorld (mode : TaskFeatureMode) (start : Host.VisitStart config goal) (cap : UInt64) :
    Kernel.World Grid.interface :=
  Kernel.visits (gridWorld config mode) (some ⟨start.world, start.carried⟩) cap.toNat

/-- The first state of the kernel's world in visits of a run. -/
abbrev visitOrigin (mode : TaskFeatureMode) (start : Host.VisitStart config goal) (cap : UInt64) :
    (visitWorld mode start cap).State :=
  Kernel.visitStart (gridWorld config mode) (some ⟨start.world, start.carried⟩) cap.toNat

/-- A kernel agent simulates a host's callbacks under a relation of their states: the host's whole
step on an observation and a carried result takes the action of the kernel agent's decision on the
grid percept of that observation and result and keeps the relation, and the host's two accounting
writes keep it. -/
structure Simulates (callbacks : Host.AgentCallbacks order α β) (mode : TaskFeatureMode)
    (agent : Kernel.Agent Grid.interface) (related : α → agent.Memory → Prop) : Prop where
  /-- The whole step. -/
  act : ∀ state memory observation (result : Host.RawStepResult), related state memory →
    (callbacks.act state observation result).1 = Host.Action.fromIndex
        (agent.act memory (Grid.percept mode observation result.reward result.events.done)).1.val ∧
      related (callbacks.act state observation result).2
        (agent.act memory (Grid.percept mode observation result.reward result.events.done)).2
  /-- The environment write. -/
  environment : ∀ state memory family reward, related state memory →
    related (callbacks.recordEnvironment state family reward) memory
  /-- The attempt write. -/
  attempt : ∀ state memory family visit steps achieved, related state memory →
    related (callbacks.recordAttempt state family visit steps achieved) memory

/-- The state of the kernel's world in visits that a run stands at. -/
abbrev visitHere (mode : TaskFeatureMode) (start : Host.VisitStart config goal)
    (run : Host.VisitRun config α goal cap) : (visitWorld mode start cap).State :=
  (some ⟨run.attempt.run.world, run.attempt.run.carried⟩, run.attempt.steps)

theorem release_accepted {selected : Host.OwnedStep config α goal cap}
    {environment : Host.OwnedEnvironment config α goal cap}
    (h : selected.release = .accepted environment) : environment.selected = selected := by
  unfold Host.OwnedStep.release at h
  split at h
  · cases h
  · cases h
    rfl

theorem release_refused {selected learned : Host.OwnedStep config α goal cap}
    {error : Host.WorldError}
    (h : selected.release = .refused error learned) : learned = selected := by
  unfold Host.OwnedStep.release at h
  split at h
  · cases h
    rfl
  · cases h

theorem selectOwned_action (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).action =
      (callbacks.act input.before.run.agent input.observation input.before.run.carried).1 := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

theorem selectOwned_agent (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).agent =
      (callbacks.act input.before.run.agent input.observation input.before.run.carried).2 := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

theorem selectOwned_world (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).before.run.world = input.before.run.world := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

theorem selectOwned_steps (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).before.steps = input.before.steps := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

theorem visit_step_within (mode : TaskFeatureMode) (start : Host.VisitStart config goal)
    (live : Live config) (steps : Fin (cap.toNat + 1)) (within : steps.val < cap.toNat)
    (action : Kernel.Act Grid.interface) :
    (visitWorld mode start cap).step (some live, steps) action =
      (advance live action, ⟨steps.val + 1, by omega⟩) :=
  dite_eq_left within

theorem visit_step_last (mode : TaskFeatureMode) (start : Host.VisitStart config goal)
    (live : Live config) (steps : Fin (cap.toNat + 1)) (last : ¬ steps.val < cap.toNat)
    (action : Kernel.Act Grid.interface) :
    (visitWorld mode start cap).step (some live, steps) action =
      (some ⟨start.world, start.carried⟩, ⟨0, Nat.succ_pos _⟩) :=
  dite_eq_right last

/-- One decision of a run, accepted or at a visit's last state, is one interaction of the kernel. -/
theorem decide_kernel {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related)
    (start : Host.VisitStart config goal) (run : Host.VisitRun config α goal cap)
    (memory : agent.Memory) (holds : related run.attempt.run.agent memory) :
    (∀ decision, run.decide callbacks start = .ok decision →
      decision.action = Host.Action.fromIndex
        (agent.act memory ((visitWorld mode start cap).percept (visitHere mode start run))).1.val ∧
      (visitWorld mode start cap).step (visitHere mode start run)
          (agent.act memory ((visitWorld mode start cap).percept (visitHere mode start run))).1 =
        visitHere mode start decision.next ∧
      related decision.next.attempt.run.agent
        (agent.act memory ((visitWorld mode start cap).percept (visitHere mode start run))).2) ∧
    (∀ error learned, run.decide callbacks start = .error ⟨error, some learned⟩ →
      learned.action = Host.Action.fromIndex
        (agent.act memory ((visitWorld mode start cap).percept (visitHere mode start
            run))).1.val) := by
  obtain ⟨attempt, achieved, solved⟩ := run
  have perceived : ∀ observation, attempt.run.world.observe = .ok observation →
      (visitWorld mode start cap).percept
          (visitHere mode start (⟨attempt, achieved, solved⟩ : Host.VisitRun config α goal cap)) =
        Grid.percept mode observation attempt.run.carried.reward
          attempt.run.carried.events.done :=
    fun observation seen => percept_live mode ⟨attempt.run.world, attempt.run.carried⟩
        observation seen
  constructor
  · intro decision decided
    unfold Host.VisitRun.decide at decided
    dsimp only at decided
    split at decided
    · cases decided
    · rename_i observation seen
      rw [perceived observation seen]
      have sim := simulates.act attempt.run.agent memory observation attempt.run.carried holds
      split at decided
      · rename_i within
        split at decided
        · cases decided
        · rename_i environment accepted
          have sameStage := release_accepted accepted
          obtain ⟨selected, next, result, stepped⟩ := environment
          dsimp only at sameStage
          subst sameStage
          cases decided
          have action := selectOwned_action callbacks ⟨attempt, within, observation, seen⟩
          have learned := selectOwned_agent callbacks ⟨attempt, within, observation, seen⟩
          have world := selectOwned_world callbacks ⟨attempt, within, observation, seen⟩
          have steps := selectOwned_steps callbacks ⟨attempt, within, observation, seen⟩
          dsimp only at action learned world steps
          refine ⟨action.trans sim.1, ?_, ?_⟩
          · have taken := stepped
            rw [world, action, sim.1] at taken
            have here := advance_ok ⟨attempt.run.world, attempt.run.carried⟩ _ next result taken
            refine (visit_step_within mode start ⟨attempt.run.world, attempt.run.carried⟩
              attempt.steps within _).trans ?_
            rw [here]
            refine Prod.ext rfl (Fin.ext ?_)
            change attempt.steps.val + 1 = (Host.DecisionInput.selectOwned ⟨attempt, within,
                observation, seen⟩ callbacks).before.steps.val + 1
            rw [steps]
          · simp only [Host.OwnedEnvironment.record]
            exact simulates.environment _ _ _ _ (learned ▸ sim.2)
      · rename_i within
        cases decided
        refine ⟨sim.1, ?_, simulates.attempt _ _ _ _ _ _ sim.2⟩
        exact visit_step_last mode start ⟨attempt.run.world, attempt.run.carried⟩ attempt.steps
            within _
  · intro error learned refused
    unfold Host.VisitRun.decide at refused
    dsimp only at refused
    split at refused
    · cases refused
    · rename_i observation seen
      rw [perceived observation seen]
      have sim := simulates.act attempt.run.agent memory observation attempt.run.carried holds
      split at refused
      · rename_i within
        split at refused
        · rename_i other stage answer
          cases refused
          rw [release_refused answer]
          exact (selectOwned_action callbacks ⟨attempt, within, observation, seen⟩).trans sim.1
        · cases refused
      · cases refused

/-- The state and the memory of the kernel's run, after every number of decisions a run reached. -/
theorem visits_invariant {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related)
    (start : Host.VisitStart config goal) (state : α) (behavior : UInt64)
    (holds : related state agent.initial) (time : ℕ) (run : Host.VisitRun config α goal cap)
    (reached : Host.VisitRun.after callbacks start (start.begin cap state behavior) time = .ok
        run) :
    Kernel.stateAt (visitWorld mode start cap) agent (visitOrigin mode start cap) time =
        visitHere mode start run ∧
      related run.attempt.run.agent
        (Kernel.memoryAt (visitWorld mode start cap) agent (visitOrigin mode start cap) time) := by
  induction time generalizing run with
  | zero =>
    cases reached
    exact ⟨rfl, holds⟩
  | succ time ih =>
    unfold Host.VisitRun.after at reached
    split at reached
    · cases reached
    · rename_i previous prior
      split at reached
      · cases reached
      · rename_i decision decided
        cases reached
        obtain ⟨here, memory⟩ := ih previous prior
        obtain ⟨_, moved, kept⟩ := (decide_kernel simulates start previous _ memory).1 decision
            decided
        constructor
        · change (visitWorld mode start cap).step
            (Kernel.stateAt (visitWorld mode start cap) agent (visitOrigin mode start cap) time)
            (agent.act (Kernel.memoryAt (visitWorld mode start cap) agent (visitOrigin mode
                start cap) time)
              ((visitWorld mode start cap).percept
                (Kernel.stateAt (visitWorld mode start cap) agent (visitOrigin mode start cap)
                    time))).1 = _
          rw [here]
          exact moved
        · change related _ (agent.act
            (Kernel.memoryAt (visitWorld mode start cap) agent (visitOrigin mode start cap) time)
            ((visitWorld mode start cap).percept
              (Kernel.stateAt (visitWorld mode start cap) agent (visitOrigin mode start cap)
                  time))).2
          rw [here]
          exact kept

/-- **Every decision of a run of visits is the kernel's.** After every number of decisions the run
reached, its world, carried result and step count are the state of the kernel's world in visits,
its agent stands in the relation to the kernel's memory, and the action of its next decision,
accepted, refused or dropped at a visit's last state, decodes the kernel's action at that time. -/
theorem visits_simulation {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related)
    (start : Host.VisitStart config goal) (state : α) (behavior : UInt64)
    (holds : related state agent.initial) (time : ℕ) (run : Host.VisitRun config α goal cap)
    (reached : Host.VisitRun.after callbacks start (start.begin cap state behavior) time = .ok
        run) :
    Kernel.stateAt (visitWorld mode start cap) agent (visitOrigin mode start cap) time =
        (some ⟨run.attempt.run.world, run.attempt.run.carried⟩, run.attempt.steps) ∧
      related run.attempt.run.agent
        (Kernel.memoryAt (visitWorld mode start cap) agent (visitOrigin mode start cap) time) ∧
      (∀ decision, run.decide callbacks start = .ok decision →
        decision.action = Host.Action.fromIndex
          (Kernel.actionAt (visitWorld mode start cap) agent (visitOrigin mode start cap)
              time).val) ∧
      (∀ error learned, run.decide callbacks start = .error ⟨error, some learned⟩ →
        learned.action = Host.Action.fromIndex
          (Kernel.actionAt (visitWorld mode start cap) agent (visitOrigin mode start cap)
              time).val) := by
  obtain ⟨here, memory⟩ := visits_invariant simulates start state behavior holds time run reached
  obtain ⟨accepted, refused⟩ := decide_kernel simulates start run _ memory
  refine ⟨here, memory, ?_, ?_⟩
  · intro decision decided
    have taken := (accepted decision decided).1
    rw [← here] at taken
    exact taken
  · intro error learned answer
    have taken := refused error learned answer
    rw [← here] at taken
    exact taken

/-- What a decision does to a run's report. -/
theorem decide_cases {callbacks : Host.AgentCallbacks order α β}
    {start : Host.VisitStart config goal} {run : Host.VisitRun config α goal cap}
    {decision : Host.VisitDecision config α goal cap}
    (decided : run.decide callbacks start = .ok decision) :
    (decision.next.solved = run.solved ∧
      decision.next.attempt.steps.val = run.attempt.steps.val + 1 ∧
      decision.next.achieved = (run.achieved || decision.next.attempt.run.carried.events.done) ∧
      decision.next.attempt.run.carried.events.done =
        decision.next.attempt.run.world.goalSatisfied ∧
      decision.outcome = none) ∨
    (run.attempt.steps.val = cap.toNat ∧ decision.next.solved = run.solved.push run.achieved ∧
      decision.next.attempt.steps.val = 0 ∧ decision.next.achieved = false ∧
      decision.outcome.isSome ∧ decision.next.attempt.run.world = start.world ∧
      decision.next.attempt.run.carried = start.carried) := by
  obtain ⟨attempt, achieved, solved⟩ := run
  unfold Host.VisitRun.decide at decided
  dsimp only at decided
  split at decided
  · cases decided
  · split at decided
    · rename_i within
      split at decided
      · cases decided
      · rename_i environment accepted
        have sameStage := release_accepted accepted
        obtain ⟨selected, next, result, stepped⟩ := environment
        dsimp only at sameStage
        subst sameStage
        cases decided
        left
        refine ⟨rfl, ?_, rfl, Host.World.step_completion _ _ _ _ stepped, rfl⟩
        simp only [Host.OwnedEnvironment.record]
        rw [selectOwned_steps]
    · rename_i within
      cases decided
      right
      have bound := attempt.steps.isLt
      refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      change attempt.steps.val = cap.toNat
      omega

/-- The goal of a run's installed target is met at a time of the kernel's run. -/
abbrev MetAt (mode : TaskFeatureMode) (start : Host.VisitStart config goal) (cap : UInt64)
    (agent : Kernel.Agent Grid.interface) (time : ℕ) : Prop :=
  (completion config mode cap.toNat).satisfied
    (Kernel.stateAt (visitWorld mode start cap) agent (visitOrigin mode start cap) time).1

/-- A run's report, at every time. -/
theorem visits_report {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related)
    (start : Host.VisitStart config goal) (state : α) (behavior : UInt64)
    (holds : related state agent.initial) (time : ℕ) (run : Host.VisitRun config α goal cap)
    (reached : Host.VisitRun.after callbacks start (start.begin cap state behavior) time = .ok
        run) :
    time = run.solved.size * (cap.toNat + 1) + run.attempt.steps.val ∧
      (run.achieved = true ↔ ∃ step, 1 ≤ step ∧ step ≤ run.attempt.steps.val ∧
        MetAt mode start cap agent (run.solved.size * (cap.toNat + 1) + step)) ∧
      ∀ visit reported, run.solved[visit]? = some reported →
        (reported = true ↔ ∃ step, 1 ≤ step ∧ step ≤ cap.toNat ∧
          MetAt mode start cap agent (visit * (cap.toNat + 1) + step)) := by
  induction time generalizing run with
  | zero =>
    cases reached
    refine ⟨by simp [Host.VisitStart.begin, Host.VisitStart.attempt], ?_, ?_⟩
    · simp [Host.VisitStart.begin, Host.VisitStart.attempt]
    · intro visit reported found
      simp [Host.VisitStart.begin] at found
  | succ time ih =>
    have whole := reached
    unfold Host.VisitRun.after at reached
    split at reached
    · cases reached
    · rename_i previous prior
      split at reached
      · cases reached
      · rename_i decision decided
        cases reached
        obtain ⟨clock, soFar, earlier⟩ := ih previous prior
        have here := (visits_invariant simulates start state behavior holds (time + 1)
          decision.next whole).1
        have metNow : MetAt mode start cap agent (time + 1) ↔
            decision.next.attempt.run.world.goalSatisfied = true := by
          unfold MetAt
          rw [here]
          constructor
          · rintro ⟨live, same, done⟩
            cases same
            exact done
          · intro done
            exact ⟨_, rfl, done⟩
        rcases decide_cases decided with ⟨same, steps, achieved, done, _⟩ | ⟨atEnd, pushed,
            zero, cleared, _⟩
        · refine ⟨by rw [same, steps]; omega, ?_, ?_⟩
          · rw [same, steps, achieved, Bool.or_eq_true, soFar, done]
            constructor
            · rintro (⟨step, low, high, met⟩ | now)
              · exact ⟨step, low, by omega, met⟩
              · refine ⟨previous.attempt.steps.val + 1, by omega, by omega, ?_⟩
                have index : previous.solved.size * (cap.toNat + 1) +
                    (previous.attempt.steps.val + 1) = time + 1 := by omega
                rw [index]
                exact metNow.mpr now
            · rintro ⟨step, low, high, met⟩
              by_cases last : step = previous.attempt.steps.val + 1
              · right
                subst last
                have index : previous.solved.size * (cap.toNat + 1) +
                    (previous.attempt.steps.val + 1) = time + 1 := by omega
                rw [index] at met
                exact metNow.mp met
              · left
                exact ⟨step, low, by omega, met⟩
          · rw [same]
            exact earlier
        · refine ⟨?_, ?_, ?_⟩
          · rw [pushed, zero, Array.size_push, Nat.add_mul, Nat.one_mul]
            omega
          · rw [cleared, zero]
            constructor
            · intro absurdity
              cases absurdity
            · rintro ⟨step, low, high, _⟩
              omega
          · intro visit reported found
            rw [pushed, Array.getElem?_push] at found
            split at found
            · rename_i last
              cases found
              subst last
              rw [soFar, atEnd]
            · exact earlier visit reported found

/-- **What a run reports is the kernel's solving on a visit.** A run of the class of concealed
targets has completed one visit for every `cap + 1` decisions, and it reports a completed visit
solved exactly when the kernel's agent solves the member on that visit. -/
theorem visits_solved {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related) (live : Live config)
    (target : (findClass config mode live).Index) (state : α) (behavior : UInt64)
    (holds : related state agent.initial) (time : ℕ)
    (run : Host.VisitRun config α (.find target.1) cap)
    (reached : Host.VisitRun.after callbacks
      (Host.VisitStart.install live.world live.carried (.find target.1))
      ((Host.VisitStart.install live.world live.carried (.find target.1)).begin cap state behavior)
      time = .ok run) :
    run.solved.size = time / (cap.toNat + 1) ∧
      ∀ visit reported, run.solved[visit]? = some reported →
        (reported = true ↔ Kernel.SolvesOnVisit (findClass config mode live)
          (fun _ => completion config mode cap.toNat) cap.toNat agent visit target) := by
  obtain ⟨clock, _, earlier⟩ := visits_report simulates _ state behavior holds time run reached
  refine ⟨?_, fun visit reported found => earlier visit reported found⟩
  have bound := run.attempt.steps.isLt
  rw [clock, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
    Nat.div_eq_of_lt bound, Nat.zero_add]

/-- The fold from one more decision, from its first decision. -/
theorem after_succ (callbacks : Host.AgentCallbacks order α β) (start : Host.VisitStart config goal)
    (initial : Host.VisitRun config α goal cap) (time : ℕ) :
    Host.VisitRun.after callbacks start initial (time + 1) =
      match initial.decide callbacks start with
      | .error refusal => .error refusal
      | .ok decision => Host.VisitRun.after callbacks start decision.next time := by
  induction time with
  | zero =>
    rfl
  | succ time ih =>
    rw [Host.VisitRun.after, ih]
    cases initial.decide callbacks start with
    | error refusal => rfl
    | ok decision => rfl

/-- What a native run of visits may return from a run within a budget of decisions. A refusal is
the refusal of the next decision after fewer decisions than the budget. Any other value holds the
fold after a number of decisions within the budget: all of them when the budget ran out, and, when
a stop was honored, a number that leaves the run at the start of a visit: the held world and result,
a count of zero and no goal met. -/
def VisitsAgree (callbacks : Host.AgentCallbacks order α β) (start : Host.VisitStart config goal)
    (initial : Host.VisitRun config α goal cap) (fuel : ℕ) :
    Except (Host.Refusal config α goal cap) (Host.VisitsResult config α goal cap) → Prop
  | .error refusal => ∃ time run, time < fuel ∧
      Host.VisitRun.after callbacks start initial time = .ok run ∧
      run.decide callbacks start = .error refusal
  | .ok result => ∃ time, time ≤ fuel ∧
      Host.VisitRun.after callbacks start initial time = .ok result.run ∧
      (result.ending = .complete → time = fuel) ∧
      (result.ending = .stopped → result.run.attempt.run.world = start.world ∧
        result.run.attempt.run.carried = start.carried ∧ result.run.attempt.steps.val = 0 ∧
        result.run.achieved = false)

/-- The native result after a first decision is a native result of one more decision. -/
theorem lift_complete {callbacks : Host.AgentCallbacks order α β}
    {start : Host.VisitStart config goal} {initial : Host.VisitRun config α goal cap} {fuel : ℕ}
    {decision : Host.VisitDecision config α goal cap}
    (answer : initial.decide callbacks start = .ok decision)
    (inner : Except (Host.Refusal config α goal cap) (Host.VisitsResult config α goal cap))
    (found : VisitsAgree callbacks start decision.next fuel inner) :
    VisitsAgree callbacks start initial (fuel + 1) inner := by
  cases inner with
  | error refusal =>
    obtain ⟨time, run, bound, ran, refused⟩ := found
    exact ⟨time + 1, run, by omega, by rw [after_succ, answer]; exact ran, refused⟩
  | ok result =>
    obtain ⟨time, bound, ran, complete, stopped⟩ := found
    exact ⟨time + 1, by omega, by rw [after_succ, answer]; exact ran,
      fun same => by rw [complete same], stopped⟩

/-- **The native loop returns the pure fold.** For every callback record, observer, stop reader,
budget, run, resource record, checkpoint capability and world token: a value the loop returned
agrees with the fold (`VisitsAgree`). Nothing here says that the loop returns. -/
theorem runVisitDecisions_complete (callbacks : Host.AgentCallbacks order α β)
    (observer : Host.StreamObserver β) (start : Host.VisitStart config goal)
    (readStop : BaseIO Bool) (fuel : ℕ) (initial : Host.VisitRun config α goal cap)
    (resources : Host.RunnerResources)
    (checkpoint : Option (Host.WritableCheckpoint × (α → System.FilePath → IO Unit)))
    (world after : Void IO.RealWorld)
    (value : Except (Host.Refusal config α goal cap) (Host.VisitsResult config α goal cap))
    (returned : Host.runVisitDecisions callbacks observer start readStop fuel initial resources
      checkpoint world = .ok value after) :
    VisitsAgree callbacks start initial fuel value := by
  induction fuel generalizing initial resources checkpoint world with
  | zero =>
    unfold Host.runVisitDecisions at returned
    have same := Host.returned_pure _ _ _ _ returned
    subst same
    exact ⟨0, le_refl _, rfl, fun _ => rfl, fun stopped => by cases stopped⟩
  | succ fuel ih =>
    unfold Host.runVisitDecisions at returned
    obtain ⟨decided, w1, ran, returned⟩ := Host.returned_bind _ _ _ _ _ returned
    have decidedEq := Host.returned_lazyPure _ _ _ _ ran
    subst decidedEq
    cases answer : initial.decide callbacks start with
    | error refusal =>
      rw [answer] at returned
      have same := Host.returned_pure _ _ _ _ returned
      subst same
      exact ⟨0, initial, by omega, rfl, answer⟩
    | ok decision =>
      rw [answer] at returned
      dsimp only at returned
      cases outcome : decision.outcome with
      | none =>
        rw [outcome] at returned
        exact lift_complete answer _ (ih decision.next resources checkpoint w1 returned)
      | some row =>
        rw [outcome] at returned
        dsimp only at returned
        obtain ⟨notified, w2, _, returned⟩ := Host.returned_bind _ _ _ _ _ returned
        obtain ⟨stopping, w3, _, returned⟩ := Host.returned_bind _ _ _ _ _ returned
        obtain ⟨saved, w4, _, returned⟩ := Host.returned_bind _ _ _ _ _ returned
        cases stopping with
        | true =>
          simp only [↓reduceIte] at returned
          have same := Host.returned_pure _ _ _ _ returned
          subst same
          have boundary : decision.next.attempt.run.world = start.world ∧
              decision.next.attempt.run.carried = start.carried ∧
              decision.next.attempt.steps.val = 0 ∧ decision.next.achieved = false := by
            rcases decide_cases answer with ⟨_, _, _, _, none⟩ |
                ⟨_, _, zero, cleared, _, sameWorld, sameCarried⟩
            · rw [outcome] at none
              cases none
            · exact ⟨sameWorld, sameCarried, zero, cleared⟩
          refine ⟨1, by omega, ?_, (fun complete => by cases complete), fun _ => boundary⟩
          rw [after_succ, answer]
          rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at returned
          exact lift_complete answer _ (ih decision.next saved _ w4 returned)

/-- A completed visit of a value a native run of visits returned, with what it reports. -/
def ReportedVisit (callbacks : Host.AgentCallbacks order α β) (start : Host.VisitStart config goal)
    (cap : UInt64) (state : α) (visit : ℕ) (reported : Bool) : Prop :=
  ∃ (observer : Host.StreamObserver β) (readStop : BaseIO Bool) (fuel : ℕ) (behavior : UInt64)
    (resources : Host.RunnerResources)
    (checkpoint : Option (Host.WritableCheckpoint × (α → System.FilePath → IO Unit)))
    (world after : Void IO.RealWorld) (result : Host.VisitsResult config α goal cap),
    Host.runVisitDecisions callbacks observer start readStop fuel (start.begin cap state behavior)
        resources checkpoint world = .ok (.ok result) after ∧
      result.run.solved[visit]? = some reported

theorem reported_solves {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related) (live : Live config)
    (target : (findClass config mode live).Index) (state : α)
    (holds : related state agent.initial) (visit : ℕ) (reported : Bool)
    (report : ReportedVisit callbacks
      (Host.VisitStart.install live.world live.carried (.find target.1)) cap state visit reported) :
    reported = true ↔ Kernel.SolvesOnVisit (findClass config mode live)
      (fun _ => completion config mode cap.toNat) cap.toNat agent visit target := by
  obtain ⟨observer, readStop, fuel, behavior, resources, checkpoint, world, after, result,
    returned, flag⟩ := report
  obtain ⟨time, _, ran, _, _⟩ := runVisitDecisions_complete callbacks observer _ readStop fuel _
    resources checkpoint world after (.ok result) returned
  exact (visits_solved simulates live target state behavior holds time result.run ran).2 visit
    reported flag

/-- Agents whose memories stay in a relation, from related first memories, run one path of states:
the relation is kept at every time, and every decision gives one action. -/
theorem related_loop {first second : Kernel.Agent Grid.interface}
    (related : first.Memory → second.Memory → Prop)
    (initial : related first.initial second.initial)
    (kept : ∀ left right percept, related left right →
      (first.act left percept).1 = (second.act right percept).1 ∧
        related (first.act left percept).2 (second.act right percept).2)
    (world : Kernel.World Grid.interface) (start : world.State) (time : ℕ) :
    (Kernel.loop world first start time).1 = (Kernel.loop world second start time).1 ∧
      related (Kernel.loop world first start time).2 (Kernel.loop world second start time).2 := by
  induction time with
  | zero => exact ⟨rfl, initial⟩
  | succ time ih =>
    have decided := kept _ _ (world.percept (Kernel.loop world first start time).1) ih.2
    change world.step (Kernel.loop world first start time).1
          (first.act (Kernel.loop world first start time).2
            (world.percept (Kernel.loop world first start time).1)).1 =
        world.step (Kernel.loop world second start time).1
          (second.act (Kernel.loop world second start time).2
            (world.percept (Kernel.loop world second start time).1)).1 ∧
      related
        (first.act (Kernel.loop world first start time).2
          (world.percept (Kernel.loop world first start time).1)).2
        (second.act (Kernel.loop world second start time).2
          (world.percept (Kernel.loop world second start time).1)).2
    rw [← ih.1]
    exact ⟨congrArg _ decided.1, decided.2⟩

/-- The learners of a kernel memory and of a construction's state. -/
abbrev sameLearners (construction : AgentConstruction) (state : construction.State)
    (host : construction.State)
    (memory : (orderedAgent construction.order state.agent).Memory) : Prop :=
  learners host.agent.control = learners memory.control

/-- The executed agent of a construction simulates its callbacks, at every step order. -/
theorem construction_simulates (construction : AgentConstruction) (state : construction.State) :
    Simulates construction.callbacks construction.profile.taskMode
      (orderedAgent construction.order state.agent) (sameLearners construction state) := by
  refine ⟨?_, ?_, ?_⟩
  · intro host memory observation result same
    have whole := AgentConstruction.callbacks_act construction host observation result
    have ordered := Agent.callbacks_ordered construction.order host.agent observation result
    have kept := actOrdered_learners host.agent memory same construction.order
      (Grid.percept construction.profile.taskMode observation result.reward result.events.done)
    constructor
    · refine (congrArg Prod.fst whole).trans ((congrArg Prod.fst ordered).trans ?_)
      exact congrArg (fun decision => Host.Action.fromIndex decision.action.val) kept.1
    · have learned : (construction.callbacks.act host observation result).2.agent =
          (host.agent.actOrdered construction.order (Grid.percept construction.profile.taskMode
            observation result.reward result.events.done)).1 :=
        (congrArg Prod.snd whole).trans (congrArg Prod.snd ordered)
      exact (congrArg (fun next => learners next.control) learned).trans kept.2
  · intro host memory family reward same
    exact same
  · intro host memory family visit steps achieved same
    exact same

/-- The comparator's kernel agent simulates the comparator's callbacks: their memories are one
stream. -/
theorem comparator_simulates (mode : TaskFeatureMode) (stream : Rng.Xoshiro256) :
    Simulates Host.comparatorCallbacks mode (comparator stream)
      (fun (host : Rng.Xoshiro256) (memory : Rng.Xoshiro256) => host = memory) := by
  refine ⟨?_, ?_, ?_⟩
  · intro host memory observation result same
    subst same
    exact ⟨(Host.Action.index_roundtrip _).symm, rfl⟩
  · intro host memory family reward same
    exact same
  · intro host memory family visit steps achieved same
    exact same

/-- **The executed agent at every step of every visit.** For every construction, at every step
order, from every state of it: after every number of decisions a run reached, the kernel's world in
visits holds the run's world, carried result and step count, the run's agent has the kernel memory's
learners, and the action of the run's next decision, whether the world takes it, refuses it or, at a
visit's last state, does not receive it, decodes the kernel's action at that time. -/
theorem executed_visits_closed_loop (construction : AgentConstruction)
    (start : Host.VisitStart config goal) (cap : UInt64) (state : construction.State)
    (behavior : UInt64) (time : ℕ) (run : Host.VisitRun config construction.State goal cap)
    (reached : Host.VisitRun.after construction.callbacks start (start.begin cap state behavior)
      time = .ok run) :
    Kernel.stateAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order state.agent)
        (visitOrigin construction.profile.taskMode start cap) time =
      (some ⟨run.attempt.run.world, run.attempt.run.carried⟩, run.attempt.steps) ∧
    learners run.attempt.run.agent.agent.control =
      learners (Kernel.memoryAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order state.agent)
        (visitOrigin construction.profile.taskMode start cap) time).control ∧
    (∀ decision, run.decide construction.callbacks start = .ok decision →
      decision.action = Host.Action.fromIndex
        (Kernel.actionAt (visitWorld construction.profile.taskMode start cap)
          (orderedAgent construction.order state.agent)
          (visitOrigin construction.profile.taskMode start cap) time).val) ∧
    (∀ error learned, run.decide construction.callbacks start = .error ⟨error, some learned⟩ →
      learned.action = Host.Action.fromIndex
        (Kernel.actionAt (visitWorld construction.profile.taskMode start cap)
          (orderedAgent construction.order state.agent)
          (visitOrigin construction.profile.taskMode start cap) time).val) :=
  visits_simulation (construction_simulates construction state) start state behavior rfl time run
    reached

/-- **What a run of a construction reports.** The specialization of `visits_solved` to a
construction, at every step order, from every state of it. -/
theorem executed_visits_solved (construction : AgentConstruction) (live : Live config)
    (target : (findClass config construction.profile.taskMode live).Index)
    (state : construction.State) (behavior : UInt64) (time : ℕ)
    (run : Host.VisitRun config construction.State (.find target.1) cap)
    (reached : Host.VisitRun.after construction.callbacks
      (Host.VisitStart.install live.world live.carried (.find target.1))
      ((Host.VisitStart.install live.world live.carried (.find target.1)).begin cap state behavior)
      time = .ok run) :
    run.solved.size = time / (cap.toNat + 1) ∧
      ∀ visit reported, run.solved[visit]? = some reported →
        (reported = true ↔ Kernel.SolvesOnVisit
          (findClass config construction.profile.taskMode live)
          (fun _ => completion config construction.profile.taskMode cap.toNat) cap.toNat
          (orderedAgent construction.order state.agent) visit target) :=
  visits_solved (construction_simulates construction state) live target state behavior rfl time run
    reached

/-- **First success, on the runs as executed.** Take one state of a construction and, for each of
some members of the class of concealed targets, native runs of that member from that state. For one
visit index, the same for every member, the members whose runs report that visit solved and every
earlier visit unsolved number at most `49 + 7 cap`. Members solved first at a visit each chooses for
itself are not bounded here: an agent that learns may solve more of them with experience. -/
theorem executed_runs_first_success (construction : AgentConstruction) (live : Live config)
    (cap : UInt64) (state : construction.State) (visit : ℕ)
    (solved : Finset (findClass config construction.profile.taskMode live).Index)
    (each : ∀ target ∈ solved,
      ReportedVisit construction.callbacks
          (Host.VisitStart.install live.world live.carried (.find target.1)) cap state visit true ∧
        ∀ earlier, earlier < visit →
          ReportedVisit construction.callbacks
            (Host.VisitStart.install live.world live.carried (.find target.1)) cap state earlier
            false) :
    solved.card ≤ 49 + 7 * cap.toNat := by
  have simulates := construction_simulates construction state
  refine find_visits_first_success config construction.profile.taskMode live cap.toNat
    (orderedAgent construction.order state.agent) visit solved (fun target member => ⟨?_, ?_⟩)
  · exact (reported_solves simulates live target state rfl visit true (each target member).1).mp rfl
  · intro earlier before solves
    have flag := (reported_solves simulates live target state rfl earlier false
      ((each target member).2 earlier before)).mpr solves
    cases flag

/-- **Need on every visit, on the comparator's runs as executed.** For one stream and one visit
index, the same for every member, the members whose native runs report that visit solved number at
most `49 + 7 cap`. -/
theorem comparator_runs_need (mode : TaskFeatureMode) (live : Live config) (cap : UInt64)
    (stream : Rng.Xoshiro256) (visit : ℕ) (solved : Finset (findClass config mode live).Index)
    (each : ∀ target ∈ solved,
      ReportedVisit Host.comparatorCallbacks
        (Host.VisitStart.install live.world live.carried (.find target.1)) cap stream visit true) :
    solved.card ≤ 49 + 7 * cap.toNat :=
  comparator_find_visits config mode live cap.toNat stream visit solved (fun target member =>
    (reported_solves (comparator_simulates mode stream) live target stream rfl visit true
      (each target member)).mp rfl)

/-- **A crash loses nothing the kernel's run keeps.** Take a run at a visit's boundary, the bytes a
save of its agent wrote, and the state a later process resumes from those bytes. From a visit's
first state the resumed agent's kernel run is the original kernel run from that boundary: the same
states, actions and learners at every later time. So a visit a crash interrupted runs again exactly
and no learning is lost. -/
theorem visits_resumed (construction : AgentConstruction) (start : Host.VisitStart config goal)
    (cap : UInt64) (state receiver resumed : construction.State) (behavior : UInt64) (visits : ℕ)
    (run : Host.VisitRun config construction.State goal cap)
    (reached : Host.VisitRun.after construction.callbacks start (start.begin cap state behavior)
      (Host.visitDecisions cap visits) = .ok run)
    (bytes : List UInt8)
    (written : Checkpoint.saveBytes construction run.attempt.run.agent = .ok bytes)
    (loaded : Checkpoint.resume construction receiver bytes = .ok resumed) (later : ℕ) :
    Kernel.stateAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order resumed.agent)
        (visitOrigin construction.profile.taskMode start cap) later =
      Kernel.stateAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order state.agent)
        (visitOrigin construction.profile.taskMode start cap)
        (Host.visitDecisions cap visits + later) ∧
    Kernel.actionAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order resumed.agent)
        (visitOrigin construction.profile.taskMode start cap) later =
      Kernel.actionAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order state.agent)
        (visitOrigin construction.profile.taskMode start cap)
        (Host.visitDecisions cap visits + later) ∧
    learners (Kernel.memoryAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order resumed.agent)
        (visitOrigin construction.profile.taskMode start cap) later).control =
      learners (Kernel.memoryAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order state.agent)
        (visitOrigin construction.profile.taskMode start cap)
        (Host.visitDecisions cap visits + later)).control := by
  have simulates := construction_simulates construction state
  obtain ⟨_, kept⟩ := visits_invariant simulates start state behavior rfl _ run reached
  rw [CurrentCheckpoint.resume_saved construction receiver _ bytes written] at loaded
  cases loaded
  simp only [Host.visitDecisions] at kept ⊢
  have period := Kernel.visits_period (gridWorld config construction.profile.taskMode)
    (some ⟨start.world, start.carried⟩) cap.toNat
    (orderedAgent construction.order state.agent) visits
  have pair := Kernel.loop_add (visitWorld construction.profile.taskMode start cap)
    (orderedAgent construction.order state.agent)
    (visitOrigin construction.profile.taskMode start cap) (visits * (cap.toNat + 1)) later
  rw [period] at pair
  have decides : ∀ (left right : Agent Grid.interface construction.profile construction.config
      construction.criterion construction.dimension construction.planning) percept,
      learners left.control = learners right.control →
      (left.actOrdered construction.order percept).2.action =
          (right.actOrdered construction.order percept).2.action ∧
        learners (left.actOrdered construction.order percept).1.control =
          learners (right.actOrdered construction.order percept).1.control :=
    fun left right percept held =>
      ⟨congrArg (fun decision => decision.action)
        (actOrdered_learners left right held construction.order percept).1,
        (actOrdered_learners left right held construction.order percept).2⟩
  have same := related_loop
    (first := orderedAgent construction.order run.attempt.run.agent.beginSession.agent)
    (second := (orderedAgent construction.order state.agent).resume
      (Kernel.memoryAt (visitWorld construction.profile.taskMode start cap)
        (orderedAgent construction.order state.agent)
        (visitOrigin construction.profile.taskMode start cap) (visits * (cap.toNat + 1))))
    (fun (left right : Agent Grid.interface construction.profile construction.config
      construction.criterion construction.dimension construction.planning) =>
      learners left.control = learners right.control)
    kept decides (visitWorld construction.profile.taskMode start cap)
    (visitOrigin construction.profile.taskMode start cap) later
  unfold Kernel.actionAt Kernel.memoryAt Kernel.perceptAt Kernel.stateAt
  rw [pair]
  refine ⟨same.1, ?_, same.2⟩
  have taken := (decides _ _ ((visitWorld construction.profile.taskMode start cap).percept
    (Kernel.loop (visitWorld construction.profile.taskMode start cap)
      (orderedAgent construction.order run.attempt.run.agent.beginSession.agent)
      (visitOrigin construction.profile.taskMode start cap) later).1) same.2).1
  rw [same.1] at taken ⊢
  exact taken

/-- **The entry's refusal is the class's condition.** A target's goal box holds a world's body,
which `Host.targetHoldsBody` decides, exactly when the box of the class's condition does. -/
theorem targetHoldsBody_iff (world : Host.World config) (target : Host.Position) :
    Host.targetHoldsBody world target = true ↔
      CurrentGoals.InGoalBox target world.body.position.position :=
  CurrentGoals.find_goal_iff (world.setGoal (.find target)) target rfl

end AcornVerif.CurrentVisits
