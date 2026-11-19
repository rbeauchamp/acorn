/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetRung

/-!
# A candidate statement over the rung of targets by day and by night

This module states a candidate for a discovery mission's statement over
`AcornVerif.CurrentForkedTargetRung.rungForks`, with its three numbers left as parameters, and
proves what the statement excludes and that it can be met. It is no target: nothing here is
registered, and no number is chosen.

`ForksLearn limit horizon lapses` says that, for one planning selection, the executed agent from
the rung's cold construction

* masters before the visit `limit`: under one order, on one visit, it solves each of more than
  98 members with different first targets whichever situation that visit brings
  (`Kernel.MastersBy`);
* keeps before the visit `horizon` but for `lapses` lapses: under every order, a member solved
  on a visit is solved on every later visit that brings the same situation, but for at most
  `lapses` of that member's visits (`Kernel.KeepsBut`);
* acts from the values it holds at its percept and explores by the declared draw
  (`ActsFromValues`), from the seeded cold explorer (`StartsCold`).

`ActsFromValues` is the statement of `AcornVerif.CurrentExplorer.act_draws` written as an
obligation: at every state of the agent's type and on every percept, the step's action is the
action of one decision of primitive control over the policy that the primitive controller
freezes at the percept's frame, at the declared rate, and the returned agent holds that
decision's run and generator. The agent as it is meets it and `StartsCold` under either planning
selection (`acts_met`, `starts_cold_met`). Neither says anything of how the controller's weights
come to hold what they hold.

What the first promise excludes, for every limit:

- an agent that keeps nothing of its experience (`rung_fork_need`);
- an agent whose actions depend on its clock, its reward words and its achievement flags, at
  every bound (`rung_fork_blind`), which serves at most one side of each fork
  (`rung_fork_sides`);
- an agent that differs from such an agent only on percepts the class never delivers
  (`rung_fork_hybrid`).

What it forces of the agent that meets it: on some visit, from one memory at the visit's start,
the executed agent's actions differ between the visit's two situations (`forks_read`).

That the two promises can be met together, by an agent built for the purpose, is
`AcornVerif.CurrentForkedTargetRung.witness_masters` and `witness_keeps`, joined in
`rung_fork_met`, and at every choice of the numbers that leaves six visits in
`witness_promises`. Whether the executed agent as it is meets either promise is not known.
-/

namespace AcornVerif.CurrentForkedTargetCandidate
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentExplorer
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung

/-! ## How the agent acts -/

/-- **The agent acts from the values it holds at its percept, and explores by the declared
draw.** For every state of the rung's agent and every percept: the step's action is the action of
one decision of primitive control over the policy the primitive controller freezes at the
percept's frame, at the declared rate, and the returned agent holds that decision's run and
generator. -/
def ActsFromValues (planning : PlanningSelection) : Prop :=
  ∀ (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface),
    (agent.act percept).2.action = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate)).1 ∧
      explorerOf (agent.act percept).1.control = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate)).2

/-- **The cold start holds the seeded explorer.** The cold state holds no committed run, and the
generator the agent seeds for its action stream from the configuration's seed. It says nothing
of the cold weights. -/
def StartsCold (planning : PlanningSelection) : Prop :=
  explorerOf (rungConstruction planning).initial.agent.control =
    Explorer.cold Grid.interface.actions (rungConstruction planning).config.seed

/-- The agent as it is acts from the values it holds at its percept, under both planning
selections: it is `AcornVerif.CurrentExplorer.act_draws` at the rung's profile, which has no
hierarchy and the declared rate. -/
theorem acts_met (planning : PlanningSelection) : ActsFromValues planning :=
  fun agent percept => act_draws agent rfl rfl percept

/-- The agent as it is starts from the seeded explorer. -/
theorem starts_cold_met (planning : PlanningSelection) : StartsCold planning := rfl

/-! ## The candidate statement -/

/-- **A candidate statement, with its numbers left open.** For one planning selection, the
executed agent from the rung's cold construction masters before the visit `limit` at the
covering bound 98, with members counted by their first targets; keeps before the visit `horizon`
but for `lapses` lapses; acts from the values it holds at its percept and explores by the
declared draw; and starts from the seeded explorer. Visits are counted from zero and have 7
steps. -/
def ForksLearn (limit horizon lapses : ℕ) : Prop :=
  ∃ planning : PlanningSelection,
    Kernel.MastersBy (rungForks (rungConstruction planning).profile.taskMode)
        (rungForkGoals (rungConstruction planning).profile.taskMode) 7 98
        (firstTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7) limit
        (executedAgent (rungConstruction planning).initial.agent) ∧
      Kernel.KeepsBut (rungForks (rungConstruction planning).profile.taskMode)
        (rungForkGoals (rungConstruction planning).profile.taskMode) 7 horizon lapses
        (executedAgent (rungConstruction planning).initial.agent) ∧
      ActsFromValues planning ∧ StartsCold planning

/-- The feedback an agent that ignores what it perceives still reads: the reward word and the
achievement flag. -/
def rewardAndFlag (percept : Percept Grid.interface) : Binary32 × Bool :=
  (percept.reward, percept.frame.achieved)

/-! ## What mastery excludes -/

/-- **No agent that keeps nothing masters at the covering bound**, before any visit. -/
theorem rung_fork_need (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent) (limit : ℕ) :
    ¬ Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 98
      (firstTarget mode witnessLive duskLive 7) limit agent :=
  forked_need mode witnessLive duskLive 7 free limit

/-- **No agent that goes by its clock, its reward words and its achievement flags masters**, at
any bound, key and limit. The class of such agents is defined over every sequence of percepts,
and they fail on percepts the rung's class itself delivers: the two starts of one member. -/
theorem rung_fork_blind (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven rewardAndFlag agent) (bound limit : ℕ) {κ : Type}
    (key : (rungForks mode).Index → κ) :
    ¬ Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 bound key limit agent :=
  forked_blind mode witnessLive duskLive 7 dusk_carried blind bound limit key

/-- **Such an agent serves at most one side of each fork.** Under any order and on any visit, of
any finite set of sides of members that it solves on that visit, no two are sides of one member:
of the two sides of each of `n` members it solves at most `n`, and so both sides of none. -/
theorem rung_fork_sides (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven rewardAndFlag agent) (order : ℕ → Bool) (visit : ℕ)
    [DecidableEq (rungForks mode).Index] (sides : Finset ((rungForks mode).Index × Bool))
    (each : ∀ side ∈ sides, Kernel.SolvesTurn (rungForks mode) (rungForkGoals mode) 7
      (Function.update order visit side.2) agent visit side.1) :
    sides.card = (sides.image Prod.fst).card :=
  blind.sides (forked_mute mode witnessLive duskLive 7 dusk_carried)
    (forked_apart mode witnessLive duskLive 7) order visit sides each

/-- **An agent that differs from such an agent only where the class never looks does not
master.** A chooser whose preference and memory read the percept through the reward word and the
achievement flag, made to hold a resting preference on a set of percepts that no member of the
rung's class delivers, is not driven by that feedback over every sequence of percepts, and it
masters at no bound, key and limit. -/
theorem rung_fork_hybrid (mode : TaskFeatureMode) {E Core V : Type}
    (select : E → V → Kernel.Act Grid.interface × E) (core : Core) (seed : E)
    (prefer : Core → Binary32 × Bool → V)
    (advance : Core → Binary32 × Bool → Kernel.Act Grid.interface → Core)
    (alien : Percept Grid.interface → Prop) [DecidablePred alien] (rest : V)
    (never : ∀ state : Option (Live witnessConfig),
      ¬ alien ((gridWorld witnessConfig mode).percept state))
    (bound limit : ℕ) {κ : Type} (key : (rungForks mode).Index → κ) :
    ¬ Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 bound key limit
      (Kernel.chooser select core seed
        (Kernel.aloof alien rest (fun inner percept => prefer inner (rewardAndFlag percept)))
        (fun inner percept action => advance inner (rewardAndFlag percept) action)) :=
  Kernel.aloof_masters select core seed prefer advance alien rest (fun _ state => never state)
    (forked_mute mode witnessLive duskLive 7 dusk_carried)
    (forked_apart mode witnessLive duskLive 7) bound limit key

/-! ## What the candidate forces, and that it can be met -/

/-- **An agent that meets the candidate reads what it perceives.** From a proof of the candidate
at any numbers: for its planning selection there are an order, a visit, a member and a step of
that visit at which the executed agent's actions differ between the two runs that differ in that
visit's situation alone, while its memory at the visit's start is the same in both. -/
theorem forks_read {limit horizon lapses : ℕ} (learns : ForksLearn limit horizon lapses) :
    ∃ (planning : PlanningSelection) (order : ℕ → Bool) (visit : ℕ)
      (pair : (rungForks (rungConstruction planning).profile.taskMode).Index) (step : ℕ),
      step < 7 ∧
        Kernel.turnMemory ((rungForks (rungConstruction planning).profile.taskMode).world pair)
            ((rungForks (rungConstruction planning).profile.taskMode).start pair)
            (Function.update order visit false) 7
            (executedAgent (rungConstruction planning).initial.agent) visit =
          Kernel.turnMemory ((rungForks (rungConstruction planning).profile.taskMode).world pair)
            ((rungForks (rungConstruction planning).profile.taskMode).start pair)
            (Function.update order visit true) 7
            (executedAgent (rungConstruction planning).initial.agent) visit ∧
        Kernel.actionAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit false) 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit false) 7 0) (visit * (7 + 1) + step) ≠
          Kernel.actionAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit true) 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit true) 7 0) (visit * (7 + 1) + step) := by
  obtain ⟨planning, ⟨order, visit, solved, -, many, -, each⟩, -, -, -⟩ := learns
  obtain ⟨pair, member⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le 98) many)
  obtain ⟨step, short, differ⟩ := Kernel.turn_differs
    (forked_apart (rungConstruction planning).profile.taskMode witnessLive duskLive 7) order
    (executedAgent (rungConstruction planning).initial.agent) visit pair (each pair member)
  exact ⟨planning, order, visit, pair, step, short,
    (Kernel.turnMemory_sides _ _ order 7 _ visit false).trans
      (Kernel.turnMemory_sides _ _ order 7 _ visit true).symm, differ⟩

/-- The two promises of the candidate statement, of any agent over the grid's interface: it
masters before the visit `limit` at the covering bound 98, with members counted by their first
targets, and keeps before the visit `horizon` but for `lapses` lapses. The candidate statement
asks them of the executed agent, with the two clauses about how it acts. -/
def Promises (mode : TaskFeatureMode) (limit horizon lapses : ℕ)
    (agent : Kernel.Agent Grid.interface) : Prop :=
  Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 98
      (firstTarget mode witnessLive duskLive 7) limit agent ∧
    Kernel.KeepsBut (rungForks mode) (rungForkGoals mode) 7 horizon lapses agent

/-- **The witness meets both promises at every choice of the numbers that leaves six visits.**
For every task mode, every limit of at least 6, every horizon and every number of lapses,
`AcornVerif.CurrentForkedTargetRung.forkWitness` masters before the limit and keeps before the
horizon but for the lapses. It is a kernel agent built for the purpose, so the clauses about how
the executed agent acts are not statements about it. -/
theorem witness_promises (mode : TaskFeatureMode) {limit : ℕ} (room : 6 ≤ limit)
    (horizon lapses : ℕ) : Promises mode limit horizon lapses forkWitness :=
  ⟨(witness_masters mode).mono room,
    (witness_keeps mode horizon).mono (Nat.zero_le lapses)⟩

/-- **The two promises can be met together.** For every task mode there is an agent that masters
at the covering bound before visit 6 and keeps with no lapse before every horizon. It is
`AcornVerif.CurrentForkedTargetRung.forkWitness`, built for the purpose. -/
theorem rung_fork_met (mode : TaskFeatureMode) :
    ∃ agent : Kernel.Agent Grid.interface,
      Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 98
        (firstTarget mode witnessLive duskLive 7) 6 agent ∧
      ∀ horizon, Kernel.KeepsBut (rungForks mode) (rungForkGoals mode) 7 horizon 0 agent :=
  ⟨forkWitness, witness_masters mode, witness_keeps mode⟩

end AcornVerif.CurrentForkedTargetCandidate
