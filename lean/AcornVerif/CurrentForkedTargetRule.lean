/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentDeclaredStep
import AcornVerif.CurrentForkedTargetRung

/-!
# The rung's agent stepping by the declared rule, and when a visit is calm

This module states, for the construction of the rung of targets by day and by night, the two
clauses about how the agent acts and learns, and the predicate that says a visit is calm.

**How the agent acts and learns.**

- `StepsByRule planning` is `AcornVerif.CurrentDeclaredStep.StepsByRule` at the rung's
  construction: on every percept and from every state, the step's decision and everything it
  leaves in its control outside the representation and the lifetime observations are the
  declared step's, with a list of units forgotten, and every unit outside that list keeps its
  projection.
- `StartsCold planning` says that the control of the construction's cold agent is the
  executing library's cold control: every weight a zero word, no stored prediction, no pending
  decision, the generators seeded from the configuration's seed and the bank drawn from it.

The agent as it is meets both under either planning selection (`steps_met`, `starts_cold_met`).

**What the two clauses give**, for every definition of the agent's step and cold state that
meets them:

- every action is the declared readout: one decision of primitive control over the policy the
  primitive controller freezes from its weights at the active set of the percept's frame, at the
  declared rate (`steps_act`);
- in every world, until the first percept whose reward word is not a zero word, the agent takes
  the actions of the explorer that holds no run and the generator seeded from the
  configuration's seed (`cold_until_rewarded`). Nothing the step does to the representation
  changes an action before the agent has been rewarded.

**A calm visit.** `CalmAt` reads a state of the agent and a percept: the decision of primitive
control at that state over the policy frozen at the percept's frame serves no committed
exploratory run and its persistent draw begins none. `TurnCalm` says that each of the first
seven decisions of a visit of a member's run under an order is calm. The step's own report, the
flag `Acorn.Features.TemporalDecision.explored`, is not read: it marks a decision that begins a
run and not one that serves a run already begun. The visit's last decision is not read, since
the world moves to the next visit's start whatever that action is. A greedy choice among tied
candidates draws on the generator and is calm. For an agent that steps by the rule, the action
of a calm decision is the greedy choice among the frozen policy's values (`calm_action`).

Degenerate instances, read for what they say. `CalmAt` does not hold at a state that holds a
committed run with a step left, whatever the percept. `TurnCalm` constrains nothing about the
eighth decision of a visit.
-/

namespace AcornVerif.CurrentForkedTargetRule
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentExplorer
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung
open AcornVerif.CurrentPreReward

/-! ## How the agent acts and learns -/

/-- **The rung's agent steps by the declared rule.** -/
def StepsByRule (planning : PlanningSelection) : Prop :=
  CurrentDeclaredStep.StepsByRule Grid.interface (rungConstruction planning).profile
    (rungConstruction planning).config (rungConstruction planning).criterion
    (rungConstruction planning).dimension (rungConstruction planning).planning

/-- **The rung's cold agent holds the cold control.** -/
def StartsCold (planning : PlanningSelection) : Prop :=
  (rungConstruction planning).initial.agent.control =
    TemporalControl.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension

/-- The agent as it is steps by the declared rule, under both planning selections. -/
theorem steps_met (planning : PlanningSelection) : StepsByRule planning :=
  CurrentDeclaredStep.act_steps rfl

/-- The agent as it is starts from the cold control. -/
theorem starts_cold_met (planning : PlanningSelection) : StartsCold planning := rfl

/-- **Every agent that steps by the rule acts by the declared readout.** On every percept and
from every state of the rung's agent, the step's action is the action of one decision of
primitive control over the policy the primitive controller freezes at the percept's frame, at
the declared rate, and the agent it returns holds that decision's run and generator. -/
theorem steps_act (planning : PlanningSelection) (rule : StepsByRule planning)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface) :
    (agent.act percept).2.action = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate)).1 ∧
      explorerOf (agent.act percept).1.control = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate)).2 :=
  CurrentDeclaredStep.StepsByRule.draws rule rfl rfl agent percept

/-- **Until its first reward the agent takes the cold explorer's actions.** For every definition
of the step and the cold state that meets the two clauses, in every world of the grid interface
and from every start: if every reward word delivered before a time is a zero word, the action at
that time is the action, at that time, of the explorer that holds no run and the generator
seeded from the configuration's seed. The decision on the first percept that carries another
reward word is among them. -/
theorem cold_until_rewarded (planning : PlanningSelection) (rule : StepsByRule planning)
    (cold : StartsCold planning) (world : Kernel.World Grid.interface) (start : world.State)
    (time : ℕ)
    (unpaid : ∀ earlier, earlier < time →
      (Kernel.perceptAt world (executedAgent (rungConstruction planning).initial.agent) start
        earlier).reward.isZero = true) :
    Kernel.actionAt world (executedAgent (rungConstruction planning).initial.agent) start time =
      (Explorer.cold Grid.interface.actions (rungConstruction planning).config.seed).actionAt
        time := by
  have rest : Quiet (rungConstruction planning).initial.agent.control := by
    rw [cold]
    exact Quiet.initial
  have explorer : explorerOf (rungConstruction planning).initial.agent.control =
      Explorer.cold Grid.interface.actions (rungConstruction planning).config.seed := by
    rw [cold]
    rfl
  have followed := (CurrentDeclaredStep.StepsByRule.quiet_actions rule rfl rfl
    (rungConstruction planning).initial.agent rest world start time unpaid).2.2
  rw [explorer] at followed
  exact followed

/-! ## A calm visit -/

/-- **A calm decision.** At a state of the rung's agent and a percept, the decision of primitive
control over the policy the primitive controller freezes at the percept's frame, at the declared
rate, serves no committed exploratory run, and its persistent draw begins none. -/
def CalmAt (planning : PlanningSelection)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface) : Prop :=
  (explorerOf agent.control).run.bind ExploratoryRun.serve = none ∧
    ((agent.control.runtime.lifecycle.consumers.control.snapshot
        (agent.advanceClock.frame percept.frame).active declaredRate).drawPersistent
      (explorerOf agent.control).rng).1.explored = false

/-- **A calm visit.** On a visit of a member's run under an order, each of the first seven
decisions of the executed agent from the rung's cold construction is calm, at the state and the
percept the run brings it. The visit's last decision is not read: the world moves to the next
visit's start whatever that action is. -/
def TurnCalm (planning : PlanningSelection)
    (pair : (rungForks (rungConstruction planning).profile.taskMode).Index) (order : ℕ → Bool)
    (visit : ℕ) : Prop :=
  ∀ step, step < 7 →
    CalmAt planning
      (Kernel.memoryAt
        (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
        (executedAgent (rungConstruction planning).initial.agent)
        (Kernel.turnStart ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
        (visit * (7 + 1) + step))
      (Kernel.perceptAt
        (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
        (executedAgent (rungConstruction planning).initial.agent)
        (Kernel.turnStart ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
        (visit * (7 + 1) + step))

/-- **A calm decision takes the greedy choice.** For an agent that steps by the rule, the action
of the step at a calm decision is the action of the persistent draw that began no run: the
greedy choice among the frozen policy's values. -/
theorem calm_action (planning : PlanningSelection) (rule : StepsByRule planning)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface) (calm : CalmAt planning agent percept) :
    (agent.act percept).2.action =
      ((agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate).drawPersistent
        (explorerOf agent.control).rng).1.action := by
  rw [(steps_act planning rule agent percept).1]
  unfold Explorer.stepOver
  rw [calm.1]

end AcornVerif.CurrentForkedTargetRule
