/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetCandidate
import AcornVerif.TurnsBoth

/-!
# When a visit of the rung's run by day and by night is calm

`TurnCalm` says that on one visit of one member's run under one order the executed agent takes
no exploratory action, and it says so through the law of the decision and not through a flag the
agent's step reports.

`CalmAt` reads a state of the agent and a percept. The decision of primitive control at that
state over the policy the primitive controller freezes at the percept's frame
(`AcornVerif.CurrentExplorer.Explorer.stepOver`) is *calm* when it serves no committed
exploratory run and its persistent draw begins none. The action of a calm decision is the greedy
choice among the frozen policy's values. Where the agent meets
`AcornVerif.CurrentForkedTargetCandidate.ActsFromValues`, that decision is the one its step
takes, so a calm visit is one on which every action the world takes is such a greedy choice.

The step's own report, the flag `Acorn.Features.TemporalDecision.explored`, is not read. A
submission may change the step, and a clause that read the flag would ask only what the step
says of itself. The flag is also narrower: it marks a decision that begins a run, and a decision
that serves a run already begun carries none.

Three choices this definition records. The visit's last decision is not read, since the world
moves to the next visit's start whatever that action is. A greedy choice among tied candidates
draws on the generator and is calm. And a calm visit is not a visit on which the declared draw
was not taken: the draw is taken at every decision that no committed run serves, and a calm
visit is one on which no draw began a run and no run was served.
-/

namespace AcornVerif.CurrentForkedTargetCalm
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentExplorer
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung
open AcornVerif.CurrentForkedTargetCandidate

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

/-- **A calm decision takes the greedy choice.** For an agent that acts from its values, the
action of the step at a calm decision is the action of the persistent draw that began no run:
the greedy choice among the frozen policy's values. -/
theorem calm_action (planning : PlanningSelection) (acts : ActsFromValues planning)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface) (calm : CalmAt planning agent percept) :
    (agent.act percept).2.action =
      ((agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate).drawPersistent
        (explorerOf agent.control).rng).1.action := by
  rw [(acts agent percept).1]
  unfold Explorer.stepOver
  rw [calm.1]

end AcornVerif.CurrentForkedTargetCalm
