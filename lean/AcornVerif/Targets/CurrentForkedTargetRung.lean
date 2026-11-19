/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetBoth
import AcornVerif.CurrentForkedTargetCalm

/-! # Target: the rung's agent masters by day and by night, keeps it, and acts from its values

A *target* is a statement that a mission is to prove, held as a definition of type `Prop`. This
module holds one target, for the discovery mission that succeeds
[#283](https://github.com/rbeauchamp/acorn/issues/283). It introduces no definition: the
statement is built from definitions of `AcornVerif.CurrentForkedTargetCalm`,
`AcornVerif.CurrentForkedTargetBoth` and the modules they import. Nothing here is proved; the
mission is to prove the target, for the agent as a submission changes it or for the agent as it
is. It is not yet listed in
`AcornVerif.Targets.registry`: the registry lists a target under its mission's issue number, and
the mission has none until it is filed.

## What the statement fixes by its own text

The values below are written in the statement as numerals and structure literals. A proof has to
show that the named definitions have these values, so a change to one of those definitions makes
the target unprovable and does not change what it says.

- The world's configuration, every field: seed 1, side 64, a day of 2048 steps, regrowth after
  400, a food interval of 48, no food, no deer, and the noise scale `0x41000000`.
- The two situations' starts: the host's empty world of that configuration, and that world with
  its clock at 1024; in both, a carried step result that reports nothing and a reward word of
  zero. The body's tile, (32, 32), is the same in both, since the two worlds differ in the clock
  alone.
- The agent's construction: the host's standard construction at seed 1 for the primitive research
  profile under the discounted criterion, at the default step order; and that this profile is
  primitive actions only, with per-step credit, the declared exploration rate and learned
  subtasks.
- A visit of 7 steps, the covering bound 49, and three numbers: the limit 576, the horizon 1728
  and 288 lapses.

## What it reads through definitions

No numeral states these, and the statement means what they mean: the class and its members
(`rungForks`, built by `AcornVerif.CurrentForkedTarget.forkedFind`), a member's goal
(`rungForkGoals`), a member's two keys (`firstTarget`, `secondTarget`), a world in turns and
solving on a visit (`Kernel.turns`, `Kernel.SolvesTurn`), the two promises
(`Kernel.MastersGridBy`, `Kernel.KeepsOn`), a calm visit (`TurnCalm`), the two clauses about how
the agent acts (`ActsFromValues`, `StartsCold`), and the wrapper that makes the executed step a
kernel agent (`executedAgent`).

## What it leaves unsaid

The statement does not exclude an agent that records what was rewarded in each situation it
perceives and replays it through its values. It asks the agent to use what it perceives once in
each visit and not at every decision. It bounds the visits on which the agent explores only in
the runs of mastery, and it does not ask that the declared draw ever begin an exploration. It
promises nothing about work, memory, learning from each experience once or resumption, nor about
any other world, seed, visit length or profile.
`AcornVerif.CurrentForkedTargetRungLearns` proves what follows from a proof of the target, what
the statement excludes, and that its promises can be met.
-/

namespace AcornVerif.Targets.CurrentForkedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung
open AcornVerif.CurrentForkedTargetBoth AcornVerif.CurrentForkedTargetCalm
open AcornVerif.CurrentForkedTargetCandidate

/-- **The rung's agent masters by day and by night, keeps it, and acts from its values.** The
world is the grid world of the literal configuration below. A visit starts either from the host's
empty world or from that world with its clock at 1024, with nothing carried. For one planning
selection, the rung's construction is the host's standard construction at seed 1 for the
primitive research profile under the discounted criterion, and the executed agent, from that
construction's cold state:

* under one order, on one visit before visit 576, masters a grid: there are more than 49 first
  targets and more than 49 second targets such that every pair of them is a member that it
  solves on that visit in both situations, and in each of those runs every visit before visit
  1728 is calm but for at most 288 (`Kernel.MastersGridBy`, `TurnCalm`);
* under every order, solves again every member it has solved, on every later visit before visit
  1728 that brings the same situation and is calm (`Kernel.KeepsOn`);
* at every state and on every percept, takes the action of one decision of primitive control over
  the policy its primitive controller freezes at the percept's frame, at the declared rate
  (`ActsFromValues`);
* starts from the seeded explorer (`StartsCold`).

A visit is calm when, at each of its first seven decisions, the decision of primitive control at
the agent's state serves no committed exploratory run and its draw begins none. Visits are
counted from zero and have 7 steps. -/
def forks_learn : Prop :=
  witnessConfig.raw =
      { seed := 1, side := ⟨64, by decide⟩, dayLength := 2048, regrow := 400, foodInterval := 48,
        foodCap := 0, deerCap := 0, baseScale := ⟨0x41000000⟩ } ∧
    witnessLive.world = Host.World.empty witnessConfig ∧
    duskLive.world = { Host.World.empty witnessConfig with time := 1024 } ∧
    witnessLive.carried = ⟨⟨false, false, none, false, none, false, 0⟩, ⟨0⟩⟩ ∧
    duskLive.carried = ⟨⟨false, false, none, false, none, false, 0⟩, ⟨0⟩⟩ ∧
    ∃ planning : PlanningSelection,
      rungConstruction planning =
          AgentConstruction.standard 1 ⟨.primitive, .discounted⟩ planning .learnThenAct ∧
        (rungConstruction planning).profile = ⟨.primitiveOnly, .perStep, .declared, .learned⟩ ∧
        (rungConstruction planning).criterion = .discounted ∧
        (rungConstruction planning).order = .learnThenAct ∧
        (rungConstruction planning).config.seed = 1 ∧
        Kernel.MastersGridBy (rungForks (rungConstruction planning).profile.taskMode)
          (rungForkGoals (rungConstruction planning).profile.taskMode) 7 49
          (firstTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7)
          (secondTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7)
          576 1728 288 (TurnCalm planning)
          (executedAgent (rungConstruction planning).initial.agent) ∧
        Kernel.KeepsOn (rungForks (rungConstruction planning).profile.taskMode)
          (rungForkGoals (rungConstruction planning).profile.taskMode) 7 1728
          (TurnCalm planning) (executedAgent (rungConstruction planning).initial.agent) ∧
        ActsFromValues planning ∧ StartsCold planning

end AcornVerif.Targets.CurrentForkedTargetRung
