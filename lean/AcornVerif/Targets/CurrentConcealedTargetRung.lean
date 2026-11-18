/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetRung

/-! # Target of mission #283: the first rung's agent gets ahead and keeps what it has solved

A *target* is a statement that a mission is to prove, held as a definition of type `Prop`. This
module holds the one target of the first rung's discovery mission,
[#283](https://github.com/rbeauchamp/acorn/issues/283). It introduces no definition: the
statement is built from definitions of `AcornVerif.CurrentConcealedTargetRung` and the modules it
imports. Nothing here is proved; the mission is to prove the target, for the agent as a
submission changes it or for the agent as it is. `AcornVerif.Targets.registry` lists it.

## What the statement fixes by its own text

The values below are written in the statement as numerals and structure literals. A proof has to
show that the named definitions have these values, so a change to one of those definitions makes
the target unprovable and does not change what it says.

- The world's configuration, every field: seed 1, side 64, a day of 2048 steps, regrowth after
  400, a food interval of 48, no food, no deer, and the noise scale `0x41000000`.
- The start: the host's empty world of that configuration, with the body on the tile (32, 32) and
  a carried step result that reports nothing and a reward word of zero.
- The agent's construction: the host's standard construction at seed 1 for the primitive research
  profile under the discounted criterion, at the default step order; and that this profile is
  primitive actions only, with per-step credit, the declared exploration rate and learned
  subtasks.
- A visit of 7 steps, the covering bound 98, and the three numbers of the promise: the advantage
  before visit 288, the horizon 864 and 144 lapses.

## What it reads through definitions

No numeral states these, and the statement means what they mean: the class and its members
(`feasibleFind`), a member's goal (`completion`), the world's step and what its percept shows
(`gridWorld`), a world in visits and solving on a visit (`Kernel.visits`, `Kernel.SolvesOnVisit`),
the two promises (`Kernel.SeparatesBy`, `Kernel.RetainsBut`), the host's empty world and standard
construction (`Host.World.empty`, `AgentConstruction.standard`), and the wrapper that makes the
executed step a kernel agent (`executedAgent`). The statement does not name the agent's state, its
cold start and its step: it reaches them through the construction's cold state and through
`executedAgent`, and every build elaborates it over them as they are in that build.

## What it leaves unsaid

The statement asks for its two promises and for nothing about how the agent explores. No theorem
about what the agent as it is finds, `rung_finds` among them, is part of the target or a condition
of proving it: an agent that explores on another schedule meets the target when both promises
hold of it.

## What a submission changes

The agent's state, its cold start and its step (`Acorn.Handcrafted.Agent`, `Agent.initial`,
`Agent.act`) are what a submission changes. The mission's issue says which declarations stay as
they are and which theorems a submission may remove or restate, and holds every other rule.

`AcornVerif.CurrentConcealedTargetRungLearns` proves what follows from a proof of the target.
-/

namespace AcornVerif.Targets.CurrentConcealedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung

/-- **The first rung's agent gets ahead and keeps what it has solved.** The rung's world is the
grid world of the literal configuration below, started from the host's empty world with the body
on the tile (32, 32) and nothing carried. For one planning selection, the rung's construction is
the host's standard construction at seed 1 for the primitive research profile under the
discounted criterion, and there is a list of distinct members of the class such that the executed
agent, from that construction's cold state:

* on one visit before visit 288 solves each member of a set of more than 98 listed members, each
  in that member's own run, where a member first solved on that visit counts as much as one
  solved before it (`Kernel.SeparatesBy`); and
* solves again every member it has solved, on every later visit before visit 864, but for at
  most 144 visits of that member (`Kernel.RetainsBut`).

Visits are counted from zero and have 7 steps. -/
def rung_learns : Prop :=
  witnessConfig.raw =
      { seed := 1, side := ⟨64, by decide⟩, dayLength := 2048, regrow := 400, foodInterval := 48,
        foodCap := 0, deerCap := 0, baseScale := ⟨0x41000000⟩ } ∧
    witnessLive.world = Host.World.empty witnessConfig ∧
    witnessLive.world.body.position.position.x.val = 32 ∧
    witnessLive.world.body.position.position.y.val = 32 ∧
    witnessLive.carried = ⟨⟨false, false, none, false, none, false, 0⟩, ⟨0⟩⟩ ∧
    ∃ (planning : PlanningSelection)
      (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index),
      rungConstruction planning =
          AgentConstruction.standard 1 ⟨.primitive, .discounted⟩ planning .learnThenAct ∧
        (rungConstruction planning).profile = ⟨.primitiveOnly, .perStep, .declared, .learned⟩ ∧
        (rungConstruction planning).criterion = .discounted ∧
        (rungConstruction planning).order = .learnThenAct ∧
        (rungConstruction planning).config.seed = 1 ∧
        counted.Nodup ∧
        Kernel.SeparatesBy
          (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
          (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
          98 counted 288 (executedAgent (rungConstruction planning).initial.agent) ∧
        Kernel.RetainsBut
          (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
          (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
          864 144 (executedAgent (rungConstruction planning).initial.agent)

end AcornVerif.Targets.CurrentConcealedTargetRung
