/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission
import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.CurrentFrameSize

/-!
# The first rung's class for the executed agent

`AcornVerif.CurrentConcealedTargetMission.executed_mission` proves the mission theorem's statement
of the executed agent from named premises, for every host world that carries a reward of zero,
every visit length and every agent state. This module fixes those for the first rung of the
mission's ladder (`docs/mission-contract.md`, section "The mission theorem and its ladder") and
says what each is chosen for. `rung_mission` is the statement at these constants.

## The constants

- **The world** is the world of the separation witness
  (`AcornVerif.CurrentConcealedTarget.witnessConfig`, `witnessLive`): the host's standard
  configuration at seed 1 and the smallest side, 64, with no deer and no food
  (`AcornVerif.CurrentConcealedTarget.witness_standard`), started at the box's center
  (`witness_start`) with full energy and a carried reward of zero. So its day, its noise scale and
  its terrain are those of the world the host builds at that seed and side.
- **A visit** is seven steps of the world.
- **The agent** is the cold agent the host constructs for the primitive research profile under the
  discounted criterion, at the world's seed and the default step order (`rungConstruction`), under
  either planning selection.

The members the comparison counts are not fixed here: they are members the executed agent finds,
which the premise `ExecutedFinds` names.

## What the choices rest on

The world and the visit length each rest on a theorem. The agent's profile is the one the roadmap
decides first (rbeauchamp/acorn#232), its criterion is the one the host's entry for runs of visits
constructs, and the seed is the least at which the host's own world was observed to start at the
box's center, as this world does (`docs/roadmap.md`); no theorem singles these out.

- **The class is proved big in this world at this visit length.** The feasible concealed targets
  are a big class with the covering bound 98 (`AcornVerif.CurrentConcealedTarget.witness_big`), and
  147 distinct members are listed (`witness_mission`). It is the one world and visit length at
  which the tree proves a class big; no theorem says a shorter visit fails. Every member's target
  lies within ten tiles of the start (`AcornVerif.CurrentConcealedTarget.feasible_window`), so the
  class has at most 392 members (`rung_members`); that window, tiles 22 to 42 on both axes, lies
  inside the box.
- **No deer and no food, so that every frame is proved small.** In a world that admits neither,
  every percept has at most 139 words (`AcornVerif.CurrentFrameSize.percept_words`), so every frame
  of the rung's agent has at most 1712 active slots (`rung_frames`), and the credit horizon holds
  of it with no hypothesis on frames (`rung_weight_rests`). Of a world with deer and food the tree
  proves only the interface's bound of 3648 slots (`AcornVerif.CurrentFrameSize`), which is above
  the 1999 that horizon assumes. A smaller bound for the host's own world along a visit of seven
  steps is not proved. It looks within reach: from a generated world no food is due at the times
  one to seven, and a box of side 64 admits at most eight deer, which would give 147 words and
  1776 slots (argued).
- **A visit of seven steps is within the proved reach of a first reward.** On a primitive
  controller's cold run, a slot laid at most 81 steps before a first reward of one has a weight
  the reward moves (`AcornVerif.CurrentCreditHorizon.recent_weight_moves`); `rung_reach` is that
  statement for frames of the rung's size and a slot laid at most seven steps before. In the
  kernel's world in visits a reward is the result of one of a visit's seven steps and arrives with
  the decision that follows that step, so a first reward arrives at most seven decisions after its
  visit's first (argued, from `AcornVerif.Kernel.visits` and `reward_step`). The statement is about
  the controller's run, not yet about the agent's, and it says that a weight moves, not that the
  greedy choice changes.

## What is not proved here

- No premise of `rung_mission` about the agent. Whether the executed agent finds and retains in
  this class is rbeauchamp/acorn#232. `ExecutedRetains` is argued to fail of the agent as built
  (`AcornVerif.CurrentConcealedTargetMission`, header), and rbeauchamp/acorn#248 decides how
  retention is asked.
- Anything about saving or resuming the rung's agent. Its profile is the primitive one, which the
  host neither saves nor loads (`Acorn.Checkpoint.save_refuses`,
  `AcornVerif.CurrentCheckpoint.unresumable_unloaded`). So exact resumption (`load_saved`,
  `resume_saved`), the account of a crash (`AcornVerif.CurrentVisits.visits_resumed`) and the count
  of the states a host runs (`AcornVerif.CurrentRunningMemory.running_memory_bits`) say nothing of
  it.
- That a run of the host is a run of this world. The host's entry `acorn-core visits` builds the
  standard configuration, with its deer and food, and starts where its spawn search ends. At seed
  1 and side 64 that start was observed to be the box's center, with one of the world's eight deer
  in view from part of a visit's reach and no food along a visit (`docs/roadmap.md`). No theorem
  relates a run of it to a member of this class. The class in the host's own world, deer
  included, is a later rung.
- That a class of a longer visit, or of a world with deer and food, is big, or that its frames are
  within the sizes the credit horizon assumes.

## What a proof about a world's layout costs

The kernel evaluates the executed terrain for each tile a proof reads, each time the module is
rebuilt (`docs/roadmap.md` records the timing). The witness reads 21 tiles (`witness_walk`). A
class with visits of 81 steps, the proved reach of a first reward, has a covering bound of 616;
each step of a walk brings at most seven more targets within reach
(`AcornVerif.Coverage.card_swept`), so its count needs the terrain of at least 89 tiles (argued).
The host's spawn search evaluates the terrain 163 times for each candidate it considers
(`Acorn.Host.considerSpawn`: two counts over a nine-by-nine square, and the candidate's own tile)
and stops at the first walkable candidate whose square holds two trees. How many candidates it
considers at seed 1 and side 64 is not proved; an evaluation of it there ended at the center,
its first candidate (observed, `docs/roadmap.md`).
-/

namespace AcornVerif.CurrentConcealedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentCreditHorizon
open AcornVerif.CurrentFrameSize AcornVerif.Intent AcornVerif.Intent.MissionTheorem

/-! ## The first rung -/

/-- The witness's configuration admits no deer and no food. -/
theorem witness_unpopulated : Unpopulated witnessConfig := ⟨rfl, rfl⟩

/-- The construction of the first rung's agent: the one the host builds for the primitive research
profile under the discounted criterion, at the seed of the rung's world and the default step
order, under a planning selection. -/
def rungConstruction (planning : PlanningSelection) : AgentConstruction :=
  AgentConstruction.standard witnessConfig.raw.seed ⟨.primitive, .discounted⟩ planning
    .learnThenAct

/-- **The frames of the first rung.** Over percepts the rung's world delivers, every step of the
rung's agent lays a frame of at most 1712 slots, from every state and under every step order. -/
theorem rung_frames (planning : PlanningSelection) (mode : TaskFeatureMode) (order : StepOrder)
    (percepts : List (Percept Grid.interface)) (delivered : Delivered witnessConfig mode percepts)
    (state : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning) :
    ∀ step ∈ (traced order state percepts).2, step.features.indices.length ≤ 1712 :=
  fun step member => Nat.le_trans
    (unpopulated_fits witness_unpopulated mode order percepts delivered state step member)
    (Nat.le_of_eq (standard_slots _ _ _ _))

/-- **The credit horizon of the first rung.** For the rung's agent from cold initialization, over
percepts the rung's world delivers whose reward words are zero, and then any percepts at all, a
primitive weight is a zero word unless its row laid its slot in the window: the last 119 steps
without reward and every later step. No hypothesis on frames remains. -/
theorem rung_weight_rests (planning : PlanningSelection) (mode : TaskFeatureMode)
    (order : StepOrder) (quiet post : List (Percept Grid.interface))
    (delivered : Delivered witnessConfig mode quiet)
    (silent : ∀ percept ∈ quiet, percept.reward.isZero = true) :
    let start := (rungConstruction planning).initial.agent
    let first := traced order start quiet
    let second := traced order first.1 post
    ∀ (row : Action Grid.interface.actions.word.toNat)
      (slot : FeatIdx (rungConstruction planning).dimension),
      (∀ step ∈ window (rungConstruction planning).criterion first.2 second.2,
        ¬step.Lays row slot) →
      (((controlOf second.1).learners.get row).state.weights.get slot).value.isZero = true :=
  unpopulated_weight_rests witness_unpopulated mode _ _ _ _ _ order rfl
    (Nat.le_trans (Nat.le_of_eq (standard_slots _ _ _ _)) (by decide)) quiet post delivered silent

/-- **The reach of a first reward at the rung's frame size and visit length.** On a primitive
controller's cold run over frames of at most 1712 slots, a slot that a step laid, followed by at
most six more steps, has a weight that a reward of one at the next step moves, under either
criterion. It is `AcornVerif.CurrentCreditHorizon.recent_weight_moves` at the rung's sizes. The
statement is of the controller's run, not of the agent's, and it mentions no visit: this module's
header argues that a first reward arrives at most seven decisions after its visit's first. -/
theorem rung_reach (criterion : Criterion) (dimension : Dimension) {actions : Nat}
    (before after : List (Laid dimension actions)) (laid : Laid dimension actions)
    (slot : FeatIdx dimension) (held : slot ∈ laid.features.indices)
    (within : after.length + 1 ≤ 7)
    (fits : ∀ step ∈ before ++ laid :: after, step.features.indices.length ≤ 1712)
    (next : Laid dimension actions) :
    let quiet : Controller (criterion.config .control) dimension actions :=
      quietRun (before ++ laid :: after)
    (((quiet.step next.features next.row .one).1.learners.get laid.row).state.weights.get
      slot).value.isZero = false :=
  recent_weight_moves criterion dimension before after laid slot held (by omega)
    (fun step member => Nat.le_trans (fits step member) (by decide)) next

/-- **The members of the first rung.** Every member's target lies within ten tiles of the start
on both axes, so the class has at most 392 members. It has at least 147
(`AcornVerif.CurrentConcealedTargetMission.witness_mission` lists that many distinct members), and
its covering bound is 98. -/
theorem rung_members (mode : TaskFeatureMode)
    (members : Finset (feasibleFind witnessConfig mode witnessLive 7).Index) :
    members.card ≤ 392 :=
  feasible_count mode witnessLive 7 members

/-- **The mission theorem on the first rung, from its named premises.** In the rung's world, with
visits of seven steps and a list of distinct counted members: if the rung's agent finds and
retains, then every agent that takes its actions, and whose own memory and reports meet the four
premises of contract 3, achieves goals over the class. It is
`AcornVerif.CurrentConcealedTargetMission.executed_mission` at the rung's constants; no premise is
proved. -/
theorem rung_mission (planning : PlanningSelection)
    (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
      witnessLive 7).Index)
    (distinct : counted.Nodup) {agent : Kernel.Agent Grid.interface}
    (acts : ActsAsExecuted (rungConstruction planning).initial.agent agent)
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    (finds : ExecutedFinds (rungConstruction planning).initial.agent witnessConfig witnessLive 7
      counted)
    (retains : ExecutedRetains (rungConstruction planning).initial.agent witnessConfig
      witnessLive 7)
    (memory : MemoryBounded (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume))
    (bounded : WorkBounded (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume))
    (arrival : LearnsOnArrival (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume))
    (discipline : KeepsDiscipline (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 counted agent updates work
      resume)) :
    Mission (findRung witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7
      counted agent updates work resume) :=
  executed_mission (rungConstruction planning).initial.agent witnessConfig witnessLive 7 rfl
    counted distinct acts finds retains memory bounded arrival discipline

end AcornVerif.CurrentConcealedTargetRung
