/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Tactic.NormNum
import AcornVerif.Generated

/-!
# The big world hypothesis, checked — and where it does not hold

The design premise that gives this crate its name (Javed & Sutton, 2024): the
agent is orders of magnitude smaller than the world it acts in, so it *"can
neither fully perceive the state of the world nor can it represent the value or
optimal action for every state."*

Every number below comes from the explicit model constants in
`AcornVerif.Generated`. `AcornVerif.CurrentConstants` checks its listed finite
interface with current execution; the inequalities here concern this model.

**Which comparison the hypothesis is about.** It is about *states the agent must
value*, not about the size of the world's description. Those give opposite
answers here, and both are stated:

* `big_world_margin_holds` — against the states the agent must assign values to,
  the world exceeds the agent by at least `minStateMargin` (10⁵). This is the
  hypothesis, and it holds with room to spare.
* `agent_exceeds_terrain_description` — against the *terrain description*, the
  agent is at least **nineteen times larger**, with 19 declared as a floor. A
  learned parameter is 32 bits; a tile is 3, so any comparison of parameter
  count to tile count is off by an order of magnitude in the flattering
  direction. This theorem exists so the unflattering fact is compiler-checked
  rather than left for a reader to find.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- The agent's learned parameter budget, from the build.

Counts primary learners, option models and the reserved gain slot (dormant
under the discounted default). Each
learner holds `w` *and* `beta`, and `beta` is the parameter SwiftTD exists to
learn. `knowledgeArraysPerLearner` is emitted from the constant the checkpoint
writer uses, so a definition here cannot silently exclude a learned array —
counting only `w` would halve the agent and flatter both theorems below, in
opposite directions. -/
def agentParameters : ℕ :=
  Generated.runtimeLearnerCount * Generated.weightSpace * Generated.knowledgeArraysPerLearner +
    Generated.gainParameterCount

/-- A **lower bound** on the distinct world states, over the components whose
ranges the compiler knows: position within the campaign box, facing, energy, day
phase, and the two craft flags.

Deliberately conservative as a *state count*: inventory, deer, regrowth and the
terrain are excluded, so the true state space is larger.

Read the factors honestly. Position × facing alone is 4.2·10⁶, a margin of only
2.2 against the agent; the remaining orders of magnitude come from energy
(2001 levels) and day phase (8). Those are cheap to enumerate and two states
differing by 0.1 energy plainly do not need distinct values, so this is a count
of **distinguishable world states**, not a proof that each needs its own
parameter. The hypothesis it supports is that the agent cannot hold one
parameter per state and must therefore generalise — which the count does
establish. -/
def reachableStates : ℕ :=
  Generated.worldSide * Generated.worldSide
    * Generated.facings
    * (Generated.energyMax + 1)
    * Generated.dayPhases
    * 2
    * 2

/-- The margin this build is required to hold: the world must offer at least
10⁵ states per agent parameter.

A *declared* minimum, not a description of the current build — the point of
naming it is that lowering the world or inflating the agent fails this theorem
instead of quietly eroding the premise. -/
def minStateMargin : ℕ := 100000

/-- **The big world hypothesis, as a checked fact of this build.**

The agent cannot hold one parameter per distinguishable world state by five
orders of magnitude, so it is forced to generalise — which is the entire design
premise. -/
theorem big_world_margin_holds :
    agentParameters * minStateMargin ≤ reachableStates := by
  norm_num [agentParameters, reachableStates, minStateMargin, Generated.runtimeLearnerCount,
    Generated.gainParameterCount,
    Generated.weightSpace, Generated.knowledgeArraysPerLearner, Generated.worldSide,
    Generated.facings, Generated.energyMax, Generated.dayPhases]

/-- The agent's learned parameters, in bits (`f32` each). -/
def agentBits : ℕ := agentParameters * 32

/-- The world's terrain description, in bits: eight tile kinds is three bits per
tile. -/
def worldTerrainBits : ℕ := Generated.worldSide * Generated.worldSide * 3

/-- The floor this build is required to clear on the unfavourable side.

Declared for the same reason `minStateMargin` is: a bare `<` pins no ratio, so
shrinking the agent must also move the documented floor. The learner arrays
give ratio 19 — `57 · 2 · 32 / (3 · 64)` — plus the shared scalar gain. -/
def minTerrainRatio : ℕ := 19

/-- **Where the hypothesis does not hold.** Against the terrain *description*
the agent is larger — 59.77 Mbit against 3.15 Mbit, at least nineteen times, at
the default side.

This is not a defect: the hypothesis is about representing values over states,
and `big_world_margin_holds` is the statement that matters. It is proven here so
that no document can quietly compare a parameter count to a tile count and call
the result a margin — a parameter is 32 bits and a tile is 3, and the honest
ratio runs the other way. -/
theorem agent_exceeds_terrain_description :
    worldTerrainBits * minTerrainRatio ≤ agentBits := by
  norm_num [worldTerrainBits, agentBits, agentParameters, minTerrainRatio,
    Generated.runtimeLearnerCount, Generated.gainParameterCount,
    Generated.weightSpace, Generated.knowledgeArraysPerLearner,
    Generated.worldSide]

end AcornVerif
