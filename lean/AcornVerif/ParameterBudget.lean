/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Tactic.NormNum
import AcornVerif.ModelConstants

/-!
# Parameter budget against a declared state product

Counting arithmetic over fixed model inputs. `CurrentConstants` links its stated
subset of the inputs to current execution; the remaining factors are explicit
model inputs in `ModelConstants`.

`state_product_exceeds_parameter_count` compares the declared parameter count
with a Cartesian product of position, facing, energy, day phase and two craft
flags: a table with one entry per element of that product would need at least
90000 times the declared parameters. The comparison concerns tabular
representation of the declared product and nothing more. It does not prove that
every Cartesian combination is reachable, that every state needs a distinct
parameter, or that the executing agent learns to generalise.

## The world's state in bits

In bits the world is the smaller of the two. At side 1024 its whole state fits
in fewer than 67.7 million bits, and the declared parameters hold 94.4 million
(`agentBits`, 2949121 × 32 = 94371872). `agent_exceeds_terrain_description`
checks the corresponding inequality for the packed terrain description alone.

The state bound is derived here by counting the values of `Acorn.Host.World`
under `Acorn.Host.WorldConfig.standard` at side 1024; no theorem in this module
checks it. Terrain is a function of the configuration's seed and scale, so it is
configuration and not state. A field with at most `2 ^ b` values counts as `b`
bits:

* `time` and `goalStart`: 64 bits each.
* `body`: 163 bits, from a position of two `Fin 1024` indices (20), four
  facings (2), an energy in `Fin 2001` (11) and an inventory of four `UInt32`
  counts and two flags (130).
* `goal`: 129 bits. The largest constructor holds a position of two 64-bit
  coordinates, and all four constructors together with the absent goal have
  `2 ^ 128 + 4 * 2 ^ 32 + 2 + 2 ^ 64 + 1` values, fewer than `2 ^ 129`.
* `harvested`: 67371265 bits. It is a map from `Fin (1026 * 1026)` to `UInt64`,
  and there are `(2 ^ 64 + 1) ^ 1052676` such maps, fewer than
  `2 ^ (64 * 1052676 + 1)`.
* `deer`: 262145 bits. The population holds at most `1024 * 1024 / 512 = 2048`
  positions of 128 bits each, so there are fewer than `2 ^ (128 * 2048 + 1)`
  populations.
* `food`: 12001 bits, for at most 600 in-box positions of 20 bits each.
* `rng`: 256 bits.

The sum is 67646087 bits.

Native object overhead and complete checkpoint size are outside the
parameter-budget model.
-/

namespace AcornVerif

open AcornVerif.ModelConstants

/-- Declared learned-parameter budget: two arrays per learner, two weight arrays per
off-policy question (`Acorn.OffPolicy`) and one reserved gain slot.
The array counts are model inputs, not generated facts about checkpoint storage. -/
def agentParameters : ℕ :=
  ModelConstants.runtimeLearnerCount * ModelConstants.weightSpace *
    ModelConstants.knowledgeArraysPerLearner +
    ModelConstants.questionCount * ModelConstants.weightSpace *
      ModelConstants.weightArraysPerQuestion +
    ModelConstants.gainParameterCount

/-- Size of the declared Cartesian product of position, facing, energy, day phase and two
craft flags. It multiplies declared ranges and asserts no reachability of any combination
under world dynamics. -/
def declaredStateProduct : ℕ :=
  ModelConstants.worldSide * ModelConstants.worldSide
    * ModelConstants.facings
    * (ModelConstants.energyMax + 1)
    * ModelConstants.dayPhases
    * 2
    * 2

/-- Declared ratio used in the state-product comparison: the largest multiple of ten thousand
that `state_product_exceeds_parameter_count` proves. It was 100000 while the budget counted the
`runtimeLearnerCount` learners alone. The off-policy question weights raise the budget from
1867777 to 2949121 parameters, which lowers the quotient of the state product by the budget
from 143791 to 91067, so 100000 no longer holds. -/
def minStateMargin : ℕ := 90000

/-- The declared state product is at least `minStateMargin` times the declared parameter
count. -/
theorem state_product_exceeds_parameter_count :
    agentParameters * minStateMargin ≤ declaredStateProduct := by
  norm_num [agentParameters, declaredStateProduct, minStateMargin,
    ModelConstants.runtimeLearnerCount,
    ModelConstants.gainParameterCount, ModelConstants.questionCount,
    ModelConstants.weightArraysPerQuestion,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner, ModelConstants.worldSide,
    ModelConstants.facings, ModelConstants.energyMax, ModelConstants.dayPhases]

/-- Modeled parameter bits, assigning 32 bits to each learned parameter. -/
def agentBits : ℕ := agentParameters * 32

/-- Packed terrain bits for the selected square world, with three bits per tile. -/
def worldTerrainBits : ℕ := ModelConstants.worldSide * ModelConstants.worldSide * 3

/-- Declared lower ratio for parameter bits versus packed terrain bits. -/
def minTerrainRatio : ℕ := 19

/-- The modeled parameter bits exceed the packed terrain description by the stated ratio. -/
theorem agent_exceeds_terrain_description :
    worldTerrainBits * minTerrainRatio ≤ agentBits := by
  norm_num [worldTerrainBits, agentBits, agentParameters, minTerrainRatio,
    ModelConstants.runtimeLearnerCount, ModelConstants.gainParameterCount,
    ModelConstants.questionCount, ModelConstants.weightArraysPerQuestion,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner,
    ModelConstants.worldSide]

end AcornVerif
