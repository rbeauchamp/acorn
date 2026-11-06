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
140000 times the declared parameters, the largest multiple of ten thousand for
which the comparison holds (`state_margin_largest`). The comparison concerns tabular
representation of the declared product and nothing more. It does not prove that
every Cartesian combination is reachable, that every state needs a distinct
parameter, or that the executing agent learns to generalise.

## The world's state in bits

In bits the agent is the smaller of the two. The declared parameters hold 59.8
million bits (`agentBits`, 1867777 × 32 = 59768864: `agent_parameters_value` and
`agent_bits_value`), and at side 1024 the world's whole state fits in fewer than
67.7 million (`worldStateBits`, 67646087: `world_state_bits_value`), more than the
parameter bits (`world_state_exceeds_agent_bits`). The packed terrain description
alone is smaller: `agent_exceeds_terrain_description` checks that the parameter
bits exceed it nineteen times over, the largest whole ratio that holds
(`terrain_ratio_largest`).

The field counts below are derived here by counting the values of
`Acorn.Host.World` under `Acorn.Host.WorldConfig.standard` at side 1024; no
theorem in this module checks a field's count, and `world_state_bits_value`
checks their sum. Terrain is a function of the configuration's seed and scale, so it is
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

/-- Declared learned-parameter budget: two arrays per learner and one reserved gain slot.
The array counts are model inputs, not generated facts about checkpoint storage. -/
def agentParameters : ℕ :=
  ModelConstants.runtimeLearnerCount * ModelConstants.weightSpace *
    ModelConstants.knowledgeArraysPerLearner +
    ModelConstants.gainParameterCount

/-- The declared budget is 1867777 parameters. -/
theorem agent_parameters_value : agentParameters = 1867777 := by
  norm_num [agentParameters, ModelConstants.runtimeLearnerCount, ModelConstants.weightSpace,
    ModelConstants.knowledgeArraysPerLearner, ModelConstants.gainParameterCount]

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

/-- The quotient of the state product by the budget is 143791. -/
theorem state_quotient_value : declaredStateProduct / agentParameters = 143791 := by
  norm_num [agentParameters, declaredStateProduct,
    ModelConstants.runtimeLearnerCount, ModelConstants.gainParameterCount,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner, ModelConstants.worldSide,
    ModelConstants.facings, ModelConstants.energyMax, ModelConstants.dayPhases]

/-- Declared ratio used in the state-product comparison: the largest multiple of ten thousand
that `state_product_exceeds_parameter_count` proves (`state_margin_largest`), below the
quotient 143791 (`state_quotient_value`). -/
def minStateMargin : ℕ := 140000

/-- The declared state product is at least `minStateMargin` times the declared parameter
count. -/
theorem state_product_exceeds_parameter_count :
    agentParameters * minStateMargin ≤ declaredStateProduct := by
  norm_num [agentParameters, declaredStateProduct, minStateMargin,
    ModelConstants.runtimeLearnerCount, ModelConstants.gainParameterCount,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner, ModelConstants.worldSide,
    ModelConstants.facings, ModelConstants.energyMax, ModelConstants.dayPhases]

/-- No larger multiple of ten thousand holds: the quotient of the state product by the budget
is below 150000. -/
theorem state_margin_largest :
    ¬ agentParameters * (minStateMargin + 10000) ≤ declaredStateProduct := by
  norm_num [agentParameters, declaredStateProduct, minStateMargin,
    ModelConstants.runtimeLearnerCount, ModelConstants.gainParameterCount,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner, ModelConstants.worldSide,
    ModelConstants.facings, ModelConstants.energyMax, ModelConstants.dayPhases]

/-- Modeled parameter bits, assigning 32 bits to each learned parameter. -/
def agentBits : ℕ := agentParameters * 32

/-- The declared parameters hold 59768864 bits. -/
theorem agent_bits_value : agentBits = 59768864 := by
  rw [agentBits, agent_parameters_value]

/-- Bits of the world's state at side 1024, the sum of the field counts in the module
documentation: `time`, `goalStart`, `body`, `goal`, `harvested`, `deer`, `food` and `rng`. -/
def worldStateBits : ℕ := 64 + 64 + 163 + 129 + 67371265 + 262145 + 12001 + 256

/-- The field counts sum to 67646087 bits. -/
theorem world_state_bits_value : worldStateBits = 67646087 := by
  norm_num [worldStateBits]

/-- The world's state takes more bits than the declared parameters. -/
theorem world_state_exceeds_agent_bits : agentBits < worldStateBits := by
  rw [agent_bits_value, world_state_bits_value]
  norm_num

/-- Packed terrain bits for the selected square world, with three bits per tile. -/
def worldTerrainBits : ℕ := ModelConstants.worldSide * ModelConstants.worldSide * 3

/-- Declared lower ratio for parameter bits versus packed terrain bits: the largest whole ratio
that `agent_exceeds_terrain_description` proves (`terrain_ratio_largest`). -/
def minTerrainRatio : ℕ := 19

/-- The modeled parameter bits exceed the packed terrain description by the stated ratio. -/
theorem agent_exceeds_terrain_description :
    worldTerrainBits * minTerrainRatio ≤ agentBits := by
  rw [agent_bits_value]
  norm_num [worldTerrainBits, minTerrainRatio, ModelConstants.worldSide]

/-- No larger whole ratio holds: twenty times the packed terrain bits exceed the parameter
bits. -/
theorem terrain_ratio_largest : ¬ worldTerrainBits * (minTerrainRatio + 1) ≤ agentBits := by
  rw [agent_bits_value]
  norm_num [worldTerrainBits, minTerrainRatio, ModelConstants.worldSide]

end AcornVerif
