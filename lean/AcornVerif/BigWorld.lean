/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Tactic.NormNum
import AcornVerif.ModelConstants

/-!
# State-space and parameter-budget arithmetic

This fixed dimensional model compares a declared parameter budget with a
Cartesian product of position, facing, energy, day phase and craft flags, and
with a packed terrain description. `CurrentConstants` links its stated subset
of the inputs to current execution; the remaining factors are explicit model
inputs in `ModelConstants`.

The inequalities concern these formulas. They do not prove that every Cartesian
combination is reachable, that every state needs a distinct parameter, or that
the executing agent learns to generalise. Native object overhead and complete
checkpoint size are outside the parameter-budget model.
-/

namespace AcornVerif

open AcornVerif.ModelConstants

/-- Declared learned-parameter budget: two arrays per learner and one reserved gain slot.
The array count is a model input, not a generated fact about checkpoint storage. -/
def agentParameters : ℕ :=
  ModelConstants.runtimeLearnerCount * ModelConstants.weightSpace *
    ModelConstants.knowledgeArraysPerLearner +
    ModelConstants.gainParameterCount

/-- Size of the declared Cartesian product of state components.
The name does not assert reachability of every combination under world dynamics. -/
def reachableStates : ℕ :=
  ModelConstants.worldSide * ModelConstants.worldSide
    * ModelConstants.facings
    * (ModelConstants.energyMax + 1)
    * ModelConstants.dayPhases
    * 2
    * 2

/-- Declared ratio used in the state-product comparison. -/
def minStateMargin : ℕ := 100000

/-- The declared state product exceeds the modeled parameter count by the stated margin. -/
theorem big_world_margin_holds :
    agentParameters * minStateMargin ≤ reachableStates := by
  norm_num [agentParameters, reachableStates, minStateMargin, ModelConstants.runtimeLearnerCount,
    ModelConstants.gainParameterCount,
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
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner,
    ModelConstants.worldSide]

end AcornVerif
