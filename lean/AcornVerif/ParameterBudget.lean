import Mathlib.Tactic.NormNum
import AcornVerif.ModelConstants

namespace AcornVerif

open AcornVerif.ModelConstants

def agentParameters : ℕ :=
  ModelConstants.runtimeLearnerCount * ModelConstants.weightSpace *
    ModelConstants.knowledgeArraysPerLearner +
    ModelConstants.gainParameterCount

theorem agent_parameters_value : agentParameters = 1867777 := by
  norm_num [agentParameters, ModelConstants.runtimeLearnerCount, ModelConstants.weightSpace,
    ModelConstants.knowledgeArraysPerLearner, ModelConstants.gainParameterCount]

def declaredStateProduct : ℕ :=
  ModelConstants.worldSide * ModelConstants.worldSide
    * ModelConstants.facings
    * (ModelConstants.energyMax + 1)
    * ModelConstants.dayPhases
    * 2
    * 2

theorem state_quotient_value : declaredStateProduct / agentParameters = 143791 := by
  norm_num [agentParameters, declaredStateProduct,
    ModelConstants.runtimeLearnerCount, ModelConstants.gainParameterCount,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner, ModelConstants.worldSide,
    ModelConstants.facings, ModelConstants.energyMax, ModelConstants.dayPhases]

def minStateMargin : ℕ := 140000

theorem state_product_exceeds_parameter_count :
    agentParameters * minStateMargin ≤ declaredStateProduct := by
  norm_num [agentParameters, declaredStateProduct, minStateMargin,
    ModelConstants.runtimeLearnerCount, ModelConstants.gainParameterCount,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner, ModelConstants.worldSide,
    ModelConstants.facings, ModelConstants.energyMax, ModelConstants.dayPhases]

theorem state_margin_largest :
    ¬ agentParameters * (minStateMargin + 10000) ≤ declaredStateProduct := by
  norm_num [agentParameters, declaredStateProduct, minStateMargin,
    ModelConstants.runtimeLearnerCount, ModelConstants.gainParameterCount,
    ModelConstants.weightSpace, ModelConstants.knowledgeArraysPerLearner, ModelConstants.worldSide,
    ModelConstants.facings, ModelConstants.energyMax, ModelConstants.dayPhases]

def agentBits : ℕ := agentParameters * 32

theorem agent_bits_value : agentBits = 59768864 := by
  rw [agentBits, agent_parameters_value]

def worldStateBits : ℕ := 64 + 64 + 163 + 129 + 67371265 + 262145 + 12001 + 256

theorem world_state_bits_value : worldStateBits = 67646087 := by
  norm_num [worldStateBits]

theorem world_state_exceeds_agent_bits : agentBits < worldStateBits := by
  rw [agent_bits_value, world_state_bits_value]
  norm_num

def worldTerrainBits : ℕ := ModelConstants.worldSide * ModelConstants.worldSide * 3

def minTerrainRatio : ℕ := 19

theorem agent_exceeds_terrain_description :
    worldTerrainBits * minTerrainRatio ≤ agentBits := by
  rw [agent_bits_value]
  norm_num [worldTerrainBits, minTerrainRatio, ModelConstants.worldSide]

theorem terrain_ratio_largest : ¬ worldTerrainBits * (minTerrainRatio + 1) ≤ agentBits := by
  rw [agent_bits_value]
  norm_num [worldTerrainBits, minTerrainRatio, ModelConstants.worldSide]

end AcornVerif
