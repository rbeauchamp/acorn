/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Generated
import AcornVerif.CurrentArithmetic
import Acorn.Average
import Acorn.FeatureConstants
import AcornSpec.StudySchedule

/-! # Retained model and current constant compatibility

Current consumers import their owning constants directly. These small closed
interfaces additionally keep the retained rational model and protocol inputs
compatible with the machine definitions they describe. They establish constant
identity, not behavioral correspondence between independently written programs.
-/
namespace AcornVerif.CurrentConstants
open Acorn AcornVerif.CurrentArithmetic

/-- Every member of the closed discount domain has the retained exact rational
value and rounded horizon. The conversion reads the actual binary32 operations. -/
theorem discount_values (discount : Discount) :
    (numerical32 discount.gamma, numerical32 discount.horizon) =
      (match discount with
      | .g90 => (Generated.gammaG90, Generated.horizonG90)
      | .g95 => (Generated.gammaG95, Generated.horizonG95)
      | .g99 => (Generated.gammaG99, Generated.horizonG99)) := by
  cases discount with
  | g90 =>
    change ((1:ℚ)*15099494*2^(-24:Int), (1:ℚ)*10485758*2^(-20:Int)) = _
    norm_num [Generated.gammaG90, Generated.horizonG90]
  | g95 =>
    change ((1:ℚ)*15938355*2^(-24:Int), (1:ℚ)*10485758*2^(-19:Int)) = _
    norm_num [Generated.gammaG95, Generated.horizonG95]
  | g99 =>
    change ((1:ℚ)*16609444*2^(-24:Int), (1:ℚ)*13107213*2^(-17:Int)) = _
    norm_num [Generated.gammaG99, Generated.horizonG99]

/-- The gain and demon configuration model constants denote the actual machine
words and derived gain step, rather than decimal approximations. -/
theorem numeric_values :
    numerical32 gainTrackingStep = Generated.gainStepSize ∧
    gainTrackingHorizon.toNat = Generated.gainTrackingHorizon ∧
    numerical32 (ValueRule.bound .differential) = Generated.differentialValueBound ∧
    numerical32 ({ role := .demon, rule := .discounted .g99 } : Config).eta = Generated.eta ∧
    numerical32 ({ role := .demon, rule := .discounted .g99 } : Config).alphaInitial =
      Generated.alphaInit ∧
    numerical32 Discount.g99.gamma = Generated.metaGamma ∧
    numerical32 Discount.g99.gamma = Generated.optionGamma := by
  change (1:ℚ)*13743895*2^(-38:Int) = Generated.gainStepSize ∧
    20000 = Generated.gainTrackingHorizon ∧
    (1:ℚ)*13107213*2^(-17:Int) = Generated.differentialValueBound ∧
    (1:ℚ)*13421773*2^(-27:Int) = Generated.eta ∧
    (1:ℚ)*13743895*2^(-38:Int) = Generated.alphaInit ∧
    (1:ℚ)*16609444*2^(-24:Int) = Generated.metaGamma ∧
    (1:ℚ)*16609444*2^(-24:Int) = Generated.optionGamma
  norm_num [Generated.gainStepSize, Generated.gainTrackingHorizon,
    Generated.differentialValueBound, Generated.eta, Generated.alphaInit,
    Generated.metaGamma, Generated.optionGamma]

/-- Current dimensions and the retained storage arithmetic share the same closed
interface. Concrete receiver traversal is owned by CurrentFeatureConsumers. -/
theorem dimensions :
    FeatureConstants.defaultWeightSpace = Generated.weightSpace ∧
    FeatureConstants.primitiveCount + FeatureConstants.metaActionCount +
      FeatureConstants.skillCount * FeatureConstants.primitiveCount +
      FeatureConstants.demonCount = Generated.learnerCount ∧
    Generated.learnerCount + FeatureConstants.skillCount * 2 = Generated.runtimeLearnerCount ∧
    FeatureConstants.energyMax = Generated.energyMax ∧
    FeatureConstants.energyRestRecover = Generated.energyRestRecover ∧
    FeatureConstants.energyEatRestore = Generated.energyEatRestore ∧
    FeatureConstants.dayPhases = Generated.dayPhases ∧
    FeatureConstants.reachRadius = Generated.reachRadius ∧
    FeatureConstants.explorationMaxDuration = Generated.ezMaxDuration := by decide

/-- The shared immutable study schedule and seed list retain the mathematical
reducer's original input values. This executes no world or learning transition. -/
theorem study_inputs :
    AcornSpec.stepsPerAttempt.toNat = Generated.studyStepsPerAttempt ∧
    AcornSpec.attemptsPerGoal = Generated.studyAttemptsPerGoal ∧
    AcornSpec.studyCycles = Generated.studyCycles ∧
    AcornSpec.studyGoals = Generated.studyGoals ∧
    AcornSpec.studyWorldSide.toNat = Generated.studyWorldSide ∧
    AcornSpec.Constants.agentSeedValue.toNat = Generated.studyAgentSeed ∧
    (AcornSpec.Constants.heldOutSeeds.toList.map UInt64.toNat) = Generated.studySeeds ∧
    AcornSpec.Constants.heldOutSeeds.size = Generated.studySeedCount ∧
    FeatureConstants.defaultTilings = Generated.studyAgentTilings ∧
    FeatureConstants.defaultImprintUnits = Generated.studyAgentImprintUnits ∧
    AcornSpec.Constants.bootstrapSeedValue.toNat = Generated.studyBootstrapSeed := by decide

end AcornVerif.CurrentConstants
