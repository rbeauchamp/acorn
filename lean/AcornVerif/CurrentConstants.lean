import AcornVerif.ModelConstants
import AcornVerif.CurrentArithmetic
import Acorn.Average
import Acorn.FeatureConstants
import Acorn.Handcrafted.TemporalProfile

namespace AcornVerif.CurrentConstants
open Acorn AcornVerif.CurrentArithmetic

theorem discount_values (discount : Discount) :
    (numerical32 discount.gamma, numerical32 discount.horizon) =
      (match discount with
      | .g90 => (ModelConstants.gammaG90, ModelConstants.horizonG90)
      | .g95 => (ModelConstants.gammaG95, ModelConstants.horizonG95)
      | .g99 => (ModelConstants.gammaG99, ModelConstants.horizonG99)) := by
  cases discount with
  | g90 =>
    change ((1:ℚ)*15099494*2^(-24:Int), (1:ℚ)*10485758*2^(-20:Int)) = _
    norm_num [ModelConstants.gammaG90, ModelConstants.horizonG90]
  | g95 =>
    change ((1:ℚ)*15938355*2^(-24:Int), (1:ℚ)*10485758*2^(-19:Int)) = _
    norm_num [ModelConstants.gammaG95, ModelConstants.horizonG95]
  | g99 =>
    change ((1:ℚ)*16609444*2^(-24:Int), (1:ℚ)*13107213*2^(-17:Int)) = _
    norm_num [ModelConstants.gammaG99, ModelConstants.horizonG99]

theorem numeric_values :
    numerical32 gainTrackingStep = ModelConstants.gainStepSize ∧
    gainTrackingHorizon.toNat = ModelConstants.gainTrackingHorizon ∧
    numerical32 (ValueRule.bound .differential) = ModelConstants.differentialValueBound ∧
    numerical32 ({ role := .demon, rule := .discounted .g99 } : Config).eta = ModelConstants.eta ∧
    numerical32 ({ role := .demon, rule := .discounted .g99 } : Config).alphaInitial =
      ModelConstants.alphaInit ∧
    numerical32 Discount.g99.gamma = ModelConstants.metaGamma ∧
    numerical32 Discount.g99.gamma = ModelConstants.optionGamma := by
  change (1:ℚ)*13743895*2^(-38:Int) = ModelConstants.gainStepSize ∧
    20000 = ModelConstants.gainTrackingHorizon ∧
    (1:ℚ)*13107213*2^(-17:Int) = ModelConstants.differentialValueBound ∧
    (1:ℚ)*13421773*2^(-27:Int) = ModelConstants.eta ∧
    (1:ℚ)*13743895*2^(-38:Int) = ModelConstants.alphaInit ∧
    (1:ℚ)*16609444*2^(-24:Int) = ModelConstants.metaGamma ∧
    (1:ℚ)*16609444*2^(-24:Int) = ModelConstants.optionGamma
  norm_num [ModelConstants.gainStepSize, ModelConstants.gainTrackingHorizon,
    ModelConstants.differentialValueBound, ModelConstants.eta, ModelConstants.alphaInit,
    ModelConstants.metaGamma, ModelConstants.optionGamma]

theorem explore_rate_value :
    numerical32 Handcrafted.declaredRate.value = ModelConstants.exploreRate := by
  change (1:ℚ)*10737418*2^(-30:Int) = ModelConstants.exploreRate
  norm_num [ModelConstants.exploreRate]

theorem dimensions :
    FeatureConstants.defaultWeightSpace = ModelConstants.weightSpace ∧
    FeatureConstants.primitiveCount + FeatureConstants.metaActionCount +
      FeatureConstants.skillCount * FeatureConstants.primitiveCount +
      FeatureConstants.demonCount = ModelConstants.learnerCount ∧
    ModelConstants.learnerCount + FeatureConstants.skillCount * 2 =
      ModelConstants.runtimeLearnerCount ∧
    FeatureConstants.energyMax = ModelConstants.energyMax ∧
    FeatureConstants.energyRestRecover = ModelConstants.energyRestRecover ∧
    FeatureConstants.energyEatRestore = ModelConstants.energyEatRestore ∧
    FeatureConstants.dayPhases = ModelConstants.dayPhases ∧
    FeatureConstants.reachRadius = ModelConstants.reachRadius ∧
    FeatureConstants.explorationMaxDuration = ModelConstants.ezMaxDuration := by decide

end AcornVerif.CurrentConstants
