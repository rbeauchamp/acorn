/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Rat.Defs

/-!
# Mathematical inputs for current mechanism proofs

Exact rational and natural values used by the supporting algorithm proofs.
Current execution imports its machine-word and dimension owners directly;
`AcornVerif.CurrentConstants` checks correspondence over its stated finite
interface. A mathematical identity establishes an execution property only
through the relevant implementation linkage and hypotheses.
-/

namespace AcornVerif.ModelConstants

/-- Rational value of `Acorn.Discount.g90.gamma`, checked by `CurrentConstants.discount_values`. -/
def gammaG90 : ℚ := (15099494 : ℚ) / 16777216

/-- Rounded horizon of `Acorn.Discount.g90`, checked by `CurrentConstants.discount_values`. -/
def horizonG90 : ℚ := (10485758 : ℚ) / 1048576

/-- Rational value of `Acorn.Discount.g95.gamma`, checked by `CurrentConstants.discount_values`. -/
def gammaG95 : ℚ := (15938355 : ℚ) / 16777216

/-- Rounded horizon of `Acorn.Discount.g95`, checked by `CurrentConstants.discount_values`. -/
def horizonG95 : ℚ := (10485758 : ℚ) / 524288

/-- Rational value of `Acorn.Discount.g99.gamma`, checked by `CurrentConstants.discount_values`. -/
def gammaG99 : ℚ := (16609444 : ℚ) / 16777216

/-- Rounded horizon of `Acorn.Discount.g99`, checked by `CurrentConstants.discount_values`. -/
def horizonG99 : ℚ := (13107213 : ℚ) / 131072

/-- Meta-controller model discount; `CurrentConstants.numeric_values` equates it to g99. -/
def metaGamma : ℚ := (16609444 : ℚ) / 16777216

/-- Option model discount; `CurrentConstants.numeric_values` equates it to g99. -/
def optionGamma : ℚ := (16609444 : ℚ) / 16777216

/-- Rational value of `Acorn.gainTrackingStep`, checked by `CurrentConstants.numeric_values`. -/
def gainStepSize : ℚ := (13743895 : ℚ) / 274877906944

/-- Differential numerical budget, checked by `CurrentConstants.numeric_values`.
This bounds represented values; it is not a bound on the environment's true differential value. -/
def differentialValueBound : ℚ := (13107213 : ℚ) / 131072

/-- Host-time gain horizon, checked against `Acorn.gainTrackingHorizon` by `CurrentConstants`. -/
def gainTrackingHorizon : ℕ := 20000

/-- Primitive, meta, skill and demon learner count from the feature dimensions.
`CurrentConstants.dimensions` checks this sum. -/
def learnerCount : ℕ := 51

/-- Discounted storage-model count: primary learners plus two model learners per skill.
`CurrentConstants.dimensions` checks this arithmetic; concrete storage depends on the criterion. -/
def runtimeLearnerCount : ℕ := 57

/-- Reserved scalar gain slot in the storage model. -/
def gainParameterCount : ℕ := 1

/-- Default learner dimension, checked by `CurrentConstants.dimensions`. -/
def weightSpace : ℕ := 16384

/-- Two learned arrays per learner (`w` and `beta`) assumed by the storage model.
This declaration does not inspect the checkpoint implementation. -/
def knowledgeArraysPerLearner : ℕ := 2

/-- World side selected for the fixed dimensional comparison. -/
def worldSide : ℕ := 1024

/-- Energy capacity matched to `Acorn.FeatureConstants.energyMax` by `CurrentConstants`. -/
def energyMax : ℕ := 2000

/-- Rest recovery matched to `Acorn.FeatureConstants.energyRestRecover` by `CurrentConstants`. -/
def energyRestRecover : ℕ := 20

/-- Eating recovery matched to `Acorn.FeatureConstants.energyEatRestore` by `CurrentConstants`. -/
def energyEatRestore : ℕ := 400

/-- Upper per-action cost supplied to the conditional energy-ledger analysis. -/
def energyMaxStepCost : ℕ := 4

/-- Lower per-action cost supplied to the conditional energy-ledger analysis. -/
def energyMinStepCost : ℕ := 1

/-- Four facings assumed by the dimensional comparison. -/
def facings : ℕ := 4

/-- Day-phase count matched to `Acorn.FeatureConstants.dayPhases` by `CurrentConstants`. -/
def dayPhases : ℕ := 8

/-- Reach radius matched to `Acorn.FeatureConstants.reachRadius` by `CurrentConstants`. -/
def reachRadius : ℕ := 3

/-- Exploration cap matched to `Acorn.FeatureConstants.explorationMaxDuration`
by `CurrentConstants`. -/
def ezMaxDuration : ℕ := 128

/-- Demon overshoot budget for discounted g99, checked by `CurrentConstants.numeric_values`. -/
def eta : ℚ := (13421773 : ℚ) / 134217728

/-- Demon initial step size for discounted g99, checked by `CurrentConstants.numeric_values`. -/
def alphaInit : ℚ := (13743895 : ℚ) / 274877906944

/-- Rational discount/horizon pairs for g90, g95 and g99, respectively. -/
def discounts : List (ℚ × ℚ) :=
  [(gammaG90, horizonG90), (gammaG95, horizonG95), (gammaG99, horizonG99)]

end AcornVerif.ModelConstants
