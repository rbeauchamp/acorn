import Mathlib.Data.Rat.Defs

namespace AcornVerif.ModelConstants

def gammaG90 : ℚ := (15099494 : ℚ) / 16777216

def horizonG90 : ℚ := (10485758 : ℚ) / 1048576

def gammaG95 : ℚ := (15938355 : ℚ) / 16777216

def horizonG95 : ℚ := (10485758 : ℚ) / 524288

def gammaG99 : ℚ := (16609444 : ℚ) / 16777216

def horizonG99 : ℚ := (13107213 : ℚ) / 131072

def metaGamma : ℚ := (16609444 : ℚ) / 16777216

def optionGamma : ℚ := (16609444 : ℚ) / 16777216

def gainStepSize : ℚ := (13743895 : ℚ) / 274877906944

def differentialValueBound : ℚ := (13107213 : ℚ) / 131072

def gainTrackingHorizon : ℕ := 20000

def learnerCount : ℕ := 51

def runtimeLearnerCount : ℕ := 57

def gainParameterCount : ℕ := 1

def weightSpace : ℕ := 16384

def knowledgeArraysPerLearner : ℕ := 2

def worldSide : ℕ := 1024

def energyMax : ℕ := 2000

def energyRestRecover : ℕ := 20

def energyEatRestore : ℕ := 400

def energyMaxStepCost : ℕ := 4

def energyMinStepCost : ℕ := 1

def facings : ℕ := 4

def dayPhases : ℕ := 8

def reachRadius : ℕ := 3

def ezMaxDuration : ℕ := 128

def exploreRate : ℚ := (10737418 : ℚ) / 1073741824

def eta : ℚ := (13421773 : ℚ) / 134217728

def alphaInit : ℚ := (13743895 : ℚ) / 274877906944

def discounts : List (ℚ × ℚ) :=
  [(gammaG90, horizonG90), (gammaG95, horizonG95), (gammaG99, horizonG99)]

end AcornVerif.ModelConstants
