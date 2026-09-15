/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# Retained mathematical-model constants

These exact rational and natural inputs preserve the established mathematical
models and historical study reductions. The module name is retained for source
compatibility. Current native storage imports machine-word/interface owners
directly; a model theorem is not an execution-correspondence theorem. Current
constant compatibility is checked by `AcornVerif.CurrentConstants` over its
explicitly listed finite interface.
-/

namespace AcornVerif.Generated

/-- `Discount::G90.gamma()` — the discount factor. -/
def gammaG90 : ℚ := (15099494 : ℚ) / 16777216

/-- `Discount::G90.horizon()` — the value bound, as computed in `f32`. -/
def horizonG90 : ℚ := (10485758 : ℚ) / 1048576

/-- `Discount::G95.gamma()` — the discount factor. -/
def gammaG95 : ℚ := (15938355 : ℚ) / 16777216

/-- `Discount::G95.horizon()` — the value bound, as computed in `f32`. -/
def horizonG95 : ℚ := (10485758 : ℚ) / 524288

/-- `Discount::G99.gamma()` — the discount factor. -/
def gammaG99 : ℚ := (16609444 : ℚ) / 16777216

/-- `Discount::G99.horizon()` — the value bound, as computed in `f32`. -/
def horizonG99 : ℚ := (13107213 : ℚ) / 131072

/-- Meta-controller discount, read from `Agent::meta`. -/
def metaGamma : ℚ := (16609444 : ℚ) / 16777216

/-- Option-controller discount, read from `Agent::skills[0]`. -/
def optionGamma : ℚ := (16609444 : ℚ) / 16777216

/-- Fixed reward-residual gain step (`AverageRewardTracker::STEP_SIZE`). -/
def gainStepSize : ℚ := (13743895 : ℚ) / 274877906944

/-- Differential numerical budget (`DifferentialValue::BOUND`), not a true bias bound. -/
def differentialValueBound : ℚ := (13107213 : ℚ) / 131072

/-- Independent host-time gain horizon (`GainTrackingHorizon::TRANSITIONS`). -/
def gainTrackingHorizon : ℕ := 20000

/-- Dyadic envelope of the complete weight domain. -/
def predictionWeightEnvelope : ℚ := (8388608 : ℚ) / 65536

/-- Exact integer increments of the binary32 mantissa. -/
def predictionExactAdditions : ℕ := 16777216

/-- Learners in the agent: primitive control, meta, one controller per
skill, and one per demon (`agent::LEARNER_COUNT`). -/
def learnerCount : ℕ := 51

/-- Actual stored default learners, counting optional model storage once. -/
def runtimeLearnerCount : ℕ := 57

/-- Scalar gain tracker storage in f32 words; dormant under discounted control. -/
def gainParameterCount : ℕ := 1

/-- Weights per learner (`agent::DEFAULT_WEIGHT_SPACE`). -/
def weightSpace : ℕ := 16384

/-- Arrays per learner that carry knowledge across a restart —
`checkpoint::KNOWLEDGE_ARRAYS_PER_LEARNER` (`w` and `beta`). -/
def knowledgeArraysPerLearner : ℕ := 2

/-- Default world side (`WorldConfig::DEFAULT_SIDE`). -/
def worldSide : ℕ := 1024

/-- `Energy::MAX` — the energy capacity, in units of 0.1. -/
def energyMax : ℕ := 2000

/-- `Energy::REST_RECOVER` — energy returned on an exhausted step. -/
def energyRestRecover : ℕ := 20

/-- `Energy::EAT_RESTORE` — energy returned by eating. -/
def energyEatRestore : ℕ := 400

/-- `Energy::MAX_STEP_COST` — exhausted over `Action::ALL` × the
day/night multipliers. -/
def energyMaxStepCost : ℕ := 4

/-- `Energy::MIN_STEP_COST` — by the same exhaustion. -/
def energyMinStepCost : ℕ := 1

/-- `Dir::ALL.len()` — the facings a body can hold. -/
def facings : ℕ := 4

/-- `World::day_phase` range — the phase buckets a day is cut into. -/
def dayPhases : ℕ := 8

/-- Side of every agent-baseline held-out world. -/
def studyWorldSide : ℕ := 1024

/-- Goal occurrences in one agent-baseline curriculum cycle. -/
def studyGoals : ℕ := 13

/-- Complete agent-baseline curriculum cycles. -/
def studyCycles : ℕ := 3

/-- Attempts available to one agent-baseline goal occurrence. -/
def studyAttemptsPerGoal : ℕ := 3

/-- Environment-step cap of one agent-baseline attempt. -/
def studyStepsPerAttempt : ℕ := 4000

/-- Cumulative environment-step cap of one agent-baseline goal occurrence. -/
def studyStepsPerGoal : ℕ := 12000

/-- Reach time assigned to a failed occurrence: the cap plus one. -/
def studyReachFailureTime : ℕ := 12001

/-- Agent initialization seed, fixed independently of held-out world identity. -/
def studyAgentSeed : ℕ := 17297202496056317182

/-- Sensory tiling count read from the registered agent configuration. -/
def studyAgentTilings : ℕ := 8

/-- Imprint-unit count read from the registered agent configuration. -/
def studyAgentImprintUnits : ℕ := 512

/-- Size of the fixed held-out benchmark population. -/
def studySeedCount : ℕ := 30

/-- Required evaluator-arm count. -/
def studyArmCount : ℕ := 5

/-- Arm semantics in registered execution order: learning, Reach relation,
temporal abstraction, deterministic pseudorandom policy. -/
def studyArmSemantics : List (Bool × Bool × Bool × Bool) := [
  (true, true, true, false),
  (false, false, false, true),
  (false, true, true, false),
  (true, false, true, false),
  (true, true, false, false)
]

/-- Fixed held-out seeds, in the registered execution order. -/
def studySeeds : List ℕ := [
  9016730989737993802,
  15584263927826207376,
  5074385090136322597,
  13214739808955630584,
  2260754871798853763,
  2396729331672454084,
  10624045427111211233,
  17657197785719970634,
  18011533756336924530,
  9457964815634238784,
  11412248836293663304,
  11439529482346486891,
  16904397590850837933,
  16700864479362968399,
  6422086290073316155,
  2268568929412746579,
  6675331489026331364,
  12955938599993307058,
  7465941113074525545,
  3170178326827601461,
  7098767358082369501,
  4197455624923437127,
  15794369556855821662,
  11721522751964944195,
  7092587069793486527,
  15985307262422689539,
  7200542430949300130,
  13592118800738238450,
  18340171756978161658,
  11643494274582612114
]

/-- Minimum paired probability of improvement. -/
def studyProbabilityThreshold : ℚ := (3 : ℚ) / 4

/-- Numerator of the paired probability threshold. -/
def studyProbabilityThresholdNumerator : ℕ := 3

/-- Denominator of the paired probability threshold. -/
def studyProbabilityThresholdDenominator : ℕ := 4

/-- Strict lower interval-bound threshold. -/
def studyIntervalThreshold : ℚ := (1 : ℚ) / 2

/-- Minimum held-out Reach success rate. -/
def studyReachThreshold : ℚ := (3 : ℚ) / 5

/-- Registered paired-bootstrap resample count. -/
def studyBootstrapSamples : ℕ := 10000

/-- Registered paired-bootstrap seed. -/
def studyBootstrapSeed : ℕ := 5821716393

/-- Reach completion radius shared by observation and reward. -/
def reachRadius : ℕ := 3

/-- `EzGreedy::MAX_DURATION` — the longest a single exploratory run may
last. -/
def ezMaxDuration : ℕ := 128

/-- `SwiftTdConfig::demon(..).eta()` — the overshoot budget η. -/
def eta : ℚ := (13421773 : ℚ) / 134217728

/-- `SwiftTdConfig::demon(..)` initial step size α₀. -/
def alphaInit : ℚ := (13743895 : ℚ) / 274877906944

/-- The closed discount set as (γ, horizon) pairs, in `Discount::ALL` order. -/
def discounts : List (ℚ × ℚ) :=
  [(gammaG90, horizonG90), (gammaG95, horizonG95), (gammaG99, horizonG99)]

end AcornVerif.Generated
