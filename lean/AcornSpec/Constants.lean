/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Shared machine-word constants

This leaf owns the exact IEEE-754 words and deterministic stream parameters
imported directly by the current native program and preserved specification.
Algorithm modules own their source citations and semantic contracts. Changing a
word changes its consumers by construction; no cross-language emission is needed.
-/

namespace AcornSpec.Constants

/-- Binary64 reduction constant `ln2HiBits`. -/
def ln2HiBits : UInt64 := 0x3fe62e42fee00000
/-- Binary64 reduction constant `ln2LoBits`. -/
def ln2LoBits : UInt64 := 0x3dea39ef35793c77
/-- Binary64 reduction constant `log2eBits`. -/
def log2eBits : UInt64 := 0x3ff71547652b82fe
/-- Binary64 reduction constant `sqrt2Bits`. -/
def sqrt2Bits : UInt64 := 0x3ff6a09e667f3bcd
/-- Binary32 exponential bound `expOverflowBits`. -/
def expOverflowBits : UInt32 := 0x42b20000
/-- Binary32 exponential bound `expUnderflowBits`. -/
def expUnderflowBits : UInt32 := 0xc2d00000
/-- `GainTrackingHorizon::TRANSITIONS`, the host reward-rate lag budget. -/
def gainTrackingHorizon : UInt32 := 20000
/-- Exact f32 bits of the configured decimal value (`0.3`). -/
def band030Bits : UInt32 := 0x3e99999a
/-- Exact f32 bits of the configured decimal value (`0.335`). -/
def band0335Bits : UInt32 := 0x3eab851f
/-- Exact f32 bits of the configured decimal value (`0.6`). -/
def band060Bits : UInt32 := 0x3f19999a
/-- Exact f32 bits of the configured decimal value (`0.72`). -/
def band072Bits : UInt32 := 0x3f3851ec
/-- Exact f32 bits of the configured decimal value (`0.8`). -/
def band080Bits : UInt32 := 0x3f4ccccd
/-- Exact f32 bits of the configured decimal value (`0.4`). -/
def moist040Bits : UInt32 := 0x3ecccccd
/-- Exact f32 bits of the configured decimal value (`0.9`). -/
def gamma90Bits : UInt32 := 0x3f666666
/-- Exact f32 bits of the configured decimal value (`0.95`). -/
def gamma95Bits : UInt32 := 0x3f733333
/-- Exact f32 bits of the configured decimal value (`0.99`). -/
def gamma99Bits : UInt32 := 0x3f7d70a4
/-- Exact f32 bits of the configured decimal value (`0.9`). -/
def lambda09Bits : UInt32 := 0x3f666666
/-- Exact f32 bits of the configured decimal value (`0.95`). -/
def lambda095Bits : UInt32 := 0x3f733333
/-- Exact f32 bits of the configured decimal value (`0.00005`). -/
def alphaInit5e5Bits : UInt32 := 0x3851b717
/-- Exact f32 bits of the configured decimal value (`0.0001`). -/
def alphaInit1e4Bits : UInt32 := 0x38d1b717
/-- Exact f32 bits of the configured decimal value (`0.00001`). -/
def epsilon1e5Bits : UInt32 := 0x3727c5ac
/-- Exact f32 bits of the configured decimal value (`0.1`). -/
def eta01Bits : UInt32 := 0x3dcccccd
/-- Exact f32 bits of the configured decimal value (`0.25`). -/
def eta025Bits : UInt32 := 0x3e800000
/-- Exact f32 bits of the configured decimal value (`0.0000000001`). -/
def etaMin1e10Bits : UInt32 := 0x2edbe6ff
/-- Exact f32 bits of the configured decimal value (`0.999`). -/
def decay0999Bits : UInt32 := 0x3f7fbe77
/-- Exact f32 bits of the configured decimal value (`0.001`). -/
def meta1e3Bits : UInt32 := 0x3a83126f
/-- Exact f32 bits of the configured decimal value (`0.03`). -/
def meta3e2Bits : UInt32 := 0x3cf5c28f
/-- Exact f32 bits of the configured decimal value (`0.000001`). -/
def tie1e6Bits : UInt32 := 0x358637bd
/-- Exact f32 bits of the configured decimal value (`0.5`). -/
def epsStartBits : UInt32 := 0x3f000000
/-- Exact f32 bits of the configured decimal value (`0.05`). -/
def epsMinBits : UInt32 := 0x3d4ccccd
/-- Exact f32 bits of the configured decimal value (`0.99999`). -/
def epsDecayBits : UInt32 := 0x3f7fff58
/-- Exact f32 bits of the configured decimal value (`0.1`). -/
def optionEpsilonBits : UInt32 := 0x3dcccccd

/-- `agent_baseline::AGENT_BASELINE_HELD_OUT_SEEDS`, in frozen index order. -/
def heldOutSeeds : Array UInt64 := #[
  0x7d21dd0ffe96e64a,
  0xd8466d793003d290,
  0x466bd65aaf1d3225,
  0xb7642fd7700383f8,
  0x1f5fd093f1cdf083,
  0x2142e4a0f51893c4,
  0x937031070093b0e1,
  0xf50af7d592a71b4a,
  0xf9f5d285ae6b6772,
  0x834170e3ae058d40,
  0x9e6073da17a61a48,
  0x9ec15f7478dedc6b,
  0xea987c0ba8a21dad,
  0xe7c563c24e5e6b4f,
  0x591fd57484b9eb3b,
  0x1f7b936c02228d53,
  0x5ca38a9f3164d2e4,
  0xb3ccbd83605f6fb2,
  0x679c59e2d6caa569,
  0x2bfebc6455338e35,
  0x6283e34d21a347dd,
  0x3a405ba6dc06d847,
  0xdb30df6e07a2955e,
  0xa2ab36d6f1879743,
  0x626dee5ca191c6bf,
  0xddd73842ea2d2703,
  0x63ed7730dadc57a2,
  0xbca0e808fee93ff2,
  0xfe85610ae655c7fa,
  0xa196005a54ca8892
]

/-- `fnv1a(agent_baseline::FOLD_TAG)` — the binding fold's initial value, for
the specification's decidable crosscheck of its own computation. -/
def foldInitValue : UInt64 := 0xbe84953016cbac84

/-- `agent_baseline::AGENT_SEED`, for the same crosscheck. -/
def agentSeedValue : UInt64 := 0xf00c0206916fd4fe

/-- `agent_baseline::BOOTSTRAP_SEED` — the registered analysis seed. -/
def bootstrapSeedValue : UInt64 := 0x000000015b0057a9

/-- `fnv1a(agent_baseline::BOOTSTRAP_TAG)` — the D3 resample stream id, for
the specification's decidable crosscheck of its own tag computation. -/
def bootstrapTagFnvValue : UInt64 := 0xb86ea26d9f8eb1bd

/-! Compatibility domains: explicit byte strings and numeric identities. The
kernel checks their correspondence in `AcornVerif.StudyCompatibility`. -/

namespace Compatibility

/-- The complete compatibility domain set. -/
inductive Domain where
  /-- Historical `actionFold` domain. -/
  | actionFold
  /-- Historical `agentBaselineInitialization` domain. -/
  | agentBaselineInitialization
  /-- Historical `agentBaselineRandom` domain. -/
  | agentBaselineRandom
  /-- Historical `agentBaselineBootstrap` domain. -/
  | agentBaselineBootstrap
  /-- Historical `intraOptionCreditInitialization` domain. -/
  | intraOptionCreditInitialization
  /-- Historical `intraOptionCreditRandom` domain. -/
  | intraOptionCreditRandom
  /-- Historical `intraOptionCreditBootstrap` domain. -/
  | intraOptionCreditBootstrap
  /-- Historical `intraOptionCreditPopulation` domain. -/
  | intraOptionCreditPopulation
  /-- Historical `derivedExplorationRateInitialization` domain. -/
  | derivedExplorationRateInitialization
  /-- Historical `derivedExplorationRateRandom` domain. -/
  | derivedExplorationRateRandom
  /-- Historical `derivedExplorationRateBootstrap` domain. -/
  | derivedExplorationRateBootstrap
  /-- Historical `derivedExplorationRatePopulation` domain. -/
  | derivedExplorationRatePopulation
  /-- Historical `stompPlanningInitialization` domain. -/
  | stompPlanningInitialization
  /-- Historical `stompPlanningRandom` domain. -/
  | stompPlanningRandom
  /-- Historical `stompPlanningBootstrap` domain. -/
  | stompPlanningBootstrap
  /-- Historical `stompPlanningPopulation` domain. -/
  | stompPlanningPopulation
  deriving DecidableEq, Repr

/-- Original UTF-8 domain bytes, retained as sealed compatibility data. -/
def Domain.bytes : Domain → List UInt8
  | .actionFold => [115, 116, 117, 100, 121, 45, 100, 101, 99, 105, 115, 105, 111, 110, 45, 115, 116, 114, 101, 97, 109, 45, 118, 49]
  | .agentBaselineInitialization => [105, 115, 115, 117, 101, 45, 49, 53, 45, 97, 103, 101, 110, 116, 45, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 45, 118, 49]
  | .agentBaselineRandom => [105, 115, 115, 117, 101, 45, 49, 53, 45, 114, 97, 110, 100, 111, 109, 45, 97, 114, 109, 45, 118, 49]
  | .agentBaselineBootstrap => [105, 115, 115, 117, 101, 45, 49, 53, 45, 98, 111, 111, 116, 115, 116, 114, 97, 112, 45, 118, 50]
  | .intraOptionCreditInitialization => [105, 115, 115, 117, 101, 45, 50, 50, 45, 97, 103, 101, 110, 116, 45, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 45, 118, 49]
  | .intraOptionCreditRandom => [105, 115, 115, 117, 101, 45, 50, 50, 45, 114, 97, 110, 100, 111, 109, 45, 97, 114, 109, 45, 118, 49]
  | .intraOptionCreditBootstrap => [105, 115, 115, 117, 101, 45, 50, 50, 45, 98, 111, 111, 116, 115, 116, 114, 97, 112, 45, 118, 49]
  | .intraOptionCreditPopulation => [105, 115, 115, 117, 101, 45, 50, 50, 45, 104, 101, 108, 100, 45, 111, 117, 116, 45, 112, 111, 112, 117, 108, 97, 116, 105, 111, 110, 45, 118, 49]
  | .derivedExplorationRateInitialization => [105, 115, 115, 117, 101, 45, 50, 56, 45, 97, 103, 101, 110, 116, 45, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 45, 118, 49]
  | .derivedExplorationRateRandom => [105, 115, 115, 117, 101, 45, 50, 56, 45, 114, 97, 110, 100, 111, 109, 45, 97, 114, 109, 45, 118, 49]
  | .derivedExplorationRateBootstrap => [105, 115, 115, 117, 101, 45, 50, 56, 45, 98, 111, 111, 116, 115, 116, 114, 97, 112, 45, 118, 49]
  | .derivedExplorationRatePopulation => [105, 115, 115, 117, 101, 45, 50, 56, 45, 104, 101, 108, 100, 45, 111, 117, 116, 45, 112, 111, 112, 117, 108, 97, 116, 105, 111, 110, 45, 118, 49]
  | .stompPlanningInitialization => [105, 115, 115, 117, 101, 45, 51, 48, 45, 97, 103, 101, 110, 116, 45, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 45, 118, 49]
  | .stompPlanningRandom => [105, 115, 115, 117, 101, 45, 51, 48, 45, 114, 97, 110, 100, 111, 109, 45, 97, 114, 109, 45, 118, 49]
  | .stompPlanningBootstrap => [105, 115, 115, 117, 101, 45, 51, 48, 45, 98, 111, 111, 116, 115, 116, 114, 97, 112, 45, 118, 49]
  | .stompPlanningPopulation => [105, 115, 115, 117, 101, 45, 51, 48, 45, 104, 101, 108, 100, 45, 111, 117, 116, 45, 112, 111, 112, 117, 108, 97, 116, 105, 111, 110, 45, 118, 49]

/-- Numeric domain identities derived by the owning FNV implementation. -/
def Domain.value : Domain → UInt64
  | .actionFold => 0xbe84953016cbac84
  | .agentBaselineInitialization => 0xf00c0206916fd4fe
  | .agentBaselineRandom => 0x1a155a5c4c2c19ae
  | .agentBaselineBootstrap => 0xb86ea26d9f8eb1bd
  | .intraOptionCreditInitialization => 0xee9815e9c4de8d2c
  | .intraOptionCreditRandom => 0x8c9ed15182524dfc
  | .intraOptionCreditBootstrap => 0x37e7cdc9e018fcea
  | .intraOptionCreditPopulation => 0x9cb41aa166ce283a
  | .derivedExplorationRateInitialization => 0xfccbe3a1076b72be
  | .derivedExplorationRateRandom => 0x1ba534a8396cd06e
  | .derivedExplorationRateBootstrap => 0xd338fd3f6f20d2e4
  | .derivedExplorationRatePopulation => 0x839459356c4d2cb8
  | .stompPlanningInitialization => 0x20adb2b5a4cd00bf
  | .stompPlanningRandom => 0xda05fd260cfd99af
  | .stompPlanningBootstrap => 0xae181c2d31b67ecb
  | .stompPlanningPopulation => 0x151cb8f4abc92263

/-- Historical canonical output, retained byte-for-byte. -/
def intraOptionCreditNoValue : String := "collapse22: NO VALUE — an empty required stratum (registered hard failure)"

/-- Historical canonical output, retained byte-for-byte. -/
def derivedExplorationRateNoValue : String := "collapse28: NO VALUE — an empty required stratum (registered hard failure)"

/-- Historical canonical output, retained byte-for-byte. -/
def stompPlanningNoValue : String := "collapse30: NO VALUE — an empty required stratum (registered hard failure)"

end Compatibility
/-- Differential-control model population. -/
def averageRewardSeeds : List Nat := [17398715263585586064, 2039201990969981266, 8163707731031670308, 861121861259781844, 11725299783053946930, 232674698427835041, 5459730271191926315, 9152024572230751724]

/-- Differential-control study cycle count. -/
def averageRewardCycles : Nat := 3

/-- Differential-control study goal count. -/
def averageRewardGoals : Nat := 13

/-- Differential-control study attempts per goal. -/
def averageRewardAttempts : Nat := 2

/-- Differential-control study steps per attempt. -/
def averageRewardStepCap : Nat := 1000

/-- Differential-control study world side. -/
def averageRewardWorldSide : Nat := 1024

/-- Differential-control study shared agent initialization. -/
def averageRewardAgentSeed : Nat := 66

/-- Differential-control study wall budget, in seconds. -/
def averageRewardWallBudget : Nat := 7200

/-- Differential-control study sampled RSS budget, in bytes. -/
def averageRewardRssBudget : Nat := 2147483648

/-- Differential-control study raw output budget, in bytes. -/
def averageRewardRawBudget : Nat := 536870912

/-- Second differential-control model population. -/
def averageRewardRevisionSeeds : List Nat := [18233659390142340353, 12475207274233935420, 7310888561924176371, 239988586019406723, 6897438374650800621, 5229332303366468230, 114735174369132775, 106886276994699673, 17843530178709329386, 6604739643961507034, 48814801905999895, 14966468741004622142, 14011820953792392275, 18010148010172030318, 11427834556704071050, 2859612306292544068, 15668215832784454518, 4568955728924258961, 3195770332396127673, 1603147715334887284]

/-- Revised differential-control raw output budget, in bytes. -/
def averageRewardRevisionRawBudget : Nat := 805306368


end AcornSpec.Constants
