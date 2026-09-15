/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! Current feature, world and lifecycle interface constants. All current consumers
import these declarations directly; there is no cross-language copy. -/
namespace Acorn.FeatureConstants

/-- Current feature/lifecycle interface constant. -/
def defaultWeightSpace : Nat := 16384
/-- Current feature/lifecycle interface constant. -/
def defaultTilings : Nat := 8
/-- Current feature/lifecycle interface constant. -/
def defaultImprintUnits : Nat := 512
/-- Current feature/lifecycle interface constant. -/
def worldMinSide : Nat := 64
/-- Current feature/lifecycle interface constant. -/
def worldMaxSide : Nat := 3000000000
/-- Current feature/lifecycle interface constant. -/
def worldDayLength : Nat := 2048
/-- Current feature/lifecycle interface constant. -/
def worldRegrow : Nat := 400
/-- Current feature/lifecycle interface constant. -/
def worldFoodInterval : Nat := 48
/-- Current feature/lifecycle interface constant. -/
def worldFoodCap : Nat := 600
/-- Current feature/lifecycle interface constant. -/
def worldDeerArea : Nat := 512
/-- Current feature/lifecycle interface constant. -/
def worldScaleDivisor : Nat := 16
/-- Current feature/lifecycle interface constant. -/
def worldMinScale : Nat := 8
/-- Current feature/lifecycle interface constant. -/
def energyMax : Nat := 2000
/-- Current feature/lifecycle interface constant. -/
def energyLow : Nat := 300
/-- Current feature/lifecycle interface constant. -/
def energyRestRecover : Nat := 20
/-- Current feature/lifecycle interface constant. -/
def energyEatRestore : Nat := 400
/-- Current feature/lifecycle interface constant. -/
def dayMultiplier : Nat := 1
/-- Current feature/lifecycle interface constant. -/
def nightMultiplier : Nat := 2
/-- Current feature/lifecycle interface constant. -/
def harvestCost : Nat := 2
/-- Current feature/lifecycle interface constant. -/
def dayPhases : Nat := 8
/-- Current feature/lifecycle interface constant. -/
def axeWood : Nat := 3
/-- Current feature/lifecycle interface constant. -/
def axeStone : Nat := 2
/-- Current feature/lifecycle interface constant. -/
def boatWood : Nat := 4
/-- Current feature/lifecycle interface constant. -/
def boatStone : Nat := 0
/-- Current feature/lifecycle interface constant. -/
def patchSide : Nat := 11
/-- Current feature/lifecycle interface constant. -/
def reachRadius : Nat := 3
/-- Current feature/lifecycle interface constant. -/
def primitiveCount : Nat := 9
/-- Current feature/lifecycle interface constant. -/
def skillCount : Nat := 3
/-- Current feature/lifecycle interface constant. -/
def metaActionCount : Nat := 4
/-- Current feature/lifecycle interface constant. -/
def demonCount : Nat := 11
/-- Current feature/lifecycle interface constant. -/
def checkpointFormatVersion : Nat := 14
/-- Current feature/lifecycle interface constant. -/
def checkpointHeaderBytes : Nat := 64
/-- Current feature/lifecycle interface constant. -/
def checkpointLifetimeBytes : Nat := 4144
/-- Current feature/lifecycle interface constant. -/
def historyBins : Nat := 64
/-- Current feature/lifecycle interface constant. -/
def exactCycles : Nat := 8
/-- Current feature/lifecycle interface constant. -/
def cycleBins : Nat := 16
/-- Current feature/lifecycle interface constant. -/
def settleStride : Nat := 24
/-- Current feature/lifecycle interface constant. -/
def maxSettlement : Nat := 600
/-- Current feature/lifecycle interface constant. -/
def pendingSamples : Nat := 26
/-- Current feature/lifecycle interface constant. -/
def predictionBuckets : Nat := 9
/-- Current feature/lifecycle interface constant. -/
def optionMaxDuration : Nat := 128
/-- Current feature/lifecycle interface constant. -/
def explorationMaxDuration : Nat := 128
/-- Exact f32 bits of the current lifetime settlement threshold. -/
def settleRemainingBits : UInt32 := 0x3c23d70a
/-- Exact checkpoint magic bytes, generated from the format owner. -/
def checkpointMagic : List UInt8 := [79, 65, 75, 67, 75, 80, 84, 1]

end Acorn.FeatureConstants
