namespace Acorn.FeatureConstants

def defaultWeightSpace : Nat := 16384
def defaultTilings : Nat := 8
def defaultImprintUnits : Nat := 512
def worldMinSide : Nat := 64
def worldMaxSide : Nat := 3000000000
def worldDayLength : Nat := 2048
def worldRegrow : Nat := 400
def worldFoodInterval : Nat := 48
def worldFoodCap : Nat := 600
def worldDeerArea : Nat := 512
def worldScaleDivisor : Nat := 16
def worldMinScale : Nat := 8
def energyMax : Nat := 2000
def energyLow : Nat := 300
def energyRestRecover : Nat := 20
def energyEatRestore : Nat := 400
def dayMultiplier : Nat := 1
def nightMultiplier : Nat := 2
def harvestCost : Nat := 2
def dayPhases : Nat := 8
def axeWood : Nat := 3
def axeStone : Nat := 2
def boatWood : Nat := 4
def boatStone : Nat := 0
def patchSide : Nat := 11
def taskContextWords : Nat := 10
def reachRadius : Nat := 3
def primitiveCount : Nat := 9
def skillCount : Nat := 3
def metaActionCount : Nat := 4
def demonCount : Nat := 11
def checkpointFormatVersion : Nat := 21
def checkpointHeaderBytes : Nat := 64
def historyBins : Nat := 64
def exactCycles : Nat := 8
def cycleBins : Nat := 16
def settleStride : Nat := 24
def maxSettlement : Nat := 600
def pendingSamples : Nat := 26
def predictionBuckets : Nat := 9
def optionMaxDuration : Nat := 128
def explorationMaxDuration : Nat := 128
def settleRemainingBits : UInt32 := 0x3c23d70a
def checkpointMagic : List UInt8 := [79, 65, 75, 67, 75, 80, 84, 1]

end Acorn.FeatureConstants
