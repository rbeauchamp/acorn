namespace Acorn

inductive Departure where
  | featureChannels
  | spatialPotentials
  | explorationDuration
  | learnerParameters
  | cumulants
  | explorationRate
  | featureTester
  | achievementEvent
  deriving DecidableEq

class Provenance (α : Type) where
  origin : Option Departure

end Acorn
