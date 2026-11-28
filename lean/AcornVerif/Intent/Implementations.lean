import AcornVerif.Intent.Decisions
import AcornVerif.Intent.DayCycleWorld

namespace AcornVerif.Intent.Implementations

open LeanIntent AcornVerif.Intent.DayCycle AcornVerif.Intent.Decisions

def dayImplementation : Implementation dayDeliverable where
  subject := acornStandardDay
  meets := acornStandardDay_meets

end AcornVerif.Intent.Implementations
