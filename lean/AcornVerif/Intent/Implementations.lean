import AcornVerif.Intent.Decisions
import AcornVerif.Intent.DayCycleWorld

namespace AcornVerif.Intent.Implementations

open LeanIntent AcornVerif.Intent.DayCycle AcornVerif.Intent.Decisions

def dayImplementation : Implementation dayDeliverable where
  subject := acornStandardDay
  fulfils := acornStandardDay_fulfils

end AcornVerif.Intent.Implementations
