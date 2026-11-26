import AcornVerif.LeanIntentBridge

namespace AcornVerif.Intent

open LeanIntent

def reasons : String := "docs/spec-first-pilot.md, The decisions made on the owner's behalf"

def agentsAnswer : Answerer := .onBehalf (.of "agents") (.of "agents-below-intent") reasons

end AcornVerif.Intent
