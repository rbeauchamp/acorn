/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LeanIntentBridge

/-!
# Who settles the records' consequences

The owner's decision of 2026-10-29 leaves every detail below their intent to the agents, under the
delegation `agents-below-intent` of the owners' log (`AcornVerif.Intent.Decisions.ownersLog`). The
explanations of the day and hash records record each consequence they show as settled by that
delegation, and lean-intent's confirmation check compares each such status with the answer of the
log that settles it: the same principal, the same delegation and, as the reason, the same text as
the answer's source. This module holds that answerer once, so that the explanations and the log's
answers name one reason.
-/

namespace AcornVerif.Intent

open LeanIntent

/-- Where the reason for each decision made on the owner's behalf is kept: the source every answer
of the agents under `agents-below-intent` records. -/
def reasons : String := "docs/spec-first-pilot.md, The decisions made on the owner's behalf"

/-- The agents, answering under the owner's delegation `agents-below-intent`, for the reasons kept
where `reasons` says: never the owner. -/
def agentsAnswer : Answerer := .onBehalf (.of "agents") (.of "agents-below-intent") reasons

end AcornVerif.Intent
