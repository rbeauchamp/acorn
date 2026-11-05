/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.Decisions
import AcornVerif.Intent.DayCycleWorld

/-!
# The implementations of Acorn's deliverables

lean-intent's deliverable names no implementation, and every satisfiable record is fulfilled by
some model that no program runs. A `LeanIntent.Implementation` value names the constant that
implements a deliverable, as the record's subject, with the proof that it fulfils the record, and
Lean's kernel accepts the value only where that proof is of that very constant.
`LeanIntent.Implementation.Read.check`, which Acorn's merge gate runs, reads these values from the
build.

* **The day record** (`AcornVerif.Intent.Decisions.dayDeliverable`) is implemented by
  `AcornVerif.Intent.DayCycle.acornStandardDay`: Acorn's `World.dayPhase` and `Action.energyCost`,
  read through `acornDay` in the world of the standard configuration, which is the day of every
  standard configuration and every situation (`acornStandardDay_eq`).
* **The hash record** (`AcornVerif.Intent.Decisions.hashDeliverable`) has no implementation here:
  no theorem proves that `Acorn.Rng.hash2` and `Acorn.Rng.hash3` meet its second property
  (rbeauchamp/acorn#184), and a model built to meet it would not be Acorn's code. The gate lists it
  as awaiting an implementation (`AcornIntentCheck.awaiting`).
* **The interface record** (`AcornVerif.Intent.Decisions.worldInterfaceDeliverable`), contract 1 of
  Acorn's mission contract, has no implementation here: no theorem yet proves that Acorn's executing
  worlds, agent and host meet it, which is the fifth step of rbeauchamp/acorn#213. The gate lists it
  as awaiting an implementation.

That `acornStandardDay` is what Acorn's executable runs is not checked here: the value's proof
binds that constant, and that the world's entry point calls `World.dayPhase` and that its compiled
code computes its definition are trusted.
-/

namespace AcornVerif.Intent.Implementations

open LeanIntent AcornVerif.Intent.DayCycle AcornVerif.Intent.Decisions

/-- The day record's implementation: Acorn's standard day, and the proof that it fulfils the record
at the types of Acorn's world. -/
def dayImplementation : Implementation dayDeliverable where
  subject := acornStandardDay
  fulfils := acornStandardDay_fulfils

end AcornVerif.Intent.Implementations
