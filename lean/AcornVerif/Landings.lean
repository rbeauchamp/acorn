/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Targets.Registry

/-! # The record of landed targets

A *target* is an open statement held as a definition of type `Prop` under
`lean/AcornVerif/Targets/`, and `AcornVerif.Targets.registry` lists every one. A target has
*landed* when `landings` below holds an entry for it.

A mission's pull request proves each of its targets as a theorem in the modules its contract
names, imports those modules here, and adds one entry for each target, such as

    ⟨``Targets.StateEntry.arm_letter, ``StateEntry.arm_letter, @StateEntry.arm_letter⟩

The fields are the target's name, the theorem's name and the theorem itself, written with `@` so
that Lean takes it whole. The entry has type `Targets.Landing`, so Lean's kernel accepts it only
when the theorem proves the statement the registry holds under the target's name
(`Targets.Landing.proves`): an entry for a name that is not registered, or with a proof of another
statement, does not compile.

This module is outside `lean/AcornVerif/Targets/`, so recording a landing changes no file that
`.github/CODEOWNERS` gives to the owner. What an entry must hold is fixed there, by
`Targets.Landing`. Nothing checks that the theorem an entry names is the proof it holds; the name
is for readers.
-/

namespace AcornVerif

/-- The targets on record as proved, each with the theorem that proves it. -/
def landings : List Targets.Landing := []

end AcornVerif
