/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Targets.Registry

/-! # The record of proved targets

A *target* is a statement that a mission is to prove, held as a definition of type `Prop` under
`lean/AcornVerif/Targets/` and listed in `AcornVerif.Targets.registry`. It is open until
`landings` below holds an entry for it.

A mission's pull request proves each of its targets as a theorem in the modules its contract
names, imports those modules here, and adds one entry for each target to the list, such as

    ⟨``Targets.StateEntry.arm_letter, ``StateEntry.arm_letter, @StateEntry.arm_letter⟩

The fields are the target's name, the theorem's name and the theorem itself, written with `@` so
that Lean takes it whole. The entry has type `Targets.Landing`, so Lean's kernel accepts it only
when the theorem proves the statement the registry holds under the target's name
(`Targets.Landing.proves`): an entry for a name that is not registered, or with a proof of another
statement, does not compile.

This module is outside `lean/AcornVerif/Targets/`, the directory `.github/CODEOWNERS` names for
the owner's review. What an entry must hold is fixed there, by `Targets.Landing`. The merge
gate's frame check reads this list from the build and fails unless `Landed.registered` in that
directory registers exactly its entries, with the statement of each theorem an entry names and
the project's declarations that statement reads (`lean/AcornTools/Frame.lean`). So adding an
entry needs a change to that file, which is the owner's to admit, and removing one does too.
Lean does not check that the theorem an entry names is the proof it holds. The frame check
does: it refuses an entry whose proof is any term but the theorem the entry names.

The entries of missions #195, #196, #197 and #199 record theorems that landed before their
statements were targets; each of those targets takes its statement from its theorem.
-/

namespace AcornVerif

/-- The targets on record as proved, each with the theorem that proves it. -/
def landings : List Targets.Landing := [
  ⟨``Targets.CurrentRunningMemory.running_naturals_allowed,
    ``CurrentRunningMemory.running_naturals_allowed,
    @CurrentRunningMemory.running_naturals_allowed⟩,
  ⟨``Targets.CurrentRunningMemory.running_snapshot_size,
    ``CurrentRunningMemory.running_snapshot_size,
    @CurrentRunningMemory.running_snapshot_size⟩,
  ⟨``Targets.CurrentRunningMemory.running_memory_bits,
    ``CurrentRunningMemory.running_memory_bits,
    @CurrentRunningMemory.running_memory_bits⟩,
  ⟨``Targets.CurrentPreReward.pre_reward_weights_zero,
    ``CurrentPreReward.pre_reward_weights_zero,
    @CurrentPreReward.pre_reward_weights_zero⟩,
  ⟨``Targets.CurrentControl.candidates_of_gap,
    ``CurrentControl.candidates_of_gap,
    @CurrentControl.candidates_of_gap⟩,
  ⟨``Targets.CurrentControl.candidates_of_resting,
    ``CurrentControl.candidates_of_resting,
    @CurrentControl.candidates_of_resting⟩,
  ⟨``Targets.CurrentCreditHorizon.dormant_weight_rests,
    ``CurrentCreditHorizon.dormant_weight_rests,
    @CurrentCreditHorizon.dormant_weight_rests⟩,
  ⟨``Targets.CurrentCreditHorizon.candidates_read_window,
    ``CurrentCreditHorizon.candidates_read_window,
    @CurrentCreditHorizon.candidates_read_window⟩,
  ⟨``Targets.CurrentCreditHorizon.recent_weight_moves,
    ``CurrentCreditHorizon.recent_weight_moves,
    @CurrentCreditHorizon.recent_weight_moves⟩]

end AcornVerif
