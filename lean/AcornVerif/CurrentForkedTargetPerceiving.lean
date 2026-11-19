/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetRung
import AcornVerif.Perceiving

/-!
# The day-and-night class needs perceiving

`rung_fork_perceiving`: with the reward word and the achievement flag as the feedback, no agent
that acts as a clock-and-feedback agent on everything the day-and-night class shows it masters,
at any bound, key and limit. The class is a witness of condition (e) of contract 2 of
`docs/mission-contract.md` through forks in time: `witness_masters` and `witness_keeps` of
`AcornVerif.CurrentForkedTargetRung` show an agent that meets both of the class's promises.

This module states no mission. A statement of a mission on this class is under revision and is
no target.
-/

namespace AcornVerif.CurrentForkedTargetPerceiving
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget
open AcornVerif.CurrentForkedTargetRung

/-- **The day-and-night class needs perceiving**, with the reward word and the achievement flag as
the feedback, for mastery at every bound, key and limit. -/
theorem rung_fork_perceiving (mode : TaskFeatureMode) (bound limit : ℕ) {κ : Type}
    (key : (rungForks mode).Index → κ) :
    Kernel.PerceivingNeeded
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved))
      (Kernel.turnRuns (rungForks mode) 7)
      (Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 bound key limit) := by
  rintro agent ⟨shadow, blind, same⟩ masters
  exact forked_blind mode witnessLive duskLive 7 dusk_carried blind bound limit key
    (Kernel.MastersBy.of_states (fun index order time => same (index, order) time) masters)

end AcornVerif.CurrentForkedTargetPerceiving
