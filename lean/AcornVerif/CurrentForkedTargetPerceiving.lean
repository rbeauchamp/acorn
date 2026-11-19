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
whose effect on every run of the day-and-night class is that of a clock-and-feedback agent
masters, at any bound, key and limit. That is the negative half of condition (e) of contract 2 of
`docs/mission-contract.md`, and it holds with nothing to exclude where no agent masters, as before
visit 0 (`Kernel.not_decides_before_zero`). `rung_fork_decides`: the class is a witness of the
condition, through forks in time, at the covering bound 98 before visit 6, where `witness_masters`
of `AcornVerif.CurrentForkedTargetRung` shows an agent that masters.

This module states no mission. A statement of a mission on this class is under revision and is
no target.
-/

namespace AcornVerif.CurrentForkedTargetPerceiving
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget
open AcornVerif.CurrentForkedTargetRung

/-- **In the day-and-night class perceiving is needed**, with the reward word and the achievement
flag as the feedback, for mastery at every bound, key and limit. This is the negative half of
condition (e); the condition holds where an agent also masters (`rung_fork_decides`). -/
theorem rung_fork_perceiving (mode : TaskFeatureMode) (bound limit : ℕ) {κ : Type}
    (key : (rungForks mode).Index → κ) :
    Kernel.PerceivingNeeded
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved))
      (Kernel.turnRuns (rungForks mode) 7)
      (Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 bound key limit) := by
  rintro agent ⟨shadow, blind, same⟩ masters
  exact forked_blind mode witnessLive duskLive 7 dusk_carried blind bound limit key
    (Kernel.MastersBy.of_states (fun index order time => same (index, order) time) masters)

/-- **The day-and-night class meets condition (e)**, for mastery at the covering bound 98 before
visit 6, the bound and the limit its witness is proved for: no agent whose effect on every run of
the class is that of a clock-and-feedback agent masters there, and `forkWitness` does. -/
theorem rung_fork_decides (mode : TaskFeatureMode) :
    Kernel.PerceivingDecides
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved))
      (Kernel.turnRuns (rungForks mode) 7)
      (Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 (49 + 7 * 7)
        (firstTarget mode witnessLive duskLive 7) 6) :=
  ⟨rung_fork_perceiving mode (49 + 7 * 7) 6 _, forkWitness, witness_masters mode⟩

end AcornVerif.CurrentForkedTargetPerceiving
