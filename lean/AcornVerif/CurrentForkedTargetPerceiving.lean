import AcornVerif.CurrentForkedTargetRung
import AcornVerif.Perceiving

namespace AcornVerif.CurrentForkedTargetPerceiving
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget
open AcornVerif.CurrentForkedTargetRung

theorem rung_fork_perceiving (mode : TaskFeatureMode) (bound limit : ℕ) {κ : Type}
    (key : (rungForks mode).Index → κ) :
    Kernel.PerceivingNeeded
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved))
      (Kernel.turnRuns (rungForks mode) 7)
      (Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 bound key limit) := by
  rintro agent ⟨shadow, blind, same⟩ masters
  exact forked_blind mode witnessLive duskLive 7 dusk_carried blind bound limit key
    (Kernel.MastersBy.of_states (fun index order time => same (index, order) time) masters)

theorem rung_fork_decides (mode : TaskFeatureMode) :
    Kernel.PerceivingDecides
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved))
      (Kernel.turnRuns (rungForks mode) 7)
      (Kernel.MastersBy (rungForks mode) (rungForkGoals mode) 7 (49 + 7 * 7)
        (firstTarget mode witnessLive duskLive 7) 6) :=
  ⟨rung_fork_perceiving mode (49 + 7 * 7) 6 _, forkWitness, witness_masters mode⟩

end AcornVerif.CurrentForkedTargetPerceiving
