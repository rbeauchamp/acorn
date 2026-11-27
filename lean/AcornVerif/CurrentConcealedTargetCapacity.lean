import AcornVerif.Capacity
import AcornVerif.CurrentConcealedTargetMission

namespace AcornVerif.CurrentConcealedTargetCapacity
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission

theorem rung_beyond (mode : TaskFeatureMode) :
    Nonempty (Kernel.BeyondCapacity (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 1 1 0) := by
  classical
  obtain ⟨counted, distinct, size, -⟩ := witness_mission mode
  refine ⟨{
    reference := gridWorld witnessConfig mode
    origin := member witnessLive nowhere
    conceals := feasibleFind_conceals mode witnessLive 7 7
    cover := 49 + 7 * 7
    covered := feasibleFind_covered witnessConfig mode witnessLive 7
    members := counted.toFinset
    beyond := ?_ }⟩
  rw [List.toFinset_card_of_nodup distinct, size]
  decide

theorem rung_one_bit (mode : TaskFeatureMode) (agent : Kernel.Agent Grid.interface)
    (fits : Kernel.MemoryWithin agent 1) (cycle : ℕ) :
    ∃ assignment : Fin (1 + 1) → (feasibleFind witnessConfig mode witnessLive 7).Index,
      ¬ ∀ slot, Kernel.SolvesSlot (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 1 assignment agent cycle slot := by
  obtain ⟨beyond⟩ := rung_beyond mode
  obtain ⟨assignment, -, unsolved⟩ := beyond.unsolved agent fits cycle
  exact ⟨assignment, unsolved⟩

end AcornVerif.CurrentConcealedTargetCapacity
