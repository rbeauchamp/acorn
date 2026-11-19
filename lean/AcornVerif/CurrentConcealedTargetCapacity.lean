/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Capacity
import AcornVerif.CurrentConcealedTargetMission

/-!
# The first rung's class is beyond one bit of memory at two slots

`rung_beyond`: the feasible concealed targets of the first rung's world, with visits of seven
steps, meet `BeyondCapacity` for a memory of one bit and campaigns of two slots: 147 members
against the covering bound 98 give more assignments of members to two slots than one bit can
solve wholly. It is the witness of that definition. `rung_one_bit` is what follows: every agent of
one bit of memory leaves some slot of some two-slot assignment unsolved on every cycle.

This says nothing of Acorn's executed agent, whose memory is far wider; at its width the count
needs millions of slots, as contract 2 of `docs/mission-contract.md` says.
-/

namespace AcornVerif.CurrentConcealedTargetCapacity
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission

/-- **A witness of `BeyondCapacity`.** The first rung's class is beyond one bit of memory, with no
margin, in campaigns of two slots. -/
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

/-- Every agent whose memory fits one bit leaves, on every cycle, some slot of some assignment of
the first rung's members to two slots unsolved. -/
theorem rung_one_bit (mode : TaskFeatureMode) (agent : Kernel.Agent Grid.interface)
    (fits : Kernel.MemoryWithin agent 1) (cycle : ℕ) :
    ∃ assignment : Fin (1 + 1) → (feasibleFind witnessConfig mode witnessLive 7).Index,
      ¬ ∀ slot, Kernel.SolvesSlot (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 1 assignment agent cycle slot := by
  obtain ⟨beyond⟩ := rung_beyond mode
  obtain ⟨assignment, -, unsolved⟩ := beyond.unsolved agent fits cycle
  exact ⟨assignment, unsolved⟩

end AcornVerif.CurrentConcealedTargetCapacity
