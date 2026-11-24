import AcornVerif.Perceiving
import AcornVerif.CurrentConcealedTargetTwin

namespace AcornVerif.CurrentConcealedTargetFlag
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetTwin

theorem replay_solver (mode : TaskFeatureMode) :
    ∃ counted : List (feasibleFind witnessConfig mode witnessLive 7).Index, counted.Nodup ∧
      Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 98 counted 288
        (Kernel.replay Grid.interface 7 achievedSignal witnessExplore) ∧
      Kernel.RetainsBut (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 864 144
        (Kernel.replay Grid.interface 7 achievedSignal witnessExplore) := by
  classical
  obtain ⟨members, count, explored⟩ := witness_explored mode
  have feasible : ∀ target ∈ members,
      Kernel.Feasible (completion witnessConfig mode 7) (member witnessLive target.1) := by
    intro target chosen
    obtain ⟨visit, -, step, low, high, met⟩ := explored target chosen
    exact ⟨witnessExplore visit, step, low, high, met⟩
  let admitted : { target // target ∈ members } →
      (feasibleFind witnessConfig mode witnessLive 7).Index :=
    fun target => ⟨target.1, feasible target.1 target.2⟩
  have injective : Function.Injective admitted := by
    intro first second same
    exact Subtype.ext (congrArg
      (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => target.1) same)
  refine ⟨(members.attach.map ⟨admitted, injective⟩).toList, Finset.nodup_toList _, ?_, ?_⟩
  · refine ⟨2, members.attach.map ⟨admitted, injective⟩, by decide, ?_, fun index listed => ?_⟩
    · rw [Finset.card_map, Finset.card_attach, count]
      decide
    · refine ⟨Finset.mem_toList.mpr listed, ?_⟩
      obtain ⟨target, -, rfl⟩ := Finset.mem_map.mp listed
      obtain ⟨visit, before, meets⟩ := explored target.1 target.2
      exact Kernel.replay_solves_explored (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 achievedSignal witnessExplore
        (admitted target) (achieved_decodes witnessConfig mode 7) visit 2 before meets
  · intro index
    refine ⟨∅, by simp only [Finset.card_empty]; exact Nat.zero_le _, ?_⟩
    intro visit later after _ solved _
    exact Kernel.replay_solves (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 achievedSignal witnessExplore index
      (achieved_decodes witnessConfig mode 7) visit later after solved

theorem flag_solver (mode : TaskFeatureMode) :
    ∃ (agent : Kernel.Agent Grid.interface)
      (counted : List (feasibleFind witnessConfig mode witnessLive 7).Index),
      Kernel.Stepped achievedSignal agent ∧ counted.Nodup ∧
        Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 98 counted 288 agent ∧
        Kernel.RetainsBut (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 864 144 agent := by
  obtain ⟨counted, distinct, separates, retains⟩ := replay_solver mode
  exact ⟨Kernel.replay Grid.interface 7 achievedSignal witnessExplore, counted,
    Kernel.replay_steppedBy 7 achievedSignal witnessExplore, distinct, separates, retains⟩

end AcornVerif.CurrentConcealedTargetFlag
