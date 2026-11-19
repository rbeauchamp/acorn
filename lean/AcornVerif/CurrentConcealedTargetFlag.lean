/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Replay
import AcornVerif.CurrentConcealedTargetTwin

/-!
# An agent that reads only the achievement flag meets both promises of the frozen target

The replaying agent of `AcornVerif.Replay`, with the percept's achievement flag as its signal and
the witness's three walks as its exploration, is stepped by that flag: its step reads nothing else
of its percept. It meets both promises of the frozen target of mission #283 at the target's own
numbers, on the rung's class under every task mode. So the promises about solving, by themselves,
are met without reading the observation.
-/

namespace AcornVerif.CurrentConcealedTargetFlag
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetTwin

/-- The replaying agent is stepped by its signal. -/
theorem replay_stepped {interface : Interface} (length : ℕ) (signal : Percept interface → Bool)
    (explore : ℕ → ℕ → Kernel.Act interface) :
    Kernel.Stepped signal (Kernel.replay interface length signal explore) :=
  ⟨fun memory shown =>
    (memory.choose (memory.record shown) explore,
      if memory.step < length then
        ⟨memory.step + 1, memory.choose (memory.record shown) explore :: memory.taken,
          memory.count, memory.record shown⟩
      else ⟨0, [], memory.count + 1, memory.record shown⟩),
    fun _ _ => rfl⟩

/-- **Both promises of the frozen target are met by an agent that reads only the achievement
flag.** On the rung's class, under every task mode, there are an agent stepped by the percept's
achievement flag and a list of distinct members such that the agent solves more than 98 listed
members on one visit before visit 288, and solves again every member it has solved on every later
visit before visit 864, with no lapse. -/
theorem flag_solver (mode : TaskFeatureMode) :
    ∃ (agent : Kernel.Agent Grid.interface)
      (counted : List (feasibleFind witnessConfig mode witnessLive 7).Index),
      Kernel.Stepped achievedSignal agent ∧ counted.Nodup ∧
        Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 98 counted 288 agent ∧
        Kernel.RetainsBut (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 864 144 agent := by
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
  refine ⟨Kernel.replay Grid.interface 7 achievedSignal witnessExplore,
    (members.attach.map ⟨admitted, injective⟩).toList,
    replay_stepped 7 achievedSignal witnessExplore, Finset.nodup_toList _, ?_, ?_⟩
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

end AcornVerif.CurrentConcealedTargetFlag
