/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentConcealedTargetFlag
import AcornVerif.StoredExperience

/-!
# The first rung's class fails `PerceptNeeded`

On the feasible concealed targets of the first rung's world, with visits of seven steps, at the
covering bound 98 and the visit limit 288 that mission 283 named:

* `rung_dominated`: every agent has a rival stepped by the achievement flag alone that solves on
  every visit every member the agent solves on it, and retains with no lapse.
* `rung_flag_unneeded`, `rung_reward_unneeded`: the class does not meet `PerceptNeeded`, for the
  achievement flag or for the reward word as the feedback.
-/

namespace AcornVerif.CurrentConcealedTargetPerceiving
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetTwin AcornVerif.CurrentConcealedTargetFlag
open AcornVerif.MissionVisits AcornVerif.Intent AcornVerif.CurrentConcealedTargetMission

/-- On the first rung's class every agent is dominated by a replayer that reads its percept through
the achievement flag alone. -/
theorem rung_dominated (mode : TaskFeatureMode) (agent : Kernel.Agent Grid.interface) :
    ∃ rival : Kernel.Agent Grid.interface, Kernel.Stepped achievedSignal rival ∧
      (∀ index visit, Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 agent visit index →
        Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 rival visit index) ∧
      Kernel.Retains (feasibleFind witnessConfig mode witnessLive 7)
        (fun _ => completion witnessConfig mode 7) 7 rival :=
  ⟨_, Kernel.replay_dominates (feasibleFind_conceals mode witnessLive 7 7) 7 achievedSignal
    (fun _ => achieved_decodes witnessConfig mode 7) agent⟩

/-- The first rung's class does not meet `PerceptNeeded` for the achievement flag, at the bound 98
and the limit 288: an agent stepped by that flag separates there. -/
theorem rung_flag_unneeded (mode : TaskFeatureMode) :
    ¬ Nonempty (Kernel.PerceptNeeded achievedSignal
      (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 98 288) := by
  rintro ⟨needed⟩
  obtain ⟨agent, counted, stepped, -, separates, -⟩ := flag_solver mode
  exact needed.need stepped.feedbackDriven counted separates

/-- Nor for the reward word: the flag solver's twin is stepped by the reward word and separates
exactly when the flag solver does. -/
theorem rung_reward_unneeded (mode : TaskFeatureMode) :
    ¬ Nonempty (Kernel.PerceptNeeded (fun percept : Percept Grid.interface => percept.reward)
      (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 98 288) := by
  rintro ⟨needed⟩
  obtain ⟨agent, counted, -, -, separates, -⟩ := flag_solver mode
  obtain ⟨twin, stepped, -, clauses⟩ := rung_twin mode agent
  exact needed.need stepped.feedbackDriven counted ((clauses 98 288 0 0 counted).1.mpr separates)

/-- **The first rung's class does not need perceiving**, by the meaning of the condition: for the
achievement flag and for the reward word, some agent driven by that feedback meets separation at
the bound 98 before visit 288. -/
theorem rung_not_perceivingNeeded (mode : TaskFeatureMode) :
    ∃ counted : List (feasibleFind witnessConfig mode witnessLive 7).Index,
      ¬ Kernel.PerceivingNeeded achievedSignal
        (Kernel.visitRuns (feasibleFind witnessConfig mode witnessLive 7) 7)
        (Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 98 counted 288) ∧
      ¬ Kernel.PerceivingNeeded (fun percept : Percept Grid.interface => percept.reward)
        (Kernel.visitRuns (feasibleFind witnessConfig mode witnessLive 7) 7)
        (Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
          (fun _ => completion witnessConfig mode 7) 7 98 counted 288) := by
  obtain ⟨agent, counted, stepped, -, separates, -⟩ := flag_solver mode
  obtain ⟨twin, steppedTwin, -, clauses⟩ := rung_twin mode agent
  exact ⟨counted, fun needed => needed agent (stepped.feedbackDriven.actsAsDriven _) separates,
    fun needed => needed twin (steppedTwin.feedbackDriven.actsAsDriven _)
      ((clauses 98 288 0 0 counted).1.mpr separates)⟩

/-- **The postcondition's record admits an agent that stores a rewarded visit's actions and
replays them.** On the first rung's class, with the horizon 864 and the 144 lapses mission 283
named, an agent stepped by the achievement flag alone meets the record of the postcondition. -/
theorem rung_replay_achieves (mode : TaskFeatureMode) :
    ∃ (agent : Kernel.Agent Grid.interface)
      (counted : List (feasibleFind witnessConfig mode witnessLive 7).Index),
      Kernel.Stepped achievedSignal agent ∧
        Postcondition.postcondition.Meets
          (visitsTrial (feasibleFind witnessConfig mode witnessLive 7) 7 864 144 reward
            (fun _ => goalMet) counted agent) := by
  obtain ⟨agent, counted, stepped, distinct, separates, retains⟩ := flag_solver mode
  exact ⟨agent, counted, stepped,
    visits_achieves _ _ 7 864 144 _ _ counted agent (find_pays mode witnessLive 7 rfl)
      (feasibleFind_conceals mode witnessLive 7 7)
      (feasibleFind_covered witnessConfig mode witnessLive 7) distinct separates (by decide)
      retains⟩

end AcornVerif.CurrentConcealedTargetPerceiving
