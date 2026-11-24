import AcornVerif.CurrentConcealedTargetFlag
import AcornVerif.StoredExperience

namespace AcornVerif.CurrentConcealedTargetPerceiving
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetTwin AcornVerif.CurrentConcealedTargetFlag
open AcornVerif.MissionVisits AcornVerif.Intent AcornVerif.CurrentConcealedTargetMission

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

theorem rung_flag_unneeded (mode : TaskFeatureMode) :
    ¬ Nonempty (Kernel.PerceptNeeded achievedSignal
      (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 98 288) := by
  rintro ⟨needed⟩
  obtain ⟨agent, counted, stepped, -, separates, -⟩ := flag_solver mode
  exact needed.need stepped.feedbackDriven counted separates

theorem rung_reward_unneeded (mode : TaskFeatureMode) :
    ¬ Nonempty (Kernel.PerceptNeeded (fun percept : Percept Grid.interface => percept.reward)
      (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 98 288) := by
  rintro ⟨needed⟩
  obtain ⟨agent, counted, -, -, separates, -⟩ := flag_solver mode
  obtain ⟨twin, stepped, -, clauses⟩ := rung_twin mode agent
  exact needed.need stepped.feedbackDriven counted ((clauses 98 288 0 0 counted).1.mpr separates)

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
  exact ⟨counted, fun needed => needed agent (stepped.feedbackDriven.runsAsDriven _) separates,
    fun needed => needed twin (steppedTwin.feedbackDriven.runsAsDriven _)
      ((clauses 98 288 0 0 counted).1.mpr separates)⟩

theorem rung_replay_achieves (mode : TaskFeatureMode) :
    Kernel.Stepped achievedSignal (Kernel.replay Grid.interface 7 achievedSignal witnessExplore) ∧
      ∃ counted : List (feasibleFind witnessConfig mode witnessLive 7).Index,
        Postcondition.postcondition.Meets
          (visitsTrial (feasibleFind witnessConfig mode witnessLive 7) 7 864 144 reward
            (fun _ => goalMet) counted
            (Kernel.replay Grid.interface 7 achievedSignal witnessExplore)) := by
  obtain ⟨counted, distinct, separates, retains⟩ := replay_solver mode
  exact ⟨Kernel.replay_steppedBy 7 achievedSignal witnessExplore, counted,
    visits_achieves _ _ 7 864 144 _ _ counted _ (find_pays mode witnessLive 7 rfl)
      (feasibleFind_conceals mode witnessLive 7 7)
      (feasibleFind_covered witnessConfig mode witnessLive 7) distinct separates (by decide)
      retains⟩

end AcornVerif.CurrentConcealedTargetPerceiving
