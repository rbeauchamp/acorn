import AcornVerif.Targets.CurrentConcealedTargetRung

namespace AcornVerif.CurrentConcealedTargetRungLearns
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.Intent AcornVerif.Intent.MissionTheorem

theorem learns_frame (planning : PlanningSelection)
    (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
      witnessLive 7).Index)
    (distinct : counted.Nodup)
    (separates : Kernel.SeparatesBy
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      98 counted 288 (executedAgent (rungConstruction planning).initial.agent))
    (retains : Kernel.RetainsBut
      (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
      (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
      864 144 (executedAgent (rungConstruction planning).initial.agent)) :
    Targets.CurrentConcealedTargetRung.rung_learns := by
  unfold Targets.CurrentConcealedTargetRung.rung_learns
  exact ⟨rfl, rfl, by decide, by decide, rfl, planning, counted, rfl, rfl, rfl, rfl, rfl,
    distinct, separates, retains⟩

theorem learns_mission (learns : Targets.CurrentConcealedTargetRung.rung_learns) :
    ∃ (planning : PlanningSelection)
      (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index),
      ∀ {agent : Kernel.Agent Grid.interface},
        ActsAsExecuted (rungConstruction planning).initial.agent agent →
        ∀ {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
          {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
          {resume : agent.Memory → agent.Memory},
          MemoryBounded (findRung witnessConfig (rungConstruction planning).profile.taskMode
            witnessLive 7 864 144 counted agent updates work resume) →
          WorkBounded (findRung witnessConfig (rungConstruction planning).profile.taskMode
            witnessLive 7 864 144 counted agent updates work resume) →
          LearnsOnArrival (findRung witnessConfig (rungConstruction planning).profile.taskMode
            witnessLive 7 864 144 counted agent updates work resume) →
          KeepsDiscipline (findRung witnessConfig (rungConstruction planning).profile.taskMode
            witnessLive 7 864 144 counted agent updates work resume) →
          Mission (findRung witnessConfig (rungConstruction planning).profile.taskMode
            witnessLive 7 864 144 counted agent updates work resume) := by
  obtain ⟨-, -, -, -, -, planning, counted, -, -, -, -, -, distinct, separates, retains⟩ := learns
  refine ⟨planning, counted,
    @fun agent acts updates work resume memory bounded arrival discipline => ?_⟩
  refine find_mission witnessConfig _ witnessLive 7 864 144 288 rfl counted distinct ?_
    (by decide) ?_ (Rung.stream_met memory bounded arrival discipline)
  · obtain ⟨visit, solved, early, many, each⟩ := separates
    exact ⟨visit, solved, early, many, fun index member => ⟨(each index member).1,
      (Kernel.solvesOnVisit_of_actions acts visit index).mpr (each index member).2⟩⟩
  · intro index
    obtain ⟨lapsed, few, keeps⟩ := retains index
    exact ⟨lapsed, few, fun visit later after before solved out =>
      (Kernel.solvesOnVisit_of_actions acts later index).mpr
        (keeps visit later after before
          ((Kernel.solvesOnVisit_of_actions acts visit index).mp solved) out)⟩

theorem learns_again (learns : Targets.CurrentConcealedTargetRung.rung_learns) :
    ∃ planning : PlanningSelection,
      ∀ (index : (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
          witnessLive 7).Index) (visit since : ℕ), visit < since → since + 144 < 864 →
        Kernel.SolvesOnVisit
          (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
          (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
          (executedAgent (rungConstruction planning).initial.agent) visit index →
        ∃ later, since ≤ later ∧ later ≤ since + 144 ∧
          Kernel.SolvesOnVisit
            (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive
              7)
            (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
            (executedAgent (rungConstruction planning).initial.agent) later index := by
  obtain ⟨-, -, -, -, -, planning, -, -, -, -, -, -, -, -, retains⟩ := learns
  exact ⟨planning, fun index visit since earlier room solved =>
    retains.again index visit since (Nat.le_of_lt earlier) room solved⟩

theorem learns_needs (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent)
    (counted : List (feasibleFind witnessConfig mode witnessLive 7).Index) (limit : ℕ) :
    ¬ Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 98 counted limit agent := by
  rintro ⟨visit, solved, -, many, each⟩
  exact absurd (Kernel.visits_need (feasibleFind_conceals mode witnessLive 7 7)
    (feasibleFind_covered witnessConfig mode witnessLive 7) free visit solved
    (fun index member => (each index member).2)) (by omega)

theorem retainsBut_iff_on {interface : Interface} {family : Kernel.WorldClass interface}
    {goals : family.Goals} {length horizon lapses : ℕ} {agent : Kernel.Agent interface} :
    Kernel.RetainsBut family goals length horizon lapses agent ↔
      ∃ admits : family.Index → ℕ → Prop,
        Kernel.RetainsOn family goals length horizon admits agent ∧
          Kernel.AdmitsBut admits horizon lapses := by
  constructor
  · intro retains
    obtain ⟨lapsed, held⟩ := Classical.axiomOfChoice retains
    exact ⟨fun index later => later ∉ lapsed index,
      fun index visit later after before solved out =>
        (held index).2 visit later after before solved out,
      fun index => ⟨lapsed index, (held index).1, fun _ _ out => out⟩⟩
  · rintro ⟨admits, core, few⟩
    exact core.but few

end AcornVerif.CurrentConcealedTargetRungLearns
