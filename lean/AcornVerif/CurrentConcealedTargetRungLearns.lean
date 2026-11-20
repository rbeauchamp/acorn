/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Targets.CurrentConcealedTargetRung

/-!
# What a proof of the first rung's learning target gives

`AcornVerif.Targets.CurrentConcealedTargetRung.rung_learns` is the statement of the first rung's
discovery mission: the rung's agent gets ahead of every agent that keeps nothing of its
experience, and solves again what it has solved. This module proves nothing toward its two
promises. It proves that they are all the target asks, and what follows from it, so that a reader
can check what the statement asks without reading it against every definition it names.

- `learns_frame`: the target follows from its two promises, for either planning selection and
  any list of distinct members. Its proof shows each value the target writes as a numeral or a
  structure literal to be the value of the definition the target asserts it of, so it fails if
  one differs. So the target is not false for a mistyped value, and what is left to prove is its
  two promises.
- `learns_mission`: from the target, the mission theorem's statement holds of the first rung at
  the horizon 864 and 144 lapses, for every agent that takes the rung's agent's actions and whose
  own memory and reports meet contract 3's four remaining premises. The premises of
  `AcornVerif.CurrentConcealedTargetRung.rung_mission` on finding, on calm visits and on their
  counts are not used, and the target does not prove them. The statement meant is the Lean one,
  `Mission`: it keeps the comparison of 2026-11-03, read before the horizon as decided on
  2026-11-17, and is not the postcondition as the owner confirmed it on 2026-11-20;
  `lean/AcornVerif/Intent/MissionTheorem.lean` sets out the difference under what the proposition
  does not say.
- `learns_again`: from the target, a member the agent has solved on a visit is solved on a later
  visit within every 145 consecutive visits that begin after that visit and end before visit 864.
- `learns_needs`: no agent that keeps nothing of its experience meets the target's first promise,
  at any list of members and any visit. So an agent that does nothing does not meet the target.
- `retainsBut_iff_on`: retention before a horizon but for a number of lapses holds exactly when
  some predicate on a member's visits has the two parts the owner's decision of 2026-11-17 on
  rbeauchamp/acorn#248 names: the agent solves again on the visits the predicate admits
  (`Kernel.RetainsOn`), and the predicate admits all but the lapses (`Kernel.AdmitsBut`). So a
  target stated over solving alone asks what the two parts give for some predicate, and no more:
  it reads no report of exploration, and a proof through calm visits
  (`AcornVerif.CurrentConcealedTargetMission.ExecutedCalm`) proves it.

What is not proved here: the target, for any agent.
-/

namespace AcornVerif.CurrentConcealedTargetRungLearns
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetMission AcornVerif.CurrentConcealedTargetRung
open AcornVerif.Intent AcornVerif.Intent.MissionTheorem

/-- **The target follows from its two promises.** For a planning selection and a list of distinct
members of the class, separation before visit 288 and retention before visit 864 but for 144
lapses, of the executed agent from the rung's construction's cold state, give the target. The
proof shows the configuration, the start and the construction that the target writes out as
numerals and structure literals to be those of `witnessConfig`, `witnessLive` and
`rungConstruction`. It proves neither promise. -/
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

/-- **From the target, the mission theorem's statement holds of the rung.** From the target, for
the planning selection and the list of members it gives, every agent that takes the rung's agent's
actions, and whose own memory and reports meet the four remaining premises of contract 3, achieves
goals over the first rung's class with the horizon 864 and 144 lapses. The target stands where
`AcornVerif.CurrentConcealedTargetRung.rung_mission` has its premises on finding, on calm visits
and on their counts, and does not prove them. The statement meant is the Lean one, `Mission`: it
keeps the comparison of 2026-11-03, read before the horizon as decided on 2026-11-17, and is not the
postcondition as the owner confirmed it on 2026-11-20; `lean/AcornVerif/Intent/MissionTheorem.lean`
sets out the difference under what the proposition does not say. -/
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

/-- **What the target asks of retention, member by member.** From the target, for the planning
selection it gives: a member that the rung's agent has solved on a visit is solved on one of the
145 visits from any visit `since` after it, where all of them come before visit 864. That visit
is later than the one on which the member was solved. -/
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

/-- **No agent that keeps nothing of its experience meets the target's first promise.** In the
rung's world with visits of seven steps, an agent whose memory advances without reading its
percepts solves more than 98 listed members on no visit, whatever the list and the visit before
which it is asked. -/
theorem learns_needs (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent)
    (counted : List (feasibleFind witnessConfig mode witnessLive 7).Index) (limit : ℕ) :
    ¬ Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
      (fun _ => completion witnessConfig mode 7) 7 98 counted limit agent := by
  rintro ⟨visit, solved, -, many, each⟩
  exact absurd (Kernel.visits_need (feasibleFind_conceals mode witnessLive 7 7)
    (feasibleFind_covered witnessConfig mode witnessLive 7) free visit solved
    (fun index member => (each index member).2)) (by omega)

/-- **Retention but for lapses is the two parts, for some predicate.** An agent retains before a
horizon but for a number of lapses exactly when some predicate on a member's visits is such that
the agent retains on the visits it admits and it admits every visit before the horizon but for
at most that many of each member's. -/
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
