import Acorn.Host.AgentAdmission
import AcornVerif.CurrentConcealedTargetFinding
import AcornVerif.CurrentFrameSlots
import AcornVerif.CurrentKernelMemory

namespace AcornVerif.CurrentConcealedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetFinding AcornVerif.CurrentConcealedTargetMission
open AcornVerif.CurrentCreditHorizon AcornVerif.CurrentExplorer
open AcornVerif.CurrentFrameSize AcornVerif.CurrentFrameSlots AcornVerif.CurrentKernelMemory
open AcornVerif.CurrentRunningMemory
open AcornVerif.Intent AcornVerif.Intent.MissionTheorem

theorem witness_unpopulated : Unpopulated witnessConfig := ⟨rfl, rfl⟩

def rungConstruction (planning : PlanningSelection) : AgentConstruction :=
  AgentConstruction.standard witnessConfig.raw.seed ⟨.primitive, .discounted⟩ planning
    .learnThenAct

theorem rung_frame (planning : PlanningSelection) (mode : TaskFeatureMode) (order : StepOrder)
    (state : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (inner : Option (Live witnessConfig)) :
    (state.choose order ((gridWorld witnessConfig mode).percept inner)).features.indices.length ≤
      1712 :=
  Nat.le_trans (unpopulated_frame witness_unpopulated mode order state inner)
    (Nat.le_of_eq (standard_slots _ _ _ _))

theorem rung_frame_slot (planning : PlanningSelection) (mode : TaskFeatureMode)
    (order : StepOrder)
    (state : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (inner : Option (Live witnessConfig)) :
    ∃ slot, slot ∈
      (state.choose order ((gridWorld witnessConfig mode).percept inner)).features.indices :=
  grid_frame_slot mode order state inner (by
    change 0 < Acorn.FeatureConstants.defaultTilings.toUInt64.toNat
    decide)

theorem rung_weight_rests (planning : PlanningSelection) (mode : TaskFeatureMode)
    (order : StepOrder) (quiet post : List (Percept Grid.interface))
    (delivered : Delivered witnessConfig mode quiet)
    (silent : ∀ percept ∈ quiet, percept.reward.isZero = true) :
    let start := (rungConstruction planning).initial.agent
    let first := traced order start quiet
    let second := traced order first.1 post
    ∀ (row : Action Grid.interface.actions.word.toNat)
      (slot : FeatIdx (rungConstruction planning).dimension),
      (∀ step ∈ window (rungConstruction planning).criterion first.2 second.2,
        ¬step.Lays row slot) →
      (((controlOf second.1).learners.get row).state.weights.get slot).value.isZero = true :=
  unpopulated_weight_rests witness_unpopulated mode _ _ _ _ _ order rfl
    (Nat.le_trans (Nat.le_of_eq (standard_slots _ _ _ _)) (by decide)) quiet post delivered silent

theorem rung_reach (criterion : Criterion) (dimension : Dimension) {actions : Nat}
    (before after : List (Laid dimension actions)) (laid : Laid dimension actions)
    (slot : FeatIdx dimension) (held : slot ∈ laid.features.indices)
    (within : after.length + 1 ≤ 7)
    (fits : ∀ step ∈ before ++ laid :: after, step.features.indices.length ≤ 1712)
    (next : Laid dimension actions) :
    let quiet : Controller (criterion.config .control) dimension actions :=
      quietRun (before ++ laid :: after)
    (((quiet.step next.features next.row .one).1.learners.get laid.row).state.weights.get
      slot).value.isZero = false :=
  recent_weight_moves criterion dimension before after laid slot held (by omega)
    (fun step member => Nat.le_trans (fits step member) (by decide)) next

theorem rung_members (mode : TaskFeatureMode)
    (members : Finset (feasibleFind witnessConfig mode witnessLive 7).Index) :
    members.card ≤ 392 :=
  feasible_count mode witnessLive 7 members

theorem rung_mission (planning : PlanningSelection) (horizon lapses last limit spare : ℕ)
    (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
      witnessLive 7).Index)
    (distinct : counted.Nodup) {agent : Kernel.Agent Grid.interface}
    (acts : ActsAsExecuted (rungConstruction planning).initial.agent agent)
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    (finds : ExecutedFindsBy (rungConstruction planning).initial.agent witnessConfig witnessLive
      7 counted last spare)
    (retains : ExecutedRetainsOn (rungConstruction planning).initial.agent witnessConfig
      witnessLive 7 horizon
      (ExecutedCalm (rungConstruction planning).initial.agent witnessConfig witnessLive 7))
    (few : Kernel.AdmitsBut
      (ExecutedCalm (rungConstruction planning).initial.agent witnessConfig witnessLive 7)
      horizon lapses)
    (once : Kernel.AdmitsOnce
      (ExecutedCalm (rungConstruction planning).initial.agent witnessConfig witnessLive 7)
      counted last limit spare)
    (room : limit + lapses < horizon)
    (memory : MemoryBounded (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 horizon lapses counted agent
      updates work resume))
    (bounded : WorkBounded (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 horizon lapses counted agent
      updates work resume))
    (arrival : LearnsOnArrival (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 horizon lapses counted agent
      updates work resume))
    (discipline : KeepsDiscipline (findRung witnessConfig
      (rungConstruction planning).profile.taskMode witnessLive 7 horizon lapses counted agent
      updates work resume)) :
    Mission (findRung witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7
      horizon lapses counted agent updates work resume) :=
  executed_mission (rungConstruction planning).initial.agent witnessConfig witnessLive 7 horizon
    lapses last limit spare rfl counted distinct acts finds retains few once room memory bounded
    arrival discipline

def rungExplorer : Explorer Grid.interface.actions :=
  Explorer.cold Grid.interface.actions witnessConfig.raw.seed

theorem rung_explorer (planning : PlanningSelection) :
    Explorer.cold Grid.interface.actions (rungConstruction planning).config.seed =
      rungExplorer := rfl

abbrev rungAgent (planning : PlanningSelection) : Kernel.Agent Grid.interface :=
  executedAgent (rungConstruction planning).initial.agent

theorem rung_finds_iff (planning : PlanningSelection)
    (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
      witnessLive 7).Index) :
    ExecutedFinds (rungConstruction planning).initial.agent witnessConfig witnessLive 7 counted ↔
      ∃ solved : Finset (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
          witnessLive 7).Index,
        98 < solved.card ∧ ∀ index ∈ solved, index ∈ counted ∧
          ∃ visit, (completion witnessConfig (rungConstruction planning).profile.taskMode
              7).MetBy (member witnessLive index.1.1)
            (fun step => rungExplorer.actionAt (visit * 8 + step)) :=
  cold_finds_iff (profile := (rungConstruction planning).profile) rfl rfl planning witnessLive
    rfl 7 counted

theorem rung_memory_bounded (planning : PlanningSelection) (horizon lapses : ℕ)
    (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
      witnessLive 7).Index)
    (updates : (executedAgent (rungConstruction planning).initial.agent).Memory →
      Percept Grid.interface × ℚ → List OneStream.Update)
    (work : (executedAgent (rungConstruction planning).initial.agent).Memory →
      Percept Grid.interface × ℚ → ℕ)
    (resume : (executedAgent (rungConstruction planning).initial.agent).Memory →
      (executedAgent (rungConstruction planning).initial.agent).Memory) :
    MemoryBounded (findRung witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7
      horizon lapses counted (executedAgent (rungConstruction planning).initial.agent) updates
      work resume) :=
  find_memory_bounded (rungConstruction planning) rfl .initial witnessConfig witnessLive 7 horizon
    lapses counted updates work resume

end AcornVerif.CurrentConcealedTargetRung
