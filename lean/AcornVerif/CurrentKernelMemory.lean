import AcornVerif.Campaign
import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.CurrentRunningMemory
import Mathlib.Data.Fintype.Card

namespace AcornVerif.CurrentKernelMemory
open Acorn Acorn.Features Acorn.Handcrafted Acorn.Checkpoint
open AcornVerif.CurrentGridWorld AcornVerif.CurrentRunningMemory
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentConcealedTargetMission
open AcornVerif.MissionVisits AcornVerif.Intent AcornVerif.Intent.MissionTheorem

def ShowsGrid (mode : TaskFeatureMode) (world : Kernel.World Grid.interface) : Prop :=
  ∀ state, ∃ (observation : Host.Observation) (result : Host.RawStepResult),
    world.percept state = Grid.percept mode observation result.reward result.events.done

theorem gridWorld_shows (config : Host.WorldConfig) (mode : TaskFeatureMode) :
    ShowsGrid mode (gridWorld config mode)
  | none => ⟨blank, {}, rfl⟩
  | some live => ⟨sensed live.world, live.carried, rfl⟩

theorem visits_shows {mode : TaskFeatureMode} {world : Kernel.World Grid.interface}
    (shows : ShowsGrid mode world) (start : world.State) (length : ℕ) :
    ShowsGrid mode (Kernel.visits world start length) :=
  fun state => shows state.1

theorem campaign_shows {mode : TaskFeatureMode} {family : Kernel.WorldClass Grid.interface}
    (shows : ∀ index, ShowsGrid mode (family.world index)) (length slots : ℕ)
    (assignment : Fin (slots + 1) → family.Index) :
    ShowsGrid mode (Kernel.campaign family length slots assignment) :=
  fun state => shows (assignment state.1) state.2.1

section Link

variable (construction : AgentConstruction)

theorem step_running (default : construction.order = .learnThenAct)
    {state : construction.State} (running : Running construction state)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    ∃ next : construction.State, Running construction next ∧
      next.agent = (state.agent.act (Grid.percept construction.profile.taskMode observation
        result.reward result.events.done)).1 := by
  refine ⟨_, .step running observation result, ?_⟩
  have ordered := congrArg Prod.snd (construction.callbacks_act state observation result)
  rw [Agent.callbacks_ordered] at ordered
  rw [Agent.act_parts, ← default]
  exact ordered

theorem loop_running (default : construction.order = .learnThenAct)
    {world : Kernel.World Grid.interface}
    (shows : ShowsGrid construction.profile.taskMode world)
    {origin : construction.State} (running : Running construction origin) (start : world.State) :
    ∀ time, ∃ state : construction.State, Running construction state ∧
      state.agent = Kernel.memoryAt world (executedAgent origin.agent) start time
  | 0 => ⟨origin, running, rfl⟩
  | time + 1 => by
    obtain ⟨state, held, same⟩ := loop_running default shows running start time
    obtain ⟨observation, result, shown⟩ :=
      shows (Kernel.stateAt world (executedAgent origin.agent) start time)
    obtain ⟨next, stepped, agent⟩ := step_running construction default held observation result
    refine ⟨next, stepped, ?_⟩
    rw [agent, same, ← shown]
    rfl

end Link

theorem running_agents (construction : AgentConstruction) :
    ∃ agents : List (Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning),
      ∀ state : construction.State, Running construction state → state.agent ∈ agents := by
  obtain ⟨embedding⟩ := running_memory_bits construction
  have : Finite { state : construction.State // Running construction state } :=
    Finite.of_injective embedding embedding.injective
  obtain ⟨states, -, all⟩ :=
    Finite.exists_univ_list { state : construction.State // Running construction state }
  exact ⟨states.map fun state => state.1.agent, fun state running =>
    List.mem_map.mpr ⟨⟨state, running⟩, all _, rfl⟩⟩

section Projected

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {planning : PlanningSelection}

theorem projected_actsAs
    (state : Agent Grid.interface profile features criterion dimension planning)
    (agent : Kernel.Agent Grid.interface)
    (project : Agent Grid.interface profile features criterion dimension planning → agent.Memory)
    (begins : agent.initial = project state)
    (answers : ∀ memory percept,
      (agent.act (project memory) percept).1 = (memory.act percept).2.action)
    (follows : ∀ memory percept,
      (agent.act (project memory) percept).2 = project (memory.act percept).1) :
    ActsAsExecuted state agent := by
  intro world start time
  have same : ∀ count, Kernel.loop world agent start count =
      ((Kernel.loop world (executedAgent state) start count).1,
        project (Kernel.loop world (executedAgent state) start count).2) := by
    intro count
    induction count with
    | zero => exact Prod.ext rfl begins
    | succ count ih =>
      change Kernel.interact world agent (Kernel.loop world agent start count) = _
      rw [ih]
      exact Prod.ext (congrArg (world.step _) (answers _ _)) (follows _ _)
  unfold Kernel.actionAt Kernel.memoryAt Kernel.perceptAt Kernel.stateAt
  rw [same time]
  exact answers _ _

end Projected

theorem projected_memory_bounded (construction : AgentConstruction)
    (default : construction.order = .learnThenAct)
    {origin : construction.State} (running : Running construction origin)
    (family : Kernel.WorldClass Grid.interface)
    (shows : ∀ index, ShowsGrid construction.profile.taskMode (family.world index))
    (length horizon lapses : ℕ) (pay : Percept Grid.interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index) (agent : Kernel.Agent Grid.interface)
    (project : Agent Grid.interface construction.profile construction.config
      construction.criterion construction.dimension construction.planning → agent.Memory)
    (begins : agent.initial = project origin.agent)
    (follows : ∀ memory percept,
      (agent.act (project memory) percept).2 = project (memory.act percept).1)
    (updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update)
    (work : agent.Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : agent.Memory → agent.Memory) :
    MemoryBounded
      (visitsRung family length horizon lapses pay met counted agent updates work resume) := by
  obtain ⟨agents, listed⟩ := running_agents construction
  refine ⟨agents.map project, fun index ins time state memory reached => ?_⟩
  suffices held : ∃ host : construction.State,
      Running construction host ∧ project host.agent = memory by
    obtain ⟨host, ran, same⟩ := held
    exact same ▸ List.mem_map.mpr ⟨host.agent, listed host ran, rfl⟩
  induction reached with
  | start => exact ⟨origin, running, begins.symm⟩
  | next earlier goes ih =>
    obtain ⟨host, ran, same⟩ := ih
    rename_i before held
    obtain ⟨observation, result, shown⟩ := shows index before.1
    obtain ⟨next, stepped, kept⟩ := step_running construction default ran observation result
    refine ⟨next, stepped, ?_⟩
    rw [kept, ← follows, same, ← shown]
    rfl

theorem visits_memory_bounded (construction : AgentConstruction)
    (default : construction.order = .learnThenAct)
    {origin : construction.State} (running : Running construction origin)
    (family : Kernel.WorldClass Grid.interface)
    (shows : ∀ index, ShowsGrid construction.profile.taskMode (family.world index))
    (length horizon lapses : ℕ) (pay : Percept Grid.interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index)
    (updates : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ →
      List OneStream.Update)
    (work : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : (executedAgent origin.agent).Memory → (executedAgent origin.agent).Memory) :
    MemoryBounded (visitsRung family length horizon lapses pay met counted
      (executedAgent origin.agent) updates work resume) :=
  projected_memory_bounded construction default running family shows length horizon lapses pay
    met counted
    (executedAgent origin.agent) id rfl (fun _ _ => rfl) updates work resume

theorem find_memory_bounded (construction : AgentConstruction)
    (default : construction.order = .learnThenAct)
    {origin : construction.State} (running : Running construction origin)
    (config : Host.WorldConfig) (live : Live config) (length horizon lapses : ℕ)
    (counted : List (feasibleFind config construction.profile.taskMode live length).Index)
    (updates : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ →
      List OneStream.Update)
    (work : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : (executedAgent origin.agent).Memory → (executedAgent origin.agent).Memory) :
    MemoryBounded (findRung config construction.profile.taskMode live length horizon lapses
      counted (executedAgent origin.agent) updates work resume) :=
  visits_memory_bounded construction default running _
    (fun _ => gridWorld_shows config construction.profile.taskMode) length horizon lapses reward
    (fun _ => goalMet) counted updates work resume

theorem executed_campaign_count (construction : AgentConstruction)
    (default : construction.order = .learnThenAct)
    {origin : construction.State} (running : Running construction origin)
    {family : Kernel.WorldClass Grid.interface} {goals : family.Goals}
    {reference : Kernel.World Grid.interface} {hide : reference.State}
    (hidden : Kernel.Conceals family goals reference hide) {length bound : ℕ}
    (covered : Kernel.Covered family (Kernel.visitGoals goals length) bound)
    (shows : ∀ index, ShowsGrid construction.profile.taskMode (family.world index))
    (slots cycle : ℕ) (assignments : Finset (Fin (slots + 1) → family.Index))
    (each : ∀ assignment ∈ assignments, ∀ slot,
      Kernel.SolvesSlot family goals length slots assignment (executedAgent origin.agent) cycle
        slot) :
    assignments.card ≤ 2 ^ (8 * (maximumBytes construction + 1)) * bound ^ (slots + 1) := by
  classical
  let start : (Fin (slots + 1) → family.Index) →
      Agent Grid.interface construction.profile construction.config construction.criterion
        construction.dimension construction.planning :=
    fun assignment =>
      Kernel.memoryAt (Kernel.campaign family length slots assignment) (executedAgent origin.agent)
        (Kernel.campaignStart family length slots assignment)
        (Kernel.campaignTime length slots cycle 0)
  have reached := Kernel.campaign_count hidden covered (executedAgent origin.agent) slots cycle
    (assignments.image start) assignments
    (fun assignment present => Finset.mem_image_of_mem start present) each
  have few : (assignments.image start).card ≤ 2 ^ (8 * (maximumBytes construction + 1)) := by
    have within : Set.MapsTo (agentCode construction) (assignments.image start)
        (Finset.range (2 ^ (8 * (maximumBytes construction + 1)))) := by
      intro memory member
      obtain ⟨assignment, -, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨host, ran, same⟩ := loop_running construction default
        (campaign_shows shows length slots assignment) running
        (Kernel.campaignStart family length slots assignment)
        (Kernel.campaignTime length slots cycle 0)
      have below := imageCode_lt construction host ran
      rw [Finset.coe_range]
      change agentCode construction (start assignment) < _
      change agentCode construction host.agent < _ at below
      rw [same] at below
      exact below
    have counted := Finset.card_le_card_of_injOn (agentCode construction) within
      (fun first _ second _ same => agentCode_injective construction first second same)
    rwa [Finset.card_range] at counted
  exact reached.trans (Nat.mul_le_mul_right _ few)

theorem find_campaign_count (construction : AgentConstruction)
    (default : construction.order = .learnThenAct)
    {origin : construction.State} (running : Running construction origin)
    (config : Host.WorldConfig) (live : Live config) (length slots cycle : ℕ)
    (assignments : Finset (Fin (slots + 1) →
      (feasibleFind config construction.profile.taskMode live length).Index))
    (each : ∀ assignment ∈ assignments, ∀ slot,
      Kernel.SolvesSlot (feasibleFind config construction.profile.taskMode live length)
        (fun _ => completion config construction.profile.taskMode length) length slots assignment
        (executedAgent origin.agent) cycle slot) :
    assignments.card ≤
      2 ^ (8 * (maximumBytes construction + 1)) * (49 + 7 * length) ^ (slots + 1) :=
  executed_campaign_count construction default running
    (feasibleFind_conceals construction.profile.taskMode live length length)
    (feasibleFind_covered config construction.profile.taskMode live length)
    (fun _ => gridWorld_shows config construction.profile.taskMode) slots cycle assignments each

theorem standard_width (seed : UInt64) (selection : Host.AgentSelection)
    (planning : PlanningSelection) (order : StepOrder) :
    8 * (maximumBytes (AgentConstruction.standard seed selection planning order) + 1) =
      455844664 := by
  change 8 * (maximumBytes (AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .none
    .learnThenAct) + 1) = 455844664
  decide

end AcornVerif.CurrentKernelMemory
