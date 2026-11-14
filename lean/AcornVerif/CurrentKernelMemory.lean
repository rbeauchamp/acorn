/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Campaign
import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.CurrentRunningMemory
import Mathlib.Data.Fintype.Card

/-!
# The memories the executed agent holds in a kernel run

`AcornVerif.CurrentRunningMemory` bounds the states a host runs (`Running`): their images fit the
construction's read limit, so they embed in the bit strings of a fixed width
(`running_memory_bits`). Two results read the memories of a kernel run instead: the premise
`AcornVerif.Intent.MissionTheorem.MemoryBounded` of a class's theorem, over the run of a class in
visits, and `AcornVerif.Kernel.campaign_count`, over a campaign's cycles. This module links the two,
which is what obligation 6 of `docs/mission-contract.md` asks of a kernel run.

**The link.** The executed agent as a kernel agent (`AcornVerif.CurrentGridWorld.executedAgent`)
takes the executed step of the default order on each percept. A host's whole step is the agent's
step of the construction's order on a grid percept: an observation of the host with the carried
reward and achievement flag (`Acorn.Handcrafted.AgentConstruction.callbacks_act`). So, for a
construction of the default order, from the agent of a running state and on a grid percept, the
kernel agent's next memory is the agent of a running state (`step_running`). A world shows grid
percepts when each of its percepts is one (`ShowsGrid`): the grid world does at every state, the
refused state included, and so do its visits and its campaigns (`gridWorld_shows`, `visits_shows`,
`campaign_shows`). In such a world every memory of the kernel's closed loop is the agent of a
running state (`loop_running`).

**What follows.**

- One finite list holds the agent of every running state (`running_agents`), so the premise
  `MemoryBounded` holds of the executed agent on every class of such worlds in visits
  (`visits_memory_bounded`), and on the concealed targets of every host world
  (`find_memory_bounded`).
- The campaign counting bound holds of the executed agent with a number in place of a set of
  memories: the assignments on which it solves every slot of one cycle number at most
  `2 ^ (8 * (maximumBytes construction + 1))` times the covering bound to the power of the slots
  (`executed_campaign_count`, and `find_campaign_count` on the concealed targets).

**Hypotheses and limits.**

- The construction's order is the default one, since the kernel agent takes the step of that
  order. The run starts from the agent of a running state: the cold state is one.
- `MemoryBounded` is proved of the agent whose memory is the executed agent's whole state. An agent
  whose memory is a function of that state holds at most as many memories; which memory contract 3
  reads is rbeauchamp/acorn#249.
- `Running` is a definition. That a native loop holds only such states is argued in
  `AcornVerif.CurrentRunningMemory`, not proved, and nothing here ties a kernel run to a native
  loop.
- The width is that of the checkpoint image, which holds every field of the agent. It bounds the
  count and says nothing of native allocation.
-/

namespace AcornVerif.CurrentKernelMemory
open Acorn Acorn.Features Acorn.Handcrafted Acorn.Checkpoint
open AcornVerif.CurrentGridWorld AcornVerif.CurrentRunningMemory
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentConcealedTargetMission
open AcornVerif.MissionVisits AcornVerif.Intent AcornVerif.Intent.MissionTheorem

/-! ## Worlds that show grid percepts -/

/-- Each percept of the world is a grid percept in the task mode: the grid adapter's percept of
some observation of the host, with the reward and the achievement flag of some carried result. -/
def ShowsGrid (mode : TaskFeatureMode) (world : Kernel.World Grid.interface) : Prop :=
  ∀ state, ∃ (observation : Host.Observation) (result : Host.RawStepResult),
    world.percept state = Grid.percept mode observation result.reward result.events.done

/-- The grid world of a configuration shows grid percepts at every state, the refused state
included. -/
theorem gridWorld_shows (config : Host.WorldConfig) (mode : TaskFeatureMode) :
    ShowsGrid mode (gridWorld config mode)
  | none => ⟨blank, {}, rfl⟩
  | some live => ⟨sensed live.world, live.carried, rfl⟩

/-- A world in visits shows grid percepts where the world does. -/
theorem visits_shows {mode : TaskFeatureMode} {world : Kernel.World Grid.interface}
    (shows : ShowsGrid mode world) (start : world.State) (length : ℕ) :
    ShowsGrid mode (Kernel.visits world start length) :=
  fun state => shows state.1

/-- A campaign over a class shows grid percepts where every world of the class does. -/
theorem campaign_shows {mode : TaskFeatureMode} {family : Kernel.WorldClass Grid.interface}
    (shows : ∀ index, ShowsGrid mode (family.world index)) (length slots : ℕ)
    (assignment : Fin (slots + 1) → family.Index) :
    ShowsGrid mode (Kernel.campaign family length slots assignment) :=
  fun state => shows (assignment state.1) state.2.1

/-! ## The link -/

section Link

variable (construction : AgentConstruction)

/-- **One step of the kernel agent stays among the running states.** For a construction of the
default order, from the agent of a running state and on a grid percept of the construction's task
mode, the executed step returns the agent of a running state: the state after the host's whole
step on that observation and carried result. -/
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

/-- **Every memory of the kernel's closed loop is the agent of a running state.** For a
construction of the default order, in a world that shows grid percepts of its task mode, from every
start state and from the agent of a running state. -/
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

/-- One finite list holds the agent of every state a host runs. -/
theorem running_agents :
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

end Link

/-! ## Contract 3's bound on memory -/

/-- **The executed agent holds one of finitely many memories on a class in visits.** For a
construction of the default order and a class whose worlds show grid percepts of its task mode:
the rung of the class in visits with the executed agent, from the agent of a running state, meets
the premise `MemoryBounded`, whatever the agent reports of its steps. -/
theorem visits_memory_bounded (construction : AgentConstruction)
    (default : construction.order = .learnThenAct)
    {origin : construction.State} (running : Running construction origin)
    (family : Kernel.WorldClass Grid.interface)
    (shows : ∀ index, ShowsGrid construction.profile.taskMode (family.world index))
    (length : ℕ) (pay : Percept Grid.interface → ℚ)
    (met : (index : family.Index) → (family.world index).State → Bool)
    (counted : List family.Index)
    (updates : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ →
      List OneStream.Update)
    (work : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : (executedAgent origin.agent).Memory → (executedAgent origin.agent).Memory) :
    MemoryBounded (visitsRung family length pay met counted (executedAgent origin.agent) updates
      work resume) := by
  obtain ⟨agents, listed⟩ := running_agents construction
  refine ⟨agents, fun index ins time state memory reached => ?_⟩
  suffices held : ∃ host : construction.State, Running construction host ∧ host.agent = memory by
    obtain ⟨host, ran, same⟩ := held
    exact same ▸ listed host ran
  induction reached with
  | start => exact ⟨origin, running, rfl⟩
  | next earlier goes ih =>
    obtain ⟨host, ran, same⟩ := ih
    rename_i before held
    obtain ⟨observation, result, shown⟩ := shows index before.1
    obtain ⟨next, stepped, agent⟩ := step_running construction default ran observation result
    refine ⟨next, stepped, ?_⟩
    rw [agent, same, ← shown]
    rfl

/-- **The executed agent holds one of finitely many memories on the concealed targets.** For a
construction of the default order, every host world, visit length and list of counted members: the
rung of the feasible concealed targets with the executed agent, from the agent of a running state,
meets the premise `MemoryBounded`. -/
theorem find_memory_bounded (construction : AgentConstruction)
    (default : construction.order = .learnThenAct)
    {origin : construction.State} (running : Running construction origin)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (counted : List (feasibleFind config construction.profile.taskMode live length).Index)
    (updates : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ →
      List OneStream.Update)
    (work : (executedAgent origin.agent).Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : (executedAgent origin.agent).Memory → (executedAgent origin.agent).Memory) :
    MemoryBounded (findRung config construction.profile.taskMode live length counted
      (executedAgent origin.agent) updates work resume) :=
  visits_memory_bounded construction default running _
    (fun _ => gridWorld_shows config construction.profile.taskMode) length reward
    (fun _ => goalMet) counted updates work resume

/-! ## The campaign counting bound -/

/-- **The campaign counting bound of the executed agent.** For a construction of the default order
and a class that conceals its goals, has a covering bound for one visit and shows grid percepts of
the construction's task mode: the assignments of `slots + 1` slots on each of which the executed
agent, from the agent of a running state, solves every slot on one cycle number at most
`2 ^ (8 * (maximumBytes construction + 1))` times the bound to the power of the slots. -/
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

/-- **The campaign counting bound of the executed agent on the concealed targets.** For a
construction of the default order, every host world and visit length: the assignments of feasible
concealed targets to `slots + 1` slots on each of which the executed agent, from the agent of a
running state, solves every slot on one cycle number at most
`2 ^ (8 * (maximumBytes construction + 1)) * (49 + 7 * length) ^ (slots + 1)`. -/
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

end AcornVerif.CurrentKernelMemory
