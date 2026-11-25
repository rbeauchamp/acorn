import Acorn.Host.AgentAdmission
import Acorn.Host.Runner
import AcornVerif.CurrentAccounting
import AcornVerif.CurrentGridWorld
import AcornVerif.Visits

namespace AcornVerif.CurrentHostLoop
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld
open AcornVerif.CurrentAccounting

def orderedAgent {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (order : StepOrder) (state : Agent interface profile features criterion dimension planning) :
    Kernel.Agent interface where
  Memory := Agent interface profile features criterion dimension planning
  initial := state
  act := fun memory percept =>
    ((memory.actOrdered order percept).2.action, (memory.actOrdered order percept).1)

theorem orderedAgent_default {interface : Interface} {profile : FeatureProfile}
    {features : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {planning : PlanningSelection}
    (state : Agent interface profile features criterion dimension planning) :
    orderedAgent .learnThenAct state = executedAgent state := by
  unfold orderedAgent executedAgent
  congr
  funext memory percept
  rw [Agent.act_parts]

section Simulation

variable {order : StepOrder} {config : Host.WorldConfig} {α β : Type} {goal : Host.Goal}
  {cap : UInt64}

structure Simulates (callbacks : Host.AgentCallbacks order α β) (mode : TaskFeatureMode)
    (agent : Kernel.Agent Grid.interface) (related : α → agent.Memory → Prop) : Prop where
  act : ∀ state memory observation (result : Host.RawStepResult), related state memory →
    (callbacks.act state observation result).1 = Host.Action.fromIndex
        (agent.act memory (Grid.percept mode observation result.reward result.events.done)).1.val ∧
      related (callbacks.act state observation result).2
        (agent.act memory (Grid.percept mode observation result.reward result.events.done)).2
  environment : ∀ state memory family reward, related state memory →
    related (callbacks.recordEnvironment state family reward) memory
  attempt : ∀ state memory family visit steps achieved, related state memory →
    related (callbacks.recordAttempt state family visit steps achieved) memory

theorem release_accepted {selected : Host.OwnedStep config α goal cap}
    {environment : Host.OwnedEnvironment config α goal cap}
    (h : selected.release = .accepted environment) : environment.selected = selected := by
  unfold Host.OwnedStep.release at h
  split at h
  · cases h
  · cases h
    rfl

theorem release_refused {selected learned : Host.OwnedStep config α goal cap}
    {error : Host.WorldError}
    (h : selected.release = .refused error learned) : learned = selected := by
  unfold Host.OwnedStep.release at h
  split at h
  · cases h
    rfl
  · cases h

theorem selectOwned_action (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).action =
      (callbacks.act input.before.run.agent input.observation input.before.run.carried).1 := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

theorem selectOwned_agent (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).agent =
      (callbacks.act input.before.run.agent input.observation input.before.run.carried).2 := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

theorem selectOwned_world (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).before.run.world = input.before.run.world := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

theorem selectOwned_steps (callbacks : Host.AgentCallbacks order α β)
    (input : Host.DecisionInput config α goal cap) :
    (input.selectOwned callbacks).before.steps = input.before.steps := by
  rw [Host.DecisionInput.selectOwned_eq]
  rfl

abbrev sameLearners (construction : AgentConstruction) (state : construction.State)
    (host : construction.State)
    (memory : (orderedAgent construction.order state.agent).Memory) : Prop :=
  learners host.agent.control = learners memory.control

theorem construction_simulates (construction : AgentConstruction) (state : construction.State) :
    Simulates construction.callbacks construction.profile.taskMode
      (orderedAgent construction.order state.agent) (sameLearners construction state) := by
  refine ⟨?_, ?_, ?_⟩
  · intro host memory observation result same
    have whole := AgentConstruction.callbacks_act construction host observation result
    have ordered := Agent.callbacks_ordered construction.order host.agent observation result
    have kept := actOrdered_learners host.agent memory same construction.order
      (Grid.percept construction.profile.taskMode observation result.reward result.events.done)
    constructor
    · refine (congrArg Prod.fst whole).trans ((congrArg Prod.fst ordered).trans ?_)
      exact congrArg (fun decision => Host.Action.fromIndex decision.action.val) kept.1
    · have learned : (construction.callbacks.act host observation result).2.agent =
          (host.agent.actOrdered construction.order (Grid.percept construction.profile.taskMode
            observation result.reward result.events.done)).1 :=
        (congrArg Prod.snd whole).trans (congrArg Prod.snd ordered)
      exact (congrArg (fun next => learners next.control) learned).trans kept.2
  · intro host memory family reward same
    exact same
  · intro host memory family visit steps achieved same
    exact same

theorem sense_before {attempt : Host.Attempt config α goal cap}
    {input : Host.DecisionInput config α goal cap}
    (sensed : attempt.sense = .ok (some input)) : input.before = attempt := by
  unfold Host.Attempt.sense at sensed
  split at sensed
  · cases sensed
  · split at sensed
    · split at sensed
      · cases sensed
      · cases sensed
        rfl
    · cases sensed

theorem pass_kernel {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related)
    (input : Host.DecisionInput config α goal cap)
    (environment : Host.OwnedEnvironment config α goal cap)
    (accepted : (input.selectOwned callbacks).release = .accepted environment)
    (memory : agent.Memory) (holds : related input.before.run.agent memory) :
    let decision := agent.act memory ((gridWorld config mode).percept
      (some ⟨input.before.run.world, input.before.run.carried⟩))
    (environment.record callbacks).lastAction = Host.Action.fromIndex decision.1.val ∧
      (gridWorld config mode).step (some ⟨input.before.run.world, input.before.run.carried⟩)
          decision.1 =
        some ⟨(environment.record callbacks).run.world,
          (environment.record callbacks).run.carried⟩ ∧
      related (environment.record callbacks).run.agent decision.2 := by
  intro decision
  have selected := release_accepted accepted
  obtain ⟨chosen, next, result, stepped⟩ := environment
  dsimp only at selected
  subst selected
  have perceived := percept_live mode ⟨input.before.run.world, input.before.run.carried⟩
    input.observation input.sensed
  have sim := simulates.act input.before.run.agent memory input.observation
    input.before.run.carried holds
  have action := selectOwned_action callbacks input
  have learned := selectOwned_agent callbacks input
  have world := selectOwned_world callbacks input
  have same : decision = agent.act memory
      (Grid.percept mode input.observation input.before.run.carried.reward
        input.before.run.carried.events.done) := congrArg (agent.act memory) perceived
  rw [same]
  refine ⟨action.trans sim.1, ?_, ?_⟩
  · have taken := stepped
    rw [world, action, sim.1] at taken
    exact advance_ok ⟨input.before.run.world, input.before.run.carried⟩ _ next result taken
  · exact simulates.environment _ _ _ _ (learned ▸ sim.2)

theorem attempt_simulation {callbacks : Host.AgentCallbacks order α β} {mode : TaskFeatureMode}
    {agent : Kernel.Agent Grid.interface} {related : α → agent.Memory → Prop}
    (simulates : Simulates callbacks mode agent related)
    {attempt reached : Host.Attempt config α goal cap} {passes : ℕ}
    (run : Host.Attempt.Reaches callbacks passes attempt reached)
    (memory : agent.Memory) (holds : related attempt.run.agent memory) :
    let start : Option (Live config) := some ⟨attempt.run.world, attempt.run.carried⟩
    Kernel.stateAt (gridWorld config mode) (agent.resume memory) start passes =
        some ⟨reached.run.world, reached.run.carried⟩ ∧
      related reached.run.agent
        (Kernel.memoryAt (gridWorld config mode) (agent.resume memory) start passes) ∧
      ∀ earlier, passes = earlier + 1 →
        reached.lastAction = Host.Action.fromIndex
          (Kernel.actionAt (gridWorld config mode) (agent.resume memory) start earlier).val := by
  induction run generalizing memory with
  | same attempt => exact ⟨rfl, holds, fun earlier zero => by cases zero⟩
  | pass passes attempt reached input environment _ sensed accepted rest ih =>
    have before := sense_before sensed
    subst before
    obtain ⟨action, moved, kept⟩ := pass_kernel simulates input environment accepted memory holds
    obtain ⟨state, learned, last⟩ := ih _ kept
    have one : Kernel.stateAt (gridWorld config mode) (agent.resume memory)
        (some ⟨input.before.run.world, input.before.run.carried⟩) 1 =
          some ⟨(environment.record callbacks).run.world,
            (environment.record callbacks).run.carried⟩ := moved
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.add_comm, Kernel.stateAt_add, one]
      exact state
    · rw [Nat.add_comm, Kernel.memoryAt_add, one]
      exact learned
    · intro earlier same
      cases Nat.succ.inj same
      cases rest with
      | same => exact action
      | pass passes _ _ _ _ _ _ _ _ =>
        have taken := last passes rfl
        rw [taken, Nat.add_comm]
        unfold Kernel.actionAt Kernel.perceptAt
        rw [Kernel.stateAt_add, Kernel.memoryAt_add, one]
        rfl

theorem reaches_unique {callbacks : Host.AgentCallbacks order α β} {passes : ℕ}
    {attempt reached other : Host.Attempt config α goal cap}
    (run : Host.Attempt.Reaches callbacks passes attempt reached)
    (same : Host.Attempt.Reaches callbacks passes attempt other) : reached = other := by
  induction run with
  | same attempt =>
    cases same
    rfl
  | pass passes attempt reached input environment _ sensed accepted rest ih =>
    cases same with
    | pass _ _ _ input' environment' _ sensed' accepted' rest' =>
      rw [sensed] at sensed'
      cases sensed'
      rw [accepted] at accepted'
      cases accepted'
      exact ih rest'

theorem reaches_split {callbacks : Host.AgentCallbacks order α β} {total : ℕ}
    {attempt reached : Host.Attempt config α goal cap}
    (run : Host.Attempt.Reaches callbacks total attempt reached) (first later : ℕ)
    (sum : total = first + later) :
    ∃ middle, Host.Attempt.Reaches callbacks first attempt middle ∧
      Host.Attempt.Reaches callbacks later middle reached := by
  induction run generalizing first with
  | same attempt =>
    have zero : first = 0 := by omega
    have none : later = 0 := by omega
    subst zero none
    exact ⟨attempt, .same attempt, .same attempt⟩
  | pass passes attempt reached input environment unfinished sensed accepted rest ih =>
    cases first with
    | zero =>
      have count : later = passes + 1 := by omega
      subst count
      exact ⟨attempt, .same attempt, .pass passes attempt reached input environment unfinished
        sensed accepted rest⟩
    | succ first =>
      obtain ⟨middle, before, after⟩ := ih first (by omega)
      exact ⟨middle, .pass first attempt middle input environment unfinished sensed accepted before,
        after⟩

theorem complete_reaches (callbacks : Host.AgentCallbacks order α β) (context : Host.GoalContext)
    (fuel : ℕ) (attempt : Host.Attempt config α goal cap)
    (value : Host.RunState config α × Host.GoalOutcome × Host.StepFrame β)
    (returned : attempt.complete callbacks context fuel = .ok value) :
    ∃ (passes : ℕ) (reached : Host.Attempt config α goal cap),
      passes ≤ fuel ∧ Host.Attempt.Reaches callbacks passes attempt reached ∧
        reached.close callbacks context = .ok value := by
  induction fuel generalizing attempt with
  | zero => exact ⟨0, attempt, Nat.le_refl _, .same attempt, returned⟩
  | succ fuel ih =>
    unfold Host.Attempt.complete at returned
    split at returned
    · exact ⟨0, attempt, by omega, .same attempt, returned⟩
    · rename_i unfinished
      split at returned
      · cases returned
      · exact ⟨0, attempt, by omega, .same attempt, returned⟩
      · rename_i input sensed
        split at returned
        · cases returned
        · rename_i environment accepted
          obtain ⟨passes, reached, bound, reaches, closed⟩ := ih _ returned
          exact ⟨passes + 1, reached, by omega,
            .pass passes attempt reached input environment (Bool.eq_false_iff.mpr unfinished)
              sensed accepted reaches, closed⟩

theorem close_run {callbacks : Host.AgentCallbacks order α β} {context : Host.GoalContext}
    {attempt : Host.Attempt config α goal cap} {run : Host.RunState config α}
    {outcome : Host.GoalOutcome} {frame : Host.StepFrame β}
    (closed : attempt.close callbacks context = .ok (run, outcome, frame)) :
    run = { attempt.run with
      agent := callbacks.recordAttempt attempt.run.agent goal.family context.cycle
        attempt.steps.val.toUInt64 attempt.run.carried.events.done } := by
  unfold Host.Attempt.close at closed
  split at closed
  · cases closed
  · rename_i finished
    cases closed
    exact (Host.Attempt.finish_position callbacks context attempt _ _ _ finished).1

theorem campaignStep_reaches (curriculum : Host.Curriculum)
    {plan : Host.CampaignPlan curriculum.size} (callbacks : Host.AgentCallbacks order α β)
    (observer : Host.StreamObserver β) (readStop : BaseIO Bool)
    (progress next : Host.CampaignProgress config α plan) (world after : Void IO.RealWorld)
    (returned : Host.campaignStep curriculum callbacks observer readStop progress world =
      .ok (.inl next) after) :
    ∃ (cursor : Host.CampaignCursor plan) (bound : cursor.goal.val < curriculum.size)
        (passes : ℕ)
        (reached : Host.Attempt config α (curriculum[cursor.goal.val]'bound).1 plan.stepCap)
        (outcome : Host.GoalOutcome) (frame : Host.StepFrame β),
      progress.decision = .continue cursor ∧ passes ≤ plan.stepCap.toNat ∧
        Host.Attempt.Reaches callbacks passes
          (Host.Attempt.start progress.run (curriculum[cursor.goal.val]'bound).1 plan.stepCap)
          reached ∧
        reached.close callbacks (cursor.context (curriculum[cursor.goal.val]'bound).2) =
          .ok (next.run, outcome, frame) := by
  obtain ⟨cursor, bound, outcome, frame, decided, completed⟩ :=
    Host.campaignStep_attempt curriculum callbacks observer readStop progress next world after
      returned
  obtain ⟨passes, reached, within, run, closed⟩ := complete_reaches callbacks _ _ _ _ completed
  exact ⟨cursor, bound, passes, reached, outcome, frame, decided, within, run, closed⟩

end Simulation

theorem attempt_closed_loop (construction : AgentConstruction) {config : Host.WorldConfig}
    {goal : Host.Goal} {cap : UInt64}
    (attempt reached : Host.Attempt config construction.State goal cap) (passes : Nat)
    (run : Host.Attempt.Reaches construction.callbacks passes attempt reached) :
    let start : Option (Live config) := some ⟨attempt.run.world, attempt.run.carried⟩
    let kernelAgent := orderedAgent construction.order attempt.run.agent.agent
    let world := gridWorld config construction.profile.taskMode
    Kernel.stateAt world kernelAgent start passes =
        some ⟨reached.run.world, reached.run.carried⟩ ∧
      learners reached.run.agent.agent.control =
        learners (Kernel.memoryAt world kernelAgent start passes).control ∧
      ∀ earlier, passes = earlier + 1 →
        reached.lastAction =
          Host.Action.fromIndex (Kernel.actionAt world kernelAgent start earlier).val := by
  exact attempt_simulation (construction_simulates construction attempt.run.agent) run
    attempt.run.agent.agent rfl

theorem attempt_each_action (construction : AgentConstruction) {config : Host.WorldConfig}
    {goal : Host.Goal} {cap : UInt64}
    (attempt reached : Host.Attempt config construction.State goal cap) (passes : ℕ)
    (run : Host.Attempt.Reaches construction.callbacks passes attempt reached)
    (time : ℕ) (within : time < passes) :
    let start : Option (Live config) := some ⟨attempt.run.world, attempt.run.carried⟩
    let kernelAgent := orderedAgent construction.order attempt.run.agent.agent
    let world := gridWorld config construction.profile.taskMode
    ∃ middle, Host.Attempt.Reaches construction.callbacks (time + 1) attempt middle ∧
      Host.Attempt.Reaches construction.callbacks (passes - (time + 1)) middle reached ∧
      Kernel.stateAt world kernelAgent start (time + 1) =
        some ⟨middle.run.world, middle.run.carried⟩ ∧
      learners middle.run.agent.agent.control =
        learners (Kernel.memoryAt world kernelAgent start (time + 1)).control ∧
      middle.lastAction =
        Host.Action.fromIndex (Kernel.actionAt world kernelAgent start time).val := by
  obtain ⟨middle, before, after⟩ := reaches_split run (time + 1) (passes - (time + 1)) (by omega)
  obtain ⟨state, learned, action⟩ := attempt_closed_loop construction attempt middle _ before
  exact ⟨middle, before, after, state, learned, action time rfl⟩

theorem campaignStep_closed_loop (construction : AgentConstruction) {config : Host.WorldConfig}
    (curriculum : Host.Curriculum) {plan : Host.CampaignPlan curriculum.size}
    (observer : Host.StreamObserver (AgentObservation construction.config construction.dimension))
    (readStop : BaseIO Bool) (progress next : Host.CampaignProgress config construction.State plan)
    (world after : Void IO.RealWorld)
    (returned : Host.campaignStep curriculum construction.callbacks observer readStop progress
      world = .ok (.inl next) after) :
    ∃ (cursor : Host.CampaignCursor plan) (bound : cursor.goal.val < curriculum.size) (passes : ℕ)
        (reached : Host.Attempt config construction.State (curriculum[cursor.goal.val]'bound).1
          plan.stepCap),
      let context := cursor.context (curriculum[cursor.goal.val]'bound).2
      let started := Host.Attempt.start progress.run (curriculum[cursor.goal.val]'bound).1
        plan.stepCap
      let start : Option (Live config) := some ⟨started.run.world, started.run.carried⟩
      let kernelAgent := orderedAgent construction.order started.run.agent.agent
      let kernelWorld := gridWorld config construction.profile.taskMode
      progress.decision = .continue cursor ∧ passes ≤ plan.stepCap.toNat ∧
        Host.Attempt.Reaches construction.callbacks passes started reached ∧
        (∃ outcome frame, reached.close construction.callbacks context =
          .ok (next.run, outcome, frame)) ∧
        next.run = { reached.run with
          agent := construction.callbacks.recordAttempt reached.run.agent
            (curriculum[cursor.goal.val]'bound).1.family context.cycle reached.steps.val.toUInt64
            reached.run.carried.events.done } ∧
        Kernel.stateAt kernelWorld kernelAgent start passes =
          some ⟨next.run.world, next.run.carried⟩ ∧
        learners next.run.agent.agent.control =
          learners (Kernel.memoryAt kernelWorld kernelAgent start passes).control ∧
        ∀ time, time < passes → ∃ middle,
          Host.Attempt.Reaches construction.callbacks (time + 1) started middle ∧
          Host.Attempt.Reaches construction.callbacks (passes - (time + 1)) middle reached ∧
          middle.lastAction =
            Host.Action.fromIndex (Kernel.actionAt kernelWorld kernelAgent start time).val := by
  obtain ⟨cursor, bound, passes, reached, outcome, frame, decided, within, run, closed⟩ :=
    campaignStep_reaches curriculum construction.callbacks observer readStop progress next world
      after returned
  have kept := close_run closed
  obtain ⟨state, learned, _⟩ := attempt_closed_loop construction _ reached passes run
  refine ⟨cursor, bound, passes, reached, decided, within, run, ⟨outcome, frame, closed⟩, kept,
    ?_, ?_, ?_⟩
  · rw [kept]
    exact state
  · rw [kept]
    exact (construction_simulates construction reached.run.agent).attempt _ _ _ _ _ _ learned
  · intro time before
    obtain ⟨middle, first, later, _, _, action⟩ :=
      attempt_each_action construction _ reached passes run time before
    exact ⟨middle, first, later, action⟩

end AcornVerif.CurrentHostLoop
