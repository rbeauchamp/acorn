import Acorn.Host.Checkpoint.Admission

namespace Acorn.Handcrafted
open Features

abbrev AgentConstruction.agentCallbacks (construction : AgentConstruction) :=
  Agent.callbacks (profile := construction.profile) (config := construction.config)
    (criterion := construction.criterion) (dimension := construction.dimension)
    (planning := construction.planning) construction.order

inductive AgentConstruction.Reached (construction : AgentConstruction) :
    Agent Grid.interface construction.profile construction.config construction.criterion
      construction.dimension construction.planning → Prop where
  | initial : AgentConstruction.Reached construction (Agent.initial _ _ _ _ _ _)
  | loaded {bytes : List UInt8} {image : construction.Image}
      (admitted : Checkpoint.loadCandidate construction bytes = .ok image) :
      AgentConstruction.Reached construction image.agent
  | step {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) (observation : Host.Observation)
      (result : Host.RawStepResult) :
      AgentConstruction.Reached construction (construction.agentCallbacks.learn
        (construction.agentCallbacks.choose agent observation result).2)
  | environment {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) (family : Host.GoalFamily)
      (reward : Binary32) :
      AgentConstruction.Reached construction
        (construction.agentCallbacks.recordEnvironment agent family reward)
  | attempt {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) (family : Host.GoalFamily)
      (cycle steps : UInt64) (achieved : Bool) :
      AgentConstruction.Reached construction
        (construction.agentCallbacks.recordAttempt agent family cycle steps achieved)
  | censored {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) :
      AgentConstruction.Reached construction agent.censorObservations
  | session {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) :
      AgentConstruction.Reached construction agent.beginSession

structure AgentConstruction.State (construction : AgentConstruction) where
  private mk ::
  agent : Agent Grid.interface construction.profile construction.config construction.criterion
    construction.dimension construction.planning
  reached : construction.Reached agent

def AgentConstruction.initial (construction : AgentConstruction) : construction.State :=
  ⟨Agent.initial _ _ _ _ _ _, .initial⟩

theorem AgentConstruction.initial_agent (construction : AgentConstruction) :
    construction.initial.agent = Agent.initial _ _ _ _ _ _ := rfl

theorem AgentConstruction.State.ext {construction : AgentConstruction}
    {first second : construction.State} (same : first.agent = second.agent) : first = second := by
  cases first
  cases second
  cases same
  rfl

def AgentConstruction.State.restore {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image)
    (admitted : ∃ bytes, Checkpoint.loadCandidate construction bytes = .ok image) :
    Option construction.State :=
  match restored : state.agent.restore image.image with
  | none => none
  | some agent => some ⟨agent, by
      unfold Agent.restore at restored
      split at restored
      · obtain rfl := Option.some.inj restored
        exact admitted.elim fun _ loaded => .loaded loaded
      · contradiction⟩

theorem AgentConstruction.State.restore_agent {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image)
    (admitted : ∃ bytes, Checkpoint.loadCandidate construction bytes = .ok image) :
    (state.restore image admitted).map (·.agent) = state.agent.restore image.image := by
  unfold AgentConstruction.State.restore
  split
  · rename_i restored
    exact restored.symm
  · rename_i agent restored
    exact restored.symm

theorem AgentConstruction.State.restore_refuses {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image)
    (admitted : ∃ bytes, Checkpoint.loadCandidate construction bytes = .ok image)
    (unsupported : construction.profile.checkpointSupported = false) :
    state.restore image admitted = none := by
  have same := state.restore_agent image admitted
  rw [Agent.restore_refuses state.agent image.image unsupported] at same
  exact Option.map_eq_none_iff.mp same

theorem AgentConstruction.State.restore_exact {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image)
    (admitted : ∃ bytes, Checkpoint.loadCandidate construction bytes = .ok image)
    (supported : construction.profile.checkpointSupported = true) :
    ∃ restored, state.restore image admitted = some restored ∧ restored.agent = image.agent := by
  have same := state.restore_agent image admitted
  rw [Agent.restore_exact state.agent image.image supported] at same
  obtain ⟨restored, found, agent⟩ := Option.map_eq_some_iff.mp same
  exact ⟨restored, found, agent⟩

def AgentConstruction.State.censorObservations {construction : AgentConstruction}
    (state : construction.State) : construction.State :=
  ⟨state.agent.censorObservations, .censored state.reached⟩

def AgentConstruction.State.beginSession {construction : AgentConstruction}
    (state : construction.State) : construction.State :=
  ⟨state.agent.beginSession, .session state.reached⟩

structure AgentConstruction.Chosen (construction : AgentConstruction) where
  private mk ::
  chosen : Handcrafted.Chosen Grid.interface construction.profile construction.config
    construction.criterion construction.dimension construction.planning
  origin : ∃ agent observation result, construction.Reached agent ∧
    (construction.agentCallbacks.choose agent observation result).2 = chosen

def AgentConstruction.callbacks (construction : AgentConstruction) :
    Host.AgentCallbacks construction.order construction.State
      (AgentObservation construction.config construction.dimension) :=
  let raw := construction.agentCallbacks
  { Chosen := construction.Chosen
    choose := fun state observation result =>
      let chosen := raw.choose state.agent observation result
      (chosen.1, ⟨chosen.2, ⟨state.agent, observation, result, state.reached, rfl⟩⟩)
    learn := fun chosen => ⟨raw.learn chosen.chosen, by
      obtain ⟨agent, observation, result, reached, same⟩ := chosen.origin
      rw [← same]
      exact .step reached observation result⟩
    recordEnvironment := fun state family reward =>
      ⟨raw.recordEnvironment state.agent family reward, .environment state.reached family reward⟩
    recordAttempt := fun state family cycle steps achieved =>
      ⟨raw.recordAttempt state.agent family cycle steps achieved,
        .attempt state.reached family cycle steps achieved⟩
    capture := fun state => raw.capture state.agent
    metrics := fun state => raw.metrics state.agent }

theorem AgentConstruction.callbacks_act (construction : AgentConstruction)
    (state : construction.State) (observation : Host.Observation)
    (result : Host.RawStepResult) :
    ((construction.callbacks.act state observation result).1,
        (construction.callbacks.act state observation result).2.agent) =
      (Agent.callbacks construction.order).act state.agent observation result := rfl

def AgentConstruction.runCampaign (construction : AgentConstruction)
    (_ : Grid.interface.timing = .synchronized) (config : Host.WorldConfig)
    (seed : UInt64) (selection : Host.AgentSelection) (spec : Host.CampaignSpec)
    (observer : Host.StreamObserver
      (AgentObservation construction.config construction.dimension))
    (checkpoint : Option (Host.CheckpointHooks construction.State)) (readStop : BaseIO Bool) :
    IO (Except Host.RunnerError (Host.CampaignResult config construction.State)) :=
  Host.runCampaign config seed selection spec (fun _ => IO.lazyPure fun _ => construction.initial)
    construction.callbacks observer checkpoint readStop

structure DefaultConstruction where
  construction : AgentConstruction
  default : construction.order = .learnThenAct

theorem DefaultConstruction.act_step (admitted : DefaultConstruction)
    (agent : Agent Grid.interface admitted.construction.profile admitted.construction.config
      admitted.construction.criterion admitted.construction.dimension
      admitted.construction.planning)
    (observation : Host.Observation) (result : Host.RawStepResult) :
    admitted.construction.agentCallbacks.learn
        (admitted.construction.agentCallbacks.choose agent observation result).2 =
      (agent.act (Grid.percept admitted.construction.profile.taskMode observation result.reward
        result.events.done)).1 := by
  unfold AgentConstruction.agentCallbacks
  rw [admitted.default]
  exact congrArg Prod.snd (Agent.callbacks_act agent observation result)

theorem DefaultConstruction.reached_prefix (admitted : DefaultConstruction) :
    ∀ (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
        admitted.construction.dimension))
      {agent : Agent Grid.interface admitted.construction.profile admitted.construction.config
        admitted.construction.criterion admitted.construction.dimension
        admitted.construction.planning},
      admitted.construction.Reached agent →
        admitted.construction.Reached (agent.runPrefix inputs).1
  | [], _, reached => reached
  | event :: rest, agent, reached => by
    cases event with
    | act observation result =>
      have stepped := AgentConstruction.Reached.step reached observation result
      rw [admitted.act_step agent observation result] at stepped
      exact DefaultConstruction.reached_prefix admitted rest stepped
    | environment family reward =>
      exact DefaultConstruction.reached_prefix admitted rest (.environment reached family reward)
    | attempt family cycle steps achieved =>
      exact DefaultConstruction.reached_prefix admitted rest (.attempt reached family cycle steps achieved)
    | clear => exact DefaultConstruction.reached_prefix admitted rest .initial
    | stop => exact reached

def DefaultConstruction.runPrefix (admitted : DefaultConstruction)
    (state : admitted.construction.State)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    admitted.construction.State × Bool :=
  let result := state.agent.runPrefix inputs
  (⟨result.1, admitted.reached_prefix inputs state.reached⟩, result.2)

theorem DefaultConstruction.runPrefix_agent (admitted : DefaultConstruction)
    (state : admitted.construction.State)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    ((admitted.runPrefix state inputs).1.agent, (admitted.runPrefix state inputs).2) =
      state.agent.runPrefix inputs := rfl

@[noinline] def AgentConstruction.execute (admitted : DefaultConstruction)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    admitted.construction.State × Bool :=
  admitted.runPrefix admitted.construction.initial inputs

end Acorn.Handcrafted
