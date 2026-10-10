/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Admission

/-!
# The states a construction admits

A state of a construction is an agent that the construction reaches
(`AgentConstruction.Reached`): its cold state, or the agent of an image that its checkpoint
loader admits from bytes, followed by any number of the construction's own whole steps and
of the host's observation writes. Every state holds the proof of that, so a state of one
construction is not a state of another by a change of index alone: a state of the other
construction needs a proof that the other construction reaches its agent. A proof of
that kind for an agent of another step history goes through the other construction's
loader, which admits the bytes of every agent's image under its own order word
(`AcornVerif.CurrentCheckpoint.loader_reaches`); the checkpoint file is not
authenticated. Under a profile that has no resumable image the loader admits no bytes
(`AcornVerif.CurrentCheckpoint.unresumable_unloaded`), so every agent of such a
construction is reached from the cold state by the construction's own operations.
-/
namespace Acorn.Handcrafted
open Features

/-- The agent's host callbacks at the construction's step order, over the agent type of the
construction. -/
abbrev AgentConstruction.agentCallbacks (construction : AgentConstruction) :=
  Agent.callbacks (profile := construction.profile) (config := construction.config)
    (criterion := construction.criterion) (dimension := construction.dimension)
    (planning := construction.planning) construction.order

/-- The agents that one construction reaches: the cold state and the agent of every image
that the construction's checkpoint loader admits from bytes, closed under the
construction's whole step (both parts of its order), the host's two observation writes,
the censoring of the observations at process exit and the start of an evaluator session.
-/
inductive AgentConstruction.Reached (construction : AgentConstruction) :
    Agent Grid.interface construction.profile construction.config construction.criterion
      construction.dimension construction.planning → Prop where
  /-- The cold state. -/
  | initial : AgentConstruction.Reached construction (Agent.initial _ _ _ _ _ _)
  /-- The agent of an image that the construction's loader admits from bytes. -/
  | loaded {bytes : List UInt8} {image : construction.Image}
      (admitted : Checkpoint.loadCandidate construction bytes = .ok image) :
      AgentConstruction.Reached construction image.agent
  /-- One whole step: the first part of the construction's order, then the second. -/
  | step {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) (observation : Host.Observation)
      (result : Host.RawStepResult) :
      AgentConstruction.Reached construction (construction.agentCallbacks.learn
        (construction.agentCallbacks.choose agent observation result).2)
  /-- The host records a completed world transition. -/
  | environment {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) (family : Host.GoalFamily)
      (reward : Binary32) :
      AgentConstruction.Reached construction
        (construction.agentCallbacks.recordEnvironment agent family reward)
  /-- The host records a completed attempt. -/
  | attempt {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) (family : Host.GoalFamily)
      (cycle steps : UInt64) (achieved : Bool) :
      AgentConstruction.Reached construction
        (construction.agentCallbacks.recordAttempt agent family cycle steps achieved)
  /-- The host censors the evaluator's unavailable futures at process exit. -/
  | censored {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) :
      AgentConstruction.Reached construction agent.censorObservations
  /-- The host begins an evaluator session. -/
  | session {agent : Agent Grid.interface construction.profile construction.config
        construction.criterion construction.dimension construction.planning}
      (before : AgentConstruction.Reached construction agent) :
      AgentConstruction.Reached construction agent.beginSession

/-- The agent of one construction, with the proof that the construction reaches it. The
construction, and with it the step order, is an index of the type, so a state of one order
and a state of another do not meet by accident, and a state of another index needs a proof
that the other construction reaches the same agent. The constructor is private, which
stops the constructor notation and the constructor name outside this module and does not
stop a tactic; the proof field holds whatever the constructor is given. A state under
another index gives the agent's step of that index's order on the same learner state
(`AgentConstruction.callbacks_act`), and a save that writes that index's word
(`AcornVerif.CurrentCheckpoint.saved_header`). -/
structure AgentConstruction.State (construction : AgentConstruction) where
  private mk ::
  /-- The learner state, with all immutable construction choices in its type. -/
  agent : Agent Grid.interface construction.profile construction.config construction.criterion
    construction.dimension construction.planning
  /-- The construction reaches the learner state. -/
  reached : construction.Reached agent

/-- Every native constructor calls the full current cold initialization. -/
def AgentConstruction.initial (construction : AgentConstruction) : construction.State :=
  ⟨Agent.initial _ _ _ _ _ _, .initial⟩

/-- Cold initialization is the agent's own initial state. -/
theorem AgentConstruction.initial_agent (construction : AgentConstruction) :
    construction.initial.agent = Agent.initial _ _ _ _ _ _ := rfl

/-- Two states of a construction with the same agent are equal. -/
theorem AgentConstruction.State.ext {construction : AgentConstruction}
    {first second : construction.State} (same : first.agent = second.agent) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Restoration takes an image of the receiver's own construction, with the proof that the
construction's loader admitted it from bytes. The learner state is replaced by the agent's
own restore. Its refusal of a profile that cannot restore is unreachable here: no image of
such a construction is admitted (`AcornVerif.CurrentCheckpoint.unresumable_unloaded`). -/
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

/-- Restoration is the agent's own restore on the admitted image. -/
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

/-- A profile that cannot restore refuses every image. The hypotheses are jointly
unsatisfiable, since no image is admitted under a profile that cannot restore
(`AcornVerif.CurrentCheckpoint.unresumable_unloaded`); the theorem closes the unreachable case
of the proof of `Acorn.Decisions.checkpoint_load`. -/
theorem AgentConstruction.State.restore_refuses {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image)
    (admitted : ∃ bytes, Checkpoint.loadCandidate construction bytes = .ok image)
    (unsupported : construction.profile.checkpointSupported = false) :
    state.restore image admitted = none := by
  have same := state.restore_agent image admitted
  rw [Agent.restore_refuses state.agent image.image unsupported] at same
  exact Option.map_eq_none_iff.mp same

/-- **Restoration of a state is exact.** Under a profile that restores, the restored state's
agent is the agent of the image. -/
theorem AgentConstruction.State.restore_exact {construction : AgentConstruction}
    (state : construction.State) (image : construction.Image)
    (admitted : ∃ bytes, Checkpoint.loadCandidate construction bytes = .ok image)
    (supported : construction.profile.checkpointSupported = true) :
    ∃ restored, state.restore image admitted = some restored ∧ restored.agent = image.agent := by
  have same := state.restore_agent image admitted
  rw [Agent.restore_exact state.agent image.image supported] at same
  obtain ⟨restored, found, agent⟩ := Option.map_eq_some_iff.mp same
  exact ⟨restored, found, agent⟩

/-- Censoring the observations a host keeps changes no step and keeps the construction. -/
def AgentConstruction.State.censorObservations {construction : AgentConstruction}
    (state : construction.State) : construction.State :=
  ⟨state.agent.censorObservations, .censored state.reached⟩

/-- A new evaluator session changes no learned state and keeps the construction. -/
def AgentConstruction.State.beginSession {construction : AgentConstruction}
    (state : construction.State) : construction.State :=
  ⟨state.agent.beginSession, .session state.reached⟩

/-- What the agent of one construction holds between the two parts of a step, with the
proof that the first part of the construction's order made it at an agent the construction
reaches. The first part of `AgentConstruction.callbacks` makes it. -/
structure AgentConstruction.Chosen (construction : AgentConstruction) where
  private mk ::
  /-- The chosen value of the agent, made under the construction's order. -/
  chosen : Handcrafted.Chosen Grid.interface construction.profile construction.config
    construction.criterion construction.dimension construction.planning
  /-- The first part of the construction's order made the value at a reached agent. -/
  origin : ∃ agent observation result, construction.Reached agent ∧
    (construction.agentCallbacks.choose agent observation result).2 = chosen

/-- The host callbacks of one construction: the two parts of the construction's own step
order, over the construction's own state type, with that order as the index a host loop
reads. The step, the loop, the state that a checkpoint stamps and the image it admits
all come from the one construction. A campaign does not take this record from a caller:
`AgentConstruction.runCampaign` derives it. The constructor of the record is public, and
no check stops a module of this project from making a record of this type. -/
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

/-- **The whole step of a construction is the agent's step of its order.** For every
construction, state, observation and carried result, the action and the learner state
of the construction's whole step are those of `Agent.callbacks` at the construction's
order on the learner state. -/
theorem AgentConstruction.callbacks_act (construction : AgentConstruction)
    (state : construction.State) (observation : Host.Observation)
    (result : Host.RawStepResult) :
    ((construction.callbacks.act state observation result).1,
        (construction.callbacks.act state observation result).2.agent) =
      (Agent.callbacks construction.order).act state.agent observation result := rfl

/-- The campaign of one construction. A caller gives the construction and no agent
function: the constructor of the agent is the construction's cold initialization, the two
parts of each step are the construction's callbacks, and the index of those callbacks
selects the loop, so the position of the world's transition is that of the construction's
order. The checkpoint hooks are over the construction's state type. The attempt loops run
only the grid world, by their type, and take each of its transitions as one call of its
step function, which is the discipline of a world that waits, so the campaign takes the
proof that the grid's interface declares `synchronized` (`Grid.interface_timing`): it
cannot be called while that interface declares a wall clock. The general entry
`Host.runCampaign` that it calls takes no such proof, since its module does not import the
module of the grid's interface. -/
def AgentConstruction.runCampaign (construction : AgentConstruction)
    (_ : Grid.interface.timing = .synchronized) (config : Host.WorldConfig)
    (seed : UInt64) (selection : Host.AgentSelection) (spec : Host.CampaignSpec)
    (observer : Host.StreamObserver
      (AgentObservation construction.config construction.dimension))
    (checkpoint : Option (Host.CheckpointHooks construction.State)) (readStop : BaseIO Bool) :
    IO (Except Host.RunnerError (Host.CampaignResult config construction.State)) :=
  Host.runCampaign config seed selection spec (fun _ => IO.lazyPure fun _ => construction.initial)
    construction.callbacks observer checkpoint readStop

/-- A construction of the default step order. The finite-prefix transition folds
`Agent.act`, which is the step of that order, so the prefix operations take this type
only. -/
structure DefaultConstruction where
  /-- The construction. -/
  construction : AgentConstruction
  /-- Its step order is the default one. -/
  default : construction.order = .learnThenAct

/-- The step of the default order is the whole step of a default-order construction: the
second part of its order on the first part's value is `Agent.act`
(`Agent.callbacks_act`). -/
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

/-- A default-order construction reaches every agent that the finite-prefix fold reaches
from an agent it reaches. -/
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

/-- Fold a finite prefix from a state of a default-order construction. The fold is
`Agent.runPrefix`, whose action edge is `Agent.act`, so its type admits a construction
of the default order and no other. The inputs are the agent's own events. -/
def DefaultConstruction.runPrefix (admitted : DefaultConstruction)
    (state : admitted.construction.State)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    admitted.construction.State × Bool :=
  let result := state.agent.runPrefix inputs
  (⟨result.1, admitted.reached_prefix inputs state.reached⟩, result.2)

/-- The prefix of a default-order construction is the agent's own prefix on the learner
state and the same events. -/
theorem DefaultConstruction.runPrefix_agent (admitted : DefaultConstruction)
    (state : admitted.construction.State)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    ((admitted.runPrefix state inputs).1.agent, (admitted.runPrefix state inputs).2) =
      state.agent.runPrefix inputs := rfl

/-- The compiled finite-prefix fold from cold initialization, for a construction of the
default order. It takes the agent's own events. -/
@[noinline] def AgentConstruction.execute (admitted : DefaultConstruction)
    (inputs : List (AgentInput admitted.construction.config admitted.construction.criterion
      admitted.construction.dimension)) :
    admitted.construction.State × Bool :=
  admitted.runPrefix admitted.construction.initial inputs

end Acorn.Handcrafted
