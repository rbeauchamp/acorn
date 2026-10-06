/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldObservation
import Acorn.Host.Metrics
import Acorn.Timing

/-!
# Streaming attempt protocol

The agent is an explicit typed callback, supplied by its composition owner.
No substitute learner or scripted policy is installed here. A step observes,
calls the agent with the carried raw result, captures the pre-environment frame,
executes the world, and records the environment result. Only current state is
retained. Supervision has no parameter on this action-selection path.

The agent's step has two parts: `choose` selects the action, and `learn` completes
the step from the value `choose` returned with it. `AgentCallbacks.act` is both parts
before the world's transition. `DecisionInput.chooseOwned`, `OwnedStep.release` and
`Released.learn` put the world's transition between the parts. The world of
this protocol takes one transition for each action and waits for it, so one pass
releases the same action and ends in the same stage either way, on acceptance and on
a refusal: `DecisionInput.chooseOwned_action` and `DecisionInput.chooseOwned_release`.
`Attempt.complete` is the pure fold of passes that both native loops compute.
-/
namespace Acorn.Host

variable {order : StepOrder}

/-- The full-agent owner supplies actual learning and accounting definitions. The step
order is an index of the type: a host loop takes the callbacks of the order whose
position of the world's transition it implements. The index is a label, and no field
depends on it: a record is of its order because of the code that made it. The ownership
audit names the modules that may apply the constructor and refuses it elsewhere in this
project. -/
structure AgentCallbacks (order : StepOrder) (α β : Type) where
  /-- What the agent holds between the two parts of one step. -/
  Chosen : Type
  /-- First part: from the observation and the carried result, select one legal world
  action, and return it with the value the second part completes the step from. -/
  choose : α → Observation → RawStepResult → Action × Chosen
  /-- Second part: complete the step from the value the first part returned. It
  receives no other input. -/
  learn : Chosen → α
  /-- Record the completed world transition after action selection. -/
  recordEnvironment : α → GoalFamily → Binary32 → α
  /-- Record the completed attempt after final observation. -/
  recordAttempt : α → GoalFamily → UInt64 → UInt64 → Bool → α
  /-- Immutable one-way observer snapshot. -/
  capture : α → β
  /-- Terminal scalar observations. -/
  metrics : α → LearnerMetrics

/-- One whole step before any world transition: the first part, then the second on the
value the first returned. The result is the selected action and the learned agent. -/
def AgentCallbacks.act {α β : Type} (callbacks : AgentCallbacks order α β) (agent : α)
    (observation : Observation) (carried : RawStepResult) : Action × α :=
  let chosen := callbacks.choose agent observation carried
  (chosen.1, callbacks.learn chosen.2)

/-- One continual stream's current state survives every attempt boundary. -/
structure RunState (config : WorldConfig) (α : Type) where
  /-- Current physical environment. -/
  world : World config
  /-- Current legal agent value, owned by the supplied callback type. -/
  agent : α
  /-- Raw previous transition, including terminal rewards. -/
  carried : RawStepResult
  /-- Current action fingerprint. -/
  behavior : UInt64

/-- Attempt metadata copied into outcomes and observer records. -/
structure GoalContext where
  /-- Effective curriculum position. -/
  index : UInt64
  /-- Exact within-goal attempt number in the admitted campaign word domain. -/
  attempt : UInt64
  /-- Difficulty tier. -/
  tier : UInt8
  /-- Saturating campaign cycle number. -/
  cycle : UInt64

/-- Observer data is a value; an observer has no return channel into the agent. -/
structure StepFrame (β : Type) where
  /-- The actual world's immutable admitted configuration. -/
  worldConfig : WorldConfig
  /-- Clock before this action, or at the terminal observation. -/
  worldTime : UInt64
  /-- Body location corresponding to the sensor window. -/
  position : Position
  /-- Body facing. -/
  facing : Direction
  /-- Exact energy in tenths. -/
  energy : Energy
  /-- Inventory at capture time. -/
  inventory : Inventory
  /-- Sensor window and complete task relation. -/
  observation : Observation
  /-- Original installed task, including absolute target and requested quantity. -/
  task : Option Goal
  /-- Result the learner consumed, or the final carried result. -/
  result : RawStepResult
  /-- Chosen action; the terminal frame retains the last action, initially wait. -/
  action : Action
  /-- Agent snapshot from the actual capture point. -/
  agent : β
  /-- Attempt metadata. -/
  goal : GoalContext

/-- Frame construction reads one physical state for every world field. -/
def captureFrame {config : WorldConfig} {α β : Type} (callbacks : AgentCallbacks order α β)
    (run : RunState config α) (observation : Observation) (action : Action) (context : GoalContext) :
    StepFrame β :=
  ⟨config, run.world.time, run.world.body.position.position, run.world.body.facing,
    run.world.body.energy, run.world.body.inventory, observation, run.world.goal, run.carried,
    action, callbacks.capture run.agent, context⟩

/-- The current attempt carries its exact cap and installed task invariant. -/
structure Attempt (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- Current stream state. -/
  run : RunState config α
  /-- No callback or world transition can silently replace this attempt's goal. -/
  installed : run.world.goal = some goal
  /-- Actual steps cannot exceed the admitted cap. -/
  steps : Fin (cap.toNat + 1)
  /-- Ordered machine reward sum, initially zero. -/
  reward : Binary32
  /-- Last action, initially wait even for an empty attempt. -/
  lastAction : Action

/-- Goal installation preserves both the agent and the previous raw result. -/
def Attempt.start {config : WorldConfig} {α : Type} (run : RunState config α)
    (goal : Goal) (cap : UInt64) : Attempt config α goal cap :=
  ⟨{ run with world := run.world.setGoal goal }, rfl, ⟨0, by omega⟩, ⟨0⟩, .wait⟩

/-- No terminal reward is dropped at an attempt boundary. -/
theorem Attempt.start_carried {config : WorldConfig} {α : Type} (run : RunState config α)
    (goal : Goal) (cap : UInt64) : (start run goal cap).run.carried = run.carried := rfl

/-- A carried terminal flag does not end a new nonempty attempt before its first action. -/
def Attempt.finished {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) : Bool :=
  attempt.steps.val == cap.toNat || (attempt.steps.val != 0 && attempt.run.carried.events.done)

/-- Selection phase retains the pre-environment stream and remaining step capacity. -/
structure PreparedStep (config : WorldConfig) (α β : Type) (goal : Goal) (cap : UInt64) where
  /-- Attempt before action selection. -/
  before : Attempt config α goal cap
  /-- Admission guarantees space for the transition. -/
  remaining : before.steps.val < cap.toNat
  /-- Agent after consuming the previous transition. -/
  agent : α
  /-- Actual selected primitive. -/
  action : Action
  /-- Immutable pre-environment observer frame. -/
  frame : StepFrame β

/-- Admitted perception at the actual pre-action world state. -/
structure DecisionInput (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- Unchanged attempt owning the next action. -/
  before : Attempt config α goal cap
  /-- Space for precisely one further environment transition. -/
  remaining : before.steps.val < cap.toNat
  /-- Actual world observation. -/
  observation : Observation
  /-- Perception is linked to this attempt, rather than supplied independently. -/
  sensed : before.run.world.observe = .ok observation

/-- Sense before measuring the learner update; finished attempts select no action. -/
def Attempt.sense {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) : Except WorldError (Option (DecisionInput config α goal cap)) := do
  if attempt.finished then return none
  if hs : attempt.steps.val < cap.toNat then
    match sensed : attempt.run.world.observe with
    | .error error => throw error
    | .ok observation => return some ⟨attempt, hs, observation, sensed⟩
  else return none

/-- The actual learner result, before observer diagnostics are captured. -/
structure SelectedStep (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- Admitted pre-action input. -/
  input : DecisionInput config α goal cap
  /-- Primitive produced by the actual callback. -/
  action : Action
  /-- Agent after that callback, before any world transition. -/
  agent : α

/-- Execute only action selection and learning; native timing surrounds this same call. -/
@[noinline] def DecisionInput.select {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    SelectedStep config α goal cap :=
  let (action, agent) := callbacks.act input.before.run.agent input.observation input.before.run.carried
  ⟨input, action, agent⟩

/-- Capture diagnostics after selection without running the learner again. -/
def SelectedStep.capture {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    PreparedStep config α β goal cap :=
  ⟨selected.input.before, selected.input.remaining, selected.agent, selected.action,
    captureFrame callbacks { selected.input.before.run with agent := selected.agent }
      selected.input.observation selected.action context⟩

/-- Preparation composes the same perception, learner and capture owners used by native IO. -/
def Attempt.prepare {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap) :
    Except WorldError (Option (PreparedStep config α β goal cap)) := do
  return (← attempt.sense).map fun input => (input.select callbacks).capture callbacks context

/-- Capturing a selected step preserves its exact post-learning agent. -/
theorem SelectedStep.capture_agent {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    (selected.capture callbacks context).agent = selected.agent := rfl

/-- The measured selection call is precisely the actual callback result. -/
theorem DecisionInput.select_result {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    ((input.select callbacks).action, (input.select callbacks).agent) =
      callbacks.act input.before.run.agent input.observation input.before.run.carried := rfl

/-- One actual environment result, before lifetime bookkeeping. -/
structure EnvironmentStep (config : WorldConfig) (α β : Type) (goal : Goal) (cap : UInt64) where
  /-- Prepared action whose observation was already published. -/
  prepared : PreparedStep config α β goal cap
  /-- Actual resulting world. -/
  world : World config
  /-- Actual resulting events. -/
  result : StepResult
  /-- Result belongs to the executed world transition. -/
  stepped : prepared.before.run.world.step prepared.action = .ok (world, result)

/-- Execute only the world transition so its duration excludes lifetime bookkeeping. -/
@[noinline] def PreparedStep.environment {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) : Except WorldError (EnvironmentStep config α β goal cap) :=
  match hstep : prepared.before.run.world.step prepared.action with
  | .error error => .error error
  | .ok (world, result) => .ok ⟨prepared, world, result, hstep⟩

/-- Record the actual environment result without stepping the world a second time. -/
def EnvironmentStep.record {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (environment : EnvironmentStep config α β goal cap) (callbacks : AgentCallbacks order α β) :
    Attempt config α goal cap := Id.run do
  let prepared := environment.prepared
  let attempt := prepared.before
  let world := environment.world
  let result := environment.result
    let run := { attempt.run with
      world := world
      agent := callbacks.recordEnvironment prepared.agent goal.family result.reward
      behavior := foldAction attempt.run.behavior prepared.action
      carried := result.raw }
    return {
      run := run
      installed := (World.step_goal attempt.run.world world prepared.action result environment.stepped).1.trans attempt.installed
      steps := ⟨attempt.steps.val + 1, by have := prepared.remaining; dsimp [attempt]; omega⟩
      reward := attempt.reward.add result.reward
      lastAction := prepared.action }

/-- Runtime selection retains the pre-action world and attempt metadata, but
has no slot capable of retaining the consumed pre-action agent. -/
structure OwnedStep (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- Agent-free pre-action attempt. -/
  before : Attempt config Unit goal cap
  /-- Space for the actual environment transition. -/
  remaining : before.steps.val < cap.toNat
  /-- Actual sensed observation. -/
  observation : Observation
  /-- Perception belongs to the retained pre-action world. -/
  sensed : before.run.world.observe = .ok observation
  /-- Actual selected primitive. -/
  action : Action
  /-- Sole agent value retained by this runtime stage. -/
  agent : α

/-- Forget only the unused old agent in the reference protocol. -/
def SelectedStep.owned {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) : OwnedStep config α goal cap :=
  let before := selected.input.before
  ⟨⟨⟨before.run.world, (), before.run.carried, before.run.behavior⟩,
    before.installed, before.steps, before.reward, before.lastAction⟩,
    selected.input.remaining, selected.input.observation, selected.input.sensed, selected.action, selected.agent⟩

/-- Consume the old agent before its callback, retaining only the independent
world and attempt fields needed after the callback returns. -/
@[noinline] def DecisionInput.selectOwned {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    OwnedStep config α goal cap :=
  let ⟨⟨⟨world, agent, carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed⟩ := input
  let (action, agent) := callbacks.act agent observation carried
  ⟨⟨⟨world, (), carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed, action, agent⟩

/-- Runtime selection is the exact projection of the reference callback result,
for every callback and input; no old-agent observer is retained. -/
theorem DecisionInput.selectOwned_eq {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    input.selectOwned callbacks = (input.select callbacks).owned := by
  cases input with
  | mk before remaining observation sensed =>
    cases before with
    | mk run installed steps reward lastAction =>
      cases run
      rfl

/-- Capture remains the same pre-environment observation when a consumer requests it. -/
def OwnedStep.frame {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    StepFrame β :=
  captureFrame callbacks
    ⟨selected.before.run.world, selected.agent, selected.before.run.carried, selected.before.run.behavior⟩
    selected.observation selected.action context

/-- Every observer field agrees with the reference capture, including the actual
post-learning agent snapshot and pre-environment world. -/
theorem SelectedStep.owned_frame {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    selected.owned.frame callbacks context = (selected.capture callbacks context).frame := rfl

/-- The actual world transition retains no obsolete agent or diagnostic snapshot. -/
structure OwnedEnvironment (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- Current selected action and agent-free preceding world. -/
  selected : OwnedStep config α goal cap
  /-- Actual resulting world. -/
  world : World config
  /-- Actual resulting events. -/
  result : StepResult
  /-- The stored result belongs to the selected environment transition. -/
  stepped : selected.before.run.world.step selected.action = .ok (world, result)

/-- Time only the same world transition, before environment bookkeeping. -/
@[noinline] def OwnedStep.environment {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) : Except WorldError (OwnedEnvironment config α goal cap) :=
  match hstep : selected.before.run.world.step selected.action with
  | .error error => .error error
  | .ok (world, result) => .ok ⟨selected, world, result, hstep⟩

/-- Record the same ordered reward, action fingerprint, lifetime event and installed goal. -/
def OwnedEnvironment.record {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (environment : OwnedEnvironment config α goal cap) (callbacks : AgentCallbacks order α β) :
    Attempt config α goal cap :=
  let selected := environment.selected
  let before := selected.before
  let world := environment.world
  let result := environment.result
  ⟨⟨world, callbacks.recordEnvironment selected.agent goal.family result.reward,
      result.raw, foldAction before.run.behavior selected.action⟩,
    (World.step_goal before.run.world world selected.action result environment.stepped).1.trans before.installed,
    ⟨before.steps.val + 1, by have := selected.remaining; dsimp [before]; omega⟩,
    before.reward.add result.reward, selected.action⟩

/-- Complete committed state and every refusal agree with the reference environment
and bookkeeping, for every selected step and callback. -/
theorem SelectedStep.owned_commit {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    selected.owned.environment.map (fun environment => environment.record callbacks) =
      (selected.capture callbacks context).environment.map (fun environment => environment.record callbacks) := by
  unfold OwnedStep.environment PreparedStep.environment
  simp only [SelectedStep.owned, SelectedStep.capture]
  split <;> rfl

/-- Selection for a host that releases the action between the two parts: run the first
part only. The stage holds the chosen value where the stage of
`DecisionInput.selectOwned` holds the learned agent, so the world can take its
transition on the action before the second part runs. The old agent is consumed
before the callback, as in `DecisionInput.selectOwned`. -/
@[noinline] def DecisionInput.chooseOwned {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    OwnedStep config callbacks.Chosen goal cap :=
  let ⟨⟨⟨world, agent, carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed⟩ := input
  let chosen := callbacks.choose agent observation carried
  ⟨⟨⟨world, (), carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed, chosen.1, chosen.2⟩

/-- The world's answer to a released action. Both answers keep the stage the action
was released from, so the value that stage holds is never dropped: a refusal returns
it with the refusal. -/
inductive Released (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- The world took the transition. -/
  | accepted (environment : OwnedEnvironment config α goal cap)
  /-- The world refused the action; the stage is unchanged. -/
  | refused (error : WorldError) (selected : OwnedStep config α goal cap)

/-- Release the action of a stage to the world: the same transition as
`OwnedStep.environment`, with the stage kept on a refusal. -/
@[noinline] def OwnedStep.release {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) : Released config α goal cap :=
  match hstep : selected.before.run.world.step selected.action with
  | .error error => .refused error selected
  | .ok (world, result) => .accepted ⟨selected, world, result, hstep⟩

/-- The transition result of a release, without the stage a refusal keeps. -/
def Released.environment {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (released : Released config α goal cap) : Except WorldError (OwnedEnvironment config α goal cap) :=
  match released with
  | .accepted environment => .ok environment
  | .refused error _ => .error error

/-- A release is the transition of `OwnedStep.environment`, for every stage. -/
theorem OwnedStep.release_environment {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) :
    selected.release.environment = selected.environment := by
  unfold OwnedStep.release OwnedStep.environment
  split <;> rfl

/-- The second part on a stage: complete the step from the chosen value the stage
holds. The pre-action attempt, the observation and the action are untouched. -/
def OwnedStep.learn {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (selected : OwnedStep config callbacks.Chosen goal cap) :
    OwnedStep config α goal cap :=
  let ⟨before, remaining, observation, sensed, action, chosen⟩ := selected
  ⟨before, remaining, observation, sensed, action, callbacks.learn chosen⟩

/-- The second part, after the world's answer, on both answers: complete the step from
the chosen value. The transition, its result and a refusal are untouched. -/
@[noinline] def Released.learn {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β)
    (released : Released config callbacks.Chosen goal cap) : Released config α goal cap :=
  match released with
  | .accepted ⟨selected, world, result, stepped⟩ =>
    .accepted ⟨selected.learn callbacks, world, result, stepped⟩
  | .refused error selected => .refused error (selected.learn callbacks)

/-- The first part followed by the second on its result is the whole step: the stage of
`DecisionInput.selectOwned`, for every callback and input. -/
theorem DecisionInput.chooseOwned_learn {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    (input.chooseOwned callbacks).learn callbacks = input.selectOwned callbacks := by
  cases input with
  | mk before remaining observation sensed =>
    cases before with
    | mk run installed steps reward lastAction =>
      cases run
      rfl

/-- **One pass is the same in both positions of the world's transition, on every
answer.** For every callback and input, releasing the action between the two parts and
then learning gives what both parts followed by the release give: on acceptance the
same committed stage, and on a refusal the same refusal with the same learned stage.
The second part therefore runs exactly once on the pass's own observation and carried
result, whether the world accepts or refuses. The world of this protocol takes one
transition for each action and waits for it; the equality is a statement about one
pass in such a world. -/
theorem DecisionInput.chooseOwned_release {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    (input.chooseOwned callbacks).release.learn callbacks = (input.selectOwned callbacks).release := by
  rw [← input.chooseOwned_learn callbacks]
  generalize input.chooseOwned callbacks = chosen
  obtain ⟨before, remaining, observation, sensed, action, value⟩ := chosen
  unfold OwnedStep.release
  simp only [OwnedStep.learn]
  split <;> rfl

/-- The action released between the two parts is the action of the whole step. -/
theorem DecisionInput.chooseOwned_action {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    (input.chooseOwned callbacks).action = (input.selectOwned callbacks).action :=
  congrArg (·.action) (input.chooseOwned_learn callbacks)

/-- Commit composes the same transition and bookkeeping owners used by native IO. -/
def PreparedStep.commit {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) (callbacks : AgentCallbacks order α β) :
    Except WorldError (Attempt config α goal cap) := do
  return (← prepared.environment).record callbacks

/-- Pure combined transition for consumers with no effectful step observer. -/
def Attempt.tick {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap) :
    Except WorldError (Attempt config α goal cap × Option (StepFrame β)) := do
  match ← attempt.prepare callbacks context with
  | none => return (attempt, none)
  | some prepared => return (← prepared.commit callbacks, some prepared.frame)

/-- Finalization returns the current stream, its outcome, and a freshly observed terminal frame. -/
def Attempt.finish {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap) :
    Except WorldError (RunState config α × GoalOutcome × StepFrame β) := do
  let observation ← attempt.run.world.observe
  let achieved := attempt.run.carried.events.done
  let steps := attempt.steps.val.toUInt64
  let agent := callbacks.recordAttempt attempt.run.agent goal.family context.cycle steps achieved
  let run := { attempt.run with agent := agent }
  let frame := captureFrame callbacks run observation attempt.lastAction context
  let outcome : GoalOutcome :=
    ⟨context.index, context.attempt, context.tier, steps, achieved, attempt.reward, callbacks.metrics agent,
      attempt.run.world.body.position.position⟩
  return (run, outcome, frame)

/-- A refusal that ends an attempt. `learned` is the stage of the refused pass after its
second part: it is present when the world refused an action, and absent when the world
refused an observation, before a pass or at the end of the attempt. A campaign reports
the error alone; the stage is what the correspondence of the native loops fixes. -/
structure Refusal (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  /-- The world's refusal. -/
  error : WorldError
  /-- The learned stage of the refused pass, for a refused action. -/
  learned : Option (OwnedStep config α goal cap)

/-- The final observation and bookkeeping of an attempt, with a refused observation as a
refusal that holds no stage. -/
def Attempt.close {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt : Attempt config α goal cap) :
    Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β) :=
  match attempt.finish callbacks context with
  | .error error => .error ⟨error, none⟩
  | .ok result => .ok result

/-- The pure content of a whole attempt: passes of the whole step, in order, until the
attempt finishes or the world refuses, then the final observation and bookkeeping.
Every value either native loop returns agrees with this fold, whichever side of the
world's transition the second part runs on (`runAttempt_complete`). A refused action
ends the fold with the stage of that pass after the whole step, the first part and
then the second, applied once to the pass's own observation and carried result. -/
def Attempt.complete {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    Nat → Attempt config α goal cap →
      Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β)
  | 0, attempt => attempt.close callbacks context
  | fuel + 1, attempt =>
    if attempt.finished then attempt.close callbacks context else
      match attempt.sense with
      | .error error => .error ⟨error, none⟩
      | .ok none => attempt.close callbacks context
      | .ok (some input) =>
        match (input.selectOwned callbacks).release with
        | .refused error learned => .error ⟨error, some learned⟩
        | .accepted environment =>
          Attempt.complete callbacks context fuel (environment.record callbacks)

/-- **The stage a refused action leaves is the stage of one whole step.** For every
callback, fuel and attempt: when the fold ends in a refusal that holds a stage, an
attempt of the fold sensed an input, the stage is the whole step on that input, and
the world refused the action of that step. A refusal that holds no stage is a refused
observation. -/
theorem Attempt.complete_learned {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (fuel : Nat)
    (attempt : Attempt config α goal cap) (error : WorldError)
    (learned : OwnedStep config α goal cap)
    (refused : (attempt.complete callbacks context fuel :
      Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β)) =
        .error ⟨error, some learned⟩) :
    ∃ (reached : Attempt config α goal cap) (input : DecisionInput config α goal cap),
      reached.sense = .ok (some input) ∧ learned = input.selectOwned callbacks ∧
        (input.selectOwned callbacks).environment = .error error := by
  have closed : ∀ current : Attempt config α goal cap,
      (current.close callbacks context :
        Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β)) ≠
          .error ⟨error, some learned⟩ := by
    intro current same
    unfold Attempt.close at same
    split at same <;> cases same
  induction fuel generalizing attempt with
  | zero =>
    unfold Attempt.complete at refused
    exact (closed attempt refused).elim
  | succ fuel ih =>
    unfold Attempt.complete at refused
    split at refused
    · exact (closed attempt refused).elim
    · cases sensed : attempt.sense with
      | error other =>
        rw [sensed] at refused
        cases refused
      | ok found =>
        cases found with
        | none =>
          rw [sensed] at refused
          exact (closed attempt refused).elim
        | some input =>
          rw [sensed] at refused
          dsimp only at refused
          cases answer : (input.selectOwned callbacks).release with
          | refused other stage =>
            rw [answer] at refused
            have same := Except.error.inj refused
            have errors : other = error := congrArg Refusal.error same
            have stages : some stage = some learned := congrArg Refusal.learned same
            have transition := (input.selectOwned callbacks).release_environment
            rw [answer] at transition
            have kept : stage = input.selectOwned callbacks := by
              unfold OwnedStep.release at answer
              split at answer
              · cases answer
                rfl
              · cases answer
            refine ⟨attempt, input, sensed, ?_, ?_⟩
            · exact (Option.some.inj stages).symm.trans kept
            · rw [← errors]
              exact transition.symm
          | accepted environment =>
            rw [answer] at refused
            exact ih _ refused

/-- The stream that continues past an attempt boundary is the attempt's own run
with the attempt recorded, for every callback: no outcome row is an input to it.
The row's position is that stream's body position, the one the terminal frame shows. -/
theorem Attempt.finish_position {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap)
    (run : RunState config α) (outcome : GoalOutcome) (frame : StepFrame β)
    (h : attempt.finish callbacks context = .ok (run, outcome, frame)) :
    run = { attempt.run with agent := (callbacks.recordAttempt attempt.run.agent goal.family
        context.cycle attempt.steps.val.toUInt64 attempt.run.carried.events.done) } ∧
      outcome.position = run.world.body.position.position ∧ frame.position = outcome.position := by
  unfold Attempt.finish at h
  cases sensed : attempt.run.world.observe with
  | error refusal => simp [sensed, bind, Except.bind] at h
  | ok observation =>
    simp only [sensed, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- A stopped attempt cannot execute another action through its public tick entry. -/
theorem Attempt.tick_finished {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap)
    (h : attempt.finished = true) : attempt.tick callbacks context = .ok (attempt, none) := by
  simp [tick, prepare, sense, h, pure, Except.pure, bind, Except.bind]

end Acorn.Host
