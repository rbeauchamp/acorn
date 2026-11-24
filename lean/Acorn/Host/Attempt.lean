import Acorn.Host.WorldObservation
import Acorn.Host.Metrics
import Acorn.Timing

namespace Acorn.Host

variable {order : StepOrder}

structure AgentCallbacks (order : StepOrder) (α β : Type) where
  Chosen : Type
  choose : α → Observation → RawStepResult → Action × Chosen
  learn : Chosen → α
  recordEnvironment : α → GoalFamily → Binary32 → α
  recordAttempt : α → GoalFamily → UInt64 → UInt64 → Bool → α
  capture : α → β
  metrics : α → LearnerMetrics

def AgentCallbacks.act {α β : Type} (callbacks : AgentCallbacks order α β) (agent : α)
    (observation : Observation) (carried : RawStepResult) : Action × α :=
  let chosen := callbacks.choose agent observation carried
  (chosen.1, callbacks.learn chosen.2)

structure RunState (config : WorldConfig) (α : Type) where
  world : World config
  agent : α
  carried : RawStepResult
  behavior : UInt64

structure GoalContext where
  index : UInt64
  attempt : UInt64
  tier : UInt8
  cycle : UInt64

structure StepFrame (β : Type) where
  worldConfig : WorldConfig
  worldTime : UInt64
  position : Position
  facing : Direction
  energy : Energy
  inventory : Inventory
  observation : Observation
  task : Option Goal
  result : RawStepResult
  action : Action
  agent : β
  goal : GoalContext

def captureFrame {config : WorldConfig} {α β : Type} (callbacks : AgentCallbacks order α β)
    (run : RunState config α) (observation : Observation) (action : Action) (context : GoalContext) :
    StepFrame β :=
  ⟨config, run.world.time, run.world.body.position.position, run.world.body.facing,
    run.world.body.energy, run.world.body.inventory, observation, run.world.goal, run.carried,
    action, callbacks.capture run.agent, context⟩

structure Attempt (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  run : RunState config α
  installed : run.world.goal = some goal
  steps : Fin (cap.toNat + 1)
  reward : Binary32
  lastAction : Action

def Attempt.start {config : WorldConfig} {α : Type} (run : RunState config α)
    (goal : Goal) (cap : UInt64) : Attempt config α goal cap :=
  ⟨{ run with world := run.world.setGoal goal }, rfl, ⟨0, by omega⟩, ⟨0⟩, .wait⟩

theorem Attempt.start_carried {config : WorldConfig} {α : Type} (run : RunState config α)
    (goal : Goal) (cap : UInt64) : (start run goal cap).run.carried = run.carried := rfl

def Attempt.finished {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) : Bool :=
  attempt.steps.val == cap.toNat || (attempt.steps.val != 0 && attempt.run.carried.events.done)

structure PreparedStep (config : WorldConfig) (α β : Type) (goal : Goal) (cap : UInt64) where
  before : Attempt config α goal cap
  remaining : before.steps.val < cap.toNat
  agent : α
  action : Action
  frame : StepFrame β

structure DecisionInput (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  before : Attempt config α goal cap
  remaining : before.steps.val < cap.toNat
  observation : Observation
  sensed : before.run.world.observe = .ok observation

def Attempt.sense {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) : Except WorldError (Option (DecisionInput config α goal cap)) := do
  if attempt.finished then return none
  if hs : attempt.steps.val < cap.toNat then
    match sensed : attempt.run.world.observe with
    | .error error => throw error
    | .ok observation => return some ⟨attempt, hs, observation, sensed⟩
  else return none

structure SelectedStep (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  input : DecisionInput config α goal cap
  action : Action
  agent : α

@[noinline] def DecisionInput.select {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    SelectedStep config α goal cap :=
  let (action, agent) := callbacks.act input.before.run.agent input.observation input.before.run.carried
  ⟨input, action, agent⟩

def SelectedStep.capture {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    PreparedStep config α β goal cap :=
  ⟨selected.input.before, selected.input.remaining, selected.agent, selected.action,
    captureFrame callbacks { selected.input.before.run with agent := selected.agent }
      selected.input.observation selected.action context⟩

def Attempt.prepare {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap) :
    Except WorldError (Option (PreparedStep config α β goal cap)) := do
  return (← attempt.sense).map fun input => (input.select callbacks).capture callbacks context

theorem SelectedStep.capture_agent {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    (selected.capture callbacks context).agent = selected.agent := rfl

theorem DecisionInput.select_result {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    ((input.select callbacks).action, (input.select callbacks).agent) =
      callbacks.act input.before.run.agent input.observation input.before.run.carried := rfl

structure EnvironmentStep (config : WorldConfig) (α β : Type) (goal : Goal) (cap : UInt64) where
  prepared : PreparedStep config α β goal cap
  world : World config
  result : StepResult
  stepped : prepared.before.run.world.step prepared.action = .ok (world, result)

@[noinline] def PreparedStep.environment {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) : Except WorldError (EnvironmentStep config α β goal cap) :=
  match hstep : prepared.before.run.world.step prepared.action with
  | .error error => .error error
  | .ok (world, result) => .ok ⟨prepared, world, result, hstep⟩

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

structure OwnedStep (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  before : Attempt config Unit goal cap
  remaining : before.steps.val < cap.toNat
  observation : Observation
  sensed : before.run.world.observe = .ok observation
  action : Action
  agent : α

def SelectedStep.owned {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) : OwnedStep config α goal cap :=
  let before := selected.input.before
  ⟨⟨⟨before.run.world, (), before.run.carried, before.run.behavior⟩,
    before.installed, before.steps, before.reward, before.lastAction⟩,
    selected.input.remaining, selected.input.observation, selected.input.sensed, selected.action, selected.agent⟩

@[noinline] def DecisionInput.selectOwned {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    OwnedStep config α goal cap :=
  let ⟨⟨⟨world, agent, carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed⟩ := input
  let (action, agent) := callbacks.act agent observation carried
  ⟨⟨⟨world, (), carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed, action, agent⟩

theorem DecisionInput.selectOwned_eq {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    input.selectOwned callbacks = (input.select callbacks).owned := by
  cases input with
  | mk before remaining observation sensed =>
    cases before with
    | mk run installed steps reward lastAction =>
      cases run
      rfl

def OwnedStep.frame {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    StepFrame β :=
  captureFrame callbacks
    ⟨selected.before.run.world, selected.agent, selected.before.run.carried, selected.before.run.behavior⟩
    selected.observation selected.action context

theorem SelectedStep.owned_frame {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    selected.owned.frame callbacks context = (selected.capture callbacks context).frame := rfl

structure OwnedEnvironment (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  selected : OwnedStep config α goal cap
  world : World config
  result : StepResult
  stepped : selected.before.run.world.step selected.action = .ok (world, result)

@[noinline] def OwnedStep.environment {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) : Except WorldError (OwnedEnvironment config α goal cap) :=
  match hstep : selected.before.run.world.step selected.action with
  | .error error => .error error
  | .ok (world, result) => .ok ⟨selected, world, result, hstep⟩

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

theorem SelectedStep.owned_commit {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (selected : SelectedStep config α goal cap) (callbacks : AgentCallbacks order α β) (context : GoalContext) :
    selected.owned.environment.map (fun environment => environment.record callbacks) =
      (selected.capture callbacks context).environment.map (fun environment => environment.record callbacks) := by
  unfold OwnedStep.environment PreparedStep.environment
  simp only [SelectedStep.owned, SelectedStep.capture]
  split <;> rfl

@[noinline] def DecisionInput.chooseOwned {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    OwnedStep config callbacks.Chosen goal cap :=
  let ⟨⟨⟨world, agent, carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed⟩ := input
  let chosen := callbacks.choose agent observation carried
  ⟨⟨⟨world, (), carried, behavior⟩, installed, steps, reward, lastAction⟩,
    remaining, observation, sensed, chosen.1, chosen.2⟩

inductive Released (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  | accepted (environment : OwnedEnvironment config α goal cap)
  | refused (error : WorldError) (selected : OwnedStep config α goal cap)

@[noinline] def OwnedStep.release {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) : Released config α goal cap :=
  match hstep : selected.before.run.world.step selected.action with
  | .error error => .refused error selected
  | .ok (world, result) => .accepted ⟨selected, world, result, hstep⟩

def Released.environment {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (released : Released config α goal cap) : Except WorldError (OwnedEnvironment config α goal cap) :=
  match released with
  | .accepted environment => .ok environment
  | .refused error _ => .error error

theorem OwnedStep.release_environment {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (selected : OwnedStep config α goal cap) :
    selected.release.environment = selected.environment := by
  unfold OwnedStep.release OwnedStep.environment
  split <;> rfl

def OwnedStep.learn {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (selected : OwnedStep config callbacks.Chosen goal cap) :
    OwnedStep config α goal cap :=
  let ⟨before, remaining, observation, sensed, action, chosen⟩ := selected
  ⟨before, remaining, observation, sensed, action, callbacks.learn chosen⟩

@[noinline] def Released.learn {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β)
    (released : Released config callbacks.Chosen goal cap) : Released config α goal cap :=
  match released with
  | .accepted ⟨selected, world, result, stepped⟩ =>
    .accepted ⟨selected.learn callbacks, world, result, stepped⟩
  | .refused error selected => .refused error (selected.learn callbacks)

theorem DecisionInput.chooseOwned_learn {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    (input.chooseOwned callbacks).learn callbacks = input.selectOwned callbacks := by
  cases input with
  | mk before remaining observation sensed =>
    cases before with
    | mk run installed steps reward lastAction =>
      cases run
      rfl

theorem DecisionInput.chooseOwned_release {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    (input.chooseOwned callbacks).release.learn callbacks = (input.selectOwned callbacks).release := by
  rw [← input.chooseOwned_learn callbacks]
  generalize input.chooseOwned callbacks = chosen
  obtain ⟨before, remaining, observation, sensed, action, value⟩ := chosen
  unfold OwnedStep.release
  simp only [OwnedStep.learn]
  split <;> rfl

theorem DecisionInput.chooseOwned_action {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (input : DecisionInput config α goal cap) (callbacks : AgentCallbacks order α β) :
    (input.chooseOwned callbacks).action = (input.selectOwned callbacks).action :=
  congrArg (·.action) (input.chooseOwned_learn callbacks)

def PreparedStep.commit {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (prepared : PreparedStep config α β goal cap) (callbacks : AgentCallbacks order α β) :
    Except WorldError (Attempt config α goal cap) := do
  return (← prepared.environment).record callbacks

def Attempt.tick {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap) :
    Except WorldError (Attempt config α goal cap × Option (StepFrame β)) := do
  match ← attempt.prepare callbacks context with
  | none => return (attempt, none)
  | some prepared => return (← prepared.commit callbacks, some prepared.frame)

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

structure Refusal (config : WorldConfig) (α : Type) (goal : Goal) (cap : UInt64) where
  error : WorldError
  learned : Option (OwnedStep config α goal cap)

def Attempt.close {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt : Attempt config α goal cap) :
    Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β) :=
  match attempt.finish callbacks context with
  | .error error => .error ⟨error, none⟩
  | .ok result => .ok result

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

inductive Attempt.Reaches {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) :
    Nat → Attempt config α goal cap → Attempt config α goal cap → Prop where
  | same (attempt : Attempt config α goal cap) : Attempt.Reaches callbacks 0 attempt attempt
  | pass (passes : Nat) (attempt reached : Attempt config α goal cap)
      (input : DecisionInput config α goal cap) (environment : OwnedEnvironment config α goal cap)
      (unfinished : attempt.finished = false) (sensed : attempt.sense = .ok (some input))
      (accepted : (input.selectOwned callbacks).release = .accepted environment)
      (rest : Attempt.Reaches callbacks passes (environment.record callbacks) reached) :
      Attempt.Reaches callbacks (passes + 1) attempt reached

theorem Attempt.complete_learned {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (fuel : Nat)
    (attempt : Attempt config α goal cap) (error : WorldError)
    (learned : OwnedStep config α goal cap)
    (refused : (attempt.complete callbacks context fuel :
      Except (Refusal config α goal cap) (RunState config α × GoalOutcome × StepFrame β)) =
        .error ⟨error, some learned⟩) :
    ∃ (passes : Nat) (reached : Attempt config α goal cap)
      (input : DecisionInput config α goal cap),
      passes < fuel ∧ Attempt.Reaches callbacks passes attempt reached ∧
        reached.finished = false ∧ reached.sense = .ok (some input) ∧
        learned = input.selectOwned callbacks ∧
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
    · rename_i unfinished
      cases sensed : attempt.sense with
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
            refine ⟨0, attempt, input, Nat.succ_pos fuel, .same attempt,
              Bool.eq_false_iff.mpr unfinished, sensed, ?_, ?_⟩
            · exact (Option.some.inj stages).symm.trans kept
            · rw [← errors]
              exact transition.symm
          | accepted environment =>
            rw [answer] at refused
            obtain ⟨passes, reached, next, bound, reaches, continues, sensedNext, stage,
              transition⟩ := ih _ refused
            exact ⟨passes + 1, reached, next, Nat.succ_lt_succ bound,
              .pass passes attempt reached input environment
                (Bool.eq_false_iff.mpr unfinished) sensed answer reaches,
              continues, sensedNext, stage, transition⟩

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

theorem Attempt.tick_finished {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext) (attempt : Attempt config α goal cap)
    (h : attempt.finished = true) : attempt.tick callbacks context = .ok (attempt, none) := by
  simp [tick, prepare, sense, h, pure, Except.pure, bind, Except.bind]

end Acorn.Host
