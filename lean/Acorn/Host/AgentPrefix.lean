/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentInterface

/-!
# Finite current-agent input prefixes

Every action input is a grid observation and the preceding raw result, delivered to
the agent as one percept of the grid interface; encoding is derived by the receiving
agent. Prefixes use these same public
operations. A stop is an attempt-boundary event supplied by the host protocol,
not an action-selection input. No prefix is stored in the agent.
-/
namespace Acorn.Handcrafted
open Features

/-- Complete pure public event domain; filesystem and telemetry delivery are external. -/
inductive AgentInput (config : Features.Config) (criterion : Criterion) (dimension : Dimension) where
  /-- One decision from the current external observation and previous environment result. -/
  | act (observation : Host.Observation) (result : Host.RawStepResult)
  /-- Account for the environment result after executing the chosen primitive. -/
  | environment (family : Host.GoalFamily) (reward : Binary32)
  /-- Complete an attempt, preserving the continuing stream. -/
  | attempt (family : Host.GoalFamily) (cycle steps : UInt64) (achieved : Bool)
  /-- Explicit fresh construction. -/
  | clear
  /-- Install an admitted image under profile refusal. -/
  | restore (image : AgentImage Grid.interface config criterion dimension)
  /-- Host has reached an admitted stop boundary. -/
  | stop

/-- The only pure full-agent refusal: incompatible restoration profile. -/
inductive AgentRefusal where
  /-- Current image representation is unsupported for this profile. -/
  | unsupportedProfile
  deriving DecidableEq

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

/-- A current event returns one replacement state and whether the stream was stopped. -/
@[noinline] def Agent.input (state : Agent Grid.interface profile config criterion dimension planning)
    (input : AgentInput config criterion dimension) :
    Except AgentRefusal (Agent Grid.interface profile config criterion dimension planning × Bool) :=
  match input with
  | .act observation result =>
    .ok ((state.act (Grid.percept profile.taskMode observation result.reward result.events.done)).1,
      false)
  | .environment family reward => .ok (state.recordEnvironment (familyIndex family) reward, false)
  | .attempt family cycle steps achieved =>
    .ok (state.recordAttempt (familyIndex family) cycle steps achieved, false)
  | .clear => .ok (state.clear, false)
  | .restore image => match state.restore image with
    | none => .error .unsupportedProfile
    | some next => .ok (next, false)
  | .stop => .ok (state, true)

/-- Fold exactly the public event operation, stopping at the first refusal or stop. -/
def Agent.runPrefix (state : Agent Grid.interface profile config criterion dimension planning) :
    List (AgentInput config criterion dimension) →
      Except AgentRefusal (Agent Grid.interface profile config criterion dimension planning × Bool)
  | [] => .ok (state, false)
  | event :: rest => do
    let (next, stopped) ← state.input event
    if stopped then return (next, true) else next.runPrefix rest

/-- A pure stop retains all current knowledge and prevents every suffix action. -/
theorem Agent.stop_suffix (state : Agent Grid.interface profile config criterion dimension planning)
    (suffix : List (AgentInput config criterion dimension)) :
    state.runPrefix (.stop :: suffix) = .ok (state, true) := rfl

/-- A clear at any boundary begins the suffix with the same complete cold constructor. -/
theorem Agent.clear_suffix (state : Agent Grid.interface profile config criterion dimension planning)
    (suffix : List (AgentInput config criterion dimension)) :
    state.runPrefix (.clear :: suffix) =
      (Agent.initial Grid.interface profile config criterion dimension planning).runPrefix suffix := rfl

/-- Each observed endpoint is reached by the actual input operation, with no internal oracle. -/
inductive AgentPath : Agent Grid.interface profile config criterion dimension planning →
    List (AgentInput config criterion dimension) →
      Agent Grid.interface profile config criterion dimension planning → Bool → Prop where
  /-- Empty input has no hidden update. -/
  | nil (state : Agent Grid.interface profile config criterion dimension planning) : AgentPath state [] state false
  /-- A stop or refusal cannot be skipped by the recursive continuation. -/
  | stopped (state next : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion dimension))
      (step : state.input event = .ok (next, true)) : AgentPath state (event :: rest) next true
  /-- A continuing step consumes exactly its actual receiver. -/
  | continued (state next finalState : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion dimension))
      (stopped : Bool) (step : state.input event = .ok (next, false))
      (tail : AgentPath next rest finalState stopped) : AgentPath state (event :: rest) finalState stopped

/-- Arbitrary finite prefixes compose those same input edges; there is no replay in storage. -/
theorem Agent.prefix_path (state finalState : Agent Grid.interface profile config criterion dimension planning)
    (events : List (AgentInput config criterion dimension)) (stopped : Bool)
    (executed : state.runPrefix events = .ok (finalState, stopped)) :
    AgentPath state events finalState stopped := by
  induction events generalizing state with
  | nil =>
    cases executed
    exact .nil finalState
  | cons event rest ih =>
    simp only [Agent.runPrefix] at executed
    cases step : state.input event with
    | error error => simp [step, bind, Except.bind] at executed
    | ok result =>
      rcases result with ⟨next, stop⟩
      cases stop with
      | true =>
        simp only [step, bind, Except.bind, pure, Except.pure, ↓reduceIte, Except.ok.injEq,
          Prod.mk.injEq] at executed
        rcases executed with ⟨rfl, rfl⟩
        exact .stopped state next event rest step
      | false =>
        simp only [step, bind, Except.bind, Bool.false_eq_true, ↓reduceIte] at executed
        exact .continued state next finalState event rest stopped step (ih next executed)

/-- The action and replacement are obtained from the same composed local transition,
using the old feedback cache, the current bank, and the once-advanced clock, in every
world. -/
theorem Agent.act_execution {interface : Interface}
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    ∃ (next : TemporalControl interface profile config criterion dimension) (valid : next.Aligned)
      (episodes : next.Episodes),
      state.advanceClock.control.step planning (state.advanceClock.frame percept.frame).active
        percept.frame percept.reward percept.frame.achieved = some (next, (state.act percept).2) ∧
      (state.act percept).1 =
        (Agent.mk next valid episodes).retire (state.advanceClock.frame percept.frame).units := by
  let result := state.advanceClock.control.alignedStep state.advanceClock.aligned planning
    (state.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved
  exact ⟨result.1.1, result.2.2, state.advanceClock.control.step_episodes result.1.1
    state.advanceClock.episodes planning (state.advanceClock.frame percept.frame).active
      percept.frame percept.reward percept.frame.achieved result.1.2 result.2.1, result.2.1, rfl⟩

/-- The tester cannot detach the observation from the decision just credited. -/
theorem Agent.retire_decision {interface : Interface}
    (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (state.retire active).control.runtime.references.lastDecision =
      state.control.runtime.references.lastDecision := by
  unfold Agent.retire
  split
  · rfl
  · exact congrArg (·.lastDecision) (state.control.runtime.retire_references active)

/-- In every world the stored last decision is precisely the decision consumed by the
completion boundary. -/
theorem Agent.act_recorded {interface : Interface}
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (state.act percept).1.control.runtime.references.lastDecision = some (state.act percept).2 := by
  obtain ⟨next, valid, episodes, step, actual⟩ := state.act_execution percept
  rw [actual, Agent.retire_decision]
  unfold TemporalControl.step at step
  cases selected : state.advanceClock.control.select planning
      (state.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
      percept.frame.achieved with
  | none => simp [selected] at step
  | some selection =>
    simp only [selected, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at step
    rcases step with ⟨rfl, decision⟩
    exact congrArg some decision

/-- Every action observer sees precisely the decision consumed by the completion boundary. -/
theorem Agent.act_decision (state : Agent Grid.interface profile config criterion dimension planning)
    (percept : Percept Grid.interface) :
    (state.act percept).1.observe.decision = some (state.act percept).2 :=
  state.act_recorded percept

end Acorn.Handcrafted
