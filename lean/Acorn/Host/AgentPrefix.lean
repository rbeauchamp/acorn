import Acorn.Host.AgentInterface

namespace Acorn.Handcrafted
open Features

inductive AgentInput (config : Features.Config) (criterion : Criterion) (dimension : Dimension) where
  | act (observation : Host.Observation) (result : Host.RawStepResult)
  | environment (family : Host.GoalFamily) (reward : Binary32)
  | attempt (family : Host.GoalFamily) (cycle steps : UInt64) (achieved : Bool)
  | clear
  | stop

variable {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}

@[noinline] def Agent.input (state : Agent Grid.interface profile config criterion dimension planning)
    (input : AgentInput config criterion dimension) :
    Agent Grid.interface profile config criterion dimension planning × Bool :=
  match input with
  | .act observation result =>
    ((state.act (Grid.percept profile.taskMode observation result.reward result.events.done)).1,
      false)
  | .environment family reward => (state.recordEnvironment (familyIndex family) reward, false)
  | .attempt family cycle steps achieved =>
    (state.recordAttempt (familyIndex family) cycle steps achieved, false)
  | .clear => (state.clear, false)
  | .stop => (state, true)

def Agent.runPrefix (state : Agent Grid.interface profile config criterion dimension planning) :
    List (AgentInput config criterion dimension) →
      Agent Grid.interface profile config criterion dimension planning × Bool
  | [] => (state, false)
  | event :: rest =>
    let (next, stopped) := state.input event
    if stopped then (next, true) else next.runPrefix rest

theorem Agent.stop_suffix (state : Agent Grid.interface profile config criterion dimension planning)
    (suffix : List (AgentInput config criterion dimension)) :
    state.runPrefix (.stop :: suffix) = (state, true) := rfl

theorem Agent.clear_suffix (state : Agent Grid.interface profile config criterion dimension planning)
    (suffix : List (AgentInput config criterion dimension)) :
    state.runPrefix (.clear :: suffix) =
      (Agent.initial Grid.interface profile config criterion dimension planning).runPrefix suffix := rfl

inductive AgentPath : Agent Grid.interface profile config criterion dimension planning →
    List (AgentInput config criterion dimension) →
      Agent Grid.interface profile config criterion dimension planning → Bool → Prop where
  | nil (state : Agent Grid.interface profile config criterion dimension planning) : AgentPath state [] state false
  | stopped (state next : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion dimension))
      (step : state.input event = (next, true)) : AgentPath state (event :: rest) next true
  | continued (state next finalState : Agent Grid.interface profile config criterion dimension planning)
      (event : AgentInput config criterion dimension) (rest : List (AgentInput config criterion dimension))
      (stopped : Bool) (step : state.input event = (next, false))
      (tail : AgentPath next rest finalState stopped) : AgentPath state (event :: rest) finalState stopped

theorem Agent.prefix_path (state : Agent Grid.interface profile config criterion dimension planning)
    (events : List (AgentInput config criterion dimension)) :
    AgentPath state events (state.runPrefix events).1 (state.runPrefix events).2 := by
  induction events generalizing state with
  | nil => exact .nil state
  | cons event rest ih =>
    cases step : state.input event with
    | mk next stop =>
      cases stop with
      | true =>
        have folded : state.runPrefix (event :: rest) = (next, true) := by
          simp only [Agent.runPrefix, step, ↓reduceIte]
        rw [folded]
        exact .stopped state next event rest step
      | false =>
        have folded : state.runPrefix (event :: rest) = next.runPrefix rest := by
          simp only [Agent.runPrefix, step, Bool.false_eq_true, ↓reduceIte]
        rw [folded]
        exact .continued state next _ event rest _ step (ih next)

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

theorem Agent.retire_decision {interface : Interface}
    (state : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (state.retire active).control.runtime.references.lastDecision =
      state.control.runtime.references.lastDecision := by
  unfold Agent.retire
  split
  · rfl
  · exact congrArg (·.lastDecision) (state.control.runtime.retire_references active)

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

theorem Agent.act_decision (state : Agent Grid.interface profile config criterion dimension planning)
    (percept : Percept Grid.interface) :
    (state.act percept).1.observe.decision = some (state.act percept).2 :=
  state.act_recorded percept

end Acorn.Handcrafted
