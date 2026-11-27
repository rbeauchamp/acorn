import Acorn.Host.Cli
import Acorn.Host.Forever

namespace Acorn.Host

structure AnsiState (config : WorldConfig) (α : Type) where
  world : World config
  agent : α
  carried : RawStepResult
  observation : Observation
  steps : UInt64

structure AnsiFrame (config : WorldConfig) where
  observation : Observation
  world : World config
  result : StepResult
  action : Action
  steps : UInt64
  goalIndex : Nat

def AnsiState.tick {config : WorldConfig} {α β : Type} (state : AnsiState config α)
    (callbacks : AgentCallbacks .learnThenAct α β) (goalIndex : Nat) :
    Except RunnerError (AnsiState config α × AnsiFrame config) := do
  let (action, agent) := callbacks.act state.agent state.observation state.carried
  let (world, result) ← (state.world.step action).mapError RunnerError.world
  let some steps := Word.advanceClock state.steps 1 | .error (.metric .totalStepsOverflow)
  let next := { state with world := world, agent := agent, carried := result.raw, steps := steps }
  return (next, ⟨state.observation, world, result, action, steps, goalIndex⟩)

def AnsiState.refresh {config : WorldConfig} {α : Type} (state : AnsiState config α) :
    Except RunnerError (AnsiState config α) := do
  let observation ← state.world.observe |>.mapError RunnerError.world
  return { state with observation := observation }

theorem AnsiState.tick_observation {config : WorldConfig} {α β : Type}
    (state next : AnsiState config α) (callbacks : AgentCallbacks .learnThenAct α β) (index : Nat)
    (frame : AnsiFrame config) (h : state.tick callbacks index = .ok (next, frame)) :
    next.observation = state.observation := by
  unfold tick at h
  cases hw : state.world.step (callbacks.act state.agent state.observation state.carried).1 with
  | error error => simp [hw, Except.mapError, bind, Except.bind] at h
  | ok pair =>
    simp only [hw, Except.mapError, bind, Except.bind] at h
    cases hs : Word.advanceClock state.steps 1 with
    | none => simp [hs] at h
    | some steps =>
      simp only [hs, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]

def runAnsi {α β : Type} (common : Cli.Common) (period : Word.Count)
    (buildAgent : AgentSelection → IO α) (callbacks : AgentCallbacks .learnThenAct α β)
    (render : AnsiFrame common.world → IO Unit)
    (endGoal : Nat → UInt8 → Bool → UInt64 → IO Unit) :
    IO (Except RunnerError (AnsiState common.world α)) := do
  if common.goals == 0 && common.cycles == 0 then return .error (.campaign .emptyUnbounded)
  match World.initial common.world with
  | .error error => return .error (.world error)
  | .ok world =>
    try
      let agent ← buildAgent ⟨common.profile, .discounted⟩
      match world.observe with
      | .error error => return .error (.world error)
      | .ok observation =>
        let mut state : AnsiState common.world α := ⟨world, agent, {}, observation, 0⟩
        let curriculum := standardCurriculum common.world common.world.raw.seed
        let goals := min common.goals.toNat curriculum.size
        if goals == 0 then return .ok state
        let mut cycle : UInt64 := 0
        for _ in forever do
          for index in List.finRange goals do
            have hi : index.val < curriculum.size := by have := index.isLt; dsimp [goals] at *; omega
            let (goal, tier) := curriculum[index.val]'hi
            state := { state with world := state.world.setGoal goal }
            let mut used : UInt64 := 0
            for _ in [:common.steps.toNat] do
              match state.tick callbacks index.val with
              | .error error => return .error error
              | .ok (next, frame) =>
                state := next
                used := used + 1
                if state.steps % period.word == 0 then render frame
                if state.carried.events.done then break
                match state.refresh with
                | .error error => return .error error
                | .ok next => state := next
            endGoal index.val tier state.carried.events.done used
          cycle := saturatingIncrement64 cycle
          if common.cycles != 0 && cycle ≥ common.cycles then return .ok state
        throw (IO.userError "cycle loop ended without a result")
    catch error => return .error (.io error.toString)

end Acorn.Host
