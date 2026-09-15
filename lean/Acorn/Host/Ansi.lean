/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Cli

/-!
# Separate ANSI loop protocol

The source ANSI loop deliberately has a different observation schedule from
streaming attempts: its sensor image persists across goal installation and a
terminal step. The renderer sees that image beside the post-step world fields.
This module preserves that schedule rather than changing its action inputs.
It has no checkpoint or cooperative-control argument because CLI admission
refuses those options in this mode. Rendering is a one-way supplied IO owner.
-/
namespace Acorn.Host

/-- Current ANSI stream, including the retained sensor image. -/
structure AnsiState (config : WorldConfig) (α : Type) where
  /-- Current physical world. -/
  world : World config
  /-- Supplied real agent state. -/
  agent : α
  /-- Last world result, carried across goals. -/
  carried : RawStepResult
  /-- Sensor image at the source loop's actual observation point. -/
  observation : Observation
  /-- Exact total steps; unrepresentable increments refuse. -/
  steps : UInt64

/-- The ANSI renderer receives the old image and the post-step world state. -/
structure AnsiFrame (config : WorldConfig) where
  /-- Sensor image the agent consumed. -/
  observation : Observation
  /-- World after the selected action. -/
  world : World config
  /-- Actual result. -/
  result : StepResult
  /-- Selected action. -/
  action : Action
  /-- Aggregate action count. -/
  steps : UInt64
  /-- Current curriculum goal. -/
  goalIndex : Nat

/-- One ANSI action; the caller renders before advancing the sensor image. -/
def AnsiState.tick {config : WorldConfig} {α β : Type} (state : AnsiState config α)
    (callbacks : AgentCallbacks α β) (goalIndex : Nat) :
    Except RunnerError (AnsiState config α × AnsiFrame config) := do
  let (action, agent) := callbacks.act state.agent state.observation state.carried
  let (world, result) ← (state.world.step action).mapError RunnerError.world
  let some steps := Word.advanceClock state.steps 1 | .error (.metric .totalStepsOverflow)
  let next := { state with world := world, agent := agent, carried := result.raw, steps := steps }
  return (next, ⟨state.observation, world, result, action, steps, goalIndex⟩)

/-- The actual observation continuation is separate from rendering and terminal branching. -/
def AnsiState.refresh {config : WorldConfig} {α : Type} (state : AnsiState config α) :
    Except RunnerError (AnsiState config α) := do
  let observation ← state.world.observe |>.mapError RunnerError.world
  return { state with observation := observation }

/-- A successful tick leaves the consumed sensor image unchanged until explicit refresh. -/
theorem AnsiState.tick_observation {config : WorldConfig} {α β : Type}
    (state next : AnsiState config α) (callbacks : AgentCallbacks α β) (index : Nat)
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

/-- Native ANSI execution with the actual agent and renderer supplied by their owners.
A rendering error is an explicit IO failure; no control input changes action selection. -/
def runAnsi {α β : Type} (common : Cli.Common) (period : Word.Count)
    (buildAgent : AgentSelection → IO α) (callbacks : AgentCallbacks α β)
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
        repeat
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
    catch error => return .error (.io error.toString)

end Acorn.Host
