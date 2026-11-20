/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentHostLoop
import AcornVerif.LearnedStateFrame
import AcornVerif.Targets.LearnedStateAcorn

/-! # The frame's base agent is the agent Acorn's host runs, in every step order

For every configuration, the step order included:

* `base_cold`: the base agent's cold construction is the cold agent of the host's construction.
* `base_step_host`: the host's whole step of the construction, on an observation and the carried
  result, is the frame's base step on the grid percept of that observation: the same action and
  the same next agent.
* `base_step_parts`: the base step is the first part of the order and then the second part on
  what the first returned. The second part takes nothing else, so a store overwritten before
  the step is overwritten before both parts, whichever order is chosen.
* `base_loop`: a run of the frame's base agent in a world of the interaction kernel is the
  kernel's closed loop of `CurrentHostLoop.orderedAgent` at the configuration's order, from the
  construction's cold agent. In the order `learnThenAct` that agent is
  `CurrentGridWorld.executedAgent` from the cold state (`CurrentHostLoop.orderedAgent_default`).

`baseFails_of_stateNeeded` shows that at Acorn the base agent's failure follows from the failure
of the base agent fed no word, because a percept handed no word is the percept.
-/

namespace AcornVerif.LearnedState.Acorn
open _root_.Acorn _root_.Acorn.Handcrafted _root_.Acorn.Features

/-- The base agent's cold construction is the cold agent of the host's construction. -/
theorem base_cold (configuration : Configuration) (seed : UInt64) :
    Base.cold (configuration.construction seed) =
      (configuration.construction seed).initial.agent := rfl

/-- The base step is the first part of the construction's order, then the second part on what
the first returned. -/
theorem base_step_parts (configuration : Configuration) (seed : UInt64)
    (state : Base.State (configuration.construction seed)) (percept : Percept Grid.interface) :
    Base.step state percept =
      ((state.choose configuration.order percept).learn,
        (state.choose configuration.order percept).decision) := rfl

/-- **The frame's base step is the host's whole step, in every step order.** For every
configuration, seed, state of the host's construction, observation and carried result, the
action and the next agent of the host's whole step are those of the base step on the grid
percept of the observation. -/
theorem base_step_host (configuration : Configuration) (seed : UInt64)
    (state : (configuration.construction seed).State) (observation : Host.Observation)
    (result : Host.RawStepResult) :
    (((configuration.construction seed).callbacks.act state observation result).1,
        ((configuration.construction seed).callbacks.act state observation result).2.agent) =
      (Host.Action.fromIndex (Base.step state.agent
          (Grid.percept (configuration.construction seed).profile.taskMode observation
            result.reward result.events.done)).2.action.val,
        (Base.step state.agent
          (Grid.percept (configuration.construction seed).profile.taskMode observation
            result.reward result.events.done)).1) := by
  rw [AgentConstruction.callbacks_act, Agent.callbacks_ordered]
  rfl

/-- A run of the base agent in a kernel world is the kernel's closed loop of the agent of the
configuration's step order from the construction's cold agent, with the seed carried beside the
agent's state. -/
theorem base_loop (configuration : Configuration) (world : Kernel.World Grid.interface)
    (start : world.State) (seed : UInt64) (time : Nat) :
    run (setting configuration) (base configuration) seed (ofKernel world start) time =
      ((Kernel.loop world (CurrentHostLoop.orderedAgent configuration.order
          (configuration.construction seed).initial.agent) start time).1,
        ⟨seed, (Kernel.loop world (CurrentHostLoop.orderedAgent configuration.order
          (configuration.construction seed).initial.agent) start time).2⟩) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [run_succ (setting configuration) (base configuration) seed (ofKernel world start) time,
      ih]
    rfl

/-- A percept handed no word is the percept. -/
theorem extend_nil (percept : Percept Grid.interface) : extend percept [] = percept := by
  simp [extend, percept.frame.bounded]

/-- The base agent fed no word has the base agent's run. -/
theorem run_fed_nil (configuration : Configuration) (seed : UInt64)
    (world : World (Percept Grid.interface) (Kernel.Act Grid.interface)) (time : Nat) :
    run (setting configuration) (fed (setting configuration) fun _ _ => []) seed world time =
      ((run (setting configuration) (base configuration) seed world time).1,
        ((run (setting configuration) (base configuration) seed world time).2, time)) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    simp only [run, ih, fed]
    simp only [setting, extend_nil]

/-- **At Acorn the base agent's failure follows from `stateNeeded`**: the base agent is the base
agent fed no word. -/
theorem baseFails_of_stateNeeded (configuration : Configuration)
    (task : Task (setting configuration)) (seed : UInt64)
    (needed : Fails (setting configuration) (fed (setting configuration) fun _ _ => []) task
      seed) :
    Fails (setting configuration) (base configuration) task seed := by
  obtain ⟨member, fails⟩ := needed
  refine ⟨member, fun met => fails ?_⟩
  have same : trace (setting configuration) (fed (setting configuration) fun _ _ => []) seed
      (task.world member) = trace (setting configuration) (base configuration) seed
      (task.world member) := by
    funext time
    unfold trace
    rw [run_fed_nil configuration seed (task.world member) time]
    simp only [setting, extend_nil]
  rw [same]
  exact met

end AcornVerif.LearnedState.Acorn
