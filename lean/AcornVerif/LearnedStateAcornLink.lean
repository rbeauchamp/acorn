/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentGridWorld
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
  kernel's closed loop of `kernelBase`, and `kernelBase_default` shows that in the order
  `learnThenAct` that agent is `CurrentGridWorld.executedAgent` from the cold state.

`baseFails_of_stateNeeded` shows that at Acorn the base agent's failure follows from the failure
of the base agent fed no word, because a percept handed no word is the percept.

`idle_refused` shows that a mechanism that hands the base agent nothing has no complete result,
for any configuration and task.
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

/-- The base agent of a configuration at a seed, as an agent of the interaction kernel. -/
def kernelBase (configuration : Configuration) (seed : UInt64) : Kernel.Agent Grid.interface where
  Memory := Base.State (configuration.construction seed)
  initial := Base.cold (configuration.construction seed)
  act memory percept := ((Base.step memory percept).2.action, (Base.step memory percept).1)

/-- A run of the base agent in a kernel world is the kernel's closed loop of `kernelBase`, with
the seed carried beside the agent's state. -/
theorem base_loop (configuration : Configuration) (world : Kernel.World Grid.interface)
    (start : world.State) (seed : UInt64) (time : Nat) :
    run (setting configuration) (base configuration) seed (ofKernel world start) time =
      ((Kernel.loop world (kernelBase configuration seed) start time).1,
        ⟨seed, (Kernel.loop world (kernelBase configuration seed) start time).2⟩) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [run_succ (setting configuration) (base configuration) seed (ofKernel world start) time,
      ih]
    rfl

/-- In the order `learnThenAct` the kernel's base agent is the executed agent from the cold
state of the construction. -/
theorem kernelBase_default (configuration : Configuration) (seed : UInt64)
    (default : configuration.order = .learnThenAct) :
    kernelBase configuration seed =
      CurrentGridWorld.executedAgent (configuration.construction seed).initial.agent := by
  have step : ∀ (memory : Base.State (configuration.construction seed))
      (percept : Percept Grid.interface), Base.step memory percept = memory.act percept := by
    intro memory percept
    change memory.actOrdered configuration.order percept = memory.act percept
    rw [default, Agent.act_parts]
  unfold kernelBase CurrentGridWorld.executedAgent
  simp only [step]
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

/-- The mechanism that holds nothing and hands the base agent no word. -/
def idle (configuration : Configuration) : Mechanism (setting configuration) where
  Memory := Unit
  cold _ := ()
  read _ _ := ([], ())
  note _ _ := ()

/-- A mechanism that hands the base agent nothing has no complete result. -/
theorem idle_refused (configuration : Configuration) (task : Task (setting configuration)) :
    ¬ Complete configuration (idle configuration) task :=
  fun result => result.stateless_refused (fun _ => []) (fun _ _ => rfl)

end AcornVerif.LearnedState.Acorn
