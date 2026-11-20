/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentGridWorld
import AcornVerif.LearnedStateFrame
import AcornVerif.Targets.LearnedStateAcorn

/-! # The frame's base agent is the kernel's executed agent

`base_loop` shows that a run of the frame's base agent in a world of the interaction kernel is
the kernel's closed loop of `CurrentGridWorld.executedAgent` from the cold state of the standard
construction at the seed. So a theorem stated through the kernel's loop from that state is a
theorem about the frame's base agent, and the reverse.

`baseFails_of_stateNeeded` shows that at Acorn the base agent's failure follows from the failure
of the base agent fed no word, because a percept handed no word is the percept.

`idle_refused` shows that a mechanism that hands the base agent nothing has no complete result,
for any configuration and task.
-/

namespace AcornVerif.LearnedState.Acorn
open _root_.Acorn _root_.Acorn.Handcrafted _root_.Acorn.Features

/-- A run of the base agent in a kernel world is the kernel's closed loop of the executed agent
from the construction's cold state, with the seed carried beside the agent's state. -/
theorem base_loop (configuration : Configuration) (world : Kernel.World Grid.interface)
    (start : world.State) (seed : UInt64) (time : Nat) :
    run (setting configuration) (base configuration) seed (ofKernel world start) time =
      ((Kernel.loop world
          (CurrentGridWorld.executedAgent (configuration.construction seed).initial.agent)
          start time).1,
        ⟨seed, (Kernel.loop world
          (CurrentGridWorld.executedAgent (configuration.construction seed).initial.agent)
          start time).2⟩) := by
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
