import AcornVerif.CurrentHostLoop
import AcornVerif.LearnedStateFrame
import AcornVerif.Targets.LearnedStateAcorn

namespace AcornVerif.LearnedState.Acorn
open _root_.Acorn _root_.Acorn.Handcrafted _root_.Acorn.Features

theorem base_cold (configuration : Configuration) (seed : UInt64) :
    Base.cold (configuration.construction seed) =
      (configuration.construction seed).initial.agent := rfl

theorem base_step_parts (configuration : Configuration) (seed : UInt64)
    (state : Base.State (configuration.construction seed)) (percept : Percept Grid.interface) :
    Base.step state percept =
      ((state.choose configuration.order percept).learn,
        (state.choose configuration.order percept).decision) := rfl

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

theorem extend_nil (percept : Percept Grid.interface) : extend percept [] = percept := by
  simp [extend, percept.frame.bounded]

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
