/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.NativeContext
import Acorn.Host.AgentAdmission
import Acorn.Host.Checkpoint.IO
import Acorn.Host.Cli

/-!
# Native observed campaign composition

The admitted CLI campaign uses the current full agent and receiver-bound
checkpoint hooks. Telemetry reads the same campaign plan as execution. The
caller owns build provenance, output destinations and the stop reader's native
lifetime; this composition receives only the monotone stop capability.
Post-campaign baselines and nonstreaming commands remain separate dispatches.
-/
namespace Acorn.Host.Viewer
open Features Handcrafted

/-- The streaming criterion default is the current discounted reference within
the explicitly requested research profile; it is not a profile promotion. -/
def nativeSelection (options : Cli.Streaming) : AgentSelection :=
  ⟨options.common.profile, options.criterion.getD .discounted⟩

/-- The current ordinary campaign instantiates the full scalar planning owner. -/
def nativeConstruction (options : Cli.Streaming) : AgentConstruction :=
  AgentConstruction.standard options.common.world.raw.seed (nativeSelection options) .scalar

/-- User-facing task names are exhaustive projections of the actual host goal. -/
def curriculumGoalName : Goal → String
  | .survive steps => s!"Survive {steps} steps"
  | .collect item count => s!"Collect {GoalItem.label (some (.inl item))} ×{count}"
  | .craft item => s!"Craft {GoalItem.label (some (.inr item))}"
  | .reach position => s!"Reach ({position.x.val}, {position.y.val})"

/-- Telemetry campaign counts are projections of the execution owner's admitted
plan, including clipping and zero-attempt normalization. -/
def nativeParameters (options : Cli.Streaming) (build : TelemetryBuild)
    (plan : CampaignPlan (standardCurriculum options.common.world options.common.world.raw.seed).size) : ContextParameters where
  build := build
  run := options.runId
  seed := options.common.world.raw.seed
  resumedEpoch := options.agentEpoch
  newEpoch := options.newAgentEpoch
  newOrigin := if options.cleared then .cleared else .fresh
  goalCount := plan.goals.val.toUInt64
  curriculumNames := Vector.ofFn fun index =>
    let curriculum := standardCurriculum options.common.world options.common.world.raw.seed
    curriculumGoalName (curriculum[index.val]'(by
      have population := plan.goals.isLt
      have member := index.isLt
      have bound : plan.goals.val < 2 ^ 64 := by
        change plan.goals.val < 13 + 1 at population
        omega
      have exactCount : plan.goals.val.toUInt64.toNat = plan.goals.val := Nat.mod_eq_of_lt bound
      dsimp [curriculum]
      omega)).1
  attemptCap := plan.attempts
  stepCap := plan.stepCap
  cycleCap := plan.cycles

/-- Execute one observed campaign with the actual construction and persistence
owners. Outcome IO failures are contained by the runner just like frame IO.
The sink is unused when telemetry is disabled; no frame is manufactured for it.
The caller invokes any separately requested baseline after this result. -/
def runNativeCampaign (options : Cli.Streaming) (build : TelemetryBuild)
    (syncProgram : System.FilePath) (sink : IO.FS.Stream)
    (outcome : GoalOutcome → IO Unit) (stop : StopFlag)
    (onAttemptEnd : StepFrame (AgentObservation (nativeConstruction options).config
      (nativeConstruction options).dimension) → IO Unit := fun _ => pure ()) :
    IO (Except RunnerError (CampaignResult options.common.world (nativeConstruction options).State)) := do
  if !options.common.profile.resumable && options.checkpoint.isSome then
    return .error (.campaign .nonresumableProfile)
  let construction := nativeConstruction options
  let curriculum := standardCurriculum options.common.world options.common.world.raw.seed
  match CampaignPlan.admit curriculum.size options.campaign with
  | .error error => return .error (.campaign error)
  | .ok plan =>
    let context ← NativeContext.new (nativeParameters options build plan)
    let baseObserver : StreamObserver (AgentObservation construction.config construction.dimension) :=
      if options.telemetry then context.observer sink outcome
      else { StreamObserver.none with onOutcome := outcome }
    let finalFrame ← IO.mkRef (none : Option
      (StepFrame (AgentObservation construction.config construction.dimension) × CaptureMetrics))
    let observer := { baseObserver with
      onAttemptEnd := fun frame metrics => do
        context.beginPass frame.goal.cycle
        finalFrame.set (some (frame, metrics))
        onAttemptEnd frame
      onOutcome := fun result => do
        context.recordOutcome result
        try
          if options.telemetry then
            match ← finalFrame.get with
            | none => pure ()
            | some (frame, metrics) => baseObserver.onAttemptEnd frame metrics
        finally baseObserver.onOutcome result }
    let checkpoint ← match options.checkpoint with
      | none => pure none
      | some path => do
        let store ← Checkpoint.Store.new syncProgram
        pure (some (store.hooks construction path options.checkpointEvery))
    let result ← runCampaign options.common.world options.common.world.raw.seed (nativeSelection options)
      options.campaign (fun _ => IO.lazyPure fun _ => construction.initial)
      Agent.callbacks observer checkpoint stop.requested
    match result with
    | .error error => return .error error
    | .ok result =>
      let agent := result.run.agent.censorObservations
      let mut resources := result.resources
      if options.telemetry then
        match ← finalFrame.get with
        | none => pure ()
        | some (frame, metrics) =>
          let final := { frame with agent := Agent.observe agent }
          resources ← notifyObserver (baseObserver.onAttemptEnd final metrics) resources
      return .ok { result with run := { result.run with agent := agent }, resources := resources }

/-- The emitted effective step cap is definitionally the admitted execution cap. -/
theorem nativeParameters_stepCap (options : Cli.Streaming) (build : TelemetryBuild)
    (plan : CampaignPlan (standardCurriculum options.common.world options.common.world.raw.seed).size) :
    (nativeParameters options build plan).stepCap = plan.stepCap := rfl

/-- The criterion explicitly requested at admission reaches agent construction. -/
theorem nativeConstruction_criterion (options : Cli.Streaming) :
    (nativeConstruction options).criterion = options.criterion.getD .discounted := rfl

end Acorn.Host.Viewer
