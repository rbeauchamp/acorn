import Acorn.Host.Viewer.NativeContext
import Acorn.Host.AgentAdmission
import Acorn.Host.Checkpoint.IO
import Acorn.Host.Cli

namespace Acorn.Host.Viewer
open Features Handcrafted

def nativeSelection (options : Cli.Streaming) : AgentSelection :=
  ⟨options.common.profile, options.criterion.getD .discounted⟩

def nativeConstruction (options : Cli.Streaming) : AgentConstruction :=
  AgentConstruction.standard options.common.world.raw.seed (nativeSelection options)
    options.common.planning options.order

def curriculumGoalName : Goal → String
  | .survive steps => s!"Survive {steps} steps"
  | .collect item count => s!"Collect {(GoalItem.labels (some (.inl item))).1} ×{count}"
  | .craft item => s!"Craft {(GoalItem.labels (some (.inr item))).1}"
  | .reach position => s!"Reach ({position.x.val}, {position.y.val})"
  | .find position => s!"Find ({position.x.val}, {position.y.val})"

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
    let result ← construction.runCampaign Handcrafted.Grid.interface_timing options.common.world
      options.common.world.raw.seed (nativeSelection options) options.campaign observer
      checkpoint stop.requested
    match result with
    | .error error => return .error error
    | .ok result =>
      let agent := result.run.agent.censorObservations
      let mut resources := result.resources
      if options.telemetry then
        match ← finalFrame.get with
        | none => pure ()
        | some (frame, metrics) =>
          let final := { frame with agent := Agent.observe agent.agent }
          resources ← notifyObserver (baseObserver.onAttemptEnd final metrics) resources
      return .ok { result with run := { result.run with agent := agent }, resources := resources }

theorem nativeParameters_stepCap (options : Cli.Streaming) (build : TelemetryBuild)
    (plan : CampaignPlan (standardCurriculum options.common.world options.common.world.raw.seed).size) :
    (nativeParameters options build plan).stepCap = plan.stepCap := rfl

theorem nativeConstruction_planning (options : Cli.Streaming) :
    (nativeConstruction options).planning = options.common.planning := rfl

theorem nativeConstruction_order (options : Cli.Streaming) :
    (nativeConstruction options).order = options.order := rfl

theorem nativeConstruction_criterion (options : Cli.Streaming) :
    (nativeConstruction options).criterion = options.criterion.getD .discounted := rfl

end Acorn.Host.Viewer
