import Acorn.Host.Viewer.CoreTelemetry
import Acorn.Host.Viewer.NativeResources
import Std.Sync.Mutex
import Std.Time.DateTime.Timestamp

namespace Acorn.Host.Viewer

structure ContextParameters where
  build : TelemetryBuild
  run : UInt64
  seed : UInt64
  resumedEpoch : UInt64
  newEpoch : UInt64
  newOrigin : NewAgentOrigin
  goalCount : UInt64
  curriculumNames : Vector String goalCount.toNat
  attemptCap : UInt64
  stepCap : UInt64
  cycleCap : UInt64

structure NativeContext where
  private mk ::
  private parameters : ContextParameters
  private started : Nat
  private admission : Std.Mutex (Option CheckpointAdmission)
  private resources : NativeResources
  private goalProgress : Std.Mutex
    (GoalAchievement.State parameters.goalCount.toNat parameters.attemptCap.toNat)

def NativeContext.new (parameters : ContextParameters) : BaseIO NativeContext := do
  return ⟨parameters, ← IO.monoMsNow, ← Std.Mutex.new none, ← NativeResources.new,
    ← Std.Mutex.new (GoalAchievement.State.empty parameters.goalCount.toNat parameters.attemptCap.toNat)⟩

def NativeContext.initialized (context : NativeContext) (admission : CheckpointAdmission) : BaseIO Unit :=
  context.admission.atomically (modify fun previous => previous.or (some admission))

def ContextParameters.resolve (parameters : ContextParameters) (admission : CheckpointAdmission) :
    Identity × TelemetryOrigin :=
  match admission with
  | .loaded => (⟨parameters.run, parameters.seed, parameters.resumedEpoch⟩, .resumed)
  | .missing | .refused =>
    (⟨parameters.run, parameters.seed, parameters.newEpoch⟩,
      match parameters.newOrigin with | .fresh => .fresh | .cleared => .cleared)

def NativeContext.beginPass (context : NativeContext) (cycle : UInt64) : BaseIO Unit :=
  context.goalProgress.atomically (modify fun state => state.begin cycle)

def NativeContext.recordOutcome (context : NativeContext) (outcome : GoalOutcome) : BaseIO Unit :=
  context.goalProgress.atomically (modify fun state => state.observe outcome)

def NativeContext.capture (context : NativeContext) (metrics : CaptureMetrics) : IO TelemetryContext := do
  let some admission ← context.admission.atomically get
    | throw (IO.userError "telemetry context precedes checkpoint admission")
  let (identity, origin) := context.parameters.resolve admission
  let stamp := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
  let uptime := (← IO.monoMsNow) - context.started
  let parameters := context.parameters
  return {
    build := parameters.build
    identity, origin
    timestampMs := (min stamp.toNat (2 ^ 64 - 1)).toUInt64
    updateUs := metrics.updateUs
    environmentUs := metrics.environmentUs
    processUptimeMs := (min uptime (2 ^ 64 - 1)).toUInt64
    processStartedMs := context.started
    coreRssBytes := none
    checkpointBytes := metrics.checkpointBytes
    checkpointWriteUs := metrics.checkpointWriteUs
    checkpointFailures := metrics.checkpointFailures
    telemetryRefusals := metrics.observerRefusals
    goalCount := parameters.goalCount
    curriculumNames := parameters.curriculumNames
    attemptCap := parameters.attemptCap
    stepCap := parameters.stepCap
    cycleCap := parameters.cycleCap
    goalProgress := ← context.goalProgress.atomically get }

def NativeContext.observer {config : Features.Config} {dimension : Dimension}
    (context : NativeContext) (sink : IO.FS.Stream) (outcome : GoalOutcome → IO Unit) :
    StreamObserver (Handcrafted.AgentObservation config dimension) :=
  { (coreStreamObserver (config := config) (dimension := dimension) sink context.capture context.initialized outcome) with
    onStep := some (fun frame metrics => do
      context.beginPass frame.goal.cycle
      let rss ← context.resources.observe frame.agent.clock false
      let observer := coreStreamObserver (config := config) (dimension := dimension) sink (fun capture => do
        return { (← context.capture capture) with coreRssBytes := rss }) context.initialized outcome
      observer.deliverStep (fun _ => frame) metrics)
    onAttemptEnd := fun frame metrics => do
      context.beginPass frame.goal.cycle
      let rss ← context.resources.observe frame.agent.clock true
      let observer := coreStreamObserver (config := config) (dimension := dimension) sink (fun capture => do
        return { (← context.capture capture) with coreRssBytes := rss }) context.initialized outcome
      observer.onAttemptEnd frame metrics }

theorem ContextParameters.refused_identity (parameters : ContextParameters) :
    parameters.resolve .refused = parameters.resolve .missing := rfl

end Acorn.Host.Viewer
