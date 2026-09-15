/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.CoreTelemetry
import Acorn.Host.Viewer.NativeResources
import Std.Sync.Mutex
import Std.Time.DateTime.Timestamp

/-!
# Native telemetry context

The actual runner reports checkpoint admission before observation begins.
Only that result selects resumed versus fresh identity. Wall and monotonic
clocks use the pinned standard runtime; RSS uses the declared native sampler. Build identities and campaign counts remain bootstrap inputs.
-/
namespace Acorn.Host.Viewer

/-- Immutable launch identity and campaign context admitted by the native bootstrap. -/
structure ContextParameters where
  /-- Executing package and build identity. -/
  build : TelemetryBuild
  /-- Durable world identity and seed. -/
  run : UInt64
  /-- Terrain seed of the launched world. -/
  seed : UInt64
  /-- Logical epoch when the checkpoint actually loads. -/
  resumedEpoch : UInt64
  /-- Logical epoch of a fresh receiving agent. -/
  newEpoch : UInt64
  /-- Fresh construction provenance chosen by the run supervisor. -/
  newOrigin : NewAgentOrigin
  /-- Effective admitted campaign goal count. -/
  goalCount : UInt64
  /-- Every admitted goal name in execution order. -/
  curriculumNames : Vector String goalCount.toNat
  /-- Effective admitted attempt cap. -/
  attemptCap : UInt64
  /-- Effective admitted step cap. -/
  stepCap : UInt64
  /-- Zero for unbounded cycles. -/
  cycleCap : UInt64

/-- Process-local context cannot emit an identity before startup admission is reported. -/
structure NativeContext where
  private mk ::
  private parameters : ContextParameters
  private started : Nat
  private admission : Std.Mutex (Option CheckpointAdmission)
  private resources : NativeResources
  private goalProgress : Std.Mutex
    (GoalAchievement.State parameters.goalCount.toNat parameters.attemptCap.toNat)

/-- Record a native monotonic start and an unresolved checkpoint outcome. -/
def NativeContext.new (parameters : ContextParameters) : BaseIO NativeContext := do
  return ⟨parameters, ← IO.monoMsNow, ← Std.Mutex.new none, ← NativeResources.new,
    ← Std.Mutex.new (GoalAchievement.State.empty parameters.goalCount.toNat parameters.attemptCap.toNat)⟩

/-- The first actual startup result fixes identity for this process; later calls cannot replace it. -/
def NativeContext.initialized (context : NativeContext) (admission : CheckpointAdmission) : BaseIO Unit :=
  context.admission.atomically (modify fun previous => previous.or (some admission))

/-- Identity follows the actual checkpoint outcome, with refusal treated as fresh construction. -/
def ContextParameters.resolve (parameters : ContextParameters) (admission : CheckpointAdmission) :
    Identity × TelemetryOrigin :=
  match admission with
  | .loaded => (⟨parameters.run, parameters.seed, parameters.resumedEpoch⟩, .resumed)
  | .missing | .refused =>
    (⟨parameters.run, parameters.seed, parameters.newEpoch⟩,
      match parameters.newOrigin with | .fresh => .fresh | .cleared => .cleared)

/-- Campaign frame metadata selects the current pass before any outcome arrives. -/
def NativeContext.beginPass (context : NativeContext) (cycle : UInt64) : BaseIO Unit :=
  context.goalProgress.atomically (modify fun state => state.begin cycle)

/-- Consume the runner's actual completed outcome before invoking external reporting IO. -/
def NativeContext.recordOutcome (context : NativeContext) (outcome : GoalOutcome) : BaseIO Unit :=
  context.goalProgress.atomically (modify fun state => state.observe outcome)

/-- Read actual native clocks and the fixed initialization result, using runner-owned measurements. -/
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

/-- Wire observation receives the runner's actual initialization result and capture measurements. -/
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

/-- Every refused load selects the same fresh receiving identity as a missing file. -/
theorem ContextParameters.refused_identity (parameters : ContextParameters) :
    parameters.resolve .refused = parameters.resolve .missing := rfl

end Acorn.Host.Viewer
