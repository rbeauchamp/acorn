import Acorn.Host.Viewer.GoalAchievement
import Acorn.Host.Viewer.WorldTelemetry
import Acorn.Host.Viewer.AgentTelemetry
import Acorn.Host.Viewer.LifetimeTelemetry
import Acorn.Host.Viewer.FeatureTelemetry
import Acorn.Host.Viewer.PersistedState

namespace Acorn.Host.Viewer
open Features Handcrafted

def telemetrySchemaVersion : Nat := 10

abbrev HexText (count : Nat) := {text : String // text.length = count ∧
  text.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) = true}

structure TelemetryBuild where
  source : HexText 64
  build : HexText 64
  audit : HexText 16

inductive TelemetryOrigin where
  | fresh
  | resumed
  | cleared

def TelemetryOrigin.tag : TelemetryOrigin → String
  | .fresh => "fresh" | .resumed => "resumed" | .cleared => "cleared"

structure TelemetryContext where
  build : TelemetryBuild
  identity : Identity
  origin : TelemetryOrigin
  timestampMs : UInt64
  updateUs : UInt64
  environmentUs : UInt64
  processUptimeMs : UInt64
  processStartedMs : Nat
  coreRssBytes : Option UInt64
  checkpointBytes : Option UInt64
  checkpointWriteUs : Option UInt64
  checkpointFailures : UInt64
  telemetryRefusals : UInt64
  goalCount : UInt64
  attemptCap : UInt64
  stepCap : UInt64
  cycleCap : UInt64
  curriculumNames : Vector String goalCount.toNat
  goalProgress : GoalAchievement.State goalCount.toNat attemptCap.toNat

private def contextTelemetry (context : TelemetryContext) : List TelemetryField :=
  [⟨"schema_version", .natural, telemetrySchemaVersion⟩,
   ⟨"source_sha256", .text, context.build.source.val⟩,
   ⟨"build_sha256", .text, context.build.build.val⟩,
   ⟨"audit_digest", .text, context.build.audit.val⟩,
   ⟨"run_id", .text, runHex context.identity.run⟩,
   ⟨"agent_epoch", .natural, context.identity.agentEpoch.toNat⟩,
   ⟨"origin", .text, context.origin.tag⟩,
   ⟨"timestamp_ms", .natural, context.timestampMs.toNat⟩,
   ⟨"update_us", .natural, context.updateUs.toNat⟩,
   ⟨"environment_us", .natural, context.environmentUs.toNat⟩,
   ⟨"process_uptime_ms", .natural, context.processUptimeMs.toNat⟩,
   ⟨"process_started_ms", .natural, context.processStartedMs⟩,
   ⟨"core_rss_bytes", .optional .natural, context.coreRssBytes.map UInt64.toNat⟩,
   ⟨"checkpoint_bytes", .optional .natural, context.checkpointBytes.map UInt64.toNat⟩,
   ⟨"checkpoint_write_us", .optional .natural, context.checkpointWriteUs.map UInt64.toNat⟩,
   ⟨"checkpoint_failures", .natural, context.checkpointFailures.toNat⟩,
   ⟨"telemetry_refusals", .natural, context.telemetryRefusals.toNat⟩,
   ⟨"telemetry_drops", .natural, 0⟩,
   ⟨"goal_count", .natural, context.goalCount.toNat⟩,
   ⟨"attempt_cap", .natural, context.attemptCap.toNat⟩,
   ⟨"step_cap", .natural, context.stepCap.toNat⟩,
   ⟨"cycle_cap", .natural, context.cycleCap.toNat⟩,
   ⟨"goal_progress_invalid", .flag, context.goalProgress.invalid⟩,
   ⟨"goal_progress_cycle", .natural, context.goalProgress.cycle.toNat⟩,
   ⟨"goal_progress_resolved", .natural, context.goalProgress.current.resolved.val⟩,
   ⟨"goal_progress_attempt", .natural, context.goalProgress.nextAttempt.val⟩,
   ⟨"goal_progress_achieved", .natural, context.goalProgress.current.achieved.val⟩,
   ⟨"goal_progress_completed_cycle", .optional .natural,
     context.goalProgress.latest.map (·.cycle.toNat)⟩,
   ⟨"goal_progress_completed_achieved", .optional .natural,
     context.goalProgress.latest.map (·.pass.achieved.val)⟩,
   ⟨"goal_progress_score", .optional .natural,
     context.goalProgress.headline.map GoalAchievement.Pass.permille⟩,
   ⟨"curriculum_names", .sequence .text, context.curriculumNames.toArray⟩,
   ⟨"curriculum_failed_attempts", .sequence .natural,
     (context.goalProgress.results.map (·.failures.val)).toArray⟩,
   ⟨"curriculum_success_steps", .sequence (.optional .natural),
     (context.goalProgress.results.map (fun row => row.successSteps.map UInt64.toNat)).toArray⟩]

def coreTelemetry {config : Features.Config} {dimension : Dimension}
    (context : TelemetryContext) (frame : StepFrame (AgentObservation config dimension))
    (terminal : Bool) : List TelemetryField :=
  contextTelemetry context ++ worldTelemetry frame terminal ++ learnerTelemetry frame.agent ++
    decisionTelemetry frame.agent ++ lifetimeTelemetry frame.agent ++ featureTelemetry frame.agent ++
    predictionTelemetry frame

set_option maxRecDepth 4096 in
theorem coreTelemetry_schema_fixed {config : Features.Config} {dimension : Dimension}
    (left right : TelemetryContext)
    (first second : StepFrame (AgentObservation config dimension)) (ended ended' : Bool) :
    telemetrySchema (coreTelemetry left first ended) =
      telemetrySchema (coreTelemetry right second ended') := by
  simp only [telemetrySchema, coreTelemetry, List.map_append, contextTelemetry, worldTelemetry,
    learnerTelemetry, decisionTelemetry, lifetimeTelemetry, featureTelemetry, predictionTelemetry,
    List.map_cons, List.map_nil]
  rfl

def coreTelemetryLine {config : Features.Config} {dimension : Dimension}
    (context : TelemetryContext) (frame : StepFrame (AgentObservation config dimension))
    (terminal : Bool) : Except String WireText := do
  let some line := wireText (emitTelemetryFields (coreTelemetry context frame terminal))
    | throw "core telemetry exceeds the admitted physical-line bound"
  return line

def TelemetryContext.withCapture (context : TelemetryContext) (capture : CaptureMetrics) : TelemetryContext :=
  { context with
    updateUs := capture.updateUs
    environmentUs := capture.environmentUs
    checkpointBytes := capture.checkpointBytes
    checkpointWriteUs := capture.checkpointWriteUs
    checkpointFailures := capture.checkpointFailures
    telemetryRefusals := capture.observerRefusals }

private def writeCoreFrame {config : Features.Config} {dimension : Dimension}
    (sink : IO.FS.Stream) (readContext : CaptureMetrics → IO TelemetryContext)
    (frame : StepFrame (AgentObservation config dimension)) (capture : CaptureMetrics)
    (terminal : Bool) : IO Unit := do
  let context ← readContext capture
  match coreTelemetryLine (context.withCapture capture) frame terminal with
  | .error reason => throw (IO.userError reason)
  | .ok line =>
    sink.putStr (line.val ++ "\n")
    sink.flush

def coreStreamObserver {config : Features.Config} {dimension : Dimension}
    (sink : IO.FS.Stream) (readContext : CaptureMetrics → IO TelemetryContext)
    (initialized : CheckpointAdmission → BaseIO Unit) (outcome : GoalOutcome → IO Unit) :
    StreamObserver (AgentObservation config dimension) where
  onInitialized := initialized
  onStep := some (fun frame capture => writeCoreFrame sink readContext frame capture false)
  onAttemptEnd frame capture := writeCoreFrame sink readContext frame capture true
  onOutcome := outcome

theorem TelemetryContext.capture_update (context : TelemetryContext) (capture : CaptureMetrics) :
    (context.withCapture capture).updateUs = capture.updateUs := rfl

end Acorn.Host.Viewer
