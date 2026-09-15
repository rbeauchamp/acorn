/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.GoalAchievement
import Acorn.Host.Viewer.WorldTelemetry
import Acorn.Host.Viewer.AgentTelemetry
import Acorn.Host.Viewer.LifetimeTelemetry
import Acorn.Host.Viewer.FeatureTelemetry
import Acorn.Host.Viewer.PersistedState

/-!
# Complete core telemetry assembly

The field list is the serialization and schema source. Agent/world values come
from the actual immutable capture; the native runner supplies timing, resource,
campaign and build context. This module does not manufacture measurements or
assert that a supplied build digest identifies the executing binary.
-/
namespace Acorn.Host.Viewer
open Features Handcrafted

/-- Current native/browser telemetry protocol version. -/
def telemetrySchemaVersion : Nat := 10

/-- Full-width canonical digest spelling, admitted before frame retention. -/
abbrev HexText (count : Nat) := {text : String // text.length = count ∧
  text.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) = true}

/-- Declared source/build identities supplied by the native build bootstrap. -/
structure TelemetryBuild where
  /-- Source identity of the executing package. -/
  source : HexText 64
  /-- Toolchain and build-setting identity. -/
  build : HexText 64
  /-- Declared mutation-detection pin, not a correctness certificate. -/
  audit : HexText 16

/-- How checkpoint admission obtained the logical agent. -/
inductive TelemetryOrigin where
  /-- Fresh construction outside Clear. -/
  | fresh
  /-- Successful complete checkpoint admission. -/
  | resumed
  /-- Fresh construction for an explicitly cleared run. -/
  | cleared

/-- Exhaustive origin spelling with no arbitrary protocol string. -/
def TelemetryOrigin.tag : TelemetryOrigin → String
  | .fresh => "fresh" | .resumed => "resumed" | .cleared => "cleared"

/-- Native capture context; all measurements are reported by the shell that performs the work. -/
structure TelemetryContext where
  /-- Admitted executing source/build context. -/
  build : TelemetryBuild
  /-- Actual durable world/agent identity after checkpoint admission. -/
  identity : Identity
  /-- Actual checkpoint outcome's identity origin. -/
  origin : TelemetryOrigin
  /-- Wall clock milliseconds at capture. -/
  timestampMs : UInt64
  /-- Measured agent update latency. -/
  updateUs : UInt64
  /-- Measured preceding environment latency. -/
  environmentUs : UInt64
  /-- Monotonic process lifetime at capture. -/
  processUptimeMs : UInt64
  /-- Fixed native monotonic process-start clock, distinguishing evaluator sessions. -/
  processStartedMs : Nat
  /-- Latest available native RSS measurement. -/
  coreRssBytes : Option UInt64
  /-- Size of the latest successful checkpoint. -/
  checkpointBytes : Option UInt64
  /-- Duration of the latest successful checkpoint. -/
  checkpointWriteUs : Option UInt64
  /-- Actual refused checkpoint writes in this process. -/
  checkpointFailures : UInt64
  /-- Actual prior refused telemetry writes in this process. -/
  telemetryRefusals : UInt64
  /-- Effective admitted campaign goal count. -/
  goalCount : UInt64
  /-- Effective admitted attempt cap. -/
  attemptCap : UInt64
  /-- Effective admitted step cap. -/
  stepCap : UInt64
  /-- Zero denotes the unbounded campaign mode. -/
  cycleCap : UInt64
  /-- Complete admitted catalog, independent of client observation history. -/
  curriculumNames : Vector String goalCount.toNat
  /-- Bounded outcome accounting for precisely this admitted campaign population. -/
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

/-- The complete protocol field list is assembled from actual observation owners. -/
def coreTelemetry {config : Features.Config} {dimension : Dimension}
    (context : TelemetryContext) (frame : StepFrame (AgentObservation config dimension))
    (terminal : Bool) : List TelemetryField :=
  contextTelemetry context ++ worldTelemetry frame terminal ++ learnerTelemetry frame.agent ++
    decisionTelemetry frame.agent ++ lifetimeTelemetry frame.agent ++ featureTelemetry frame.agent ++
    predictionTelemetry frame

set_option maxRecDepth 4096 in
/-- Every capture emits the same names and dimensions, independently of all runtime values. -/
theorem coreTelemetry_schema_fixed {config : Features.Config} {dimension : Dimension}
    (left right : TelemetryContext)
    (first second : StepFrame (AgentObservation config dimension)) (ended ended' : Bool) :
    telemetrySchema (coreTelemetry left first ended) =
      telemetrySchema (coreTelemetry right second ended') := by
  simp only [telemetrySchema, coreTelemetry, List.map_append, contextTelemetry, worldTelemetry,
    learnerTelemetry, decisionTelemetry, lifetimeTelemetry, featureTelemetry, predictionTelemetry,
    List.map_cons, List.map_nil]
  rfl

/-- Whole-line byte and delimiter admission precedes any native telemetry sink write. -/
def coreTelemetryLine {config : Features.Config} {dimension : Dimension}
    (context : TelemetryContext) (frame : StepFrame (AgentObservation config dimension))
    (terminal : Bool) : Except String WireText := do
  let some line := wireText (emitTelemetryFields (coreTelemetry context frame terminal))
    | throw "core telemetry exceeds the admitted physical-line bound"
  return line

/-- Actual runner measurements replace the corresponding shell-context fields at emission. -/
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

/-- Native runner adapter emits actual frames and reports IO refusals through the runner.
The bootstrap supplies live clock/build/identity context and a separate outcome
consumer. Neither operation returns a value to the learned transition. -/
def coreStreamObserver {config : Features.Config} {dimension : Dimension}
    (sink : IO.FS.Stream) (readContext : CaptureMetrics → IO TelemetryContext)
    (initialized : CheckpointAdmission → BaseIO Unit) (outcome : GoalOutcome → IO Unit) :
    StreamObserver (AgentObservation config dimension) where
  onInitialized := initialized
  onStep := some (fun frame capture => writeCoreFrame sink readContext frame capture false)
  onAttemptEnd frame capture := writeCoreFrame sink readContext frame capture true
  onOutcome := outcome

/-- A shell-supplied value cannot override the runner's actual update duration. -/
theorem TelemetryContext.capture_update (context : TelemetryContext) (capture : CaptureMetrics) :
    (context.withCapture capture).updateUs = capture.updateUs := rfl

end Acorn.Host.Viewer
