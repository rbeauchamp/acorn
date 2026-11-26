import Acorn.Host.Viewer.TelemetryValue
import Acorn.Host.Viewer.PersistedState
import Acorn.Host.Viewer.LogPump

namespace Acorn.Host.Viewer

inductive ControlTransition where
  | initialized
  | startRequested
  | stopRequested
  | clearRequested
  | coreStarted
  | coreStopped
  | restartScheduled
  | archiving
  | cleared
  | failed
  deriving DecidableEq

def ControlTransition.tag : ControlTransition → String
  | .initialized => "initialized" | .startRequested => "start_requested"
  | .stopRequested => "stop_requested" | .clearRequested => "clear_requested"
  | .coreStarted => "core_started" | .coreStopped => "core_stopped"
  | .restartScheduled => "restart_scheduled" | .archiving => "archiving"
  | .cleared => "cleared" | .failed => "failed"

def Phase.controlTag : Phase → String
  | .idle => "stopped" | .starting _ => "starting" | .running _ => "running"
  | .stopping _ => "stopping" | .archiving => "clearing"

def Phase.representatives : List Phase :=
  [.starting 0, .running 0, .stopping 0, .archiving, .idle]

theorem Phase.controlTag_represented (phase : Phase) :
    phase.controlTag ∈ Phase.representatives.map Phase.controlTag := by
  cases phase <;> simp [Phase.representatives, Phase.controlTag]

structure ControlDetail where
  transition : ControlTransition
  reason : String
  clearDisabled : Option String
  log : LogStatus
  abnormalExit : Bool := false

structure ControlObservation where
  checkpointRefused : Bool := false
  mapPartial : Bool := false

def controlDiagnostic (text : String) : String :=
  let retained := text.toList.take 1024
  String.ofList retained ++ if text.length > 1024 then " [truncated]" else ""

def controlReason (lifecycle : Lifecycle) (detail : ControlDetail) : String :=
  controlDiagnostic detail.reason ++ if lifecycle.exhausted then
    s!" — gave up after {failureLimit} failed starts in a row" else ""

def controlTail (lifecycle : Lifecycle) (detail : ControlDetail) : List String :=
  if lifecycle.phaseValue == .idle then
    let lines := detail.log.tail.values
    (lines.drop (lines.length - 6)).map fun line =>
      controlDiagnostic ((String.fromUTF8? line.bytes).getD "[stderr line refused: invalid UTF-8]")
  else []

def controlWarning (lifecycle : Lifecycle) (detail : ControlDetail) : Option String :=
  if lifecycle.phaseValue != .idle then none
  else if detail.abnormalExit then
    some "abnormal exit; learning since the last successful checkpoint may be lost"
  else if detail.log.checkpoint == some .failed then
    some "checkpoint save failed; durability unconfirmed"
  else none

theorem controlWarning_active (lifecycle : Lifecycle) (detail : ControlDetail)
    (active : lifecycle.phaseValue != .idle) : controlWarning lifecycle detail = none := by
  simp [controlWarning, active]

def controlTelemetry (lifecycle : Lifecycle) (observed : ControlObservation)
    (detail : ControlDetail) : List TelemetryField :=
  let tail := (controlTail lifecycle detail).toArray.toVector
  [⟨"ctl", .flag, true⟩,
   ⟨"desired", .text, lifecycle.desiredValue.tag⟩,
   ⟨"actual", .text, lifecycle.phaseValue.controlTag⟩,
   ⟨"reason", .text, if lifecycle.phaseValue == .idle then controlReason lifecycle detail else ""⟩,
   ⟨"seed", .natural, lifecycle.identityValue.seed.toNat⟩,
   ⟨"runId", .text, runHex lifecycle.identityValue.run⟩,
   ⟨"agentEpoch", .natural, lifecycle.identityValue.agentEpoch.toNat⟩,
   ⟨"transition", .text, detail.transition.tag⟩,
   ⟨"transitionReason", .text, controlReason lifecycle detail⟩,
   ⟨"failures", .natural, lifecycle.failureCount⟩,
   ⟨"clearDisabled", .optional .text, detail.clearDisabled.map controlDiagnostic⟩,
   ⟨"checkpointRefused", .flag, observed.checkpointRefused⟩,
   ⟨"terminalWarning", .optional .text, controlWarning lifecycle detail⟩,
   ⟨"mapPartial", .flag, observed.mapPartial⟩,
   ⟨"tail", .array tail.size .text, tail⟩]

theorem controlTelemetry_reasons (lifecycle : Lifecycle) (observed : ControlObservation)
    (detail : ControlDetail) :
    let reason := controlDiagnostic detail.reason ++ if lifecycle.failureCount = 3 then
      " — gave up after 3 failed starts in a row" else ""
    (controlTelemetry lifecycle observed detail)[3]? =
      some ⟨"reason", .text, if lifecycle.phaseValue = .idle then reason else ""⟩ ∧
    (controlTelemetry lifecycle observed detail)[8]? =
      some ⟨"transitionReason", .text, reason⟩ := by
  simp [controlTelemetry, controlReason, Lifecycle.exhausted_iff, Phase.beq_idle, failureLimit]
  constructor <;> rfl

def controlTelemetryLine (lifecycle : Lifecycle) (observed : ControlObservation)
    (detail : ControlDetail) : Except String WireText := do
  let some line := wireText (emitTelemetryFields (controlTelemetry lifecycle observed detail))
    | throw "control state exceeds the admitted physical-line bound"
  return line

theorem controlTail_running (lifecycle : Lifecycle) (detail : ControlDetail) (generation : UInt64)
    (running : lifecycle.phaseValue = .running generation) : controlTail lifecycle detail = [] := by
  have different : (Phase.running generation == Phase.idle) = false := rfl
  simp [controlTail, running, different]

end Acorn.Host.Viewer
