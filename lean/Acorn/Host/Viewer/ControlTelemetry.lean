/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.TelemetryValue
import Acorn.Host.Viewer.PersistedState
import Acorn.Host.Viewer.LogPump

/-!
# Supervisor control-state emission

Actual phase, desired intent, identity and retry count come from the lifecycle
owner. Transition reasons and native stderr remain observations supplied by the
supervisor. Text passes through the shared JSON string encoder, and the final
physical record passes through the same byte and delimiter admission as frames.
-/
namespace Acorn.Host.Viewer

/-- Closed supervisor transition vocabulary shared with the browser contract. -/
inductive ControlTransition where
  /-- Viewer initialization. -/
  | initialized
  /-- Explicit operator Start. -/
  | startRequested
  /-- Explicit operator Stop. -/
  | stopRequested
  /-- Explicit operator Clear. -/
  | clearRequested
  /-- Successful process launch. -/
  | coreStarted
  /-- Requested process exit. -/
  | coreStopped
  /-- Unexpected exit with remaining retry budget. -/
  | restartScheduled
  /-- Whole-directory archival has begun. -/
  | archiving
  /-- A replacement run was durably installed. -/
  | cleared
  /-- Native or admission failure. -/
  | failed
  deriving DecidableEq

/-- Exhaustive wire spelling cannot silently default a newly added transition. -/
def ControlTransition.tag : ControlTransition → String
  | .initialized => "initialized" | .startRequested => "start_requested"
  | .stopRequested => "stop_requested" | .clearRequested => "clear_requested"
  | .coreStarted => "core_started" | .coreStopped => "core_stopped"
  | .restartScheduled => "restart_scheduled" | .archiving => "archiving"
  | .cleared => "cleared" | .failed => "failed"

/-- The actual UI phase is a direct projection of the process lifecycle. -/
def Phase.controlTag : Phase → String
  | .idle => "stopped" | .starting _ => "starting" | .running _ => "running"
  | .stopping _ => "stopping" | .archiving => "clearing"

/-- Supplemental observations carry no writable lifecycle fields. -/
structure ControlDetail where
  /-- Actual server-selected transition. -/
  transition : ControlTransition
  /-- Native or operator reason accompanying that transition. -/
  reason : String
  /-- Explicit reason that the current launch configuration cannot Clear. -/
  clearDisabled : Option String
  /-- Actual bounded process-local stderr observations. -/
  log : LogStatus
  /-- Persistent possibility of lost world observations, independent of agent epoch. -/
  mapPartial : Bool := false
  /-- Observed nonzero child exit; cleared with the process-local log at launch. -/
  abnormalExit : Bool := false

/-- Diagnostic presentation is capped independently of the authoritative state.
The marker makes omitted text explicit; JSON escaping may enlarge each retained
character, but no unbounded native error can consume the physical frame budget. -/
def controlDiagnostic (text : String) : String :=
  let retained := text.toList.take 1024
  String.ofList retained ++ if text.length > 1024 then " [truncated]" else ""

/-- Only the six newest retained, valid UTF-8 stderr lines enter a stopped
control frame. Invalid encoding is explicitly represented as a refusal. -/
def controlTail (lifecycle : Lifecycle) (detail : ControlDetail) : List String :=
  if lifecycle.phaseValue == .idle then
    let lines := detail.log.tail.values
    (lines.drop (lines.length - 6)).map fun line =>
      controlDiagnostic ((String.fromUTF8? line.bytes).getD "[stderr line refused: invalid UTF-8]")
  else []

/-- A requested stop cannot hide observed termination or final-save failure.
Only idle attribution can expose a completed process's warning. -/
def controlWarning (lifecycle : Lifecycle) (detail : ControlDetail) : Option String :=
  if lifecycle.phaseValue != .idle then none
  else if detail.abnormalExit then
    some "abnormal exit; learning since the last successful checkpoint may be lost"
  else if detail.log.checkpoint == some .failed then
    some "checkpoint save failed; durability unconfirmed"
  else none

/-- Active generations cannot display a previous process's terminal warning. -/
theorem controlWarning_active (lifecycle : Lifecycle) (detail : ControlDetail)
    (active : lifecycle.phaseValue != .idle) : controlWarning lifecycle detail = none := by
  simp [controlWarning, active]

/-- Complete control record with state-derived fields and bounded native tail. -/
def controlTelemetry (lifecycle : Lifecycle) (detail : ControlDetail) : List TelemetryField :=
  let tail := (controlTail lifecycle detail).toArray.toVector
  [⟨"ctl", .flag, true⟩,
   ⟨"desired", .text, lifecycle.desiredValue.tag⟩,
   ⟨"actual", .text, lifecycle.phaseValue.controlTag⟩,
   ⟨"reason", .text, if lifecycle.phaseValue == .idle then controlDiagnostic detail.reason else ""⟩,
   ⟨"seed", .natural, lifecycle.identityValue.seed.toNat⟩,
   ⟨"runId", .text, runHex lifecycle.identityValue.run⟩,
   ⟨"agentEpoch", .natural, lifecycle.identityValue.agentEpoch.toNat⟩,
   ⟨"transition", .text, detail.transition.tag⟩,
   ⟨"transitionReason", .text, controlDiagnostic detail.reason⟩,
   ⟨"failures", .natural, lifecycle.failureCount⟩,
   ⟨"clearDisabled", .optional .text, detail.clearDisabled.map controlDiagnostic⟩,
   ⟨"checkpointRefused", .flag, lifecycle.checkpointRefusedValue⟩,
   ⟨"terminalWarning", .optional .text, controlWarning lifecycle detail⟩,
   ⟨"mapPartial", .flag, detail.mapPartial⟩,
   ⟨"tail", .array tail.size .text, tail⟩]

/-- Native control emission refuses an oversized complete record before retention. -/
def controlTelemetryLine (lifecycle : Lifecycle) (detail : ControlDetail) : Except String WireText := do
  let some line := wireText (emitTelemetryFields (controlTelemetry lifecycle detail))
    | throw "control state exceeds the admitted physical-line bound"
  return line

/-- Running-phase frames cannot expose an old stopped-process tail. -/
theorem controlTail_running (lifecycle : Lifecycle) (detail : ControlDetail) (generation : UInt64)
    (running : lifecycle.phaseValue = .running generation) : controlTail lifecycle detail = [] := by
  have different : (Phase.running generation == Phase.idle) = false := rfl
  simp [controlTail, running, different]

end Acorn.Host.Viewer
