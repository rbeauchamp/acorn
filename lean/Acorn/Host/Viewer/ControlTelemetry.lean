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
the supervisor's step decided. Transition reasons and native stderr come with the
step's detail. Whether the current process refused its checkpoint and whether the
retained map may miss observations are the observer's own facts. Text passes
through the shared JSON string encoder, and the final physical record passes
through the same byte and delimiter admission as frames.
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

/-- One phase per constructor. The generation never reaches the wire spelling, so these
carry every actual-phase tag the supervisor can emit. -/
def Phase.representatives : List Phase :=
  [.starting 0, .running 0, .stopping 0, .archiving, .idle]

/-- Every phase is spelled like one of its representatives. -/
theorem Phase.controlTag_represented (phase : Phase) :
    phase.controlTag ∈ Phase.representatives.map Phase.controlTag := by
  cases phase <;> simp [Phase.representatives, Phase.controlTag]

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
  /-- Observed nonzero child exit; cleared with the process-local log at launch. -/
  abnormalExit : Bool := false

/-- Facts the observer holds about the current run's output, which no supervisor decision
writes: the stderr reader's report of a refused checkpoint and the possibility that the
retained map misses observations. -/
structure ControlObservation where
  /-- The current process refused its checkpoint, so it saves nothing this run. -/
  checkpointRefused : Bool := false
  /-- Persistent possibility of lost world observations, independent of agent epoch. -/
  mapPartial : Bool := false

/-- Diagnostic presentation is capped independently of the authoritative state.
The marker makes omitted text explicit; JSON escaping may enlarge each retained
character, but no unbounded native error can consume the physical frame budget. -/
def controlDiagnostic (text : String) : String :=
  let retained := text.toList.take 1024
  String.ofList retained ++ if text.length > 1024 then " [truncated]" else ""

/-- Explain the exhausted restart budget for every failure route at publication. Keep the
capped cause and append the explanation afterwards, so truncation cannot hide exhaustion. -/
def controlReason (lifecycle : Lifecycle) (detail : ControlDetail) : String :=
  controlDiagnostic detail.reason ++ if lifecycle.exhausted then
    s!" — gave up after {failureLimit} failed starts in a row" else ""

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

/-- **Every published reason explains exhausted retries without losing the capped cause.**
For every lifecycle, observation and detail, the fields consumed by the control encoder append
the UX-24 sentence exactly at three failures. The stopped reason remains idle-only; the
transition reason is always present. This covers exits and spawn refusals through their shared
publication boundary, without assuming the text or length of their cause. -/
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

/-- Native control emission refuses an oversized complete record before retention. -/
def controlTelemetryLine (lifecycle : Lifecycle) (observed : ControlObservation)
    (detail : ControlDetail) : Except String WireText := do
  let some line := wireText (emitTelemetryFields (controlTelemetry lifecycle observed detail))
    | throw "control state exceeds the admitted physical-line bound"
  return line

/-- Running-phase frames cannot expose an old stopped-process tail. -/
theorem controlTail_running (lifecycle : Lifecycle) (detail : ControlDetail) (generation : UInt64)
    (running : lifecycle.phaseValue = .running generation) : controlTail lifecycle detail = [] := by
  have different : (Phase.running generation == Phase.idle) = false := rfl
  simp [controlTail, running, different]

end Acorn.Host.Viewer
