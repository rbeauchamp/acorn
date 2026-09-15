/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Control
import Acorn.Host.Viewer.Buffer
import Acorn.Host.Viewer.Retry

/-!
# Viewer process ownership

A process generation is distinct from durable run identity. Retirement revokes
its output capability before archive or replacement. The native shell must
serialize the pure transition and the associated observer write under one
mutex. OS process termination and filesystem rename are reported effects, not
conclusions of these pure definitions.
-/
namespace Acorn.Host.Viewer

/-- The only requests available to an observer's operator. -/
inductive Command where
  /-- Request a process for the current durable run. -/
  | start
  /-- Request wind-up at the next attempt boundary. -/
  | stop
  /-- Request retirement followed by whole-directory archival. -/
  | clear
  deriving DecidableEq, BEq

/-- Unknown control words cannot select a lifecycle action. -/
def Command.parse : String → Option Command
  | "start" => some .start
  | "stop" => some .stop
  | "clear" => some .clear
  | _ => none

/-- Durable world and logical agent identity; process restarts have separate generations. -/
structure Identity where
  /-- Opaque durable run identifier. -/
  run : UInt64
  /-- World generation seed. -/
  seed : UInt64
  /-- Durable logical agent identity within a run. -/
  agentEpoch : UInt64
  deriving DecidableEq, BEq

/-- Operator intent persists across process failure. -/
inductive Desired where
  /-- Maintain a process subject to the failure limit. -/
  | running
  /-- Leave the process stopped. -/
  | stopped
  deriving DecidableEq, BEq

/-- A live generation exists only while a process can supply accepted output. -/
inductive Phase where
  /-- No process owns observation writes. -/
  | idle
  /-- A reserved generation is awaiting a spawn result. -/
  | starting (generation : UInt64)
  /-- The current process owns writes. -/
  | running (generation : UInt64)
  /-- The current process may finish its attempt and emit its final records. -/
  | stopping (generation : UInt64)
  /-- All process observation capabilities have been revoked. -/
  | archiving
  deriving DecidableEq, BEq

/-- Only an installed live process can admit output. -/
def Phase.accepts (phase : Phase) (generation : UInt64) : Bool :=
  match phase with
  | .running current | .stopping current => current == generation
  | .idle | .starting _ | .archiving => false

/-- Complete process intent, generation allocator and durable identity state. -/
structure Lifecycle where
  private mk ::
  /-- Durable identity changes only after successful archive/new-directory admission. -/
  private identity : Identity
  /-- Current native lifecycle boundary. -/
  private phase : Phase := .idle
  /-- Operator intent. -/
  private desired : Desired := .stopped
  /-- Last reserved generation; exhaustion refuses further spawns instead of wrapping. -/
  private lastGeneration : UInt64 := 0
  /-- Clear waits for retirement before any filesystem effect. -/
  private clearPending : Option Desired := none
  /-- A current-process refusal disarms checkpoint writes for its run. -/
  private checkpointRefused : Bool := false
  /-- Failure budget and elapsed backoff are enforced before each reservation. -/
  private retry : Retry := .initial

/-- Native startup has no live process or inherited generation capability. -/
def Lifecycle.initial (identity : Identity) (desired : Desired) : Lifecycle :=
  { identity, desired }

/-- Read-only durable identity for publication and frame admission. -/
def Lifecycle.identityValue (state : Lifecycle) : Identity := state.identity

/-- Read-only process phase; callers cannot write allocator or phase fields. -/
def Lifecycle.phaseValue (state : Lifecycle) : Phase := state.phase

/-- Read-only current operator intent. -/
def Lifecycle.desiredValue (state : Lifecycle) : Desired := state.desired

/-- Read-only current-process checkpoint refusal indicator. -/
def Lifecycle.checkpointRefusedValue (state : Lifecycle) : Bool := state.checkpointRefused

/-- Read-only consecutive-failure count for control telemetry. -/
def Lifecycle.failureCount (state : Lifecycle) : Nat := state.retry.count

/-- Clear's retained post-archive intent is visible only after process retirement. -/
def Lifecycle.archiveIntent (state : Lifecycle) : Option Desired :=
  if state.phase == .idle then state.clearPending else none

/-- A queued operator change during replacement publication changes only its
post-archive intent; it cannot leave the archival phase or admit a process. -/
def Lifecycle.replacementIntent (state : Lifecycle) (desired : Desired) : Lifecycle :=
  if state.phase == .archiving then { state with clearPending := some desired } else state

/-- Pure command handling never starts a second process or archives a live one. -/
def Lifecycle.request (state : Lifecycle) (command : Command) : Lifecycle :=
  match command with
  | .start => { state with desired := .running, clearPending := none, retry := .initial }
  | .stop =>
    { state with desired := .stopped, clearPending := none, phase := match state.phase with
        | .running generation => .stopping generation
        | phase => phase }
  | .clear =>
    { state with
      desired := .stopped, clearPending := state.clearPending.or (some state.desired)
      phase := match state.phase with
        | .running generation => .stopping generation
        | phase => phase }

/-- A spawn is reserved only from idle state, without generation reuse or overlap. -/
def Lifecycle.reserve (state : Lifecycle) (now : UInt64) : Option (UInt64 × Lifecycle) :=
  if state.phase == .idle && state.desired == .running && state.clearPending.isNone &&
      state.lastGeneration != 18446744073709551615 && state.retry.ready now then
    let generation := state.lastGeneration + 1
    some (generation, { state with phase := .starting generation, lastGeneration := generation })
  else none

/-- A spawn result installs only its own still-reserved generation. -/
def Lifecycle.started (state : Lifecycle) (generation : UInt64) : Lifecycle :=
  if state.phase == .starting generation then
    { state with phase := if state.desired == .stopped || state.clearPending.isSome then
        .stopping generation else .running generation, checkpointRefused := false }
  else state

/-- Only a failed spawn or unexpectedly exited running process consumes the restart budget. -/
def Lifecycle.acceptsFailure (state : Lifecycle) (generation : UInt64) : Bool :=
  state.phase == .starting generation || state.phase == .running generation

/-- Failure retirement and the next reservation policy update are one transition. -/
def Lifecycle.failed (state : Lifecycle) (generation now : UInt64) (healthy : Bool) : Lifecycle :=
  if state.acceptsFailure generation then
    let retry := state.retry.failed now healthy
    { state with
      phase := .idle, retry
      desired := if retry.exhausted then .stopped else state.desired }
  else state

/-- Reaping revokes observation rights before any later filesystem action. -/
def Lifecycle.retire (state : Lifecycle) (generation : UInt64) : Lifecycle :=
  if state.phase.accepts generation || state.phase == .starting generation then
    { state with phase := .idle }
  else state

/-- Only an idle owner with pending Clear may enter archival. -/
def Lifecycle.beginArchive (state : Lifecycle) : Option Lifecycle :=
  if state.phase == .idle && state.clearPending.isSome then
    some { state with phase := .archiving }
  else none

/-- Install fresh identity only after the IO owner reports completed archival and creation.
Distinct run identity is an admission condition, never inferred from a timestamp. -/
def Lifecycle.archived (state : Lifecycle) (identity : Identity) : Option Lifecycle :=
  if state.phase == .archiving && identity.run != state.identity.run then
    some { state with
      identity := identity
      phase := .idle
      desired := state.clearPending.getD state.desired
      clearPending := none
      checkpointRefused := false
      retry := .initial }
  else none

/-- Failed archival leaves the old identity installed and disables automatic restart. -/
def Lifecycle.archiveFailed (state : Lifecycle) : Lifecycle :=
  if state.phase == .archiving then
    { state with phase := .idle, desired := .stopped, clearPending := none }
  else state

/-- Late checkpoint refusal text cannot disarm another process's checkpoint writes. -/
def Lifecycle.refuseCheckpoint (state : Lifecycle) (generation : UInt64) : Lifecycle :=
  if state.phase.accepts generation then { state with checkpointRefused := true } else state

/-- Only the active process can install its checkpoint-selected logical identity.
The broadcaster separately freezes the first admitted identity for this generation. -/
def Lifecycle.adoptIdentity (state : Lifecycle) (generation : UInt64) (identity : Identity) : Lifecycle :=
  if state.phase.accepts generation then { state with identity } else state

/-- The last reserved generation retains identity attribution while its readers
drain in idle phase. This does not confer observation-forwarding rights. -/
def Lifecycle.ownsIdentity (state : Lifecycle) (generation : UInt64) : Bool :=
  state.phase.accepts generation || (state.phase == .idle && state.lastGeneration == generation)

/-- Final stderr attribution may record refusal only while the generation still owns identity. -/
def Lifecycle.refuseFinalCheckpoint (state : Lifecycle) (generation : UInt64) : Lifecycle :=
  if state.ownsIdentity generation then { state with checkpointRefused := true } else state

/-- Final refusal records a fault without reviving observation or process ownership. -/
theorem Lifecycle.finalRefusal_phase (state : Lifecycle) (generation : UInt64) :
    (state.refuseFinalCheckpoint generation).phase = state.phase := by
  simp [refuseFinalCheckpoint]; split <;> rfl

/-- A generation that no longer owns identity cannot alter checkpoint status. -/
theorem Lifecycle.finalRefusal_stale (state : Lifecycle) (generation : UInt64)
    (stale : state.ownsIdentity generation = false) :
    state.refuseFinalCheckpoint generation = state := by simp [refuseFinalCheckpoint, stale]

/-- Final pipe drain may complete identity attribution before any subsequent
reservation or archive. Frame forwarding remains governed by `Phase.accepts`. -/
def Lifecycle.adoptFinalIdentity (state : Lifecycle) (generation : UInt64) (identity : Identity) : Lifecycle :=
  if state.ownsIdentity generation then { state with identity } else state

/-- Final identity attribution cannot resurrect observation rights. -/
theorem Lifecycle.finalIdentity_phase (state : Lifecycle) (generation : UInt64) (identity : Identity) :
    (state.adoptFinalIdentity generation identity).phase = state.phase := by
  simp [adoptFinalIdentity]; split <;> rfl

/-- A retired process cannot change durable identity. -/
theorem Lifecycle.stale_identity (state : Lifecycle) (generation : UInt64) (identity : Identity)
    (stale : state.phase.accepts generation = false) :
    state.adoptIdentity generation identity = state := by simp [adoptIdentity, stale]

/-- Generation admission wraps the entire observer mutation, not just a preliminary read. -/
def Lifecycle.admit {α : Type} (state : Lifecycle) (generation : UInt64)
    (value : α) (write : α → α) : α :=
  if state.phase.accepts generation then write value else value

/-- Every stale writer preserves the complete observer state. -/
theorem Lifecycle.stale_preserves {α : Type} (state : Lifecycle) (generation : UInt64)
    (value : α) (write : α → α) (stale : state.phase.accepts generation = false) :
    state.admit generation value write = value := by simp [admit, stale]

/-- The retiring generation can no longer write, regardless of its prior phase. -/
theorem Lifecycle.retire_revokes (state : Lifecycle) (generation : UInt64) :
    (state.retire generation).phase.accepts generation = false := by
  simp only [retire]
  split
  · rfl
  · rename_i h
    cases phase : state.phase <;> simp_all [Phase.accepts]

/-- Operator commands preserve durable identity. -/
theorem Lifecycle.request_identity (state : Lifecycle) (command : Command) :
    (state.request command).identity = state.identity := by cases command <;> rfl

/-- Repeated Clear preserves the original post-archive intent and pending retirement. -/
theorem Lifecycle.clear_idempotent (state : Lifecycle) :
    (state.request .clear).request .clear = state.request .clear := by
  rcases state with ⟨identity, phase, desired, generation, pending, refused, retry⟩
  cases phase <;> cases pending <;> rfl

/-- A late stderr refusal cannot alter current state. -/
theorem Lifecycle.stale_refusal (state : Lifecycle) (generation : UInt64)
    (stale : state.phase.accepts generation = false) :
    state.refuseCheckpoint generation = state := by simp [refuseCheckpoint, stale]

/-- A successfully started process retains the durable run identity. -/
theorem Lifecycle.started_identity (state : Lifecycle) (generation : UInt64) :
    (state.started generation).identity = state.identity := by
  simp [started]; split <;> rfl

/-- An archiving owner accepts no generation, including an old buffered tail. -/
theorem Phase.archiving_rejects (generation : UInt64) :
    Phase.archiving.accepts generation = false := rfl

end Acorn.Host.Viewer
