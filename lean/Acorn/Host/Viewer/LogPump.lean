/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.RunDirectory
import Acorn.Host.Viewer.Buffer
import Acorn.Host.CheckpointDiagnostic

/-!
# Isolated stderr persistence

Each process has a separate bounded log queue and retained tail. Its pipe reader
only submits bounded lines; a dedicated consumer owns disk writes. Closing the
pump revokes submission and drains the queued prefix. The run-directory
capability independently refuses writes after archival, including a consumer
that was already waiting on its mutex. Queue overflow and IO refusal are visible
counts, never claims that every stderr byte was persisted.
-/
namespace Acorn.Host.Viewer

/-- Retained process-local stderr tail, matching the viewer display contract. -/
def logTailCapacity : Nat := 200

/-- Bounded disk backlog; storage latency cannot accumulate unbounded pending lines. -/
def logQueueCapacity : Nat := 256

/-- Read-only log delivery evidence, separate from the original line bytes. -/
structure LogStatus where
  /-- Bounded newest tail, whether or not those lines reached disk. -/
  tail : Buffer LineBytes logTailCapacity := .empty
  /-- Lines refused because the disk queue was full. -/
  dropped : Nat := 0
  /-- Oversized input records discarded before text admission. -/
  oversized : Nat := 0
  /-- Actual failed append operations. -/
  failures : Nat := 0
  /-- Most recent native error; absence is not evidence that the whole tail persisted. -/
  lastFailure : Option String := none
  /-- Canonical final checkpoint disposition survives arbitrary later log lines. -/
  checkpoint : Option CheckpointStatus := none

private structure LogState where
  accepting : Bool := true
  pending : Buffer LineBytes logQueueCapacity := .empty
  status : LogStatus := {}
  wake : IO.Promise Unit

/-- Process-local submission capability with no arbitrary file path or disk access. -/
structure LogSink where
  private mk ::
  private state : Std.Mutex LogState

/-- A retained consumer task lets the supervisor observe completion rather than detach it. -/
structure LogPump where
  private mk ::
  /-- The process's sole stderr reader submits here. -/
  sink : LogSink
  private consumer : Task (Except IO.Error Unit)

/-- Admission never waits for disk; even overflow preserves the bounded display tail. -/
def LogSink.submit (sink : LogSink) (record : LineResult) : BaseIO Unit := do
  let wake ← sink.state.atomically do
    let state ← get
    if !state.accepting then return none
    let next := match record with
      | .oversized => { state with status.oversized := state.status.oversized + 1 }
      | .line line =>
        let checkpoint := (String.fromUTF8? line.bytes).bind fun text =>
          (CheckpointStatus.parse text).or
            (if text.endsWith checkpointRefusalNotice then some .refused else none)
        let status := { state.status with
          tail := state.status.tail.retain line
          checkpoint := checkpoint.or state.status.checkpoint }
        match state.pending.offer line with
        | none => { state with status := { status with dropped := status.dropped + 1 } }
        | some pending => { state with status, pending }
    set next
    return some next.wake
  if let some wake := wake then wake.resolve ()

/-- A status snapshot has no mutation capability and keeps no unbounded history. -/
def LogSink.status (sink : LogSink) : BaseIO LogStatus :=
  sink.state.atomically do return (← get).status

/-- End input before joining the consumer; queued lines remain eligible for a write attempt. -/
def LogSink.close (sink : LogSink) : BaseIO Unit := do
  let wake ← sink.state.atomically do
    let state ← get
    set { state with accepting := false }
    return state.wake
  wake.resolve ()

private inductive LogNext where
  | done
  | line (line : LineBytes)
  | wait (task : Task (Option Unit))

private def LogSink.next (sink : LogSink) : BaseIO LogNext := do
  let wake ← IO.Promise.new
  sink.state.atomically do
    let state ← get
    match state.pending.pop with
    | some (line, pending) =>
      set { state with pending }
      return .line line
    | none =>
      if !state.accepting then return .done
      set { state with wake }
      return .wait wake.result?

private def consumeLog (sink : LogSink) (directory : RunDirectory) : IO Unit := do
  repeat
    match ← sink.next with
    | .done => return
    | .wait task =>
      if (← IO.wait task).isNone then return
    | .line line =>
      try directory.appendLog line
      catch error => sink.state.atomically (modify fun state =>
        { state with status := { state.status with
          failures := state.status.failures + 1, lastFailure := some error.toString } })

/-- One dedicated native consumer is created per owned process, with a retained join handle. -/
def LogPump.start (directory : RunDirectory) : BaseIO LogPump := do
  let sink : LogSink := ⟨← Std.Mutex.new { wake := ← IO.Promise.new }⟩
  return ⟨sink, ← IO.asTask (consumeLog sink directory) .dedicated⟩

/-- Poll the retained consumer before joining, keeping supervisor control responsive during IO. -/
def LogPump.ready (pump : LogPump) : BaseIO Bool := IO.hasFinished pump.consumer

/-- Join only after pipe completion/closure; native disk progress remains an IO assumption. -/
def LogPump.finish (pump : LogPump) : IO LogStatus := do
  pump.sink.close
  match ← IO.wait pump.consumer with
  | .error error =>
    let status ← pump.sink.status
    return { status with failures := status.failures + 1, lastFailure := some error.toString }
  | .ok () => pump.sink.status

end Acorn.Host.Viewer
