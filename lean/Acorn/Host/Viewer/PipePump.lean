/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.ProcessOwner
import Acorn.Host.Viewer.Broadcast
import Acorn.Host.Viewer.LogPump
import Acorn.Host.CheckpointDiagnostic

/-!
# Native process-output routing

Exactly one dedicated reader owns each output pipe. Stdout admission passes the
spawn's generation to the serialized broadcaster. Stderr submits to the
process-local log consumer and can report checkpoint refusal only through the
same generation gate. Completion handles and IO errors remain observable; EOF
is not synthesized on read failure. None of these capabilities writes core
stdin or supplies observations to the agent.
-/
namespace Acorn.Host.Viewer

/-- A pipe's native result separates normal EOF from failed reading. -/
inductive PipeResult where
  /-- The pipe supplied EOF after any final bounded line. -/
  | eof
  /-- A native read failed; the remaining tail was not observed. -/
  | refused (reason : String)

/-- Admission counters describe the observed stdout prefix, without asserting complete delivery. -/
structure OutputStatus where
  /-- Bounded protocol lines admitted for forwarding or pending-identity retention. -/
  published : Nat := 0
  /-- Oversized records discarded through their delimiter. -/
  oversized : Nat := 0
  /-- Invalid UTF-8 or delimiter-bearing records refused before publication. -/
  malformed : Nat := 0
  /-- Lines refused by generation or the process's frozen identity. -/
  stale : Nat := 0
  /-- Observed EOF or native failure, absent while the reader remains active. -/
  completion : Option PipeResult := none

/-- One process's readers and log task, retained until the supervisor joins them. -/
structure PipePump where
  private mk ::
  private output : Std.Mutex OutputStatus
  private stdoutTask : Task (Except IO.Error Unit)
  private stderrTask : Task (Except IO.Error PipeResult)
  private log : LogPump

private def pumpOutput (input : IO.FS.Handle) (generation : UInt64)
    (broadcast : Broadcast) (status : Std.Mutex OutputStatus) : IO Unit := do
  let result ← try
      readLines (IO.FS.Stream.ofHandle input) fun record => do
        match record with
        | .oversized => status.atomically (modify fun state =>
            { state with oversized := state.oversized + 1 })
        | .line bytes =>
          match bytes.text with
          | .error _ => status.atomically (modify fun state =>
              { state with malformed := state.malformed + 1 })
          | .ok text =>
            if text.val.startsWith "{" then
              let accepted ← broadcast.publish generation text
              status.atomically (modify fun state =>
                if accepted then { state with published := state.published + 1 }
                else { state with stale := state.stale + 1 })
      pure PipeResult.eof
    catch error => pure (.refused error.toString)
  status.atomically (modify fun state => { state with completion := some result })

private def pumpErrors (input : IO.FS.Handle) (generation : UInt64)
    (broadcast : Broadcast) (sink : LogSink) : IO PipeResult := do
  try
    readLines (IO.FS.Stream.ofHandle input) fun record => do
      sink.submit record
      if let .line bytes := record then
        if let some text := String.fromUTF8? bytes.bytes then
          if text.endsWith checkpointRefusalNotice ||
              (text.splitOn "writing disabled this run").length > 1 then
            broadcast.refuseCheckpoint generation
    return .eof
  catch error => return .refused error.toString
  finally sink.close

/-- Start readers only after the supervisor installs the successful spawn generation.
The returned owner retains all three tasks; native pipe reads and disk IO use
dedicated threads, with no network operation in a pipe callback. -/
def PipePump.start (process : ProcessOutput) (broadcast : Broadcast)
    (directory : RunDirectory) : BaseIO PipePump := do
  let status ← Std.Mutex.new ({} : OutputStatus)
  let log ← LogPump.start directory
  let stdoutTask ← IO.asTask (pumpOutput process.stdout process.generation broadcast status) .dedicated
  let stderrTask ← IO.asTask (pumpErrors process.stderr process.generation broadcast log.sink) .dedicated
  return ⟨status, stdoutTask, stderrTask, log⟩

/-- Read current admission evidence without waiting for pipe completion. -/
def PipePump.status (pump : PipePump) : BaseIO OutputStatus :=
  pump.output.atomically get

/-- Read the process-local stderr tail and persistence failures. -/
def PipePump.logStatus (pump : PipePump) : BaseIO LogStatus := pump.log.sink.status

/-- A supervisor can defer joining without spawning another set of readers or blocking controls. -/
def PipePump.ready (pump : PipePump) : BaseIO Bool := do
  return (← IO.hasFinished pump.stdoutTask) && (← IO.hasFinished pump.stderrTask) && (← pump.log.ready)

/-- Join readers after native process termination; inherited external pipe handles
can delay EOF, an OS/process-tree boundary rather than a proven join deadline. -/
def PipePump.finish (pump : PipePump) : IO (OutputStatus × PipeResult × LogStatus) := do
  let stdout ← match ← IO.wait pump.stdoutTask with
    | .error error =>
      let status ← pump.status
      pure { status with completion := some (.refused error.toString) }
    | .ok () => pump.status
  let stderr ← match ← IO.wait pump.stderrTask with
    | .error error => pure (.refused error.toString)
    | .ok result => pure result
  let log ← pump.log.finish
  return (stdout, stderr, log)

end Acorn.Host.Viewer
