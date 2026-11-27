import Acorn.Host.Viewer.ProcessOwner
import Acorn.Host.Viewer.Broadcast
import Acorn.Host.Viewer.LogPump
import Acorn.Host.CheckpointDiagnostic

namespace Acorn.Host.Viewer

inductive PipeResult where
  | eof
  | refused (reason : String)

structure OutputStatus where
  published : Nat := 0
  oversized : Nat := 0
  malformed : Nat := 0
  stale : Nat := 0
  completion : Option PipeResult := none

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

def PipePump.start (process : ProcessOutput) (broadcast : Broadcast)
    (directory : RunDirectory) : BaseIO PipePump := do
  let status ← Std.Mutex.new ({} : OutputStatus)
  let log ← LogPump.start directory
  let stdoutTask ← IO.asTask (pumpOutput process.stdout process.generation broadcast status) .dedicated
  let stderrTask ← IO.asTask (pumpErrors process.stderr process.generation broadcast log.sink) .dedicated
  return ⟨status, stdoutTask, stderrTask, log⟩

def PipePump.status (pump : PipePump) : BaseIO OutputStatus :=
  pump.output.atomically get

def PipePump.logStatus (pump : PipePump) : BaseIO LogStatus := pump.log.sink.status

def PipePump.ready (pump : PipePump) : BaseIO Bool := do
  return (← IO.hasFinished pump.stdoutTask) && (← IO.hasFinished pump.stderrTask) && (← pump.log.ready)

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
