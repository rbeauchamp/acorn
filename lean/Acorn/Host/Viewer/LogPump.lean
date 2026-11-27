import Acorn.Host.Viewer.RunDirectory
import Acorn.Host.Viewer.Buffer
import Acorn.Host.CheckpointDiagnostic
import Acorn.Host.Forever

namespace Acorn.Host.Viewer

def logTailCapacity : Nat := 200

def logQueueCapacity : Nat := 256

structure LogStatus where
  tail : Buffer LineBytes logTailCapacity := .empty
  dropped : Nat := 0
  oversized : Nat := 0
  failures : Nat := 0
  lastFailure : Option String := none
  checkpoint : Option CheckpointStatus := none

private structure LogState where
  accepting : Bool := true
  pending : Buffer LineBytes logQueueCapacity := .empty
  status : LogStatus := {}
  wake : IO.Promise Unit

structure LogSink where
  private mk ::
  private state : Std.Mutex LogState

structure LogPump where
  private mk ::
  sink : LogSink
  private consumer : Task (Except IO.Error Unit)

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

def LogSink.status (sink : LogSink) : BaseIO LogStatus :=
  sink.state.atomically do return (← get).status

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
  for _ in forever do
    match ← sink.next with
    | .done => return
    | .wait task =>
      if (← IO.wait task).isNone then return
    | .line line =>
      try directory.appendLog line
      catch error => sink.state.atomically (modify fun state =>
        { state with status := { state.status with
          failures := state.status.failures + 1, lastFailure := some error.toString } })

def LogPump.start (directory : RunDirectory) : BaseIO LogPump := do
  let sink : LogSink := ⟨← Std.Mutex.new { wake := ← IO.Promise.new }⟩
  return ⟨sink, ← IO.asTask (consumeLog sink directory) .dedicated⟩

def LogPump.ready (pump : LogPump) : BaseIO Bool := IO.hasFinished pump.consumer

def LogPump.finish (pump : LogPump) : IO LogStatus := do
  pump.sink.close
  match ← IO.wait pump.consumer with
  | .error error =>
    let status ← pump.sink.status
    return { status with failures := status.failures + 1, lastFailure := some error.toString }
  | .ok () => pump.sink.status

end Acorn.Host.Viewer
