import Acorn.Host.Viewer.ProcessOwner
import Acorn.Host.Viewer.Broadcast
import Acorn.Host.Viewer.LogPump
import Acorn.Host.CheckpointDiagnostic
import Acorn.Host.Forever

namespace Acorn.Host.Viewer

def outputQueueCapacity : Nat := 256

inductive PipeResult where
  | eof
  | refused (reason : String)

structure OutputStatus where
  published : Nat := 0
  oversized : Nat := 0
  malformed : Nat := 0
  stale : Nat := 0
  dropped : Nat := 0
  completion : Option PipeResult := none

private structure OutputQueueState where
  accepting : Bool := true
  pending : Buffer (WireText × Nat) outputQueueCapacity := .empty
  pendingDrops : Nat := 0
  status : OutputStatus := {}
  wake : IO.Promise Unit

structure PipePump where
  private mk ::
  private output : Std.Mutex OutputQueueState
  private stdoutTask : Task (Except IO.Error Unit)
  private consumerTask : Task (Except IO.Error Unit)
  private stderrTask : Task (Except IO.Error PipeResult)
  private log : LogPump

private def submitOutput (queue : Std.Mutex OutputQueueState) (text : WireText)
    (nowMonoMs : Nat) : BaseIO Unit := do
  let wake ← queue.atomically do
    let state ← get
    if !state.accepting then return none
    let evicted := state.pending.values.length == outputQueueCapacity
    let pending := state.pending.retain (text, nowMonoMs)
    let pendingDrops := state.pendingDrops + if evicted then 1 else 0
    let status := if evicted then { state.status with dropped := state.status.dropped + 1 }
      else state.status
    set { state with pending, pendingDrops, status }
    return some state.wake
  if let some wake := wake then wake.resolve ()

private def closeOutput (queue : Std.Mutex OutputQueueState) : BaseIO Unit := do
  let wake ← queue.atomically do
    let state ← get
    set { state with accepting := false }
    return state.wake
  wake.resolve ()

private inductive OutputNext where
  | done
  | item (text : WireText) (nowMonoMs : Nat) (drops : Nat)
  | wait (task : Task (Option Unit))

private def nextOutput (queue : Std.Mutex OutputQueueState) : BaseIO OutputNext := do
  let wake ← IO.Promise.new
  queue.atomically do
    let state ← get
    match state.pending.pop with
    | some ((text, nowMonoMs), pending) =>
      set { state with pending, pendingDrops := 0 }
      return .item text nowMonoMs state.pendingDrops
    | none =>
      if !state.accepting then return .done
      set { state with wake }
      return .wait wake.result?

private def consumeOutput (queue : Std.Mutex OutputQueueState) (generation : UInt64)
    (broadcast : Broadcast) : IO Unit := do
  for _ in forever do
    match ← nextOutput queue with
    | .done => return
    | .wait task =>
      if (← IO.wait task).isNone then return
    | .item text nowMonoMs drops =>
      if drops > 0 then
        broadcast.recordIngressDrop generation drops
      let decoded := decodeTelemetry text
      let accepted ← broadcast.publishDecoded generation decoded nowMonoMs
      queue.atomically (modify fun state =>
        let status := if accepted then { state.status with published := state.status.published + 1 }
          else { state.status with stale := state.status.stale + 1 }
        { state with status })

private def pumpOutput (input : IO.FS.Handle) (queue : Std.Mutex OutputQueueState) : IO Unit := do
  let result ← try
      readLines (IO.FS.Stream.ofHandle input) fun record => do
        match record with
        | .oversized => queue.atomically (modify fun state =>
            { state with status := { state.status with oversized := state.status.oversized + 1 } })
        | .line bytes =>
          match bytes.text with
          | .error _ => queue.atomically (modify fun state =>
              { state with status := { state.status with malformed := state.status.malformed + 1 } })
          | .ok text =>
            if text.val.startsWith "{" then
              let nowMonoMs ← IO.monoMsNow
              submitOutput queue text nowMonoMs
      pure PipeResult.eof
    catch error => pure (.refused error.toString)
    finally closeOutput queue
  queue.atomically (modify fun state =>
    { state with status := { state.status with completion := some result } })

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
  let output ← Std.Mutex.new ({ wake := ← IO.Promise.new } : OutputQueueState)
  let log ← LogPump.start directory
  let stdoutTask ← IO.asTask (pumpOutput process.stdout output) .dedicated
  let consumerTask ← IO.asTask (consumeOutput output process.generation broadcast) .dedicated
  let stderrTask ← IO.asTask (pumpErrors process.stderr process.generation broadcast log.sink) .dedicated
  return ⟨output, stdoutTask, consumerTask, stderrTask, log⟩

def PipePump.status (pump : PipePump) : BaseIO OutputStatus :=
  pump.output.atomically do return (← get).status

def PipePump.logStatus (pump : PipePump) : BaseIO LogStatus := pump.log.sink.status

def PipePump.ready (pump : PipePump) : BaseIO Bool := do
  return (← IO.hasFinished pump.stdoutTask) && (← IO.hasFinished pump.consumerTask) &&
    (← IO.hasFinished pump.stderrTask) && (← pump.log.ready)

def PipePump.finish (pump : PipePump) : IO (OutputStatus × PipeResult × LogStatus) := do
  let stdoutErr ← match ← IO.wait pump.stdoutTask with
    | .error error => pure (some error.toString)
    | .ok () => pure none
  closeOutput pump.output
  let consumerErr ← match ← IO.wait pump.consumerTask with
    | .error error => pure (some error.toString)
    | .ok () => pure none
  let baseStatus ← pump.status
  let stdout := match stdoutErr.or consumerErr with
    | some reason => { baseStatus with completion := some (.refused reason) }
    | none => baseStatus
  let stderr ← match ← IO.wait pump.stderrTask with
    | .error error => pure (.refused error.toString)
    | .ok result => pure result
  let log ← pump.log.finish
  return (stdout, stderr, log)

end Acorn.Host.Viewer
