import Acorn.Host.Viewer.PipePump

namespace Acorn.Host.Viewer

private inductive ProcessSlot where
  | spawned (output : ProcessOutput)
  | live (generation : UInt64) (pump : PipePump)
  | draining (pump : PipePump)

structure SupervisedProcess where
  private mk ::
  private owner : ProcessOwner
  private broadcast : Broadcast
  private slot : Std.Mutex (Option ProcessSlot)

def SupervisedProcess.new (broadcast : Broadcast) : BaseIO SupervisedProcess := do
  return ⟨← ProcessOwner.new, broadcast, ← Std.Mutex.new none⟩

def SupervisedProcess.spawn (process : SupervisedProcess) (generation : UInt64)
    (executable : System.FilePath) (arguments : Array String) : IO (Except String Unit) :=
  process.slot.atomically do
    if (← get).isSome then return .error "a core process or its readers still own the run"
    try
      let output ← process.owner.spawn generation executable arguments
      set (some (ProcessSlot.spawned output))
      return .ok ()
    catch error => return .error error.toString

private def ProcessSlot.attach (slot : ProcessSlot) (broadcast : Broadcast)
    (directory : RunDirectory) : BaseIO ProcessSlot := do
  match slot with
  | .spawned output =>
    return .live output.generation (← PipePump.start output broadcast directory)
  | slot => return slot

def SupervisedProcess.attach (process : SupervisedProcess) (generation : UInt64)
    (directory : RunDirectory) : BaseIO Unit :=
  process.slot.atomically do
    if let some (.spawned output) := ← get then
      if output.generation == generation then
        set (some (← (ProcessSlot.spawned output).attach process.broadcast directory))

def SupervisedProcess.windUp (process : SupervisedProcess) (generation : UInt64) :
    IO (Except String Unit) := do
  match ← process.owner.windUp generation with
  | .refused reason => return .error reason
  | .stale | .alreadyRequested | .sent => return .ok ()

inductive ProcessObservation where
  | quiet
  | exited (code : UInt32) (uptimeMs : Nat)
  | finished (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus)
  | refused (reason : String)

def SupervisedProcess.poll (process : SupervisedProcess) (directory : RunDirectory) :
    IO ProcessObservation :=
  process.slot.atomically do
    let some slot ← get | return .quiet
    let slot ← slot.attach process.broadcast directory
    set (some slot)
    match slot with
    | .spawned _ => return .quiet
    | .draining pump =>
      if !(← pump.ready) then return .quiet
      let (stdout, stderr, log) ← pump.finish
      set (none : Option ProcessSlot)
      return .finished stdout stderr log
    | .live generation pump =>
      match ← process.owner.poll generation with
      | .stale => return .refused "supervisor lost its owned process generation"
      | .refused reason => return .refused reason
      | .running _ => return .quiet
      | .exited code uptime =>
        set (some (ProcessSlot.draining pump))
        return .exited code uptime

def SupervisedProcess.archive (process : SupervisedProcess) (directory : RunDirectory)
    (stamp : UInt64) : IO ArchiveResult :=
  process.slot.atomically do
    if (← get).isSome then return .unchanged "a core process or its readers still own the run"
    directory.archive stamp

end Acorn.Host.Viewer
