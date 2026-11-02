/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.PipePump

/-!
# The supervised child and its readers

The child, its generation and its readers share one native slot. The slot stays occupied
until every pipe and log task finishes, so archival cannot race a retained run-directory
writer. Neither control submission nor a poll waits for pipe EOF. An external descendant
retaining a pipe may delay retirement indefinitely; no native join deadline is claimed.

The slot decides nothing about the lifecycle: the supervisor's step says when to spawn, start
the readers, send the stop line and join (`Acorn.Host.Viewer.Supervision`), and this module
performs each and reports what the operating system answered.
-/
namespace Acorn.Host.Viewer

private inductive ProcessSlot where
  | spawned (output : ProcessOutput)
  | live (generation : UInt64) (pump : PipePump)
  | draining (pump : PipePump)

/-- Supervisor process capability owns the process and every task that can write its run. -/
structure SupervisedProcess where
  private mk ::
  private owner : ProcessOwner
  private broadcast : Broadcast
  private slot : Std.Mutex (Option ProcessSlot)

/-- An empty process capability uses the same broadcaster as HTTP observation. -/
def SupervisedProcess.new (broadcast : Broadcast) : BaseIO SupervisedProcess := do
  return ⟨← ProcessOwner.new, broadcast, ← Std.Mutex.new none⟩

/-- Spawn the child of a reserved generation. Its readers start only when the step attaches
them, after the broadcaster holds the generation's output for its identity. A native spawn
error leaves the slot empty; the generation stays consumed by both allocators. -/
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

/-- Start the readers of the spawned child of this generation. -/
def SupervisedProcess.attach (process : SupervisedProcess) (generation : UInt64)
    (directory : RunDirectory) : BaseIO Unit :=
  process.slot.atomically do
    if let some (.spawned output) := ← get then
      if output.generation == generation then
        set (some (← (ProcessSlot.spawned output).attach process.broadcast directory))

/-- Send the child its one stop line. A refusal is reported; a child that already took the
line, or that no longer exists, has nothing more to receive. -/
def SupervisedProcess.windUp (process : SupervisedProcess) (generation : UInt64) :
    IO (Except String Unit) := do
  match ← process.owner.windUp generation with
  | .refused reason => return .error reason
  | .stale | .alreadyRequested | .sent => return .ok ()

/-- What a poll observed of the slot. -/
inductive ProcessObservation where
  /-- No change: no child, a live child, or readers still draining. -/
  | quiet
  /-- The live child was reaped with this status after this many milliseconds. -/
  | exited (code : UInt32) (uptimeMs : Nat)
  /-- The reaped child's readers and log writer finished; the slot is empty. -/
  | finished (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus)
  /-- The native wait refused; the slot stays owned. -/
  | refused (reason : String)

/-- Poll without waiting for pipe completion. A spawned child whose readers did not start,
because an effect before their start failed, has them started here, so its pipes are read
while it lives. -/
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

/-- Archive the run directory while no child or reader owns it; an owned slot leaves the run
unchanged. -/
def SupervisedProcess.archive (process : SupervisedProcess) (directory : RunDirectory)
    (stamp : UInt64) : IO ArchiveResult :=
  process.slot.atomically do
    if (← get).isSome then return .unchanged "a core process or its readers still own the run"
    directory.archive stamp

end Acorn.Host.Viewer
