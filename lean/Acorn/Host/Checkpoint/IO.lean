import Acorn.Host.Checkpoint.Size
import Std.Sync.Mutex

namespace Acorn.Checkpoint
open Handcrafted

private inductive Stage where
  | created | written | flushed | synced | published | directorySynced

private structure Temporary (_stage : Stage) where
  destination : System.FilePath
  path : System.FilePath
  handle : IO.FS.Handle

structure Store where
  private mk ::
  private process : UInt32
  private sequence : Std.Mutex UInt64
  private syncProgram : System.FilePath

def Store.new (syncProgram : System.FilePath) : BaseIO Store := do
  return ⟨← IO.Process.getPID, ← Std.Mutex.new 0, syncProgram⟩

def Store.processId (store : Store) : UInt32 := store.process

def temporaryPath (destination : System.FilePath) (process : UInt32) (sequence : UInt64) :
    Option System.FilePath := do
  let _ ← destination.fileName
  return ⟨destination.toString ++ s!".oak-{process}-{sequence}.tmp"⟩

private def Store.next (store : Store) : BaseIO UInt64 :=
  store.sequence.atomically do
    let sequence ← get
    set (sequence + 1)
    return sequence

private def Store.reserve (store : Store) (destination : System.FilePath) : Nat → IO (Temporary .created)
  | 0 => throw (IO.userError "checkpoint temporary names exhausted")
  | remaining + 1 => do
    let sequence ← store.next
    let some path := temporaryPath destination store.process sequence
      | throw (IO.userError "checkpoint needs a filename")
    try
      let handle ← IO.FS.Handle.mk path .writeNew
      return ⟨destination, path, handle⟩
    catch error =>
      match error with
      | .alreadyExists _ _ _ => store.reserve destination remaining
      | _ => throw error

private def Temporary.write (temporary : Temporary .created) (bytes : ByteArray) : IO (Temporary .written) := do
  temporary.handle.write bytes
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

private def Temporary.flush (temporary : Temporary .written) : IO (Temporary .flushed) := do
  temporary.handle.flush
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

private def requestSync (program : System.FilePath) (kind : String) (path : System.FilePath) :
    IO Unit := do
  let result ← IO.Process.output { cmd := program.toString, args := #[kind, path.toString] }
  unless result.exitCode == 0 do
    throw (IO.userError s!"checkpoint {kind} sync failed: {result.stderr}")
  unless result.stderr.isEmpty do
    try IO.eprint result.stderr
    catch _ => pure ()

private def Temporary.sync (temporary : Temporary .flushed) (program : System.FilePath) :
    IO (Temporary .synced) := do
  requestSync program "file" temporary.path
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

private def Temporary.publish (temporary : Temporary .synced) : IO (Temporary .published) := do
  IO.FS.rename temporary.path temporary.destination
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

private def Temporary.syncDirectory (temporary : Temporary .published) (program : System.FilePath) :
    IO (Temporary .directorySynced) := do
  requestSync program "directory" (temporary.destination.parent.getD ".")
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

private def Temporary.report (_temporary : Temporary .directorySynced) (clock : UInt64) :
    Except Error UInt64 :=
  .ok clock

private def Temporary.cleanup {stage : Stage} (temporary : Temporary stage) : IO Unit := do
  try IO.FS.removeFile temporary.path
  catch error =>
    try IO.eprintln s!"checkpoint temporary cleanup failed at {temporary.path}: {error}"
    catch _ => pure ()

@[noinline] def Store.save (store : Store) (construction : AgentConstruction) (state : construction.State)
    (destination : System.FilePath) : IO (Except Error UInt64) := do
  match saveBytes construction state with
  | .error error => return .error error
  | .ok bytes =>
    if maximumBytes construction < bytes.length then return .error .oversized
    let temporary ← store.reserve destination 64
    let published ← try
      let written ← temporary.write ⟨bytes.toArray⟩
      let flushed ← written.flush
      let synced ← flushed.sync store.syncProgram
      synced.publish
    catch error =>
      temporary.cleanup
      throw error
    let directorySynced ← published.syncDirectory store.syncProgram
    return directorySynced.report state.agent.clock

private def readChunks (handle : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  let chunk ← handle.read (min (remaining + 1) 65536).toUSize
  if _empty : chunk.size = 0 then return bytes
  else if _fits : chunk.size ≤ remaining then
    readChunks handle (remaining - chunk.size) (bytes ++ chunk)
  else throw (IO.userError "checkpoint exceeds the receiving shape's maximum byte length")
termination_by remaining

def readBounded (construction : AgentConstruction) (path : System.FilePath) : IO ByteArray := do
  let handle ← IO.FS.Handle.mk path .read
  readChunks handle (maximumBytes construction) ByteArray.empty

@[noinline] def loadFile (construction : AgentConstruction) (receiver : construction.State) (path : System.FilePath) :
    IO (Except Error construction.State) := do
  let bytes ← readBounded construction path
  return resume construction receiver bytes.data.toList

def runnerLoad {α : Type} (result : Except Error α) : Host.CheckpointLoad α :=
  match result with
  | .ok state => .loaded state
  | .error error => .refused s!"{repr error}"

theorem runnerLoad_refused {α : Type} (error : Error) :
    runnerLoad (.error error : Except Error α) = .refused s!"{repr error}" := rfl

def Store.hooks (store : Store) (construction : AgentConstruction)
    (destination : System.FilePath) (interval : UInt32) : Host.CheckpointHooks construction.State where
  path := destination
  interval := interval
  load receiver _ := do
    try return runnerLoad (← loadFile construction receiver destination)
    catch error =>
      match error with
      | .noFileOrDirectory .. => return .missing
      | _ => return .refused s!"{error}"
  save state _ := do
    match ← store.save construction state destination with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"checkpoint refused: {repr error}")

end Acorn.Checkpoint
