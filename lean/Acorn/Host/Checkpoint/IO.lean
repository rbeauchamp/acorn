/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Size
import Std.Sync.Mutex

/-!
# Native transactional checkpoint IO

Lean owns exclusive temporary creation, complete encoding/write, buffer flush,
file-sync invocation, rename and cleanup ordering. The small `checkpoint-sync`
executable exposes only the missing POSIX file-sync primitive. Standard handle
write/flush, that primitive, rename, the runtime and OS are trusted infrastructure.

The destination changes only at rename. Parent directories and temporary names
must remain stable against external mutation. Successful concurrent writers are
last-rename-wins; there is no compare-and-swap guarantee. The parent directory is
not synced, so power-loss durability of the directory entry is not promised.
-/
namespace Acorn.Checkpoint
open Handcrafted

/-- The private file capability advances only after each required IO succeeds. -/
private inductive Stage where
  | created | written | flushed | synced

/-- Destination binding and exclusive ownership cannot be manufactured by callers. -/
private structure Temporary (_stage : Stage) where
  destination : System.FilePath
  path : System.FilePath
  handle : IO.FS.Handle

/-- Process-local naming state; exclusive creation remains the cross-process authority. -/
structure Store where
  private mk ::
  /-- Immutable invoking process identity. -/
  private process : UInt32
  /-- Serialized wrapping suffix; collisions still require successful exclusive open. -/
  private sequence : Std.Mutex UInt64
  /-- Provisioned file-sync primitive, supplied by the native bootstrap. -/
  private syncProgram : System.FilePath

/-- The current process starts a separately owned checkpoint writer. -/
def Store.new (syncProgram : System.FilePath) : BaseIO Store := do
  return ⟨← IO.Process.getPID, ← Std.Mutex.new 0, syncProgram⟩

/-- Native process identity is observable without exposing naming-state mutation. -/
def Store.processId (store : Store) : UInt32 := store.process

/-- A temporary name strictly extends the complete destination filename. -/
def temporaryPath (destination : System.FilePath) (process : UInt32) (sequence : UInt64) :
    Option System.FilePath := do
  let _ ← destination.fileName
  return ⟨destination.toString ++ s!".oak-{process}-{sequence}.tmp"⟩

/-- Every retry gets a serialized suffix; no thread can reset or replace the counter. -/
private def Store.next (store : Store) : BaseIO UInt64 :=
  store.sequence.atomically do
    let sequence ← get
    set (sequence + 1)
    return sequence

/-- A bounded retry loop owns a path only after exclusive creation succeeds. -/
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

/-- The pinned standard write primitive either writes the whole buffer or raises an IO error. -/
private def Temporary.write (temporary : Temporary .created) (bytes : ByteArray) : IO (Temporary .written) := do
  temporary.handle.write bytes
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

/-- Buffer flushing precedes the separately required file synchronization. -/
private def Temporary.flush (temporary : Temporary .written) : IO (Temporary .flushed) := do
  temporary.handle.flush
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

/-- A failed or missing sync primitive cannot manufacture a publishable capability. -/
private def Temporary.sync (temporary : Temporary .flushed) (program : System.FilePath) :
    IO (Temporary .synced) := do
  let result ← IO.Process.output { cmd := program.toString, args := #[temporary.path.toString] }
  unless result.exitCode == 0 do
    throw (IO.userError s!"checkpoint file sync failed: {result.stderr}")
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

/-- Only a completely written, flushed and synced candidate can reach replacement. -/
private def Temporary.publish (temporary : Temporary .synced) : IO Unit :=
  IO.FS.rename temporary.path temporary.destination

/-- Cleanup never deletes a collided path and never replaces the original failure. -/
private def Temporary.cleanup {stage : Stage} (temporary : Temporary stage) : IO Unit := do
  try IO.FS.removeFile temporary.path
  catch error =>
    try IO.eprintln s!"checkpoint temporary cleanup failed at {temporary.path}: {error}"
    catch _ => pure ()

/-- Save only supported profiles; all failures before rename leave the destination unchanged
under the stated POSIX and stable-directory assumptions. -/
@[noinline] def Store.save (store : Store) (construction : AgentConstruction) (state : construction.State)
    (destination : System.FilePath) : IO (Except Error UInt64) := do
  match saveBytes construction state with
  | .error error => return .error error
  | .ok bytes =>
    let temporary ← store.reserve destination 64
    try
      let written ← temporary.write ⟨bytes.toArray⟩
      let flushed ← written.flush
      let synced ← flushed.sync store.syncProgram
      synced.publish
      return .ok state.clock
    catch error =>
      temporary.cleanup
      throw error

/-- Every positive read decreases the remaining byte budget; one extra byte detects oversize input.
Short reads continue until EOF, so they cannot become an apparently complete checkpoint. -/
private def readChunks (handle : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  let chunk ← handle.read (min (remaining + 1) 65536).toUSize
  if _empty : chunk.size = 0 then return bytes
  else if _fits : chunk.size ≤ remaining then
    readChunks handle (remaining - chunk.size) (bytes ++ chunk)
  else throw (IO.userError "checkpoint exceeds the receiving shape's maximum byte length")
termination_by remaining

/-- Bounded reads use the receiving capacity and bank size, never an untrusted file count. -/
def readBounded (construction : AgentConstruction) (path : System.FilePath) : IO ByteArray := do
  let handle ← IO.FS.Handle.mk path .read
  readChunks handle (maximumBytes construction) ByteArray.empty

/-- Native load calls the same parser/admission/install definition as the pure theorems. -/
@[noinline] def loadFile (construction : AgentConstruction) (receiver : construction.State) (path : System.FilePath) :
    IO (Except Error construction.State) := do
  let bytes ← readBounded construction path
  return load construction receiver bytes.data.toList

/-- Semantic refusal carries no replacement state to the streaming runner. -/
def runnerLoad {α : Type} (result : Except Error α) : Host.CheckpointLoad α :=
  match result with
  | .ok state => .loaded state
  | .error error => .refused s!"{repr error}"

/-- Refused candidates cannot supply an agent to the existing write-admission schedule. -/
theorem runnerLoad_refused {α : Type} (error : Error) :
    runnerLoad (.error error : Except Error α) = .refused s!"{repr error}" := rfl

/-- The delivered hooks bind the existing runner to this exact receiver and destination.
Missing input permits fresh-state persistence; every other load error disables writes through
`WritableCheckpoint.admit`. Save errors remain visible to the runner's failure counter. -/
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
