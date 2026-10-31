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
file and directory sync invocation, rename and cleanup ordering. The small
`checkpoint-sync` executable exposes only the missing file-sync primitive. Standard
handle write/flush, that primitive, rename, the runtime and OS are trusted infrastructure.

The destination changes only at rename. Parent directories and temporary names
must remain stable against external mutation. Successful concurrent writers are
last-rename-wins; there is no compare-and-swap guarantee.

## What a saved report establishes

`Store.save` reports success only after these steps, in this order: a sync of the complete
temporary file, the rename, and a sync of the directory holding the rename's entry. Where each
sync reaches permanent storage, the first order keeps an image whose bytes are not there from
being named by the destination, and the second keeps the report from preceding the entry; a
power loss at any earlier point then leaves no report, and the destination names the previous
image or the new complete one.

That argument does not hold where a sync stops at the drive (the macOS fsync fallback below, and
a Linux or other file system that does not flush the disk cache) or where a drive ignores a
flush, because the order of the syncs then does not order what reaches permanent storage. macOS
fsync(2) says the drive "may also re-order the data so that later writes may be present, while
earlier writes are not". A power loss, before or after the report, can then leave the destination
naming an incomplete image with the image it replaced gone, which is the previous save lost as
well as this one. A load error other than a missing file disables writes for the run
(`Store.hooks`). Not every incomplete image need raise one: the frame's checksum detects
accidental mutation only, and the body's completeness rests on image admission
(`lean/Acorn/Host/Checkpoint/Frame.lean`).

Each sync establishes what the platform's own documentation says of the call the primitive
makes, and only that:

- Where the platform's `fcntl.h` provides F_FULLFSYNC, which is macOS, and a build for Apple
  platforms without it fails. macOS fsync(2) says fsync moves data from the host to the drive,
  which may hold it and lose it on power loss. fcntl(2) says F_FULLFSYNC does the same as fsync
  and "then asks the drive to flush all buffered data to the permanent storage device". A
  success means that request succeeded for both the file and the directory. The manuals do not
  discuss directories apart from files; that a directory's sync covers its entries is read from
  fsync(2)'s "all modified data and attributes".
- On a macOS file system lacking that request. fcntl(2) names HFS, MS-DOS (FAT), UDF and APFS as
  implementing it and lists no error for it. XNU itself recognizes a file system lacking it by
  ENOTTY, ENOTSUP or EINVAL (bsd/kern/kern_descrip.c, xnu-12377.121.6, lines 3982-3983). On
  exactly those three the primitive calls fsync, and states the fallback on standard error,
  which `requestSync` forwards. A success then means only what fsync(2) says: the data reached
  the drive, which can lose it or write it out of order on power loss. The loss of this save and
  of the image it replaced, stated above, is accepted risk on such a file system, in exchange for
  keeping a save that a refusal would discard. Every other F_FULLFSYNC error, EIO included, fails
  the save.
- On every other platform the primitive calls fsync, and any failure fails the save. Linux
  fsync(2) says the transfer "includes writing through or flushing a disk cache if present",
  that the directory's entry needs an explicit fsync of the directory, and that older kernels
  and lesser used file systems do not know how to flush disk caches. POSIX leaves the nature of
  the transfer implementation-defined, so elsewhere a success means what that system documents.
  A file system whose fsync does not flush the disk cache is the stop at the drive stated above.

A failed directory sync fails the save although the rename has happened: the destination then
names the new complete image, its durability unconfirmed.

No report covers these, which are accepted risk: a file system that does not flush the disk
cache, and a drive that ignores or misreports a flush (fcntl(2) names certain FireWire drives),
which no software here can detect, each with the loss of this save and of the image it replaced
stated above; the entries of
directories above the one holding the destination, so a power loss soon after those were created
can lose them and the checkpoint with them; and rename's atomicity across a crash, which is
assumed of the file system.
-/
namespace Acorn.Checkpoint
open Handcrafted

/-- The private file capability advances only after each required IO succeeds. -/
private inductive Stage where
  | created | written | flushed | synced | published | directorySynced

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

/-- One sync of a file or directory. A fallback the primitive states on a success reaches this
process's standard error, and failing to print it does not change that success. -/
private def requestSync (program : System.FilePath) (kind : String) (path : System.FilePath) :
    IO Unit := do
  let result ← IO.Process.output { cmd := program.toString, args := #[kind, path.toString] }
  unless result.exitCode == 0 do
    throw (IO.userError s!"checkpoint {kind} sync failed: {result.stderr}")
  unless result.stderr.isEmpty do
    try IO.eprint result.stderr
    catch _ => pure ()

/-- A failed or missing sync primitive cannot manufacture a publishable capability. -/
private def Temporary.sync (temporary : Temporary .flushed) (program : System.FilePath) :
    IO (Temporary .synced) := do
  requestSync program "file" temporary.path
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

/-- Only a completely written, flushed and synced candidate can reach replacement. -/
private def Temporary.publish (temporary : Temporary .synced) : IO (Temporary .published) := do
  IO.FS.rename temporary.path temporary.destination
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

/-- `temporaryPath` extends the destination's filename, so the rename's entry lies in the
destination's parent; a name without a separator lies in the working directory, which the
primitive inherits. -/
private def Temporary.syncDirectory (temporary : Temporary .published) (program : System.FilePath) :
    IO (Temporary .directorySynced) := do
  requestSync program "directory" (temporary.destination.parent.getD ".")
  return ⟨temporary.destination, temporary.path, temporary.handle⟩

/-- Success is reachable only through the capability of a replacement whose directory sync
succeeded; the module documentation states what that establishes on each path. -/
private def Temporary.report (_temporary : Temporary .directorySynced) (clock : UInt64) :
    Except Error UInt64 :=
  .ok clock

/-- Cleanup never deletes a collided path and never replaces the original failure. -/
private def Temporary.cleanup {stage : Stage} (temporary : Temporary stage) : IO Unit := do
  try IO.FS.removeFile temporary.path
  catch error =>
    try IO.eprintln s!"checkpoint temporary cleanup failed at {temporary.path}: {error}"
    catch _ => pure ()

/-- Save only supported profiles, and only an image within the construction's read limit, so
that `loadFile` can read every file this writes; all failures before rename leave the
destination unchanged under the stated POSIX and stable-directory assumptions. Cleanup ends at
the rename, after which the temporary path no longer names this writer's file. -/
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

/-- Native load returns the verdict of `resume` on the bytes it read: the same parser,
admission and restore as the pure theorems, then a new evaluator session. It is the one host
path from a file to a running agent. -/
@[noinline] def loadFile (construction : AgentConstruction) (receiver : construction.State) (path : System.FilePath) :
    IO (Except Error construction.State) := do
  let bytes ← readBounded construction path
  return resume construction receiver bytes.data.toList

/-- Semantic refusal carries no replacement state to the streaming runner. -/
def runnerLoad {α : Type} (result : Except Error α) : Host.CheckpointLoad α :=
  match result with
  | .ok state => .loaded state
  | .error error => .refused s!"{repr error}"

/-- Refused candidates cannot supply an agent to the existing write-admission schedule. -/
theorem runnerLoad_refused {α : Type} (error : Error) :
    runnerLoad (.error error : Except Error α) = .refused s!"{repr error}" := rfl

/-- The delivered hooks bind the existing runner to this exact receiver and destination.
A loaded state begins a new session of the predictive-agreement evaluator (`loadFile`,
`resume`); every learned field is the saved agent's. Missing input permits fresh-state
persistence; every other load error disables writes through `WritableCheckpoint.admit`.
Save errors remain visible to the runner's failure counter. -/
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
