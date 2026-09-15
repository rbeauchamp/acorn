/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Lifecycle
import Acorn.Host.Viewer.Line
import Std.Sync.Mutex

/-!
# Whole-run filesystem ownership

All persisted viewer files have names from a closed domain. Clear moves the
whole directory, including files unknown to this version. Its result separates
rename failure from failure to create the replacement directory: after a
successful rename the old run belongs to the archive, even if initialization
of the replacement fails.

Publication and archival share an IO mutex. A successful rename permanently
retires this directory capability, so queued old publications cannot write into
the replacement root. The supervisor opens a fresh owner for the new run and
retires the process before archival.
POSIX rename and exclusive directory creation are trusted primitives. The run
and archive parents must remain stable against external mutation and be on the
same filesystem. Directory entries are not fsynced here; power-loss durability
is not asserted. An exclusively created empty destination reserves an archive
name before rename, so this owner never replaces an existing archive.
-/
namespace Acorn.Host.Viewer

/-- The closed vocabulary for files owned by the run directory. -/
inductive RunFile where
  /-- Core checkpoint. -/
  | weights
  /-- Durable viewer identity and operator intent. -/
  | state
  /-- Temporary viewer state before atomic publication. -/
  | stateTemporary
  /-- Current stderr log. -/
  | log
  /-- Previous rotated stderr log. -/
  | previousLog
  /-- Retained sensed-world map. -/
  | explored
  /-- Temporary map before atomic publication. -/
  | exploredTemporary
  deriving DecidableEq, BEq

/-- Every run-owned path component derives from its file kind. -/
def RunFile.name : RunFile → String
  | .weights => "weights.ckpt"
  | .state => "state.json"
  | .stateTemporary => "state.json.tmp"
  | .log => "core.log"
  | .previousLog => "core.log.1"
  | .explored => "explored.map"
  | .exploredTemporary => "explored.map.tmp"

/-- A caller cannot substitute an arbitrary child name at a file-write boundary. -/
structure RunDirectory where
  private mk ::
  private root : System.FilePath
  private archiveRoot : System.FilePath
  private process : UInt32
  private sequence : Std.Mutex UInt64
  private operations : Std.Mutex (Option System.FilePath)

/-- Resolve an existing/createable directory and derive its sibling archive root. -/
def RunDirectory.open (path : System.FilePath) : IO RunDirectory := do
  IO.FS.createDirAll path
  let root ← IO.FS.realPath path
  let some parent := root.parent | throw (IO.userError "run directory needs a parent")
  let some name := root.fileName | throw (IO.userError "filesystem root cannot be a run directory")
  return ⟨root, parent / (name ++ ".archive"), ← IO.Process.getPID,
    ← Std.Mutex.new 0, ← Std.Mutex.new none⟩

/-- The admitted run root for display and whole-directory operations. -/
def RunDirectory.rootPath (directory : RunDirectory) : System.FilePath := directory.root

/-- A fixed file path; the caller supplies no path fragment. -/
def RunDirectory.path (directory : RunDirectory) (file : RunFile) : System.FilePath :=
  directory.root / file.name

/-- Open a closed run-owned file for reading; callers cannot select a write mode. -/
def RunDirectory.openRead (directory : RunDirectory) (file : RunFile) : IO IO.FS.Handle :=
  IO.FS.Handle.mk (directory.path file) .read

/-- Adopt the single legacy checkpoint location without replacing any run-owned entry.
The move is serialized with publication/archive; the stable-path POSIX assumption
also excludes an external writer racing the destination-existence check. -/
def RunDirectory.adoptStrayCheckpoint (directory : RunDirectory) : IO Bool :=
  directory.operations.atomically do
    if (← get).isSome then throw (IO.userError "retired run cannot adopt a checkpoint")
    let destination := directory.path .weights
    let destinationExists ← try
        let _ ← destination.symlinkMetadata
        pure true
      catch error => match error with
        | .noFileOrDirectory _ _ _ => pure false
        | _ => throw error
    if destinationExists then return false
    let stray : System.FilePath := "acorn-weights.ckpt"
    let metadata ← try stray.symlinkMetadata
      catch error => match error with
        | .noFileOrDirectory _ _ _ => return false
        | _ => throw error
    unless metadata.type == .file do throw (IO.userError "legacy checkpoint is not a regular file")
    IO.FS.rename stray destination
    return true

private def RunDirectory.next (directory : RunDirectory) : BaseIO UInt64 :=
  directory.sequence.atomically do
    let sequence ← get
    set (sequence + 1)
    return sequence

/-- Reserve a new temporary within the run root; crashed writes cannot force reuse.
The exclusive open owns the name, including across counter wrap or PID reuse. -/
private def RunDirectory.reserveTemporary (directory : RunDirectory) (file : RunFile) :
    Nat → IO (System.FilePath × IO.FS.Handle)
  | 0 => throw (IO.userError "viewer temporary names exhausted")
  | remaining + 1 => do
    let sequence ← directory.next
    let path := directory.root / s!"{file.name}.{directory.process}-{sequence}.tmp"
    try
      return (path, ← IO.FS.Handle.mk path .writeNew)
    catch error =>
      match error with
      | .alreadyExists _ _ _ => directory.reserveTemporary file remaining
      | _ => throw error

/-- All publication and archival through this owner share an IO mutex.
Complete write and flush precede rename; failed temporaries never replace the target. -/
def RunDirectory.publishBytes (directory : RunDirectory) (file : RunFile) (bytes : ByteArray) : IO Unit :=
  directory.operations.atomically do
    if let some archive := ← get then
      throw (IO.userError s!"run-directory owner retired into {archive}")
    let (temporary, handle) ← directory.reserveTemporary file 64
    try
      handle.write bytes
      handle.flush
      IO.FS.rename temporary (directory.path file)
    catch error =>
      try IO.FS.removeFile temporary catch _ => pure ()
      throw error

/-- Rotation threshold for the two retained stderr files. -/
def logCapacity : Nat := 4 * 1024 * 1024

/-- Append one bounded raw stderr line under the same retirement lock as all writes.
Rotation failure refuses the write, so it cannot silently resume appending to a
full file. A dedicated log consumer must isolate filesystem latency and errors
from the core's pipe reader. The current file is at most `logCapacity +
lineCapacity` bytes after a successful append, under the stable-path and native
write assumptions; a preexisting oversized file is rotated before writing. -/
def RunDirectory.appendLog (directory : RunDirectory) (line : LineBytes) : IO Unit :=
  directory.operations.atomically do
    if let some archive := ← get then
      throw (IO.userError s!"run-directory owner retired into {archive}")
    let size ← try pure (← (directory.path .log).metadata).byteSize.toNat
      catch error =>
        match error with
        | .noFileOrDirectory _ _ _ => pure 0
        | _ => throw error
    if size ≥ logCapacity then
      IO.FS.rename (directory.path .log) (directory.path .previousLog)
    let handle ← IO.FS.Handle.mk (directory.path .log) .append
    handle.write line.bytes
    handle.write ⟨#[10]⟩
    handle.flush

/-- The rotation guard and admitted line size derive the maximum successful append size.
This arithmetic law does not assert filesystem execution or exclude external writers. -/
theorem log_append_bound (prior : Nat) (line : LineBytes) (room : prior < logCapacity) :
    prior + line.bytes.size + 1 ≤ logCapacity + lineCapacity := by
  have := line.bounded
  omega

/-- Archive failures carry the actual effect boundary, without claiming rollback. -/
inductive ArchiveResult where
  /-- No run-directory rename completed. -/
  | unchanged (reason : String)
  /-- The whole old run moved, but no fresh directory could be created. -/
  | moved (archive : System.FilePath) (reason : String)
  /-- The old run moved and an empty replacement directory exists. -/
  | ready (archive : System.FilePath)

private def RunDirectory.reserveArchive (directory : RunDirectory) (stamp : UInt64) :
    Nat → IO System.FilePath
  | 0 => throw (IO.userError "archive names exhausted")
  | attempts + 1 => do
    let destination := directory.archiveRoot / s!"{stamp}-{attempts}"
    try
      IO.FS.createDir destination
      return destination
    catch error =>
      match error with
      | .alreadyExists _ _ _ => directory.reserveArchive stamp attempts
      | _ => throw error

/-- Rename replaces only this operation's exclusively reserved empty directory.
Failure after the rename is explicitly distinct from an unchanged old run. -/
private def RunDirectory.archiveLocked (directory : RunDirectory) (stamp : UInt64) : IO ArchiveResult := do
  let destination ← try
      IO.FS.createDirAll directory.archiveRoot
      directory.reserveArchive stamp 64
    catch error => return .unchanged error.toString
  try
    IO.FS.rename directory.root destination
  catch error =>
    let cleanup ← try
        IO.FS.removeDir destination
        pure ""
      catch cleanup => pure s!"; empty reservation remains at {destination}: {cleanup}"
    return .unchanged (error.toString ++ cleanup)
  try
    IO.FS.createDir directory.root
    return .ready destination
  catch error =>
    return .moved destination error.toString

/-- Archival cannot interleave with publication and permanently revokes this writer after rename. -/
def RunDirectory.archive (directory : RunDirectory) (stamp : UInt64) : IO ArchiveResult :=
  directory.operations.atomically do
    if let some archive := ← get then
      return .moved archive "run-directory owner already retired"
    let result ← directory.archiveLocked stamp
    match result with
    | .unchanged _ => pure ()
    | .moved archive _ | .ready archive => set (some archive)
    return result

private def entropyBytes (handle : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  if remaining = 0 then return bytes
  let chunk ← handle.read remaining.toUSize
  if _empty : chunk.size = 0 then throw (IO.userError "OS entropy source ended")
  else if _fits : chunk.size ≤ remaining then
    entropyBytes handle (remaining - chunk.size) (bytes ++ chunk)
  else throw (IO.userError "OS entropy read exceeded its request")
termination_by remaining

/-- Mint a control token from the OS entropy device through the reviewed filesystem owner.
No caller supplies a path, mode, token value or predictable fallback. -/
def mintControlToken : IO String := do
  let handle ← IO.FS.Handle.mk "/dev/urandom" .read
  let bytes ← entropyBytes handle 16 ByteArray.empty
  let digit := fun (n : Nat) => Char.ofNat (if n < 10 then 48 + n else 87 + n)
  return String.ofList (bytes.data.toList.flatMap fun byte =>
    [digit (byte.toNat / 16), digit (byte.toNat % 16)])

end Acorn.Host.Viewer
