import Acorn.Host.Viewer.Lifecycle
import Acorn.Host.Viewer.Line
import Std.Sync.Mutex

namespace Acorn.Host.Viewer

inductive RunFile where
  | weights
  | state
  | stateTemporary
  | log
  | previousLog
  | explored
  | exploredTemporary
  deriving DecidableEq, BEq

def RunFile.name : RunFile → String
  | .weights => "weights.ckpt"
  | .state => "state.json"
  | .stateTemporary => "state.json.tmp"
  | .log => "core.log"
  | .previousLog => "core.log.1"
  | .explored => "explored.map"
  | .exploredTemporary => "explored.map.tmp"

structure RunDirectory where
  private mk ::
  private root : System.FilePath
  private archiveRoot : System.FilePath
  private process : UInt32
  private sequence : Std.Mutex UInt64
  private operations : Std.Mutex (Option System.FilePath)

def RunDirectory.open (path : System.FilePath) : IO RunDirectory := do
  IO.FS.createDirAll path
  let root ← IO.FS.realPath path
  let some parent := root.parent | throw (IO.userError "run directory needs a parent")
  let some name := root.fileName | throw (IO.userError "filesystem root cannot be a run directory")
  return ⟨root, parent / (name ++ ".archive"), ← IO.Process.getPID,
    ← Std.Mutex.new 0, ← Std.Mutex.new none⟩

def RunDirectory.rootPath (directory : RunDirectory) : System.FilePath := directory.root

def RunDirectory.path (directory : RunDirectory) (file : RunFile) : System.FilePath :=
  directory.root / file.name

def RunDirectory.openRead (directory : RunDirectory) (file : RunFile) : IO IO.FS.Handle :=
  IO.FS.Handle.mk (directory.path file) .read

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

def logCapacity : Nat := 4 * 1024 * 1024

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

theorem log_append_bound (prior : Nat) (line : LineBytes) (room : prior < logCapacity) :
    prior + line.bytes.size + 1 ≤ logCapacity + lineCapacity := by
  have := line.bounded
  omega

inductive ArchiveResult where
  | unchanged (reason : String)
  | moved (archive : System.FilePath) (reason : String)
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

def mintControlToken : IO String := do
  let handle ← IO.FS.Handle.mk "/dev/urandom" .read
  let bytes ← entropyBytes handle 16 ByteArray.empty
  let digit := fun (n : Nat) => Char.ofNat (if n < 10 then 48 + n else 87 + n)
  return String.ofList (bytes.data.toList.flatMap fun byte =>
    [digit (byte.toNat / 16), digit (byte.toNat % 16)])

end Acorn.Host.Viewer
