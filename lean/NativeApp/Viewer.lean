import NativeApp.Assets
import Acorn.Host.Viewer.Options
import Acorn.Host.Forever

namespace NativeApp
open Acorn.Host Acorn.Host.Viewer

private def seedBytes (handle : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  let chunk ← handle.read remaining.toUSize
  if _empty : chunk.size = 0 then throw (IO.userError "OS entropy ended early")
  else if _fits : chunk.size ≤ remaining then
    let bytes := bytes ++ chunk
    if chunk.size == remaining then return bytes
    else seedBytes handle (remaining - chunk.size) bytes
  else throw (IO.userError "OS entropy exceeded its request")
termination_by remaining

private def freshSeed : IO UInt64 := do
  let handle ← IO.FS.Handle.mk "/dev/urandom" .read
  let bytes ← seedBytes handle 8 ByteArray.empty
  return viewerSeed (bytes.data.foldl (fun word byte => word * 256 + byte.toUInt64) 0)

private def initialState (directory : RunDirectory) (child : Option (List String)) :
    IO (PersistedState × StartSource) := do
  match ← directory.readState child with
  | .restored state source =>
    unless state.identity.browserSafe do
      throw (IO.userError "state.json identity exceeds browser integer precision; preserving the run without starting its core")
    let _ ← directory.adoptStrayCheckpoint
    return (state, source)
  | .refused reason =>
    throw (IO.userError s!"state.json refused; preserving the run without starting its core: {reason}")
  | .missing =>
    let migrated ← directory.adoptStrayCheckpoint
    let seed ← if migrated then pure Cli.defaultSeed else freshSeed
    return (.unstarted seed migrated, .absent)

private def readProgram (executable : System.FilePath) : IO (Option ProgramReading) := do
  try return some (.of (← IO.FS.readBinFile executable))
  catch _ => return none

private def supervisorConfig (options : ViewerOptions) (directory : RunDirectory) :
    IO SupervisorConfig := do
  match options.launch with
  | .ranked =>
    let executable := (← IO.appDir) / "acorn-core"
    let arguments := rankedArguments options.checkpoint
    let read := readProgram executable
    let atStart ← read
    let child := atStart.bind fun reading => childRecord executable.toString reading
      (arguments referenceLaunch (directory.path .weights)).toList
    return ⟨executable, arguments, child, .ranked atStart read, options.launch.clearDisabled,
      freshSeed⟩
  | .fixed command =>
    return ⟨System.FilePath.mk "/bin/sh", fun _ _ => #["-c", "exec " ++ command], none,
      .fixed, options.launch.clearDisabled, freshSeed⟩

private abbrev BrowserChild := IO.Process.Child {
  stdin := .null, stdout := .null, stderr := .null }

private def openBrowser (url : String) : IO (Option (String × BrowserChild)) := do
  try
    let child ← IO.Process.spawn {
      cmd := if System.Platform.isOSX then "/usr/bin/open" else "xdg-open"
      args := #[url], stdin := .null, stdout := .null, stderr := .null, setsid := true }
    return some (url, child)
  catch _ =>
    IO.eprintln s!"Browser could not open automatically. Open {url} in your browser."
    return none

private def pollBrowser (opener : IO.Ref (Option (String × BrowserChild))) : IO Unit := do
  let some (url, child) ← opener.get | return
  try
    if let some status ← child.tryWait then
      opener.set none
      unless status == 0 do
        IO.eprintln s!"Browser could not open automatically. Open {url} in your browser."
  catch _ =>
    opener.set none
    try IO.eprintln s!"Browser launch status unavailable. Open {url} in your browser."
    catch _ => pure ()

def runViewer (arguments : List String) : IO UInt32 := do
  let options ← match ViewerOptions.decode arguments with
    | .ok options => pure options
    | .error error => throw (IO.userError (error.message ++
        "\nusage: acorn-viewer (--research-profile ranked | --cmd COMMAND) [--port N] [--run-dir DIR] [--no-checkpoint] [--start] [--open-browser] [--control-stdin]" ++
        "\nThe supervised child, the core or COMMAND, starts only with --start, on a Start on the viewer's control endpoint, which the page's Start button sends, or when state.json in the run directory names schema_version 2 and the same child and intends to run; under --cmd no saved intent is carried over." ++
        s!"\nN is below 65536. {Acorn.Digits.usage}"))
  let directory ← RunDirectory.open options.directory
  let config ← supervisorConfig options directory
  let (persisted, source) ← initialState directory config.child
  let supervisor ← Supervisor.new config directory persisted source
  let stop ← StopFlag.new
  stop.withCommands options.controlStdin do
    let viewer ← supervisor.http viewerAssets
    let server ← (viewer.serve options.port).wait
    let shutdown ← IO.asTask server.waitShutdown.wait (prio := .dedicated)
    let opener ← IO.mkRef none
    try
      if source.kept then
        if let some line := startAccount source persisted.desired then
          IO.println s!"Run: {line}"
          (← IO.getStdout).flush
        directory.writeState config.child persisted
      let some address := server.localAddr
        | throw (IO.userError "bound viewer address is unavailable")
      let url := s!"http://{address}/"
      IO.println s!"Acorn is ready: {url}\nRun directory: {directory.rootPath}"
      unless options.start || source.kept do
        if let some line := startAccount source persisted.desired then
          IO.println s!"Run: {line}"
      (← IO.getStdout).flush
      if options.start then
        match ← supervisor.submit .start with
        | .accepted => pure ()
        | _ => throw (IO.userError "initial Start request could not be queued")
      if options.openBrowser then opener.set (← openBrowser url)
      for _ in forever do
        pollBrowser opener
        if ← stop.requested then return 0
        if (← IO.getTaskState shutdown) == .finished then
          match shutdown.get with
          | .ok () => return 0
          | .error error => throw error
        supervisor.step
        IO.sleep 50
      throw (IO.userError "viewer loop ended without a result")
    finally
      try supervisor.shutdown
      finally
        try
          server.shutdown.wait
          match shutdown.get with
          | .ok () => pure ()
          | .error error => throw error
        finally
          pollBrowser opener

end NativeApp

def _root_.NativeApp.Viewer.main (arguments : List String) : IO UInt32 := do
  try NativeApp.runViewer arguments
  catch error =>
    try IO.eprintln s!"acorn-viewer: {error}" catch _ => pure ()
    return 1
