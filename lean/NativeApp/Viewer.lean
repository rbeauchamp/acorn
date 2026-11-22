/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.Assets
import Acorn.Host.Viewer.Options
import Acorn.Host.Forever

/-!
# Native viewer bootstrap

The bootstrap admits configuration and durable state, binds loopback HTTP, then
drives the serial supervisor. Browser request handlers cannot access a process
handle. Native entropy, files, process execution and transport remain explicit
OS/runtime boundaries.

The bootstrap gives the supervisor a running intent only from a state file that holds
one, names the current schema and names the record of the child this launch starts
(`Acorn.Host.Viewer.PersistedState.decode_running`). With no state file it builds a state
that intends to stay stopped (`Acorn.Host.Viewer.PersistedState.unstarted`), and it submits
a Start only for the `--start` flag, after the listener binds; the other source of a Start
is an admitted control request. `Acorn.Host.Viewer.ExplicitStart` proves that the
supervisor started from a state that intends to stay stopped waits on no spawn until a
Start is handed to its step. A state file the bootstrap refuses constructs no supervisor.

The order is: read the state, build the supervisor, bind, then print and submit. The
supervisor writes its start state before the bind, except for a file whose running intent
was set aside (`Acorn.Host.Viewer.StartSource.kept`), which stays as it is; so a start-up
that fails leaves that file, and its reason, to the next viewer.
-/
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

/-- The supervisor's child and its record. The ranked child is the core beside this program,
named by its path with explicit arguments, so its record is what can be read of it before it
is started: the path, the file's size and modification time, and the arguments at the
reference launch. A file that cannot be examined gives no record. A fixed command is given to
a shell, and the process a shell starts for it depends on the working directory, the
environment and the files the command names, which this program does not compare: it has no
record, so a running intent saved under it is not carried to another launch. -/
private def supervisorConfig (options : ViewerOptions) (directory : RunDirectory) :
    IO SupervisorConfig := do
  match options.launch with
  | .ranked =>
    let executable := (← IO.appDir) / "acorn-core"
    let arguments := rankedArguments options.checkpoint
    let child ← try
        let found ← executable.metadata
        pure (childRecord executable.toString found.byteSize.toNat found.modified.sec
          found.modified.nsec.toNat
          (arguments referenceLaunch (directory.path .weights)).toList)
      catch _ => pure none
    return ⟨executable, arguments, child, options.launch.clearDisabled, freshSeed⟩
  | .fixed command =>
    return ⟨System.FilePath.mk "/bin/sh", fun _ _ => #["-c", "exec " ++ command], none,
      options.launch.clearDisabled, freshSeed⟩

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
      -- tryWait consumes the status; this child must never be waited on again.
      opener.set none
      unless status == 0 do
        IO.eprintln s!"Browser could not open automatically. Open {url} in your browser."
  catch _ =>
    opener.set none
    try IO.eprintln s!"Browser launch status unavailable. Open {url} in your browser."
    catch _ => pure ()

/-- No core can launch before durable admission and successful HTTP binding. -/
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
    -- Before binding succeeds no command can launch a core.
    let server ← (viewer.serve options.port).wait
    let shutdown ← IO.asTask server.waitShutdown.wait (prio := .dedicated)
    let opener ← IO.mkRef none
    try
      let some address := server.localAddr
        | throw (IO.userError "bound viewer address is unavailable")
      let url := s!"http://{address}/"
      IO.println s!"Acorn is ready: {url}\nRun directory: {directory.rootPath}"
      -- The line on why the run is shown stopped is printed once the page is served, and not
      -- under the Start flag, which starts the run. A start-up that fails before this point
      -- prints nothing of the run and loses nothing: an earlier version's file is still on
      -- disk as it was (`Supervisor.new`), so the next viewer reads it and says the same.
      unless options.start do
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
      -- The loop has no `break`, so it ends only by returning or throwing.
      throw (IO.userError "viewer loop ended without a result")
    finally
      try supervisor.shutdown
      finally
        try
          -- Keep HTTP alive during wind-up, then release its sole shutdown waiter.
          server.shutdown.wait
          match shutdown.get with
          | .ok () => pure ()
          | .error error => throw error
        finally
          -- A desktop opener never holds a worker or blocks viewer exit. Poll
          -- once more; a still-running detached opener survives process exit.
          pollBrowser opener

end NativeApp

/-- Startup failure is visible and cannot silently launch a replacement run. -/
def _root_.NativeApp.Viewer.main (arguments : List String) : IO UInt32 := do
  try NativeApp.runViewer arguments
  catch error =>
    try IO.eprintln s!"acorn-viewer: {error}" catch _ => pure ()
    return 1
