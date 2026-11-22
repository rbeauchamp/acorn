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

The order is: read the state, build the supervisor, bind, publish a state whose running
intent was set aside, then print and submit. The supervisor writes its start state before
the bind, except for a file whose running intent was set aside
(`Acorn.Host.Viewer.StartSource.kept`), an earlier version's or one given for another child.
That file stays exactly as it is until the listener is bound; the bootstrap then publishes
the stopped state it started from, with this launch's record, before it prints the ready
line, before `--start` submits its Start and before the first step. So a start-up that fails
before that publication leaves that file, and its reason, to the next viewer, and the file
is read as an earlier version's, or as given for another child, once: in the first launch
whose start-up succeeds.
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

/-- The one reading of a recorded child: the record (`Acorn.Host.Viewer.childRecord`) of the
content read whole from the file at the executable's path, and none when the file cannot be
read whole. -/
private def readChild (executable : System.FilePath) (arguments : List String) :
    IO (Option (List String)) := do
  try return childRecord executable.toString (← IO.FS.readBinFile executable) arguments
  catch _ => return none

/-- The supervisor's child and its record. The ranked child is the core beside this program,
named by its path with explicit arguments, so its record is what can be read of it before it
is started: the path, the file's length in bytes, the 64-bit FNV-1a digest of every byte of
the file, and the arguments at the reference launch. The configuration holds the action that
reads it (`readChild`) and the record that action gave here; the actor runs the same action
again immediately before each spawn, the first and every restart, and spawns only if it
gives the same record, so a core rebuilt or replaced during this viewer's life is not started
on a Start given for the file this viewer recorded. Not compared, and assumed: the interval
between the actor's last reading of the file and the operating system's exec; the
environment the child inherits; and that two files of equal length and equal digest are one.
The digest suffices against accident, a rebuilt file that agrees in length and in a 64-bit
digest by chance; forging it needs no more power than writing the state file by hand. A file
that cannot be read whole gives no record. A fixed command is given to a shell, and the
process a shell starts for it depends on the working directory, the environment and the
files the command names, which this program does not compare: it has no record, so a running
intent saved under it is not carried to another launch, and it is spawned with no reading. -/
private def supervisorConfig (options : ViewerOptions) (directory : RunDirectory) :
    IO SupervisorConfig := do
  match options.launch with
  | .ranked =>
    let executable := (← IO.appDir) / "acorn-core"
    let arguments := rankedArguments options.checkpoint
    let record := readChild executable
      (arguments referenceLaunch (directory.path .weights)).toList
    return ⟨executable, arguments, ← record, record, options.launch.clearDisabled, freshSeed⟩
  | .fixed command =>
    return ⟨System.FilePath.mk "/bin/sh", fun _ _ => #["-c", "exec " ++ command], none,
      pure none, options.launch.clearDisabled, freshSeed⟩

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
      -- A state file whose running intent was set aside was left as it is by
      -- `Supervisor.new`. The listener is bound, so the stopped state this viewer started
      -- from is published here with this launch's record, and a viewer of the earlier
      -- version started later on the directory meets a current-version file. A crash
      -- between the bind and this publication leaves the original file, and the next launch
      -- says the reason again. Under `--start` the Start is submitted below, and so
      -- processed, after the publication. A Start that arrives on the control endpoint
      -- before it is only queued by `Supervisor.submit` and is processed by a later
      -- `supervisor.step`, so it is neither processed first nor lost. If the publication
      -- fails, the viewer exits with that error before it prints the ready line and before
      -- any step: nothing is spawned from the set-aside intent, and the file, which is
      -- replaced only by a rename after a complete write, is still the original.
      if source.kept then directory.writeState config.child persisted
      let some address := server.localAddr
        | throw (IO.userError "bound viewer address is unavailable")
      let url := s!"http://{address}/"
      IO.println s!"Acorn is ready: {url}\nRun directory: {directory.rootPath}"
      -- The line on why the run is shown stopped is printed once the page is served, and not
      -- under the Start flag, which starts the run. A start-up that fails before the
      -- publication above prints nothing of the run and loses nothing: a file whose running
      -- intent was set aside is still on disk as it was, so the next viewer reads it and
      -- says the same.
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
