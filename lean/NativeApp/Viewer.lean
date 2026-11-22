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

The order is: read the state, build the supervisor, bind, say why a running intent was set
aside and publish the stopped state in its place, then print the ready line and submit. The
supervisor writes its start state before the bind, except for a file whose running intent was
set aside (`Acorn.Host.Viewer.StartSource.kept`), an earlier version's or one given for
another child. That file stays exactly as it is until the listener is bound; the bootstrap
then prints and flushes the line that says why the run is shown stopped
(`Acorn.Host.Viewer.startAccount`), under `--start` as well, and only then publishes the
stopped state it started from, with this launch's record, before it prints the ready line,
before `--start` submits its Start and before any command is processed. If the line cannot be
written or flushed, the viewer exits before the publication and the file is still the
original. So a start-up that fails before that publication leaves that file, and its reason,
to the next viewer, and the file is read as an earlier version's, or as given for another
child, once: in the first launch that publishes the stopped state, whose first control record
and log already hold the reason. A start-up that fails after the publication, when the ready
line cannot be written for example, leaves a current-version stopped file, and the reason the
next launch gives is that the saved state says stopped; a Start queued on the control endpoint
by then is lost with the viewer. For any other stopped start state, with no state file or
with a saved stopped state, the line is printed after the ready line, and not under `--start`.
The line is printed at most once in a launch.
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

/-- The one reading of the ranked core's program: the length and the digest
(`Acorn.Host.Viewer.ProgramReading`) of the content read whole from the file at the
executable's path, and none when the file cannot be read whole. -/
private def readProgram (executable : System.FilePath) : IO (Option ProgramReading) := do
  try return some (.of (← IO.FS.readBinFile executable))
  catch _ => return none

/-- The supervisor's child, what is compared before it is started, and its record. The ranked
child is the core beside this program, named by its path with explicit arguments. The
configuration holds the action that reads its file (`readProgram`) and the reading that
action gave here, the file's length in bytes and the 64-bit FNV-1a digest of every byte of
it. The actor runs the same action again once before every start, the first and every
restart, before it records the launch, and records the launch and spawns only if it gives the
same reading, so a core rebuilt or replaced during this viewer's life is not started on a
Start given for the file this viewer read; a ranked core whose file could not be read whole
here, or cannot be then, is not spawned, and nothing is written for the refusal. That
comparison is held in memory and does not depend on the record, on the run directory's path
or on what the state file can hold. The record written to the state file is the path, that
reading and the arguments at the reference launch, and none when the file could not be read
or the state file cannot hold those words. Not compared, and assumed: the interval between
that reading and the operating system starting the program, in which the launch is recorded
(a file replaced in that interval is started); the environment the child inherits; and that
two files of equal length and equal digest are one. The digest
suffices against accident, a rebuilt file that agrees in length and in a 64-bit digest by
chance; forging it needs no more power than writing the state file by hand. A fixed command
is given to a shell, and the process a shell starts for it depends on the working directory,
the environment and the files the command names, which this program does not compare: it has
no record, so a running intent saved under it is not carried to another launch, and it is
spawned with no reading: within this viewer a Start under a fixed command is for the command
line as given, across its restarts, whatever program it designates at each of them. -/
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
      -- `Supervisor.new`. The listener is bound, so the line that says why the run is shown
      -- stopped is printed and flushed here, under `--start` as well, and only then is the
      -- stopped state this viewer started from published with this launch's record. If the
      -- line cannot be written or flushed, the viewer exits before the publication and the
      -- file is still the original, so whenever such a file is replaced its reason is
      -- already in this launch's first control record and in its log. After the
      -- publication a viewer of the earlier
      -- version started later on the directory meets a current-version file. A crash
      -- between the bind and this publication leaves the original file, and the next launch
      -- says the reason again. Under `--start` the Start is submitted below, and so
      -- processed, after the publication. A Start that arrives on the control endpoint
      -- before it is only queued by `Supervisor.submit`, so it is not processed first; it
      -- is processed by a later `supervisor.step` if the start-up goes on, and is lost with
      -- the viewer if the start-up fails after the publication. If the publication
      -- fails, the viewer exits with that error before it prints the ready line. The
      -- `finally` below then shuts the supervisor down, and its closing turns step the
      -- supervisor and can write the map, but none of them takes a command from the queue:
      -- nothing is spawned from the set-aside intent, and the file, which is replaced only
      -- by a rename after a complete write, is still the original. A failure
      -- after the publication, when the ready line cannot be written for example, leaves
      -- a current-version stopped file, and the reason the next launch gives is that the
      -- saved state says stopped.
      if source.kept then
        if let some line := startAccount source persisted.desired then
          IO.println s!"Run: {line}"
          (← IO.getStdout).flush
        directory.writeState config.child persisted
      let some address := server.localAddr
        | throw (IO.userError "bound viewer address is unavailable")
      let url := s!"http://{address}/"
      IO.println s!"Acorn is ready: {url}\nRun directory: {directory.rootPath}"
      -- For a stopped start state whose file was not set aside, no state file or a saved
      -- stopped state, the line on why the run is shown stopped is printed here, after the
      -- ready line, and not under the Start flag, which starts the run. For a file whose
      -- running intent was set aside the line was printed above, before the publication, so
      -- it is printed at most once in a launch.
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
