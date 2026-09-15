/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.Assets
import Acorn.Host.Viewer.Options

/-!
# Native viewer bootstrap

The bootstrap admits configuration and durable state, binds loopback HTTP, then
drives the serial supervisor. Browser request handlers cannot access a process
handle. Native entropy, files, process execution and transport remain explicit
OS/runtime boundaries.
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

private def initialState (directory : RunDirectory) : IO PersistedState := do
  match ← directory.readState with
  | .restored state =>
    unless state.identity.browserSafe do
      throw (IO.userError "state.json identity exceeds browser integer precision; preserving the run without starting its core")
    let _ ← directory.adoptStrayCheckpoint
    return state
  | .refused reason =>
    throw (IO.userError s!"state.json refused; preserving the run without starting its core: {reason}")
  | .missing =>
    let migrated ← directory.adoptStrayCheckpoint
    let seed ← if migrated then pure Cli.defaultSeed else freshSeed
    return ⟨⟨seed, seed, 0⟩, .running, .fresh, migrated⟩

private def supervisorConfig (options : ViewerOptions) : IO SupervisorConfig := do
  let (executable, arguments) ← match options.launch with
    | .ranked => pure ((← IO.appDir) / "acorn-core", rankedArguments options.checkpoint)
    | .fixed command =>
      pure (System.FilePath.mk "/bin/sh", fun _ _ => #["-c", "exec " ++ command])
  return ⟨executable, arguments, options.launch.clearDisabled, freshSeed⟩

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
        "\nusage: acorn-viewer (--research-profile ranked | --cmd COMMAND) [--port N] [--run-dir DIR] [--no-checkpoint] [--start] [--open-browser] [--control-stdin]"))
  let directory ← RunDirectory.open options.directory
  let supervisor ← Supervisor.new (← supervisorConfig options) directory (← initialState directory)
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
      (← IO.getStdout).flush
      if options.start then
        match ← supervisor.submit .start with
        | .accepted => pure ()
        | _ => throw (IO.userError "initial Start request could not be queued")
      if options.openBrowser then opener.set (← openBrowser url)
      repeat
        pollBrowser opener
        if ← stop.requested then return 0
        if (← IO.getTaskState shutdown) == .finished then
          match shutdown.get with
          | .ok () => return 0
          | .error error => throw error
        supervisor.step
        IO.sleep 50
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
def main (arguments : List String) : IO UInt32 := do
  try NativeApp.runViewer arguments
  catch error =>
    try IO.eprintln s!"acorn-viewer: {error}" catch _ => pure ()
    return 1
