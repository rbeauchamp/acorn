/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.PipePump

/-!
# Serialized supervised process and pipe lifetime

The child, its generation and its readers share one supervisor slot. Reaping
revokes broadcast rights immediately. The slot remains occupied until all pipe
and log tasks finish, so archival cannot race a retained run-directory writer.
Neither control submission nor the process poll waits for pipe EOF. An external
descendant retaining a pipe may delay retirement indefinitely; no native join
deadline is claimed.
-/
namespace Acorn.Host.Viewer

/-- A run longer than this many milliseconds resets the short-failure sequence. -/
def healthyRunMs : Nat := 30000

/-- Actual native exit facts, kept while the process-local pipes drain. -/
structure ProcessExit where
  /-- The generation whose child was reaped. -/
  generation : UInt64
  /-- Native exit status. -/
  code : UInt32
  /-- Native elapsed process time. -/
  uptimeMs : Nat
  /-- A wind-up request was recorded, including refused pipe writes. -/
  stopRequested : Bool

private inductive ProcessSlot where
  | live (generation : UInt64) (pump : PipePump)
  | draining (exit : ProcessExit) (pump : PipePump)

/-- Supervisor process capability owns the process and every task that can write its run. -/
structure SupervisedProcess where
  private mk ::
  private owner : ProcessOwner
  private broadcast : Broadcast
  private slot : Std.Mutex (Option ProcessSlot)

/-- An empty process capability uses the same broadcaster as HTTP observation. -/
def SupervisedProcess.new (broadcast : Broadcast) : BaseIO SupervisedProcess := do
  return ⟨← ProcessOwner.new, broadcast, ← Std.Mutex.new none⟩

/-- Launch outcomes distinguish policy refusal from an actual native spawn error. -/
inductive LaunchResult where
  /-- A child or its readers still own the previous run. -/
  | occupied
  /-- Lifecycle intent, retry policy or generation exhaustion forbids launching. -/
  | deferred
  /-- A newly installed generation owns its child and both output readers. -/
  | started (generation : UInt64)
  /-- Native spawn failed; the generation remains consumed by both allocators. -/
  | refused (reason : String)

/-- Reserve, spawn, install and attach the generation in one serialized launch.
The caller persists launch intent before invoking this operation. -/
def SupervisedProcess.launch (process : SupervisedProcess) (directory : RunDirectory)
    (executable : System.FilePath) (arguments : Array String) : IO LaunchResult :=
  process.slot.atomically do
    if (← get).isSome then return .occupied
    let now := (min (← IO.monoMsNow) (2 ^ 64 - 1)).toUInt64
    let some generation ← process.broadcast.reserve now | return .deferred
    let output ← try process.owner.spawn generation executable arguments
      catch error =>
        process.broadcast.failed generation now false
        return .refused error.toString
    process.broadcast.started generation
    process.broadcast.awaitIdentity generation
    let pump ← PipePump.start output process.broadcast directory
    set (some (ProcessSlot.live generation pump))
    return .started generation

/-- A poll retains unresolved ownership rather than treating an IO refusal as an exit. -/
inductive SupervisedPoll where
  /-- No child or reader task owns a run directory. -/
  | empty
  /-- The native child remains live. -/
  | running (generation : UInt64) (uptimeMs : Nat)
  /-- The child exited but at least one reader or log writer remains active. -/
  | draining (exit : ProcessExit)
  /-- Reaping and all output/log joins completed; later archival may proceed. -/
  | finished (exit : ProcessExit) (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus)
  /-- Native wait, wind-up or signal IO refused; the complete slot remains owned. -/
  | refused (reason : String)

/-- Poll without waiting for pipe completion. Stop and Clear intent raise the
sole allowed stdin command; elapsed time cannot authorize destructive termination.
Unexpected exits use the existing retry transition, while requested stops do
not consume its failure budget. -/
def SupervisedProcess.poll (process : SupervisedProcess) : IO SupervisedPoll :=
  process.slot.atomically do
    let some slot ← get | return .empty
    match slot with
    | .draining exit pump =>
      if !(← pump.ready) then return .draining exit
      let (stdout, stderr, log) ← pump.finish
      if log.checkpoint == some .refused then
        process.broadcast.refuseFinalCheckpoint exit.generation
      set (none : Option ProcessSlot)
      return .finished exit stdout stderr log
    | .live generation pump =>
      let lifecycle ← process.broadcast.lifecycle
      if lifecycle.phaseValue == .stopping generation then
        match ← process.owner.windUp generation with
        | .refused reason => return .refused reason
        | _ => pure ()
      match ← process.owner.poll generation with
      | .stale => return .refused "supervisor lost its owned process generation"
      | .refused reason => return .refused reason
      | .running uptime => return .running generation uptime
      | .exited code uptime stopped =>
        let exit : ProcessExit := ⟨generation, code, uptime, stopped⟩
        let now := (min (← IO.monoMsNow) (2 ^ 64 - 1)).toUInt64
        if lifecycle.phaseValue != .stopping generation then
          process.broadcast.failed generation now (uptime > healthyRunMs)
        process.broadcast.retire generation
        set (some (ProcessSlot.draining exit pump))
        return .draining exit

/-- Clear's directory effect shares the launch/retirement mutex. No child or
pipe/log task may still own the run. A successful rename keeps the lifecycle
archiving until the caller persists and admits the replacement identity.
Failures retain their exact filesystem outcome and disable automatic restart. -/
def SupervisedProcess.archive (process : SupervisedProcess) (directory : RunDirectory)
    (stamp : UInt64) (announce : IO Unit := pure ()) : IO (Option ArchiveResult) :=
  process.slot.atomically do
    if (← get).isSome then return none
    if !(← process.broadcast.beginArchive) then return none
    announce
    let result ← directory.archive stamp
    match result with
    | .ready _ => pure ()
    | .unchanged _ | .moved _ _ => process.broadcast.archiveFailed
    return some result

end Acorn.Host.Viewer
