/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Lifecycle
import Std.Sync.Mutex

/-!
# Native child-process ownership

One mutex owns spawning, the live child and reaping. A failed wait retains the
child; only a successful wait reporting its exit releases the slot. No public
method exposes the child handle or permits arbitrary writes to its stdin.
The only transmitted bytes are the core's `stop` command.

Native process creation, pipes, clocks, mutexes and wait results are trusted
runtime/OS operations. Ordinary wind-up has no kill capability or wall-clock
deadline: a finite attempt and an armed checkpoint write must be allowed to
finish. Scheduling, IO completion and external termination remain explicit
assumptions; no wall-clock termination bound follows from a finite step budget.
-/
namespace Acorn.Host.Viewer

private def corePipes : IO.Process.StdioConfig := ⟨.piped, .piped, .piped⟩

private inductive CommandInput where
  | ready (handle : IO.FS.Handle)
  | requested

private def CommandInput.wasRequested : CommandInput → Bool
  | .ready _ => false
  | .requested => true

private structure OwnedChild where
  generation : UInt64
  child : IO.Process.Child { corePipes with stdin := .null }
  input : CommandInput
  started : Nat

private structure ProcessState where
  lastGeneration : UInt64 := 0
  live : Option OwnedChild := none

/-- Exclusive process owner, separate from output admission and durable run identity. -/
structure ProcessOwner where
  private mk ::
  private state : Std.Mutex ProcessState

/-- Output handles confer observation only; neither permits input or process replacement. -/
structure ProcessOutput where
  /-- Generation attached before any bytes are consumed. -/
  generation : UInt64
  /-- Exactly one stdout reader is assigned by the supervisor. -/
  stdout : IO.FS.Handle
  /-- Exactly one stderr reader is assigned by the supervisor. -/
  stderr : IO.FS.Handle

/-- Native process state begins with no reserved or live child. -/
def ProcessOwner.new : BaseIO ProcessOwner := do
  return ⟨← Std.Mutex.new {}⟩

/-- Reserve and launch under the same mutex; occupied or reused generations refuse.
The executable and arguments come from the admitted native bootstrap. -/
def ProcessOwner.spawn (owner : ProcessOwner) (generation : UInt64)
    (executable : System.FilePath) (arguments : Array String) : IO ProcessOutput :=
  owner.state.atomically do
    let state ← get
    if state.live.isSome then throw (IO.userError "a core process is still owned")
    if generation ≤ state.lastGeneration then throw (IO.userError "process generation is not fresh")
    -- Consuming a generation before IO also excludes reuse after spawn failure.
    set { state with lastGeneration := generation }
    let started ← IO.monoMsNow
    let (input, child) ← (← IO.Process.spawn
      { corePipes with cmd := executable.toString, args := arguments }).takeStdin
    set ({ lastGeneration := generation, live := some ⟨generation, child, .ready input, started⟩ } : ProcessState)
    return ⟨generation, child.stdout, child.stderr⟩

/-- Wind-up outcome distinguishes absence, an old request, success and pipe refusal. -/
inductive WindUpResult where
  /-- No matching child can receive the command. -/
  | stale
  /-- A prior request already consumed the input capability. -/
  | alreadyRequested
  /-- The only legal command was written and flushed. -/
  | sent
  /-- IO refused the command; no destructive fallback is inferred. -/
  | refused (reason : String)

/-- Wind-up consumes the sole input handle and transmits only the fixed stop line.
Repeated requests cannot resend commands. Dropping the consumed handle closes
stdin under the native reference-counting contract, including on write failure. -/
def ProcessOwner.windUp (owner : ProcessOwner) (generation : UInt64) : IO WindUpResult :=
  owner.state.atomically do
    let state ← get
    let some live := state.live | return .stale
    if live.generation != generation then return .stale
    let .ready input := live.input | return .alreadyRequested
    set { state with live := some { live with input := .requested } }
    try
      input.write "stop\n".toUTF8
      input.flush
      return .sent
    catch error => return .refused error.toString

/-- A poll reports the actual reaping boundary, without treating an IO error as exit. -/
inductive ProcessPoll where
  /-- No matching live child belongs to this owner. -/
  | stale
  /-- The runtime reports a still-running child. -/
  | running (uptimeMs : Nat)
  /-- Successful reaping is the only result that releases the live slot. -/
  | exited (code : UInt32) (uptimeMs : Nat) (stopRequested : Bool)
  /-- The native wait failed; process ownership remains held. -/
  | refused (reason : String)

/-- Observe a child under its ownership lock; failure cannot admit an overlapping spawn.
Elapsed subtraction saturates in Nat if a native clock violates monotonicity. -/
def ProcessOwner.poll (owner : ProcessOwner) (generation : UInt64) : IO ProcessPoll :=
  owner.state.atomically do
    let state ← get
    let some live := state.live | return .stale
    if live.generation != generation then return .stale
    let now ← IO.monoMsNow
    try
      match ← live.child.tryWait with
      | none =>
        return .running (now - live.started)
      | some code =>
        set { state with live := none }
        return .exited code (now - live.started) live.input.wasRequested
    catch error => return .refused error.toString

end Acorn.Host.Viewer
