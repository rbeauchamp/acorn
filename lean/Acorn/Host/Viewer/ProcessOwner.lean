import Acorn.Host.Viewer.Lifecycle
import Std.Sync.Mutex

namespace Acorn.Host.Viewer

private def corePipes : IO.Process.StdioConfig := ⟨.piped, .piped, .piped⟩

private inductive CommandInput where
  | ready (handle : IO.FS.Handle)
  | requested

private structure OwnedChild where
  generation : UInt64
  child : IO.Process.Child { corePipes with stdin := .null }
  input : CommandInput
  started : Nat

private structure ProcessState where
  lastGeneration : UInt64 := 0
  live : Option OwnedChild := none

structure ProcessOwner where
  private mk ::
  private state : Std.Mutex ProcessState

structure ProcessOutput where
  generation : UInt64
  stdout : IO.FS.Handle
  stderr : IO.FS.Handle

def ProcessOwner.new : BaseIO ProcessOwner := do
  return ⟨← Std.Mutex.new {}⟩

def ProcessOwner.spawn (owner : ProcessOwner) (generation : UInt64)
    (executable : System.FilePath) (arguments : Array String) : IO ProcessOutput :=
  owner.state.atomically do
    let state ← get
    if state.live.isSome then throw (IO.userError "a core process is still owned")
    if generation ≤ state.lastGeneration then throw (IO.userError "process generation is not fresh")
    set { state with lastGeneration := generation }
    let started ← IO.monoMsNow
    let (input, child) ← (← IO.Process.spawn
      { corePipes with cmd := executable.toString, args := arguments }).takeStdin
    set ({ lastGeneration := generation, live := some ⟨generation, child, .ready input, started⟩ } : ProcessState)
    return ⟨generation, child.stdout, child.stderr⟩

inductive WindUpResult where
  | stale
  | alreadyRequested
  | sent
  | refused (reason : String)

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

inductive ProcessPoll where
  | stale
  | running (uptimeMs : Nat)
  | exited (code : UInt32) (uptimeMs : Nat)
  | refused (reason : String)

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
        return .exited code (now - live.started)
    catch error => return .refused error.toString

end Acorn.Host.Viewer
