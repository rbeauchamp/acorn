/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Std.Sync.Mutex

/-!
# Monotone lifecycle control

The pure command transition can only raise a stop. Its native shell serializes
reads and writes using the pinned standard mutex implementation. EOF and input
failure end only the reader. OS scheduling and mutex/runtime correctness remain
trusted operational boundaries; no liveness deadline is inferred from the proof.
-/
namespace Acorn.Host

/-- The complete lifecycle flag domain. -/
inductive StopState where
  /-- No request has arrived. -/
  | running
  /-- Stop has been requested and cannot be withdrawn. -/
  | requested
  deriving DecidableEq, BEq

/-- Unicode White_Space characters recognized by the source's trim operation. -/
def controlWhitespace (character : Char) : Bool :=
  let code := character.toNat
  (9 ≤ code && code ≤ 13) || code == 32 || code == 133 || code == 160 || code == 5760 ||
    (8192 ≤ code && code ≤ 8202) || code == 8232 || code == 8233 || code == 8239 ||
    code == 8287 || code == 12288

/-- Trim only the protocol's complete whitespace domain, without case normalization. -/
def trimControlLine (line : String) : String :=
  String.ofList ((line.toList.dropWhile controlWhitespace).reverse.dropWhile controlWhitespace).reverse

/-- Command classification has no agent-policy payload. -/
inductive ControlCommand where
  /-- The single recognized lifecycle request. -/
  | stop
  /-- Blank input. -/
  | blank
  /-- A reported and ignored unknown line. -/
  | unknown (text : String)
  deriving DecidableEq

/-- Exact, case-sensitive command classification after whitespace trimming. -/
def parseControl (line : String) : ControlCommand :=
  let command := trimControlLine line
  if command == "stop" then .stop else if command.isEmpty then .blank else .unknown command

/-- Pure lifecycle state transition; unknown input cannot withdraw or create a stop. -/
def StopState.receive (state : StopState) : ControlCommand → StopState
  | .stop => .requested
  | .blank | .unknown _ => state

/-- Every command preserves an already-raised stop request. -/
theorem StopState.monotone (command : ControlCommand) : receive .requested command = .requested := by
  cases command <;> rfl

/-- EOF has no command transition and therefore preserves the lifecycle state. -/
def StopState.receiveLine (state : StopState) (line : Option String) : StopState :=
  match line with | none => state | some line => state.receive (parseControl line)

/-- A closed pipe never asks the campaign to stop. -/
theorem StopState.eof (state : StopState) : state.receiveLine none = state := rfl

/-- Native shared state exposes no operation that lowers the stop flag. -/
structure StopFlag where
  private mk ::
  /-- Serialization uses the pinned standard mutex, not an unsynchronized shared reference. -/
  private mutex : Std.Mutex StopState

/-- Start an independent, unset native stop flag. -/
def StopFlag.new : BaseIO StopFlag := do
  return ⟨← Std.Mutex.new .running⟩

/-- Atomically raise the stop flag through the proved monotone transition. -/
def StopFlag.request (flag : StopFlag) : BaseIO Unit :=
  flag.mutex.atomically (modify (fun state => state.receive .stop))

/-- Read the serialized flag only at a runner boundary. -/
def StopFlag.requested (flag : StopFlag) : BaseIO Bool :=
  flag.mutex.atomically do return (← get) == .requested

/-- Process one input stream until EOF or an input error; neither ends the campaign.
Diagnostic-output failure is contained in this reader rather than terminating learning. -/
private def StopFlag.readCommands (flag : StopFlag) (input : IO.FS.Stream) : IO Unit := do
  repeat
    if ← IO.checkCanceled then return
    let line ← try input.getLine catch _ => return
    if (← IO.checkCanceled) || line.isEmpty then return
    match parseControl line with
    | .stop =>
      flag.request
      try IO.eprintln "control: stop requested; finishing this attempt" catch _ => pure ()
    | .blank => pure ()
    | .unknown command =>
      try IO.eprintln s!"control: ignoring unknown command {repr command}" catch _ => pure ()

private def commandPipes : IO.Process.StdioConfig := ⟨.inherit, .piped, .null⟩

private structure ClosedCommandSource where
  reader : Task (Except IO.Error Unit)

private def closeCommandSource (child : IO.Process.Child commandPipes)
    (reader : Task (Except IO.Error Unit)) : IO ClosedCommandSource := do
  IO.cancel reader
  if (← child.tryWait).isNone then
    child.kill
    let _ ← child.wait
  return ⟨reader⟩

private def ClosedCommandSource.join (source : ClosedCommandSource) : IO Unit := do
  match ← IO.ofExcept source.reader.get with
  | () => pure ()

/-- Scope the command reader to the campaign, including exceptional completion.
The POSIX byte relay has no inherited output or stderr handle from the core,
so even external core termination cannot leave its viewer output open through
this relay. The relay owns only the internal command pipe writer: reaping it closes that writer without
waiting for the external stdin owner. Only a source closed by this owner can be
joined. The reader checks cancellation on either side of a blocking read, so a
buffered command suffix cannot keep cleanup alive. `/bin/cat` byte forwarding,
pipe EOF, successful kill/wait, scheduling, and native IO remain trusted; this
structural release order establishes no OS deadline or progress after IO failure. -/
def StopFlag.withCommands {α : Type} (flag : StopFlag) (enabled : Bool)
    (body : IO α) : IO α := do
  if !enabled then return ← body
  let child ← IO.Process.spawn { commandPipes with cmd := "/bin/cat", args := #[] }
  let reader ← IO.asTask (flag.readCommands (IO.FS.Stream.ofHandle child.stdout))
    (prio := .dedicated)
  try body
  finally
    let closed ← closeCommandSource child reader
    closed.join

end Acorn.Host
