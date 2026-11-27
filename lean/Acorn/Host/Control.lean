import Std.Sync.Mutex
import Acorn.Host.Forever

namespace Acorn.Host

inductive StopState where
  | running
  | requested
  deriving DecidableEq, BEq

def controlWhitespace (character : Char) : Bool :=
  let code := character.toNat
  (9 ≤ code && code ≤ 13) || code == 32 || code == 133 || code == 160 || code == 5760 ||
    (8192 ≤ code && code ≤ 8202) || code == 8232 || code == 8233 || code == 8239 ||
    code == 8287 || code == 12288

def trimControlLine (line : String) : String :=
  String.ofList ((line.toList.dropWhile controlWhitespace).reverse.dropWhile controlWhitespace).reverse

inductive ControlCommand where
  | stop
  | blank
  | unknown (text : String)
  deriving DecidableEq

def parseControl (line : String) : ControlCommand :=
  let command := trimControlLine line
  if command == "stop" then .stop else if command.isEmpty then .blank else .unknown command

def StopState.receive (state : StopState) : ControlCommand → StopState
  | .stop => .requested
  | .blank | .unknown _ => state

theorem StopState.monotone (command : ControlCommand) : receive .requested command = .requested := by
  cases command <;> rfl

def StopState.receiveLine (state : StopState) (line : Option String) : StopState :=
  match line with | none => state | some line => state.receive (parseControl line)

theorem StopState.eof (state : StopState) : state.receiveLine none = state := rfl

structure StopFlag where
  private mk ::
  private mutex : Std.Mutex StopState

def StopFlag.new : BaseIO StopFlag := do
  return ⟨← Std.Mutex.new .running⟩

def StopFlag.request (flag : StopFlag) : BaseIO Unit :=
  flag.mutex.atomically (modify (fun state => state.receive .stop))

def StopFlag.requested (flag : StopFlag) : BaseIO Bool :=
  flag.mutex.atomically do return (← get) == .requested

private def StopFlag.readCommands (flag : StopFlag) (input : IO.FS.Stream) : IO Unit := do
  for _ in forever do
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
