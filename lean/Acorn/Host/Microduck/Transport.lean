import Std.Sync.Mutex
import Acorn.Host.Microduck.Loop
import Acorn.Host.Forever

namespace Acorn.Host.Microduck

private def connectionPipes : IO.Process.StdioConfig := ⟨.piped, .piped, .null⟩

private structure Connection where
  child : IO.Process.Child connectionPipes
  reader : Task (Except IO.Error Unit)

structure Transport where
  private mk ::
  private control : Connection
  private state : Connection
  private depth : Connection
  private heard : Std.Mutex (Array String)
  private ended : Std.Mutex (Option Nat)

private def unbroken (line : String) : String :=
  String.ofList (line.toList.filter (· != '\n'))

private def readLines (input : IO.FS.Stream) (heard : Std.Mutex (Array String))
    (ended : Std.Mutex (Option Nat)) : IO Unit := do
  try
    for _ in forever do
      if ← IO.checkCanceled then return
      let line ← input.getLine
      if line.isEmpty then return
      let text := unbroken line
      unless text.isEmpty do
        heard.atomically (modify (·.push text))
  finally
    let stopped ← IO.monoNanosNow
    ended.atomically (modify fun earliest => some (match earliest with
      | some earlier => min earlier stopped
      | none => stopped))

private def Connection.start (socket : System.FilePath) (heard : Std.Mutex (Array String))
    (ended : Std.Mutex (Option Nat)) : IO Connection := do
  let child ← IO.Process.spawn
    { connectionPipes with cmd := "/usr/bin/nc", args := #["-U", socket.toString] }
  let reader ← IO.asTask (readLines (IO.FS.Stream.ofHandle child.stdout) heard ended)
    (prio := .dedicated)
  return ⟨child, reader⟩

private def Connection.stop (connection : Connection) : IO Unit := do
  IO.cancel connection.reader
  try connection.child.kill catch _ => pure ()
  try
    discard connection.child.wait
  finally
    discard (IO.wait connection.reader)

private def Connection.stopAll (connections : List Connection) : IO Unit := do
  let mut failure : Option IO.Error := none
  for connection in connections do
    try connection.stop
    catch error =>
      if failure.isNone then failure := some error
  match failure with
  | some error => throw error
  | none => pure ()

def Transport.send (transport : Transport) (send : Send) : IO Unit := do
  let input := match send.link with
    | .control => transport.control.child.stdin
    | .state => transport.state.child.stdin
    | .depth => transport.depth.child.stdin
  input.putStr (send.text ++ "\n")
  input.flush

def Transport.take (transport : Transport) : BaseIO (Array String) :=
  transport.heard.atomically (modifyGet fun lines => (lines, #[]))

def Transport.firstEnd (transport : Transport) : BaseIO (Option Nat) :=
  transport.ended.atomically get

def Transport.within {α : Type} (control depth : System.FilePath)
    (body : Transport → IO α) : IO (α × Option Nat) := do
  let heard ← Std.Mutex.new #[]
  let ended ← Std.Mutex.new none
  let first ← Connection.start control heard ended
  let second ← (Connection.start control heard ended).tryCatch fun error => do
    Connection.stopAll [first]
    throw error
  let third ← (Connection.start depth heard ended).tryCatch fun error => do
    Connection.stopAll [first, second]
    throw error
  let result ← tryFinally (body ⟨first, second, third, heard, ended⟩)
    (Connection.stopAll [first, second, third])
  return (result, ← ended.atomically get)

end Acorn.Host.Microduck
