/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Std.Sync.Mutex
import Acorn.Host.Microduck.Loop

/-!
# The transport of a Microduck host

A host of the Microduck's world speaks to two daemons over three connections of their unix
sockets: the control connection of the state daemon, which carries commands and their
answers; a second connection of the same daemon, which carries the subscription to the
state stream; and a connection of the depth daemon, which carries the depth stream. This
module is that transport and nothing else. Each connection is a child process
`/usr/bin/nc -U <socket>`: the host writes a line to its standard input, and the child's
standard output gives the daemon's lines; its standard error is discarded. A reader task for
each child appends every line it reads, in the order read, to one list of lines heard, under a
mutex; a driver takes that list and hands each line to the loop. Only the driver writes to the
children (`Transport.send`), so the lines of one connection go out in the order sent.

**Trusted, and not stated.** This module is the trusted boundary of the host: the sockets and
the daemons behind them, `nc` and its forwarding of bytes in both directions, the pipes, the
runtime's tasks, its mutex and its kill and wait of a child, and the operating system's
scheduling. Nothing here parses a line: a line goes to the loop as text, where
`Line.ofText` reads it into the proved types. The order in which lines of different
connections are appended is the order in which their readers ran, not the order in which the
daemons wrote them. macOS `nc` has no option that closes the socket at the end of its input,
so a connection ends by a kill of its child (`Transport.within`), and the daemon sees its
socket close.
-/
namespace Acorn.Host.Microduck

/-- The pipes of a connection's child: the host writes its input and reads its output, and
its errors are discarded. -/
private def connectionPipes : IO.Process.StdioConfig := ⟨.piped, .piped, .null⟩

/-- One connection: its child process and the task that reads the child's output. -/
private structure Connection where
  /-- The child `nc -U <socket>`. -/
  child : IO.Process.Child connectionPipes
  /-- The reader of the child's output. -/
  reader : Task (Except IO.Error Unit)

/-- The three connections of a host and what their readers share. Its fields are private, so
only this module makes, writes and closes one. -/
structure Transport where
  private mk ::
  /-- The control connection of the state daemon. -/
  private control : Connection
  /-- The connection of the state daemon that carries the state stream. -/
  private state : Connection
  /-- The connection of the depth daemon. -/
  private depth : Connection
  /-- The lines heard and not yet taken, in the order the readers appended them. -/
  private heard : Std.Mutex (Array String)
  /-- The readers that have ended: at the end of a child's output, or at a failure to read
  it. -/
  private ended : Std.Mutex Nat

/-- A line without its line breaks. A line of a daemon is one JSON value, whose strings
escape a line break, so a line break in it can only be the end of the line. -/
private def unbroken (line : String) : String :=
  String.ofList (line.toList.filter (· != '\n'))

/-- Read a child's output to its end, or to a failure, appending every nonempty line. The
reader counts itself ended however it stops. -/
private def readLines (input : IO.FS.Stream) (heard : Std.Mutex (Array String))
    (ended : Std.Mutex Nat) : IO Unit := do
  try
    repeat
      if ← IO.checkCanceled then return
      let line ← input.getLine
      if line.isEmpty then return
      let text := unbroken line
      unless text.isEmpty do
        heard.atomically (modify (·.push text))
  finally
    ended.atomically (modify (· + 1))

/-- Start a connection to a socket: its child and the reader of its output. -/
private def Connection.start (socket : System.FilePath) (heard : Std.Mutex (Array String))
    (ended : Std.Mutex Nat) : IO Connection := do
  let child ← IO.Process.spawn
    { connectionPipes with cmd := "/usr/bin/nc", args := #["-U", socket.toString] }
  let reader ← IO.asTask (readLines (IO.FS.Stream.ofHandle child.stdout) heard ended)
    (prio := .dedicated)
  return ⟨child, reader⟩

/-- End a connection: cancel its reader, kill and reap its child when it still runs, and
wait for the reader, whose read then ends at the closed output. A failure of the reader is
not raised here: the count of ended readers already holds it. -/
private def Connection.stop (connection : Connection) : IO Unit := do
  IO.cancel connection.reader
  if (← connection.child.tryWait).isNone then
    connection.child.kill
    let _ ← connection.child.wait
  let _ ← IO.wait connection.reader

/-- End every connection of a list, in order, each even when an earlier one failed to end;
the first failure is raised after all of them. -/
private def Connection.stopAll (connections : List Connection) : IO Unit := do
  let mut failure : Option IO.Error := none
  for connection in connections do
    try connection.stop
    catch error =>
      if failure.isNone then failure := some error
  match failure with
  | some error => throw error
  | none => pure ()

/-- Send a line on its connection, with its line break, and flush it. -/
def Transport.send (transport : Transport) (send : Send) : IO Unit := do
  let input := match send.link with
    | .control => transport.control.child.stdin
    | .state => transport.state.child.stdin
    | .depth => transport.depth.child.stdin
  input.putStr (send.text ++ "\n")
  input.flush

/-- Take the lines heard since the last take, in the order the readers appended them. -/
def Transport.take (transport : Transport) : BaseIO (Array String) :=
  transport.heard.atomically (modifyGet fun lines => (lines, #[]))

/-- How many of the three readers have ended. -/
def Transport.endedReaders (transport : Transport) : BaseIO Nat :=
  transport.ended.atomically get

/-- Run a body with the three connections of a host open: the control and the state
connection on the state daemon's socket, and the depth connection on the depth daemon's.
Every connection that was started is stopped when the body ends, by a result or by an error,
and when a later connection fails to start. -/
def Transport.within {α : Type} (control depth : System.FilePath)
    (body : Transport → IO α) : IO α := do
  let heard ← Std.Mutex.new #[]
  let ended ← Std.Mutex.new 0
  let first ← Connection.start control heard ended
  let second ← (Connection.start control heard ended).tryCatch fun error => do
    Connection.stopAll [first]
    throw error
  let third ← (Connection.start depth heard ended).tryCatch fun error => do
    Connection.stopAll [first, second]
    throw error
  try body ⟨first, second, third, heard, ended⟩
  finally
    Connection.stopAll [first, second, third]

end Acorn.Host.Microduck
