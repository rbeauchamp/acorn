import Acorn.Host.Viewer.Wire

namespace Acorn.Host.Viewer

def controlBodyCapacity : Nat := 1024

abbrev ControlBody := {bytes : ByteArray // bytes.size ≤ controlBodyCapacity}

def controlBody (bytes : ByteArray) : Option ControlBody :=
  if h : bytes.size ≤ controlBodyCapacity then some ⟨bytes, h⟩ else none

def controlCommand (body : ControlBody) : Except String Command := do
  let some text := String.fromUTF8? body.val | throw "invalid control UTF-8"
  let value ← Json.parse text
  Json.decode value do
    let word ← Json.text "cmd"
    let some command := Command.parse word | throw "unknown lifecycle command"
    return command

def ControlSpelled (bytes : ByteArray) (command : Command) : Prop :=
  ∃ (text word : String), bytes = text.toUTF8 ∧
    Json.Grammar.Text text.toList (.object [("cmd", .string word)]) ∧
    Command.Spelled word command

structure ControlHeaders where
  method : String
  mediaType : String
  token : String
  length : Option Nat

def tokenMatches (received expected : String) : Bool :=
  if received.utf8ByteSize != expected.utf8ByteSize then false
  else
    let pairs := received.toUTF8.data.toList.zip expected.toUTF8.data.toList
    let difference := pairs.foldl (fun (difference : UInt8) pair =>
      difference ||| (pair.1 ^^^ pair.2)) 0
    difference == 0 && received == expected

def ControlHeaders.authorizes (headers : ControlHeaders) (token : String) (body : ControlBody) : Bool :=
  headers.method == "POST" && headers.mediaType == "application/json" &&
    !token.isEmpty && tokenMatches headers.token token && headers.length == some body.val.size

structure AuthorizedCommand (headers : ControlHeaders) (token : String) where
  body : ControlBody
  command : Command
  authorized : headers.authorizes token body = true
  decoded : controlCommand body = .ok command

def authorizeCommand (headers : ControlHeaders) (token : String) (body : ControlBody) :
    Except String (AuthorizedCommand headers token) :=
  if authorized : headers.authorizes token body = true then
    match decoded : controlCommand body with
    | .error reason => .error reason
    | .ok command => .ok ⟨body, command, authorized, decoded⟩
  else .error "control request refused"

theorem AuthorizedCommand.post {headers : ControlHeaders} {token : String}
    (command : AuthorizedCommand headers token) : headers.method = "POST" := by
  have := command.authorized
  simp [ControlHeaders.authorizes] at this
  exact this.1.1.1.1

end Acorn.Host.Viewer
