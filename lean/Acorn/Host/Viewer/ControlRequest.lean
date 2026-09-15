/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Wire

/-!
# Local HTTP control admission

Control requests have one closed command field, a byte bound, the POST method,
the JSON media type and the current viewer-start token. The native HTTP owner
supplies parsed header values and the exact bounded body. No body contains a
core action: admitted commands address only the viewer's process lifecycle.
-/
namespace Acorn.Host.Viewer

/-- Immutable maximum body size for local lifecycle requests. -/
def controlBodyCapacity : Nat := 1024

/-- Body bytes are bounded before retention or JSON parsing. -/
abbrev ControlBody := {bytes : ByteArray // bytes.size ≤ controlBodyCapacity}

/-- Only complete bodies within the declared bound enter the control decoder. -/
def controlBody (bytes : ByteArray) : Option ControlBody :=
  if h : bytes.size ≤ controlBodyCapacity then some ⟨bytes, h⟩ else none

/-- The sole control-body schema has one closed command word. -/
def controlCommand (body : ControlBody) : Except String Command := do
  let some text := String.fromUTF8? body.val | throw "invalid control UTF-8"
  let value ← Json.parse text
  Json.decode value do
    let word ← Json.text "cmd"
    let some command := Command.parse word | throw "unknown lifecycle command"
    return command

/-- Parsed header facts needed to authorize local control, before body decoding. -/
structure ControlHeaders where
  /-- Exact parsed HTTP method. -/
  method : String
  /-- Parsed media type, without parameters. -/
  mediaType : String
  /-- Complete control token header. -/
  token : String
  /-- Content-Length is required and must equal the complete admitted body. -/
  length : Option Nat

/-- Equal-length tokens scan every byte before equality can succeed.
This source-level work pattern is not a claim about compiler or hardware timing. -/
def tokenMatches (received expected : String) : Bool :=
  if received.utf8ByteSize != expected.utf8ByteSize then false
  else
    let pairs := received.toUTF8.data.toList.zip expected.toUTF8.data.toList
    let difference := pairs.foldl (fun (difference : UInt8) pair =>
      difference ||| (pair.1 ^^^ pair.2)) 0
    difference == 0 && received == expected

/-- Header authorization and exact framing derive one admission predicate. -/
def ControlHeaders.authorizes (headers : ControlHeaders) (token : String) (body : ControlBody) : Bool :=
  headers.method == "POST" && headers.mediaType == "application/json" &&
    !token.isEmpty && tokenMatches headers.token token && headers.length == some body.val.size

/-- An accepted command carries its actual authorization and decoding relations. -/
structure AuthorizedCommand (headers : ControlHeaders) (token : String) where
  /-- Bounded bytes actually received. -/
  body : ControlBody
  /-- Lifecycle request admitted from those bytes. -/
  command : Command
  /-- Header, token and framing checks refer to this exact body. -/
  authorized : headers.authorizes token body = true
  /-- The strict body decoder supplied this command. -/
  decoded : controlCommand body = .ok command

/-- Authentication precedes JSON decoding and construction of an enqueueable command. -/
def authorizeCommand (headers : ControlHeaders) (token : String) (body : ControlBody) :
    Except String (AuthorizedCommand headers token) :=
  if authorized : headers.authorizes token body = true then
    match decoded : controlCommand body with
    | .error reason => .error reason
    | .ok command => .ok ⟨body, command, authorized, decoded⟩
  else .error "control request refused"

/-- An accepted request necessarily has the POST method, regardless of its body. -/
theorem AuthorizedCommand.post {headers : ControlHeaders} {token : String}
    (command : AuthorizedCommand headers token) : headers.method = "POST" := by
  have := command.authorized
  simp [ControlHeaders.authorizes] at this
  exact this.1.1.1.1

end Acorn.Host.Viewer
