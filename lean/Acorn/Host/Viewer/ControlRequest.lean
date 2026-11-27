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

private def hexDigitVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

private def percentDecodeLoop (cs : List Char) (acc : ByteArray) : Option ByteArray :=
  match cs with
  | [] => some acc
  | '+' :: rest => percentDecodeLoop rest (acc.push 0x20)
  | '%' :: h1 :: h2 :: rest =>
    match hexDigitVal h1, hexDigitVal h2 with
    | some v1, some v2 => percentDecodeLoop rest (acc.push (v1 * 16 + v2).toUInt8)
    | _, _ => none
  | '%' :: _ => none
  | c :: rest =>
    let bytes := (String.singleton c).toUTF8
    percentDecodeLoop rest (acc ++ bytes)
termination_by cs.length

def percentDecode (s : String) : Option String := do
  let bytes ← percentDecodeLoop s.toList ByteArray.empty
  String.fromUTF8? bytes

def parseFormPairs (text : String) : Option (List (String × String)) := do
  if text.isEmpty then return []
  let mut pairs := []
  for part in text.splitOn "&" do
    if part.isEmpty then continue
    let segments := part.splitOn "="
    match segments with
    | [rawKey] =>
      let key ← percentDecode rawKey
      pairs := (key, "") :: pairs
    | rawKey :: rest =>
      let key ← percentDecode rawKey
      let val ← percentDecode (String.intercalate "=" rest)
      pairs := (key, val) :: pairs
    | [] => none
  return pairs.reverse

structure FormPayload where
  token : String
  command : Command
  pairs : List (String × String)
  deriving DecidableEq, BEq

def formLookup (pairs : List (String × String)) (key : String) : Option String :=
  (pairs.find? fun p => p.1 == key).map Prod.snd

def formControlPayload (body : ControlBody) : Except String FormPayload := do
  let some text := String.fromUTF8? body.val | throw "invalid control UTF-8"
  let some pairs := parseFormPairs text | throw "malformed form body"
  let some token := formLookup pairs "token" | throw "missing control token"
  let some word := formLookup pairs "cmd" | throw "missing lifecycle command"
  let some command := Command.parse word | throw "unknown lifecycle command"
  return { token, command, pairs }

structure FormControlHeaders where
  method : String
  mediaType : String
  length : Option Nat

def FormControlHeaders.authorizes (headers : FormControlHeaders) (token : String)
    (body : ControlBody) : Bool :=
  headers.method == "POST" &&
    headers.mediaType == "application/x-www-form-urlencoded" &&
    !token.isEmpty &&
    headers.length == some body.val.size

structure AuthorizedFormCommand (headers : FormControlHeaders) (token : String) where
  body : ControlBody
  payload : FormPayload
  authorized : headers.authorizes token body = true
  decoded : formControlPayload body = .ok payload
  tokenValid : tokenMatches payload.token token = true

def authorizeFormCommand (headers : FormControlHeaders) (token : String) (body : ControlBody) :
    Except String (AuthorizedFormCommand headers token) :=
  if authorized : headers.authorizes token body = true then
    match decoded : formControlPayload body with
    | .error reason => .error reason
    | .ok payload =>
      if valid : tokenMatches payload.token token = true then
        .ok ⟨body, payload, authorized, decoded, valid⟩
      else .error "control token refused"
  else .error "control request refused"

theorem AuthorizedFormCommand.post {headers : FormControlHeaders} {token : String}
    (command : AuthorizedFormCommand headers token) : headers.method = "POST" := by
  have := command.authorized
  simp [FormControlHeaders.authorizes] at this
  exact this.1.1.1

theorem AuthorizedFormCommand.token_eq {headers : FormControlHeaders} {token : String}
    (command : AuthorizedFormCommand headers token) : command.payload.token = token := by
  have h := command.tokenValid
  unfold tokenMatches at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.2

theorem authorizeFormCommand_spec {headers : FormControlHeaders} {token : String}
    {body : ControlBody} {authorized : AuthorizedFormCommand headers token}
    (_admitted : authorizeFormCommand headers token body = .ok authorized) :
    headers.method = "POST" ∧ authorized.payload.token = token :=
  ⟨authorized.post, authorized.token_eq⟩

end Acorn.Host.Viewer
