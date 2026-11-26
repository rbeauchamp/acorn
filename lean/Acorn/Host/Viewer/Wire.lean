import Acorn.Host.Viewer.Line
import Acorn.Host.Viewer.Admission
import Acorn.Json

namespace Acorn.Host.Viewer

abbrev SseLine (capacity : Nat) := {text : String // text.utf8ByteSize ≤ capacity ∧
  text.contains '\n' = false ∧ text.contains '\r' = false}

def sseLine (capacity : Nat) (text : String) : Option (SseLine capacity) :=
  if legal : text.utf8ByteSize ≤ capacity ∧
      text.contains '\n' = false ∧ text.contains '\r' = false then
    some ⟨text, legal⟩ else none

def wireTextLegal (text : String) : Bool :=
  text.utf8ByteSize ≤ lineCapacity && !text.contains '\n' && !text.contains '\r'

abbrev WireText := {text : String // wireTextLegal text = true}

def wireText (text : String) : Option WireText :=
  if h : wireTextLegal text = true then some ⟨text, h⟩ else none

theorem WireText.byte_bound (text : WireText) : text.val.utf8ByteSize ≤ lineCapacity := by
  have := text.property
  simp [wireTextLegal] at this
  exact this.1.1

theorem WireText.delimiter_bound (text : WireText) :
    text.val.contains '\n' = false ∧ text.val.contains '\r' = false := by
  have := text.property
  simp [wireTextLegal] at this
  constructor <;> simp_all

def jsonField (value : Json.Value) (key : String) : Except String Json.Value := do
  let fields ← value.fields
  let some pair := fields.find? (fun field => field.1 == key) | throw s!"missing field {key}"
  return pair.2

def jsonWord (value : Json.Value) : Except String UInt64 := do
  let word ← value.natural
  return word.toUInt64

def browserIntegerMax : Nat := 9007199254740991

def Identity.browserSafe (identity : Identity) : Bool :=
  identity.seed.toNat ≤ browserIntegerMax && identity.agentEpoch.toNat ≤ browserIntegerMax

def jsonBrowserClock (value : Json.Value) : Except String UInt64 := do
  let word ← value.natural
  unless word ≤ browserIntegerMax do throw "capture clock exceeds browser integer precision"
  return word.toUInt64

def jsonBool : Json.Value → Except String Bool
  | .bool value => .ok value
  | _ => .error "expected boolean"

def runWord (value : Json.Value) : Except String UInt64 := do
  let text ← value.text
  unless text.length == 16 do throw "run_id must have sixteen hexadecimal digits"
  let mut result : UInt64 := 0
  for character in text.toList do
    let digit := if character.isDigit then character.toNat - 48
      else if 'a' ≤ character && character ≤ 'f' then character.toNat - 87 else 16
    unless digit < 16 do throw "run_id must use lowercase hexadecimal"
    result := result * 16 + digit.toUInt64
  return result

def healthFromJson (value : Json.Value) : Except String Capture := do
  return ⟨← runWord (← jsonField value "run_id"),
    ← jsonBrowserClock (← jsonField value "agent_epoch"),
    ← jsonBrowserClock (← jsonField value "timestamp_ms"),
    ← jsonBrowserClock (← jsonField value "lifetime_step"),
    ← jsonBrowserClock (← jsonField value "world_step"), false⟩

def captureFromJson (value : Json.Value) : Except String Capture := do
  let capture ← healthFromJson value
  return { capture with terminal := ← jsonBool (← jsonField value "end") }

structure HealthEnvelope where
  source : WireText
  value : Json.Value
  parsed : Json.parse source.val = .ok value
  capture : Capture
  decoded : healthFromJson value = .ok capture

def HealthEnvelope.parse (text : WireText) : Except String HealthEnvelope :=
  match parsed : Json.parse text.val with
  | .error message => .error message
  | .ok value =>
    match decoded : healthFromJson value with
    | .error message => .error message
    | .ok capture => .ok ⟨text, value, parsed, capture, decoded⟩

structure Envelope where
  source : WireText
  value : Json.Value
  parsed : Json.parse source.val = .ok value
  capture : Capture
  decoded : captureFromJson value = .ok capture

def Envelope.parse (text : WireText) : Except String Envelope :=
  match parsed : Json.parse text.val with
  | .error message => .error message
  | .ok value =>
    match decoded : captureFromJson value with
    | .error message => .error message
    | .ok capture => .ok ⟨text, value, parsed, capture, decoded⟩

def LineBytes.text (line : LineBytes) : Except String WireText := do
  let some text := String.fromUTF8? line.bytes | throw "invalid telemetry UTF-8"
  let text := if text.endsWith "\r" then text.dropEnd 1 |>.toString else text
  let some admitted := wireText text | throw "telemetry byte or delimiter limit"
  return admitted

end Acorn.Host.Viewer
