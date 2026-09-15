/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Line
import Acorn.Host.Viewer.Admission
import Acorn.Json

/-!
# Bounded wire envelopes

The maintained total JSON parser supplies strict syntax admission, including
duplicate-key refusal. Observer identity uses exact words, never rounded JSON
floating numbers. Browser-safe numeric projection and the complete telemetry
field schema remain separate from this envelope admission.
-/
namespace Acorn.Host.Viewer

/-- A protocol-specific SSE payload bound also excludes event-delimiter injection. -/
abbrev SseLine (capacity : Nat) := {text : String // text.utf8ByteSize ≤ capacity ∧
  text.contains '\n' = false ∧ text.contains '\r' = false}

/-- Admission for larger protocol records, such as the separately bounded map snapshot. -/
def sseLine (capacity : Nat) (text : String) : Option (SseLine capacity) :=
  if legal : text.utf8ByteSize ≤ capacity ∧
      text.contains '\n' = false ∧ text.contains '\r' = false then
    some ⟨text, legal⟩ else none

/-- SSE data occupies one bounded physical line and cannot inject another event. -/
def wireTextLegal (text : String) : Bool :=
  text.utf8ByteSize ≤ lineCapacity && !text.contains '\n' && !text.contains '\r'

/-- A stored or delivered wire line carries byte and delimiter bounds. -/
abbrev WireText := {text : String // wireTextLegal text = true}

/-- Byte/delimiter admission precedes retention in any replay or subscriber queue. -/
def wireText (text : String) : Option WireText :=
  if h : wireTextLegal text = true then some ⟨text, h⟩ else none

/-- Every admitted line fits the byte budget, regardless of its Unicode encoding. -/
theorem WireText.byte_bound (text : WireText) : text.val.utf8ByteSize ≤ lineCapacity := by
  have := text.property
  simp [wireTextLegal] at this
  exact this.1.1

/-- Neither newline spelling can escape an admitted SSE data field. -/
theorem WireText.delimiter_bound (text : WireText) :
    text.val.contains '\n' = false ∧ text.val.contains '\r' = false := by
  have := text.property
  simp [wireTextLegal] at this
  constructor <;> simp_all

/-- Exact field lookup after strict whole-document JSON admission. -/
def jsonField (value : Json.Value) (key : String) : Except String Json.Value := do
  let fields ← value.fields
  let some pair := fields.find? (fun field => field.1 == key) | throw s!"missing field {key}"
  return pair.2

/-- Full-width unsigned admission does not coerce fractions, signs or overflow. -/
def jsonWord (value : Json.Value) : Except String UInt64 := do
  let word ← value.natural
  return word.toUInt64

/-- Identity clocks crossing the browser number boundary must be exactly representable.
Larger native counters remain valid native values but cannot assert browser capture freshness. -/
def browserIntegerMax : Nat := 9007199254740991

/-- Numeric parts of a durable viewer identity have an exact browser representation. -/
def Identity.browserSafe (identity : Identity) : Bool :=
  identity.seed.toNat ≤ browserIntegerMax && identity.agentEpoch.toNat ≤ browserIntegerMax

/-- Refuse clocks outside the browser's exact integer domain before attribution. -/
def jsonBrowserClock (value : Json.Value) : Except String UInt64 := do
  let word ← value.natural
  unless word ≤ browserIntegerMax do throw "capture clock exceeds browser integer precision"
  return word.toUInt64

/-- An exact JSON boolean has no truthiness conversion. -/
def jsonBool : Json.Value → Except String Bool
  | .bool value => .ok value
  | _ => .error "expected boolean"

/-- Canonical hexadecimal run identity stays exact across JavaScript's number boundary. -/
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

/-- Decode only the exact capture fields used for identity and ordering admission. -/
def healthFromJson (value : Json.Value) : Except String Capture := do
  return ⟨← runWord (← jsonField value "run_id"),
    ← jsonBrowserClock (← jsonField value "agent_epoch"),
    ← jsonBrowserClock (← jsonField value "timestamp_ms"),
    ← jsonBrowserClock (← jsonField value "lifetime_step"),
    ← jsonBrowserClock (← jsonField value "world_step"), false⟩

/-- History additionally requires the terminal flag; health has no such dependency. -/
def captureFromJson (value : Json.Value) : Except String Capture := do
  let capture ← healthFromJson value
  return { capture with terminal := ← jsonBool (← jsonField value "end") }

/-- Health admission is tied to the actual input without requiring a complete scientific frame. -/
structure HealthEnvelope where
  /-- Bounded original physical line. -/
  source : WireText
  /-- Strictly parsed input. -/
  value : Json.Value
  /-- Parser correspondence for this input. -/
  parsed : Json.parse source.val = .ok value
  /-- Exact identity and capture clocks, with no asserted terminal semantics. -/
  capture : Capture
  /-- Capture fields come from this document. -/
  decoded : healthFromJson value = .ok capture

/-- Health decoding remains usable when the full frame schema is refused. -/
def HealthEnvelope.parse (text : WireText) : Except String HealthEnvelope :=
  match parsed : Json.parse text.val with
  | .error message => .error message
  | .ok value =>
    match decoded : healthFromJson value with
    | .error message => .error message
    | .ok capture => .ok ⟨text, value, parsed, capture, decoded⟩

/-- A parsed envelope retains the actual syntax and its exact decoded capture relation. -/
structure Envelope where
  /-- The bounded single-line source. -/
  source : WireText
  /-- Strictly parsed syntax, available for complete field admission. -/
  value : Json.Value
  /-- Exact input-to-syntax relation, including duplicate-key refusal. -/
  parsed : Json.parse source.val = .ok value
  /-- Source-owned identity and clocks. -/
  capture : Capture
  /-- Capture cannot be supplied independently of the actual parsed fields. -/
  decoded : captureFromJson value = .ok capture

/-- Each constructor is gated by the executing parser and exact envelope decoder. -/
def Envelope.parse (text : WireText) : Except String Envelope :=
  match parsed : Json.parse text.val with
  | .error message => .error message
  | .ok value =>
    match decoded : captureFromJson value with
    | .error message => .error message
    | .ok capture => .ok ⟨text, value, parsed, capture, decoded⟩

/-- Invalid UTF-8 is refused before JSON sees the input. A final CR in CRLF is removed. -/
def LineBytes.text (line : LineBytes) : Except String WireText := do
  let some text := String.fromUTF8? line.bytes | throw "invalid telemetry UTF-8"
  let text := if text.endsWith "\r" then text.dropEnd 1 |>.toString else text
  let some admitted := wireText text | throw "telemetry byte or delimiter limit"
  return admitted

end Acorn.Host.Viewer
