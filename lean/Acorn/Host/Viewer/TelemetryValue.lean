/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.WireNumber
import Acorn.Host.Viewer.GoalProtocol

/-!
# Shape-bearing telemetry values

Each emitted field owns its scalar kind and exact array dimensions. The same
shape accompanies the value at schema-generation time, so a field cannot claim
an array length different from its stored vector. JSON strings are escaped at
the single emission boundary; callers never supply raw JSON fragments.
-/
namespace Acorn.Host.Viewer

/-- Closed scalar and compound kinds of the current telemetry protocol. -/
inductive TelemetryShape where
  /-- Nonnegative exact integer. -/
  | natural
  /-- Closed semantic goal family, with admission derived from its vocabulary. -/
  | goalKind
  /-- Closed semantic goal item, including craftables. -/
  | goalItem
  /-- Signed exact integer. -/
  | integer
  /-- Binary32, with null marking every exceptional pattern. -/
  | binary32
  /-- Binary64 lifetime accumulator. -/
  | binary64
  /-- Boolean flag. -/
  | flag
  /-- Escaped Unicode string. -/
  | text
  /-- Explicit absence rather than a fabricated zero. -/
  | optional (element : TelemetryShape)
  /-- Fixed-length vector with the element's own shape. -/
  | array (count : Nat) (element : TelemetryShape)
  /-- A population-sized sequence whose length is supplied by a companion field. -/
  | sequence (element : TelemetryShape)
  deriving DecidableEq

/-- The executable value domain is derived from the advertised wire shape. -/
abbrev TelemetryShape.Value : TelemetryShape → Type
  | .natural => Nat
  | .goalKind => GoalKind
  | .goalItem => GoalItem
  | .integer => Int
  | .binary32 => Binary32
  | .binary64 => Binary64
  | .flag => Bool
  | .text => String
  | .optional element => Option element.Value
  | .array count element => Vector element.Value count
  | .sequence element => Array element.Value

private def jsonChar (character : Char) : String :=
  if character = '"' then "\\\""
  else if character = '\\' then "\\\\"
  else if character.toNat < 32 then
    let digit := fun (value : Nat) => Char.ofNat (if value < 10 then 48 + value else 87 + value)
    String.ofList ['\\', 'u', '0', '0', digit (character.toNat / 16), digit (character.toNat % 16)]
  else String.singleton character

/-- The shared string encoder escapes controls, quotes and backslashes before JSON emission. -/
def telemetryString (value : String) : String :=
  "\"" ++ value.foldl (fun out character => out ++ jsonChar character) "" ++ "\""

/-- Every emitted value is constructed from its typed shape, without a raw-fragment case. -/
def TelemetryShape.emit : (shape : TelemetryShape) → shape.Value → String
  | .natural, value => toString value
  | .goalKind, value => toString (GoalKind.code value)
  | .goalItem, value => toString (GoalItem.code value)
  | .integer, value => toString value
  | .binary32, value => binary32Text value
  | .binary64, value => binary64Text value
  | .flag, value => if value then "true" else "false"
  | .text, value => telemetryString value
  | .optional element, value => match value with
    | none => "null"
    | some value => element.emit value
  | .array _ element, value =>
    "[" ++ String.intercalate "," (value.toList.map element.emit) ++ "]"

  | .sequence element, value =>
    "[" ++ String.intercalate "," (value.toList.map element.emit) ++ "]"

/-- A field's schema and executable value are one dependent pair. -/
structure TelemetryField where
  /-- Exact emitted JSON key. -/
  name : String
  /-- Scalar kind and array dimensions. -/
  shape : TelemetryShape
  /-- Value inhabiting precisely that shape. -/
  value : shape.Value

/-- Record emission uses each field's own shape for both key and value formatting. -/
def emitTelemetryFields (fields : List TelemetryField) : String :=
  "{" ++ String.intercalate "," (fields.map fun field =>
    telemetryString field.name ++ ":" ++ field.shape.emit field.value) ++ "}"

/-- Schema extraction reads the same fields that the actual emitter consumes. -/
def telemetrySchema (fields : List TelemetryField) : List (String × TelemetryShape) :=
  fields.map fun field => (field.name, field.shape)

/-- A vector's advertised length is universally the number of values the emitter visits. -/
theorem telemetry_array_length (element : TelemetryShape) (count : Nat)
    (values : (TelemetryShape.array count element).Value) :
    (values.toList.map element.emit).length = count := by
  change (values.toArray.toList.map element.emit).length = count
  simp

end Acorn.Host.Viewer
