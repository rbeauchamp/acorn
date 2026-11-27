import Acorn.Host.Viewer.WireNumber
import Acorn.Host.Viewer.GoalProtocol

namespace Acorn.Host.Viewer

inductive TelemetryShape where
  | natural
  | goalKind
  | goalItem
  | integer
  | binary32
  | binary64
  | flag
  | text
  | optional (element : TelemetryShape)
  | array (count : Nat) (element : TelemetryShape)
  | sequence (element : TelemetryShape)
  deriving DecidableEq

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

def telemetryString (value : String) : String :=
  "\"" ++ value.foldl (fun out character => out ++ jsonChar character) "" ++ "\""

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

structure TelemetryField where
  name : String
  shape : TelemetryShape
  value : shape.Value

def emitTelemetryFields (fields : List TelemetryField) : String :=
  "{" ++ String.intercalate "," (fields.map fun field =>
    telemetryString field.name ++ ":" ++ field.shape.emit field.value) ++ "}"

def telemetrySchema (fields : List TelemetryField) : List (String × TelemetryShape) :=
  fields.map fun field => (field.name, field.shape)

theorem telemetry_array_length (element : TelemetryShape) (count : Nat)
    (values : (TelemetryShape.array count element).Value) :
    (values.toList.map element.emit).length = count := by
  change (values.toArray.toList.map element.emit).length = count
  simp

end Acorn.Host.Viewer
