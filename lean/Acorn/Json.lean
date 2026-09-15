/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-! # Strict, total JSON admission

Objects retain fields until schema consumption; duplicates are rejected before
construction. Number spelling survives parsing, so integer admission cannot
truncate a fraction. Structural fuel is derived from input length; the separate
128-level bound governs nesting. Strings are Unicode scalars, with paired UTF-16
escapes decoded explicitly. The host must reject invalid UTF-8 before parsing.
-/
namespace Acorn.Json

/-- Syntax admitted before domain-specific construction. -/
inductive Value where
  /-- JSON null. -/
  | null
  /-- JSON boolean. -/
  | bool (value : Bool)
  /-- Original numeric spelling. -/
  | number (spelling : String)
  /-- Decoded Unicode string. -/
  | string (value : String)
  /-- Ordered array. -/
  | array (values : List Value)
  /-- Unique decoded field names, in source order. -/
  | object (fields : List (String × Value))
  deriving BEq


private def ws (cs : List Char) : List Char :=
  cs.dropWhile fun c => c == ' ' || c == '\r' || c == '\n' || c == '\t'

private def require (c : Char) : List Char → Except String (List Char)
  | x :: xs => if x == c then .ok xs else .error s!"expected {c}"
  | [] => .error s!"expected {c}"

private def quad (cs : List Char) : Except String (Nat × List Char) := do
  let mut rest := cs
  let mut n := 0
  for _ in [:4] do
    let c :: tail := rest | throw "incomplete Unicode escape"
    let d := if c.isDigit then c.toNat - 48
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55 else 16
    unless d < 16 do throw "invalid Unicode escape"
    n := n * 16 + d
    rest := tail
  return (n, rest)

private def unicode (cs : List Char) : Except String (Char × List Char) := do
  let (first, rest) ← quad cs
  if 0xd800 ≤ first && first ≤ 0xdbff then
    let rest ← require '\\' rest >>= require 'u'
    let (second, rest) ← quad rest
    unless 0xdc00 ≤ second && second ≤ 0xdfff do throw "high surrogate without low surrogate"
    return (Char.ofNat (0x10000 + (first - 0xd800) * 1024 + second - 0xdc00), rest)
  if 0xdc00 ≤ first && first ≤ 0xdfff then throw "invalid Unicode scalar"
  return (Char.ofNat first, rest)

private def stringBody : Nat → List Char → String → Except String (String × List Char)
  | 0, _, _ => .error "unterminated JSON string"
  | fuel + 1, cs, out => do
    match cs with
    | [] => throw "unterminated JSON string"
    | '"' :: rest => return (out, rest)
    | '\\' :: c :: rest =>
      let (decoded, rest) ← match c with
        | '"' | '\\' | '/' => pure (c, rest)
        | 'b' => pure (Char.ofNat 8, rest)
        | 'f' => pure (Char.ofNat 12, rest)
        | 'n' => pure ('\n', rest)
        | 'r' => pure ('\r', rest)
        | 't' => pure ('\t', rest)
        | 'u' => unicode rest
        | _ => throw "invalid JSON escape"
      stringBody fuel rest (out.push decoded)
    | ['\\'] => throw "unterminated JSON escape"
    | c :: rest =>
      if c.toNat < 32 then throw "unescaped JSON control character"
      stringBody fuel rest (out.push c)

private def stringValue (cs : List Char) : Except String (String × List Char) := do
  let rest ← require '"' cs
  stringBody cs.length rest ""

private def digits (cs : List Char) : Except String ((List Char) × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then .error "missing JSON number digits"
  else .ok (ds, cs.drop ds.length)

private def number (cs : List Char) : Except String (Value × List Char) := do
  let (sign, rest) := match cs with
    | '-' :: rest => (['-'], rest)
    | _ => ([], cs)
  let (whole, rest) ← match rest with
    | '0' :: rest => pure (['0'], rest)
    | _ => digits rest
  let (fraction, rest) ← match rest with
    | '.' :: rest => do
      let (ds, rest) ← digits rest
      pure ('.' :: ds, rest)
    | _ => pure ([], rest)
  let (exponent, rest) ← match rest with
    | e :: rest =>
      if e == 'e' || e == 'E' then do
        let (sign, rest) := match rest with
          | c :: tail => if c == '+' || c == '-' then ([c], tail) else ([], rest)
          | [] => ([], rest)
        let (ds, rest) ← digits rest
        pure (e :: sign ++ ds, rest)
      else pure ([], e :: rest)
    | [] => pure ([], [])
  return (.number (String.ofList (sign ++ whole ++ fraction ++ exponent)), rest)

mutual
private def value : Nat → Nat → List Char → Except String (Value × List Char)
  | 0, _, _ => .error "JSON input exhausted"
  | fuel + 1, depth, input => do
    if depth > 128 then throw "JSON nesting exceeds 128"
    let cs := ws input
    match cs with
    | '"' :: _ => let (s, rest) ← stringValue cs; return (.string s, rest)
    | '{' :: rest =>
      match ws rest with
      | '}' :: tail => return (.object [], tail)
      | rest => fields fuel (depth + 1) rest []
    | '[' :: rest =>
      match ws rest with
      | ']' :: tail => return (.array [], tail)
      | rest => elements fuel (depth + 1) rest []
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => return (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => return (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => return (.bool false, rest)
    | c :: _ => if c == '-' || c.isDigit then number cs else throw "invalid JSON value"
    | [] => throw "missing JSON value"
private def fields : Nat → Nat → List Char → List (String × Value) → Except String (Value × List Char)
  | 0, _, _, _ => .error "JSON input exhausted"
  | fuel + 1, depth, cs, out => do
    let (key, rest) ← stringValue (ws cs)
    if out.any (fun field => field.1 == key) then throw s!"duplicate JSON key {key}"
    let rest ← require ':' (ws rest)
    let (v, rest) ← value fuel depth rest
    let out := out ++ [(key, v)]
    match ws rest with
    | '}' :: tail => return (.object out, tail)
    | ',' :: tail => fields fuel depth tail out
    | _ => throw "expected object separator or end"
private def elements : Nat → Nat → List Char → List Value → Except String (Value × List Char)
  | 0, _, _, _ => .error "JSON input exhausted"
  | fuel + 1, depth, cs, out => do
    let (v, rest) ← value fuel depth cs
    let out := out ++ [v]
    match ws rest with
    | ']' :: tail => return (.array out, tail)
    | ',' :: tail => elements fuel depth tail out
    | _ => throw "expected array separator or end"
end

/-- Parse one entire document, rejecting trailing input and duplicate decoded keys. -/
def parse (text : String) : Except String Value := do
  let (v, rest) ← value (text.length + 2) 0 text.toList
  unless (ws rest).isEmpty do throw "trailing JSON input"
  return v

/-- Unicode White_Space, matching the retained manifest text admission contract.
This is distinct from JSON's four grammar whitespace characters. -/
def unicodeWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || n == 32 || n == 0x85 || n == 0xa0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 ||
    n == 0x202f || n == 0x205f || n == 0x3000

/-- Require a nonempty, non-whitespace string. -/
def Value.text : Value → Except String String
  | .string s => if s.toList.all unicodeWhitespace then .error "expected nonempty string" else .ok s
  | _ => .error "expected nonempty string"

/-- Unsigned machine-width integer admission uses spelling, never numeric rounding. -/
def Value.natural : Value → Except String Nat
  | .number s => match s.toNat? with
    | some n => if n < 2^64 then .ok n else .error "unsigned integer overflow"
    | none => .error "expected unsigned integer"
  | _ => .error "expected unsigned integer"

/-- Require an array. -/
def Value.list : Value → Except String (List Value)
  | .array vs => .ok vs
  | _ => .error "expected array"

/-- Require an object for field consumption. -/
def Value.fields : Value → Except String (List (String × Value))
  | .object vs => .ok vs
  | _ => .error "expected object"

/-- JSON null is the only absent optional value. -/
def Value.optional : Value → Option Value
  | .null => none
  | v => some v

/-- Consuming schema decoder; finishing requires every field to have an owner. -/
abbrev Decoder := StateT (List (String × Value)) (Except String)

/-- Consume exactly one required field. -/
def take (key : String) : Decoder Value := do
  let fields ← get
  let some pair := fields.find? (fun p => p.1 == key) | throw s!"missing field {key}"
  set (fields.filter fun p => p.1 != key)
  return pair.2

/-- Consume a required nonempty string. -/
def text (key : String) : Decoder String := do (← take key).text

/-- Consume a required string array. -/
def texts (key : String) : Decoder (List String) := do
  (← (← take key).list).mapM (fun v => v.text)

/-- Admit the specified schema version. -/
def version (expected : Nat) : Decoder Unit := do
  unless (← (← take "schema_version").natural) == expected do throw "unsupported schema_version"

/-- Run schema construction and reject every unrecognized field. -/
def decode {α : Type} (v : Value) (body : Decoder α) : Except String α := do
  let (result, rest) ← body.run (← v.fields)
  unless rest.isEmpty do throw s!"unknown fields: {rest.map Prod.fst}"
  return result

end Acorn.Json
