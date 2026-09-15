/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Dossier

/-! # Scientific publication admission

Every printed comparison carries its exact tally and semantic run identity.
Admission checks correspondence to retained canonical records.
The parser consumes characters, so wrapped prose and UTF-8 glosses share one
coordinate system with the trigger and population scans.
-/
namespace AcornStudy.Publication

private abbrev Parser := StateT (List Char) Option

private def literal (text : String) : Parser Unit := do
  let rest ← get
  guard (text.toList.isPrefixOf rest)
  set (rest.drop text.length)

private def ws : Parser Unit := modify (·.dropWhile Char.isWhitespace)

private def number : Parser Nat := do
  let rest ← get
  let digits := rest.takeWhile Char.isDigit
  guard (!digits.isEmpty)
  let some n := (String.ofList digits).toNat? | failure
  guard (n < 2^64)
  set (rest.drop digits.length)
  return n

private def word (text : String) : Parser Unit := do
  literal text
  guard (!(← get).head?.any (fun c => c.isAlphanum || c == '_'))

private def tally : Parser (Nat × Nat × Nat × Nat) := do
  let w ← number; ws; word "wins" <|> word "win"; literal ","; ws
  let t ← number; ws; word "ties" <|> word "tie"; literal ","; ws
  let l ← number; ws; word "losses" <|> word "loss"; ws; word "of"; ws
  let n ← number; ws; word "seeds"
  return (w, t, l, n)

private def citation : Parser (String × Comparison) := do
  let n ← number; literal "/"; let d ← number; ws
  let _ ← (do
    literal "≈" <|> literal "="; ws; let _ ← number
    let _ ← (do literal "."; let _ ← number; pure ()) <|> pure ()
    pure ()) <|> pure ()
  ws; literal "("
  let (w, t, l, seeds) ← tally
  literal ";"; ws
  let quoted ← (literal "`" *> pure true) <|> pure false
  literal "study:"
  let rest ← get
  let key := rest.takeWhile fun c => ('a' ≤ c && c ≤ 'z') || c.isDigit || "-_/".contains c
  guard (!key.isEmpty)
  set (rest.drop key.length)
  if quoted then literal "`"
  literal ")"
  return ("study:" ++ String.ofList key, ⟨n, d, w, t, l, seeds⟩)

private def valueLead : Parser Unit := do
  ws
  let _ ← (literal "|" *> ws) <|> pure ()
  let rest ← get
  for _ in [:rest.length] do
    let matched ← ((word "is" <|> word "exactly") *> ws *> pure true) <|> pure false
    unless matched do break

private def namedValue (name : String) : Parser Bool := do
  literal name; valueLead
  let rest ← get
  return rest.head?.any Char.isDigit

private def population (populations : List Nat) : Parser Unit := do
  word "of"; ws
  guard (populations.contains (← number)); ws
  let _ ← (word "paired" *> ws) <|> pure ()
  word "seeds"

private structure Printed where
  start : Nat
  stop : Nat
  key : String
  value : Comparison

private def printed (chars : List Char) : List Printed := Id.run do
  let mut result := []
  let mut rest := chars
  let mut previous : Option Char := none
  let mut position := 0
  while !rest.isEmpty do
    let continues := previous.any fun c => c.isDigit || c == '/' || c == '.'
    match if continues then none else citation.run rest with
    | some ((key, value), suffix) =>
      let consumed := rest.length - suffix.length
      result := ⟨position, position + consumed, key, value⟩ :: result
      position := position + consumed
      previous := some ')'
      rest := suffix
    | none =>
      previous := rest.head?
      rest := rest.drop 1
      position := position + 1
  return result

/-- Complete canonical records are derived from the admitted registry. -/
def records (registry : Registry) : IO (List (String × String × Comparison)) := do
  let mut result := []
  for study in registry.studies do
    for run in study.runs do
      if !run.comparisons.isEmpty then
        let some path := run.result | throw (IO.userError "comparison lacks result")
        let some size := run.population | throw (IO.userError "comparison lacks population")
        for (key, value) in ← canonicalComparisons path run.state.format size.val do
          result := (s!"studies/{study.slug.val}/README.md",
            s!"study:{study.slug.val}/{run.protocol.label}/{run.id.val}/{key}", value) :: result
  return result

/-- Every citation equals its named canonical record, every numerical probability
trigger is keyed, and every registered population mention is inside a citation.
The returned keys name comparisons published by their owning study home. -/
def check (path text : String) (canonical : List (String × String × Comparison)) : IO (List String) := do
  let chars := text.toList
  let citations := printed chars
  let mut published := []
  for c in citations do
    let some (home, _, value) := canonical.find? (fun x => x.2.1 == c.key)
      | throw (IO.userError s!"{path}: unknown comparison {c.key}")
    unless c.value == value do throw (IO.userError s!"{path}: tally differs from {c.key}")
    if path == home then published := c.key :: published
  let populations := canonical.map (·.2.2.seeds)
  let mut rest := chars
  let mut lowerRest := chars.map Char.toLower
  let mut previous : Option Char := none
  for position in [:chars.length] do
    for name in ["P(improvement)", "probability of improvement"] do
      let lowered := if name == "P(improvement)" then rest else lowerRest
      if let some (numeric, suffix) := (namedValue name).run lowered then
        let offset :=  position + rest.length - suffix.length
        if numeric && !citations.any (fun c => c.start == offset) then
          throw (IO.userError s!"{path}: probability lacks a keyed exact tally")
        if name == "P(improvement)" && !numeric &&
            !(suffix.head? == some '≥' || suffix.head? == some '>' ||
              "at least".toList.isPrefixOf suffix) &&
            !citations.any (fun c => c.start == offset) then
          throw (IO.userError s!"{path}: probability lacks a keyed citation or threshold")
    if !previous.any Char.isAlphanum && ((population populations).run rest).isSome &&
        !citations.any (fun c => c.start ≤ position && position < c.stop) then
      throw (IO.userError s!"{path}: registered seed count outside a keyed citation")
    previous := rest.head?
    rest := rest.drop 1
    lowerRest := lowerRest.drop 1
  return published

end AcornStudy.Publication
