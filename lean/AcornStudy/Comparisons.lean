/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Files

/-! # Canonical comparison admission

Counts partition the registered population and determine the printed rational.
Natural arithmetic avoids overflow; the retained unsigned-64 admission limits also
preserve the transition gate's checked-arithmetic contract.
-/
namespace AcornStudy

/-- Canonical publication tuple; all counts retain their independently admitted values. -/
structure Comparison where
  /-- Exact rational numerator. -/
  numerator : Nat
  /-- Exact rational denominator. -/
  denominator : Nat
  /-- Paired wins. -/
  wins : Nat
  /-- Paired ties. -/
  ties : Nat
  /-- Paired losses. -/
  losses : Nat
  /-- Complete registered population. -/
  seeds : Nat
  deriving DecidableEq, BEq

private def number (s : String) : Except String Nat := do
  unless !s.isEmpty && s.toList.all Char.isDigit do throw "invalid unsigned count"
  let some n := s.toNat? | throw "invalid unsigned count"
  unless n < 2^64 do throw "count exceeds unsigned 64-bit domain"
  return n

private def consistent (population num den wins ties losses seeds : Nat) : Except String Unit := do
  unless seeds == population && wins + ties + losses == seeds && den > 0 &&
      (2*wins + ties)*den == num*2*seeds &&
      (2*wins + ties)*den < 2^64 && num*2*seeds < 2^64 do
    throw "canonical tally does not partition population or determine rational"

private def split (s separator : String) : Option (String × String) :=
  match s.splitOn separator with
  | a :: b :: rest => some (a, String.intercalate separator (b :: rest))
  | _ => none

private def tallyLine (line : String) : Option (String × String) := do
  guard (line.startsWith "  ")
  let (key, rest) ← split (line.drop 2).toString ": "
  guard (!key.isEmpty && key.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'z') || c == '_'))
  return (key, rest)

private def ws (s : String) : String :=
  (s.dropWhile (fun c => [' ', '\t', '\n', '\r', Char.ofNat 12].contains c)).toString

private def countPrefix (s : String) : Except String (Nat × String) := do
  let digits := (s.takeWhile Char.isDigit).toString
  return (← number digits, ws (s.drop digits.length).toString)

private def word (s : String) (choices : List String) : Except String String := do
  let some lead := choices.find? (fun w => s.startsWith w &&
    !((s.drop w.length).toString.toList.head?.any (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_')))
    | throw "invalid tally word"
  return (s.drop lead.length).toString

private def comma (s : String) : Except String String := do
  unless s.startsWith "," do throw "invalid tally comma"
  return ws (s.drop 1).toString

private def tally (s : String) : Except String (Nat × Nat × Nat × Nat) := do
  let (w, s) ← countPrefix s
  let s ← comma (← word s ["wins", "win"])
  let (t, s) ← countPrefix s
  let s ← comma (← word s ["ties", "tie"])
  let (l, s) ← countPrefix s
  let s ← word (ws (← word s ["losses", "loss"])) ["of"]
  let (n, s) ← countPrefix (ws s)
  unless (← word s ["seeds"]).isEmpty do throw "invalid tally suffix"
  return (w, t, l, n)

private def rational (line key : String) : Except String (Nat × Nat) := do
  let prefixes := [s!"  {key}.poi = ", s!"  {key} = "]
  let some lead :=  prefixes.find? (fun p => line.startsWith p) | throw "tally lacks preceding rational"
  let s := (line.drop lead.length).toString
  let some (n, rest) := split s "/" | throw "invalid rational"
  let denominator := (rest.takeWhile Char.isDigit).toString
  let suffix := (rest.drop denominator.length).toString
  unless suffix.isEmpty || suffix.startsWith " " do throw "invalid rational suffix"
  return (← number n, ← number denominator)

private def reduction (text : String) (population : Nat) : Except String (List (String × Comparison)) := do
  let lines := (text.splitOn "\n").map (fun s => (s.dropEndWhile (· == '\r')).toString)
  let mut keys := []
  let mut previous := ""
  let mut expected : Option String := none
  for line in lines do
    let parsed := tallyLine line
    if let some key := expected then
      unless parsed.map Prod.fst == some key do throw "probability lacks following tally"
    expected := none
    match parsed with
    | some (key, rest) =>
      let (wins, ties, losses, seeds) ← tally rest
      let (num, den) ← rational previous key
      consistent population num den wins ties losses seeds
      keys := (key, ⟨num, den, wins, ties, losses, seeds⟩) :: keys
    | none =>
      if line.startsWith "  " then
        if let some (key, _) := split (line.drop 2).toString ".poi = " then expected := some key
    previous := line
  unless expected.isNone && !keys.isEmpty do throw "canonical comparisons absent or incomplete"
  return keys

private def field (value : Acorn.Json.Value) (key : String) : Except String Acorn.Json.Value := do
  let fields ← value.fields
  let some (_, v) := fields.find? (fun p => p.1 == key) | throw s!"missing report field {key}"
  return v

/-- Validate the canonical comparison inventory and population at run admission.
The baseline counts are preserved archive-derived tallies, independently checked
by its maintained calculator; they are not observations inferred from a ratio. -/
def canonicalComparisons (path : LocalPath) (format : String) (population : Nat) : IO (List (String × Comparison)) := do
  let keys ← if format == "baseline-report" then do
    let result ← checked (field (← document path) "result")
    let mut keys := []
    for (key, num, den, wins, ties, losses) in
        [("final_vs_random", 11, 15, 21, 2, 7), ("final_vs_frozen", 13, 20, 17, 5, 8)] do
      let ratio ← checked (field (← checked (field result key)) "probability_of_improvement")
      let n ← checked ((← checked (field ratio "num")).natural)
      let d ← checked ((← checked (field ratio "den")).natural)
      unless n == num && d == den do throw (IO.userError "report differs from sealed baseline tally")
      checked (consistent population num den wins ties losses population)
      keys := (key, ⟨num, den, wins, ties, losses, population⟩) :: keys
    pure keys
  else do
    let some text := String.fromUTF8? (← readBytes path) | throw (IO.userError "invalid result UTF-8")
    checked (reduction text population)
  return keys

/-- Canonical values and declared inventory have the same single admission owner. -/
def validateComparisons (path : LocalPath) (format : String) (population : Nat)
    (declared : List String) : IO Unit := do
  let keys := (← canonicalComparisons path format population).map Prod.fst
  unless keys.length == declared.length && keys.all declared.contains && declared.all keys.contains do
    throw (IO.userError "canonical comparison inventory differs from dossier")

end AcornStudy
