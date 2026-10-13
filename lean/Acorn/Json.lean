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

A number is scanned into a `Numeral`, the parts of its spelling: a minus sign, the digits
before the point, the digits after it and an exponent part. `Numeral.Formed` is the form
of a JSON number in the grammar of RFC 8259, section 6. `Numeral.scan` is the one
scanner. The parser keeps the spelling that the scanned numeral has, and `Value.numeral`
scans a kept spelling again with the same scanner, so a reader of numbers needs no second
one. Every scanned numeral is formed and its spelling is the head of the scanned list
(`Numeral.scan_formed`); the spelling of a formed numeral scans to that numeral with
nothing left (`Numeral.scan_chars`); and a value has a numeral exactly when it is a number
with the spelling of that numeral, which is formed (`Value.numeral_iff`). No theorem
states that every number of a parsed text has a numeral: it follows from `parse_sound`, whose
grammar spells each number of an accepted text as a `Grammar.Number`, with
`Grammar.number_iff` and `Value.numeral_iff`, by an induction over the derivation that no
theorem states.

A formed numeral with no exponent part is also scanned back from the head of a longer
text that goes on with no digit, point or exponent mark (`Numeral.scan_append`).
`Numeral.natural` is the numeral of a natural number, its decimal digits, and it is
formed (`Numeral.natural_formed`).

`parse` has two theorems. `Grammar.Text` is the grammar of a JSON text of RFC 8259,
written as relations that name no function of the parser, and `parse_sound` states that
every text that `parse` accepts is a text of that grammar, with the value that `parse` gives
as a value that the grammar gives the text. A `Request` is a JSON object of two levels, whose members are
scalars or one object of scalars, and `Request.chars` is its text with no space.
`parse_request` states that `parse` reads that text back as the value of the request,
for every request whose names and strings are of plain characters (no quotation mark, no
reverse solidus, no control character), whose names differ at each level and whose numbers
are formed numerals with no exponent part. Its proof follows the parser through the text:
the white space, the body of a string, the scanner of a number, the value reader and the
loop over the members of an object, each with a lemma for texts of this family, and the
fuel that `parse` derives from the length of the text is shown to be enough. No theorem
states that `parse` accepts a text of the grammar outside that family: with an array, an
escape, a nested object of more levels or white space.
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

/-- The exponent part of a JSON number, as its spelling has it. -/
structure Exponent where
  /-- Whether the mark is `E` and not `e`. -/
  upper : Bool
  /-- The sign after the mark: none, `some false` for a plus and `some true` for a minus. -/
  sign : Option Bool
  /-- The digits of the exponent. -/
  digits : List Char
  deriving DecidableEq

/-- A JSON number in the parts of its spelling. -/
structure Numeral where
  /-- Whether the spelling starts with a minus sign. -/
  negative : Bool
  /-- The digits before the point. -/
  whole : List Char
  /-- The digits after the point, if the spelling has a point. -/
  fraction : Option (List Char)
  /-- The exponent part, if the spelling has one. -/
  exponent : Option Exponent
  deriving DecidableEq

/-- The characters of the sign of an exponent. -/
def Exponent.signChars : Option Bool → List Char
  | none => []
  | some false => ['+']
  | some true => ['-']

/-- The characters of the exponent part: the mark, the sign and the digits. -/
def Exponent.chars (exponent : Exponent) : List Char :=
  (if exponent.upper then 'E' else 'e') ::
    (Exponent.signChars exponent.sign ++ exponent.digits)

/-- The characters of the part after the point: the point and the digits, or nothing. -/
def Numeral.fractionChars : Option (List Char) → List Char
  | none => []
  | some digits => '.' :: digits

/-- The characters of the exponent part, or nothing. -/
def Numeral.exponentChars : Option Exponent → List Char
  | none => []
  | some exponent => exponent.chars

/-- The spelling of a numeral, as characters. -/
def Numeral.chars (numeral : Numeral) : List Char :=
  (if numeral.negative then ['-'] else []) ++ numeral.whole ++
    Numeral.fractionChars numeral.fraction ++ Numeral.exponentChars numeral.exponent

/-- A decimal digit: a character from `0` to `9`, by its code, which is `DIGIT`
(`%x30-39`) in the grammar of RFC 8259. -/
def Numeral.Digit (c : Char) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- The test of a digit that the scanner runs accepts exactly the decimal digits. -/
theorem Numeral.digit_iff (c : Char) : c.isDigit = true ↔ Numeral.Digit c := by
  unfold Char.isDigit Numeral.Digit
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact Iff.rfl

/-- A numeral has the form of a JSON number, as the grammar of T. Bray (ed.), *The
JavaScript Object Notation (JSON) Data Interchange Format*, RFC 8259, 2017, section 6
gives it (`number = [ minus ] int [ frac ] [ exp ]`): the digits before the point are a
single zero or a run of digits that does not start with a zero (`int`), a point is
followed by at least one digit (`frac`), and an exponent mark and its optional sign are
followed by at least one digit (`exp`). -/
structure Numeral.Formed (numeral : Numeral) : Prop where
  /-- The digits before the point are a single zero, or do not start with a zero. -/
  whole : numeral.whole = ['0'] ∨
    (numeral.whole ≠ [] ∧ (∀ c ∈ numeral.whole, Numeral.Digit c) ∧
      numeral.whole.head? ≠ some '0')
  /-- A point is followed by at least one digit, and by digits only. -/
  fraction : ∀ digits, numeral.fraction = some digits →
    digits ≠ [] ∧ ∀ c ∈ digits, Numeral.Digit c
  /-- An exponent has at least one digit, and digits only. -/
  exponent : ∀ exponent, numeral.exponent = some exponent →
    exponent.digits ≠ [] ∧ ∀ c ∈ exponent.digits, Numeral.Digit c

/-- The longest run of digits at the head of a list and what follows it, or nothing when
the list does not start with a digit. -/
private def Numeral.run (cs : List Char) : Option (List Char × List Char) :=
  if (cs.takeWhile Char.isDigit).isEmpty then none
  else some (cs.takeWhile Char.isDigit, cs.dropWhile Char.isDigit)

/-- The digits before the point: a single zero, or a run of digits. -/
private def Numeral.scanWhole : List Char → Option (List Char × List Char)
  | [] => none
  | head :: tail => if head = '0' then some (['0'], tail) else Numeral.run (head :: tail)

/-- The digits after a point, if the list starts with a point. -/
private def Numeral.scanFraction : List Char → Option (Option (List Char) × List Char)
  | [] => some (none, [])
  | head :: tail =>
    if head = '.' then (Numeral.run tail).map fun found => (some found.1, found.2)
    else some (none, head :: tail)

/-- The sign of an exponent, if the list starts with one. -/
private def Numeral.scanSign : List Char → Option Bool × List Char
  | [] => (none, [])
  | head :: tail =>
    if head = '+' then (some false, tail)
    else if head = '-' then (some true, tail)
    else (none, head :: tail)

/-- The exponent part after its mark: the sign and the digits. -/
private def Numeral.scanPower (upper : Bool) (tail : List Char) :
    Option (Option Exponent × List Char) :=
  (Numeral.run (Numeral.scanSign tail).2).map fun found =>
    (some ⟨upper, (Numeral.scanSign tail).1, found.1⟩, found.2)

/-- The exponent part, if the list starts with its mark. -/
private def Numeral.scanExponent : List Char → Option (Option Exponent × List Char)
  | [] => some (none, [])
  | head :: tail =>
    if head = 'e' then Numeral.scanPower false tail
    else if head = 'E' then Numeral.scanPower true tail
    else some (none, head :: tail)

/-- The minus sign of a number, if the list starts with one. -/
private def Numeral.scanMinus : List Char → Bool × List Char
  | [] => (false, [])
  | head :: tail => if head = '-' then (true, tail) else (false, head :: tail)

/-- The numeral at the head of a list of characters and what follows it, or nothing when
the list does not start with a JSON number. This is the one reader of a number's
spelling: the parser uses it, and `Value.numeral` reads a kept spelling back with it. -/
def Numeral.scan (cs : List Char) : Option (Numeral × List Char) :=
  (Numeral.scanWhole (Numeral.scanMinus cs).2).bind fun whole =>
    (Numeral.scanFraction whole.2).bind fun fraction =>
      (Numeral.scanExponent fraction.2).map fun exponent =>
        (⟨(Numeral.scanMinus cs).1, whole.1, fraction.1, exponent.1⟩, exponent.2)

/-- The digits of a run before a list that starts with no digit are what `takeWhile`
takes. -/
private theorem Numeral.run_taken (digits rest : List Char)
    (all : ∀ c ∈ digits, c.isDigit = true)
    (stop : ∀ c, rest.head? = some c → c.isDigit = false) :
    (digits ++ rest).takeWhile Char.isDigit = digits ∧
      (digits ++ rest).dropWhile Char.isDigit = rest := by
  induction digits with
  | nil =>
    cases rest with
    | nil => exact ⟨rfl, rfl⟩
    | cons head tail =>
      have other := stop head rfl
      constructor
      · simp only [List.nil_append, List.takeWhile_cons, other, Bool.false_eq_true, ↓reduceIte]
      · simp only [List.nil_append, List.dropWhile_cons, other, Bool.false_eq_true, ↓reduceIte]
  | cons head tail hold =>
    have digit := all head List.mem_cons_self
    have inner := hold fun c member => all c (List.mem_cons_of_mem _ member)
    constructor
    · simp only [List.cons_append, List.takeWhile_cons, digit, ↓reduceIte, inner.1]
    · simp only [List.cons_append, List.dropWhile_cons, digit, ↓reduceIte, inner.2]

/-- What `takeWhile` takes with the test of a digit is digits only. -/
private theorem Numeral.taken_digits (cs : List Char) :
    ∀ c ∈ cs.takeWhile Char.isDigit, c.isDigit = true := by
  induction cs with
  | nil => exact fun c member => nomatch member
  | cons head tail hold =>
    intro c member
    rw [List.takeWhile_cons] at member
    split at member
    · rename_i digit
      rcases List.mem_cons.mp member with same | inside
      · rw [same]
        exact digit
      · exact hold c inside
    · exact nomatch member

/-- **A run of digits before a list that starts with no digit is found whole.** -/
private theorem Numeral.run_append (digits rest : List Char) (nonempty : digits ≠ [])
    (all : ∀ c ∈ digits, c.isDigit = true)
    (stop : ∀ c, rest.head? = some c → c.isDigit = false) :
    Numeral.run (digits ++ rest) = some (digits, rest) := by
  obtain ⟨taken, dropped⟩ := Numeral.run_taken digits rest all stop
  unfold Numeral.run
  rw [taken, dropped]
  cases digits with
  | nil => exact absurd rfl nonempty
  | cons head tail => rfl

/-- **A found run is at least one digit, digits only, and the head of the list.** -/
private theorem Numeral.run_some {cs digits rest : List Char}
    (found : Numeral.run cs = some (digits, rest)) :
    digits ≠ [] ∧ (∀ c ∈ digits, c.isDigit = true) ∧ cs = digits ++ rest := by
  unfold Numeral.run at found
  split at found
  · exact nomatch found
  · rename_i nonempty
    obtain ⟨taken, dropped⟩ := Prod.mk.inj (Option.some.inj found)
    subst taken dropped
    refine ⟨fun empty => nonempty (by rw [empty]; rfl),
      Numeral.taken_digits cs,
      (List.takeWhile_append_dropWhile ..).symm⟩

/-- What `scanMinus` returns spells the list. -/
private theorem Numeral.scanMinus_chars (cs : List Char) :
    cs = (if (Numeral.scanMinus cs).1 then ['-'] else []) ++ (Numeral.scanMinus cs).2 := by
  cases cs with
  | nil => rfl
  | cons head tail =>
    by_cases minus : head = '-'
    · simp only [Numeral.scanMinus, minus, ↓reduceIte, List.singleton_append]
    · simp only [Numeral.scanMinus, minus, ↓reduceIte, Bool.false_eq_true, List.nil_append]

/-- What `scanSign` returns spells the list. -/
private theorem Numeral.scanSign_chars (cs : List Char) :
    cs = Exponent.signChars (Numeral.scanSign cs).1 ++ (Numeral.scanSign cs).2 := by
  cases cs with
  | nil => rfl
  | cons head tail =>
    by_cases plus : head = '+'
    · simp only [Numeral.scanSign, plus, ↓reduceIte]
      rfl
    · by_cases minus : head = '-'
      · have other : ¬('-' = '+') := by decide
        simp only [Numeral.scanSign, minus, other, ↓reduceIte]
        rfl
      · simp only [Numeral.scanSign, plus, minus, ↓reduceIte]
        rfl

/-- The digits before the point that `scanWhole` finds are a single zero or a run with no
leading zero, and they are the head of the list. -/
private theorem Numeral.scanWhole_some {cs whole rest : List Char}
    (found : Numeral.scanWhole cs = some (whole, rest)) :
    (whole = ['0'] ∨
        (whole ≠ [] ∧ (∀ c ∈ whole, c.isDigit = true) ∧ whole.head? ≠ some '0')) ∧
      cs = whole ++ rest := by
  cases cs with
  | nil => exact nomatch found
  | cons head tail =>
    by_cases zero : head = '0'
    · simp only [Numeral.scanWhole, zero, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨same, after⟩ := found
      subst same after zero
      exact ⟨Or.inl rfl, rfl⟩
    · simp only [Numeral.scanWhole, zero, ↓reduceIte] at found
      obtain ⟨nonempty, all, parts⟩ := Numeral.run_some found
      refine ⟨Or.inr ⟨nonempty, all, fun leading => ?_⟩, parts⟩
      cases whole with
      | nil => exact nomatch leading
      | cons first others =>
        have same : first = '0' := Option.some.inj leading
        exact zero ((List.cons.inj parts).1.trans same)

/-- The digits after a point that `scanFraction` finds are a run of at least one digit,
and the point with them is the head of the list. -/
private theorem Numeral.scanFraction_some {cs rest : List Char} {fraction : Option (List Char)}
    (found : Numeral.scanFraction cs = some (fraction, rest)) :
    (∀ digits, fraction = some digits → digits ≠ [] ∧ ∀ c ∈ digits, c.isDigit = true) ∧
      cs = Numeral.fractionChars fraction ++ rest := by
  cases cs with
  | nil =>
    obtain ⟨same, after⟩ := Prod.mk.inj (Option.some.inj found)
    subst same after
    exact ⟨fun _ wrong => (nomatch wrong), rfl⟩
  | cons head tail =>
    by_cases point : head = '.'
    · simp only [Numeral.scanFraction, point, ↓reduceIte] at found
      cases ran : Numeral.run tail with
      | none =>
        rw [ran] at found
        exact nomatch found
      | some pair =>
        rw [ran] at found
        obtain ⟨same, after⟩ := Prod.mk.inj (Option.some.inj found)
        subst same after point
        obtain ⟨nonempty, all, parts⟩ := Numeral.run_some ran
        refine ⟨fun digits same => ?_, ?_⟩
        · cases Option.some.inj same
          exact ⟨nonempty, all⟩
        · rw [parts]
          rfl
    · simp only [Numeral.scanFraction, point, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at found
      obtain ⟨same, after⟩ := found
      subst same after
      exact ⟨fun _ wrong => (nomatch wrong), rfl⟩

/-- The exponent part that `scanPower` finds after a mark has a run of at least one digit,
and its characters without the mark are the head of the list. -/
private theorem Numeral.scanPower_some {tail rest : List Char} {upper : Bool}
    {exponent : Option Exponent}
    (found : Numeral.scanPower upper tail = some (exponent, rest)) :
    ∃ part, exponent = some part ∧ part.upper = upper ∧ part.digits ≠ [] ∧
      (∀ c ∈ part.digits, c.isDigit = true) ∧
      tail = Exponent.signChars part.sign ++ part.digits ++ rest := by
  unfold Numeral.scanPower at found
  cases ran : Numeral.run (Numeral.scanSign tail).2 with
  | none =>
    rw [ran] at found
    exact nomatch found
  | some pair =>
    rw [ran] at found
    obtain ⟨same, after⟩ := Prod.mk.inj (Option.some.inj found)
    subst same after
    obtain ⟨nonempty, all, parts⟩ := Numeral.run_some ran
    refine ⟨_, rfl, rfl, nonempty, all, ?_⟩
    have signed := Numeral.scanSign_chars tail
    rw [parts, ← List.append_assoc] at signed
    exact signed

/-- The exponent part that `scanExponent` finds has a run of at least one digit, and its
characters are the head of the list. -/
private theorem Numeral.scanExponent_some {cs rest : List Char} {exponent : Option Exponent}
    (found : Numeral.scanExponent cs = some (exponent, rest)) :
    (∀ part, exponent = some part →
        part.digits ≠ [] ∧ ∀ c ∈ part.digits, c.isDigit = true) ∧
      cs = Numeral.exponentChars exponent ++ rest := by
  cases cs with
  | nil =>
    obtain ⟨same, after⟩ := Prod.mk.inj (Option.some.inj found)
    subst same after
    exact ⟨fun _ wrong => (nomatch wrong), rfl⟩
  | cons head tail =>
    by_cases lower : head = 'e'
    · simp only [Numeral.scanExponent, lower, ↓reduceIte] at found
      obtain ⟨part, same, mark, nonempty, all, parts⟩ := Numeral.scanPower_some found
      subst same lower
      refine ⟨fun other equal => ?_, ?_⟩
      · cases Option.some.inj equal
        exact ⟨nonempty, all⟩
      · show 'e' :: tail = part.chars ++ rest
        unfold Exponent.chars
        rw [mark, parts]
        simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.append_assoc]
    · by_cases upper : head = 'E'
      · simp only [Numeral.scanExponent, upper, ↓reduceIte] at found
        have distinct : ¬('E' = 'e') := by decide
        simp only [distinct, ↓reduceIte] at found
        obtain ⟨part, same, mark, nonempty, all, parts⟩ := Numeral.scanPower_some found
        subst same upper
        refine ⟨fun other equal => ?_, ?_⟩
        · cases Option.some.inj equal
          exact ⟨nonempty, all⟩
        · show 'E' :: tail = part.chars ++ rest
          unfold Exponent.chars
          rw [mark, parts]
          simp only [↓reduceIte, List.cons_append, List.append_assoc]
      · simp only [Numeral.scanExponent, lower, upper, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at found
        obtain ⟨same, after⟩ := found
        subst same after
        exact ⟨fun _ wrong => (nomatch wrong), rfl⟩

/-- **Every scanned numeral is formed, and its spelling is the head of the list.** -/
theorem Numeral.scan_formed {cs rest : List Char} {numeral : Numeral}
    (found : Numeral.scan cs = some (numeral, rest)) :
    numeral.Formed ∧ cs = numeral.chars ++ rest := by
  unfold Numeral.scan at found
  cases whole : Numeral.scanWhole (Numeral.scanMinus cs).2 with
  | none =>
    rw [whole] at found
    exact nomatch found
  | some wholePair =>
    rw [whole] at found
    cases fraction : Numeral.scanFraction wholePair.2 with
    | none =>
      rw [Option.bind_some, fraction] at found
      exact nomatch found
    | some fractionPair =>
      rw [Option.bind_some, fraction] at found
      cases exponent : Numeral.scanExponent fractionPair.2 with
      | none =>
        rw [Option.bind_some, exponent] at found
        exact nomatch found
      | some exponentPair =>
        rw [Option.bind_some, exponent] at found
        obtain ⟨same, after⟩ := Prod.mk.inj (Option.some.inj found)
        subst same after
        obtain ⟨wholeFormed, wholeParts⟩ := Numeral.scanWhole_some whole
        obtain ⟨fractionFormed, fractionParts⟩ := Numeral.scanFraction_some fraction
        obtain ⟨exponentFormed, exponentParts⟩ := Numeral.scanExponent_some exponent
        refine ⟨⟨wholeFormed.imp id fun run =>
            ⟨run.1, fun c member => (Numeral.digit_iff c).mp (run.2.1 c member), run.2.2⟩,
          fun digits same => ⟨(fractionFormed digits same).1, fun c member =>
            (Numeral.digit_iff c).mp ((fractionFormed digits same).2 c member)⟩,
          fun part same => ⟨(exponentFormed part same).1, fun c member =>
            (Numeral.digit_iff c).mp ((exponentFormed part same).2 c member)⟩⟩, ?_⟩
        have minus := Numeral.scanMinus_chars cs
        rw [wholeParts, fractionParts, exponentParts] at minus
        unfold Numeral.chars
        simp only [List.append_assoc] at minus ⊢
        exact minus

/-- A digit is none of the five characters that can follow a run of digits in a number. -/
private theorem Numeral.digit_other {c : Char} (digit : c.isDigit = true) :
    c ≠ '-' ∧ c ≠ '+' ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro same <;> rw [same] at digit <;>
    exact absurd digit (by decide)

/-- The exponent part starts with its mark, which is no digit and no point. -/
private theorem Numeral.exponentChars_head (exponent : Option Exponent) (c : Char)
    (first : (Numeral.exponentChars exponent).head? = some c) :
    c.isDigit = false ∧ c ≠ '.' := by
  cases exponent with
  | none => exact nomatch first
  | some part =>
    have mark : c = if part.upper then 'E' else 'e' := (Option.some.inj first).symm
    cases upper : part.upper <;> rw [upper] at mark <;> subst mark <;> decide

/-- `scanMinus` finds the minus sign of a spelling whose next part starts with no minus
sign. -/
private theorem Numeral.scanMinus_append (negative : Bool) (tail : List Char)
    (plain : ∀ c, tail.head? = some c → c ≠ '-') :
    Numeral.scanMinus ((if negative then ['-'] else []) ++ tail) = (negative, tail) := by
  cases negative with
  | true => simp only [↓reduceIte, List.singleton_append, Numeral.scanMinus]
  | false =>
    cases tail with
    | nil => rfl
    | cons head others =>
      have other := plain head rfl
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, Numeral.scanMinus, other]

/-- `scanWhole` finds the digits before the point of a formed numeral, before a list that
starts with no digit. -/
private theorem Numeral.scanWhole_append (whole rest : List Char)
    (formed : whole = ['0'] ∨
      (whole ≠ [] ∧ (∀ c ∈ whole, c.isDigit = true) ∧ whole.head? ≠ some '0'))
    (stop : ∀ c, rest.head? = some c → c.isDigit = false) :
    Numeral.scanWhole (whole ++ rest) = some (whole, rest) := by
  rcases formed with zero | ⟨nonempty, all, leading⟩
  · subst zero
    simp only [List.singleton_append, Numeral.scanWhole, ↓reduceIte]
  · cases whole with
    | nil => exact absurd rfl nonempty
    | cons head others =>
      have other : head ≠ '0' := fun same => leading (congrArg some same)
      simp only [List.cons_append, Numeral.scanWhole, other, ↓reduceIte]
      exact Numeral.run_append (head :: others) rest nonempty all stop

/-- `scanFraction` finds the part after the point of a formed numeral, before a list that
starts with no digit and no point. -/
private theorem Numeral.scanFraction_append (fraction : Option (List Char)) (rest : List Char)
    (formed : ∀ digits, fraction = some digits →
      digits ≠ [] ∧ ∀ c ∈ digits, c.isDigit = true)
    (stop : ∀ c, rest.head? = some c → c.isDigit = false ∧ c ≠ '.') :
    Numeral.scanFraction (Numeral.fractionChars fraction ++ rest) = some (fraction, rest) := by
  cases fraction with
  | none =>
    cases rest with
    | nil => rfl
    | cons head others =>
      have other := (stop head rfl).2
      simp only [Numeral.fractionChars, List.nil_append, Numeral.scanFraction, other,
        ↓reduceIte]
  | some digits =>
    obtain ⟨nonempty, all⟩ := formed digits rfl
    simp only [Numeral.fractionChars, List.cons_append, Numeral.scanFraction, ↓reduceIte,
      Numeral.run_append digits rest nonempty all fun c first => (stop c first).1,
      Option.map_some]

/-- `scanSign` finds the sign of an exponent before a run of digits. -/
private theorem Numeral.scanSign_append (sign : Option Bool) (digits : List Char)
    (nonempty : digits ≠ []) (all : ∀ c ∈ digits, c.isDigit = true) :
    Numeral.scanSign (Exponent.signChars sign ++ digits) = (sign, digits) := by
  cases sign with
  | none =>
    cases digits with
    | nil => exact absurd rfl nonempty
    | cons head others =>
      obtain ⟨minus, plus, _⟩ := Numeral.digit_other (all head List.mem_cons_self)
      simp only [Exponent.signChars, List.nil_append, Numeral.scanSign, plus, minus,
        ↓reduceIte]
  | some negative =>
    cases negative with
    | false => simp only [Exponent.signChars, List.singleton_append, Numeral.scanSign,
        ↓reduceIte]
    | true =>
      have other : ¬('-' = '+') := by decide
      simp only [Exponent.signChars, List.singleton_append, Numeral.scanSign, other,
        ↓reduceIte]

/-- `scanExponent` finds the exponent part of a formed numeral at the end of a list. -/
private theorem Numeral.scanExponent_chars (exponent : Option Exponent)
    (formed : ∀ part, exponent = some part →
      part.digits ≠ [] ∧ ∀ c ∈ part.digits, c.isDigit = true) :
    Numeral.scanExponent (Numeral.exponentChars exponent) = some (exponent, []) := by
  cases exponent with
  | none => rfl
  | some part =>
    obtain ⟨nonempty, all⟩ := formed part rfl
    have signed := Numeral.scanSign_append part.sign part.digits nonempty all
    have ran := Numeral.run_append part.digits [] nonempty all fun c first => nomatch first
    rw [List.append_nil] at ran
    cases part with
    | mk upper sign digits =>
      cases upper with
      | false =>
        simp only [Numeral.exponentChars, Exponent.chars, Bool.false_eq_true, ↓reduceIte,
          Numeral.scanExponent, Numeral.scanPower, signed, ran, Option.map_some]
      | true =>
        have other : ¬('E' = 'e') := by decide
        simp only [Numeral.exponentChars, Exponent.chars, ↓reduceIte, Numeral.scanExponent,
          other, Numeral.scanPower, signed, ran, Option.map_some]

/-- **The spelling of a formed numeral scans to that numeral, with nothing left.** -/
theorem Numeral.scan_chars (numeral : Numeral) (formed : numeral.Formed) :
    Numeral.scan numeral.chars = some (numeral, []) := by
  have wholeChecked : numeral.whole = ['0'] ∨
      (numeral.whole ≠ [] ∧ (∀ c ∈ numeral.whole, c.isDigit = true) ∧
        numeral.whole.head? ≠ some '0') :=
    formed.whole.imp id fun run =>
      ⟨run.1, fun c member => (Numeral.digit_iff c).mpr (run.2.1 c member), run.2.2⟩
  have fractionChecked : ∀ digits, numeral.fraction = some digits →
      digits ≠ [] ∧ ∀ c ∈ digits, c.isDigit = true := fun digits same =>
    ⟨(formed.fraction digits same).1, fun c member =>
      (Numeral.digit_iff c).mpr ((formed.fraction digits same).2 c member)⟩
  have exponentChecked : ∀ part, numeral.exponent = some part →
      part.digits ≠ [] ∧ ∀ c ∈ part.digits, c.isDigit = true := fun part same =>
    ⟨(formed.exponent part same).1, fun c member =>
      (Numeral.digit_iff c).mpr ((formed.exponent part same).2 c member)⟩
  have exponent := Numeral.scanExponent_chars numeral.exponent exponentChecked
  have fraction := Numeral.scanFraction_append numeral.fraction
    (Numeral.exponentChars numeral.exponent) fractionChecked
    (Numeral.exponentChars_head numeral.exponent)
  have fractionStop : ∀ c,
      (Numeral.fractionChars numeral.fraction ++
        Numeral.exponentChars numeral.exponent).head? = some c → c.isDigit = false := by
    intro c first
    cases present : numeral.fraction with
    | none =>
      rw [present] at first
      exact (Numeral.exponentChars_head numeral.exponent c first).1
    | some digits =>
      rw [present] at first
      have point : c = '.' := (Option.some.inj first).symm
      subst point
      decide
  have whole := Numeral.scanWhole_append numeral.whole
    (Numeral.fractionChars numeral.fraction ++ Numeral.exponentChars numeral.exponent)
    wholeChecked fractionStop
  have plain : ∀ c, (numeral.whole ++ (Numeral.fractionChars numeral.fraction ++
      Numeral.exponentChars numeral.exponent)).head? = some c → c ≠ '-' := by
    intro c first
    rcases wholeChecked with zero | ⟨nonempty, all, _⟩
    · rw [zero] at first
      have same : c = '0' := (Option.some.inj first).symm
      subst same
      decide
    · cases shape : numeral.whole with
      | nil => exact absurd shape nonempty
      | cons head others =>
        rw [shape] at first all
        have same : c = head := (Option.some.inj first).symm
        subst same
        exact (Numeral.digit_other (all c List.mem_cons_self)).1
  have minus := Numeral.scanMinus_append numeral.negative
    (numeral.whole ++ (Numeral.fractionChars numeral.fraction ++
      Numeral.exponentChars numeral.exponent)) plain
  unfold Numeral.scan Numeral.chars
  rw [List.append_assoc, List.append_assoc, minus]
  simp only [whole, Option.bind_some, fraction, exponent, Option.map_some]

private def number (cs : List Char) : Except String (Value × List Char) :=
  match Numeral.scan cs with
  | some (numeral, rest) => .ok (.number (String.ofList numeral.chars), rest)
  | none => .error "missing JSON number digits"

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

/-- The numeral of a number: its kept spelling, scanned by the scanner that the parser
uses. Nothing for a value that is no number, and for a number whose spelling is not the
whole spelling of a JSON number. -/
def Value.numeral : Value → Option Numeral
  | .number spelling =>
    match Numeral.scan spelling.toList with
    | some (numeral, []) => some numeral
    | _ => none
  | _ => none

/-- A value is a number whose kept spelling is the spelling of a formed numeral. -/
def Value.Numeric (value : Value) : Prop :=
  ∃ numeral : Numeral, numeral.Formed ∧ value = .number (String.ofList numeral.chars)

/-- **A value has a numeral exactly when it is a number with the spelling of that numeral,
and the numeral is formed.** For every value and numeral. -/
theorem Value.numeral_iff (value : Value) (numeral : Numeral) :
    value.numeral = some numeral ↔
      numeral.Formed ∧ value = .number (String.ofList numeral.chars) := by
  constructor
  · intro found
    cases value with
    | number spelling =>
      change (match Numeral.scan spelling.toList with
        | some (numeral, []) => some numeral
        | _ => none) = some numeral at found
      cases scanned : Numeral.scan spelling.toList with
      | none =>
        rw [scanned] at found
        exact nomatch found
      | some pair =>
        obtain ⟨read, rest⟩ := pair
        rw [scanned] at found
        cases rest with
        | cons head tail => exact nomatch found
        | nil =>
          cases Option.some.inj found
          obtain ⟨formed, parts⟩ := Numeral.scan_formed scanned
          rw [List.append_nil] at parts
          refine ⟨formed, ?_⟩
          rw [← parts, String.ofList_toList]
    | null | bool _ | string _ | array _ | object _ => exact nomatch found
  · rintro ⟨formed, rfl⟩
    unfold Value.numeral
    simp only [String.toList_ofList, Numeral.scan_chars numeral formed]

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

/-- The value of the first member of an object that has the name, and nothing for an
object with no such member and for a value that is no object. It consumes nothing, so a
reader can take some members of an object and leave the others. `parse` refuses an object
with two members of one name, so in a parsed text the first is the only one. -/
def Value.member (name : String) : Value → Option Value
  | .object fields => (fields.find? fun field => field.1 = name).map (·.2)
  | _ => none

/-- `inner` is the value of the first member of the object `outer` that has the name: the
members of the object are some members with other names, then the member, then the rest. -/
def Value.Member (name : String) (outer inner : Value) : Prop :=
  ∃ before after : List (String × Value),
    outer = .object (before ++ (name, inner) :: after) ∧ ∀ field ∈ before, field.1 ≠ name

/-- **The member read is the first member with the name.** For every name and every two
values. -/
theorem Value.member_iff (name : String) (outer inner : Value) :
    outer.member name = some inner ↔ Value.Member name outer inner := by
  unfold Value.Member
  cases outer with
  | object fields =>
    unfold Value.member
    rw [Option.map_eq_some_iff]
    constructor
    · rintro ⟨⟨key, value⟩, found, rfl⟩
      obtain ⟨named, before, after, rfl, others⟩ := List.find?_eq_some_iff_append.mp found
      have same : key = name := by simpa using named
      subst same
      exact ⟨before, after, rfl, fun field inside => by simpa using others field inside⟩
    · rintro ⟨before, after, same, others⟩
      cases same
      exact ⟨(name, inner), List.find?_eq_some_iff_append.mpr
        ⟨by simp, before, after, rfl, fun field inside => by simpa using others field inside⟩,
        rfl⟩
  | null | bool _ | number _ | string _ | array _ =>
    exact ⟨fun found => (nomatch found), fun ⟨_, _, same, _⟩ => (nomatch same)⟩

/-! ## The text of a request, and reading it back

A request that a host writes is a JSON object of two levels: its members are scalars
(a string, a number by its numeral, a boolean) or one object of scalars. `Request.chars`
is the text of such an object, with no space. `parse_request` states that `parse`
reads that text back as the value of the request, for every request whose strings need no
escape, whose numbers are formed numerals with no exponent part, and whose member names
differ at each level. It is a statement about `parse` on a family of texts; `parse_sound`
in the next section states what every text that `parse` accepts is. -/

/-- A character that a string of a request can hold as it is: no quotation mark, no
reverse solidus and no control character. -/
def Plain (c : Char) : Prop :=
  c ≠ '"' ∧ c ≠ '\\' ∧ 32 ≤ c.toNat

instance (c : Char) : Decidable (Plain c) :=
  inferInstanceAs (Decidable (c ≠ '"' ∧ c ≠ '\\' ∧ 32 ≤ c.toNat))

/-- A scalar of a request: a string, a number by its numeral, or a boolean. -/
inductive Scalar where
  /-- A string. -/
  | text (value : String)
  /-- A number, by its numeral. -/
  | number (numeral : Numeral)
  /-- A boolean. -/
  | flag (value : Bool)

/-- The value of a scalar. -/
def Scalar.value : Scalar → Value
  | .text value => .string value
  | .number numeral => .number (String.ofList numeral.chars)
  | .flag value => .bool value

/-- The text of a scalar. -/
def Scalar.chars : Scalar → List Char
  | .text value => '"' :: (value.toList ++ ['"'])
  | .number numeral => numeral.chars
  | .flag true => ['t', 'r', 'u', 'e']
  | .flag false => ['f', 'a', 'l', 's', 'e']

/-- A scalar that the text of a request writes as it is: a string of plain characters, a
formed numeral with no exponent part, or a boolean. -/
def Scalar.Simple : Scalar → Prop
  | .text value => ∀ c ∈ value.toList, Plain c
  | .number numeral => numeral.Formed ∧ numeral.exponent = none
  | .flag _ => True

/-- The white space of the parser leaves a list that starts with no space as it is. -/
private theorem ws_cons (c : Char) (cs : List Char)
    (solid : (c == ' ' || c == '\r' || c == '\n' || c == '\t') = false) :
    ws (c :: cs) = c :: cs := by
  unfold ws
  rw [List.dropWhile_cons, solid]
  rfl

/-- Pushing characters one by one appends their string. -/
private theorem foldl_push (characters : List Char) (out : String) :
    characters.foldl String.push out = out ++ String.ofList characters := by
  induction characters generalizing out with
  | nil => simp
  | cons head tail hold =>
    rw [List.foldl_cons, hold, String.push_eq_append, String.ofList_cons, String.append_assoc]

/-- One plain character of the body of a string is pushed, and the body goes on. -/
private theorem stringBody_step (c : Char) (cs : List Char) (out : String) (fuel : Nat)
    (plain : Plain c) :
    stringBody (fuel + 1) (c :: cs) out = stringBody fuel cs (out.push c) := by
  obtain ⟨quote, solidus, visible⟩ := plain
  conv => lhs; unfold stringBody
  split
  · rename_i wrong
    exact nomatch wrong
  · rename_i wrong
    exact absurd (List.cons.inj wrong).1 quote
  · rename_i wrong
    exact absurd (List.cons.inj wrong).1 solidus
  · rename_i wrong
    exact absurd (List.cons.inj wrong).1 solidus
  · rename_i other others same
    obtain ⟨rfl, rfl⟩ := List.cons.inj same
    simp only [Nat.not_lt.mpr visible, ↓reduceIte]

/-- The body of a string of plain characters is read up to its closing quotation mark, with
fuel for each character and the mark. -/
private theorem stringBody_plain (characters rest : List Char) (out : String) (fuel : Nat)
    (plain : ∀ c ∈ characters, Plain c) (enough : characters.length < fuel) :
    stringBody fuel (characters ++ '"' :: rest) out =
      .ok (characters.foldl String.push out, rest) := by
  induction characters generalizing out fuel with
  | nil =>
    cases fuel with
    | zero => exact absurd enough (Nat.lt_irrefl 0)
    | succ fuel => rfl
  | cons head tail hold =>
    cases fuel with
    | zero => exact absurd enough (Nat.not_lt_zero _)
    | succ fuel =>
      show stringBody (fuel + 1) (head :: (tail ++ '"' :: rest)) out = _
      rw [stringBody_step head _ out fuel (plain head List.mem_cons_self), List.foldl_cons]
      exact hold (out.push head) fuel
        (fun c inside => plain c (List.mem_cons_of_mem head inside))
        (Nat.lt_of_succ_lt_succ enough)

/-- A string of plain characters between quotation marks is read as that string. -/
private theorem stringValue_plain (characters rest : List Char)
    (plain : ∀ c ∈ characters, Plain c) :
    stringValue ('"' :: (characters ++ '"' :: rest)) = .ok (String.ofList characters, rest) := by
  unfold stringValue
  show (stringBody ('"' :: (characters ++ '"' :: rest)).length (characters ++ '"' :: rest) "") = _
  rw [stringBody_plain characters rest "" _ plain (by simp; omega), foldl_push,
    String.empty_append]

/-- A character that can follow a number in the text of a request: no digit, no point and
no exponent mark. -/
private def Stops (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → c.isDigit = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E'

/-- **A formed numeral with no exponent part is scanned back from the head of a text.** For
every such numeral and every text after it that starts with no digit, no point and no
exponent mark: the scanner gives the numeral and that text. -/
theorem Numeral.scan_append (numeral : Numeral) (formed : numeral.Formed)
    (bare : numeral.exponent = none) (rest : List Char)
    (stop : ∀ c, rest.head? = some c → c.isDigit = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E') :
    Numeral.scan (numeral.chars ++ rest) = some (numeral, rest) := by
  have wholeChecked : numeral.whole = ['0'] ∨
      (numeral.whole ≠ [] ∧ (∀ c ∈ numeral.whole, c.isDigit = true) ∧
        numeral.whole.head? ≠ some '0') :=
    formed.whole.imp id fun run =>
      ⟨run.1, fun c member => (Numeral.digit_iff c).mpr (run.2.1 c member), run.2.2⟩
  have fractionChecked : ∀ digits, numeral.fraction = some digits →
      digits ≠ [] ∧ ∀ c ∈ digits, c.isDigit = true := fun digits same =>
    ⟨(formed.fraction digits same).1, fun c member =>
      (Numeral.digit_iff c).mpr ((formed.fraction digits same).2 c member)⟩
  have exponent : Numeral.scanExponent rest = some (none, rest) := by
    cases rest with
    | nil => rfl
    | cons head others =>
      obtain ⟨_, _, lower, upper⟩ := stop head rfl
      simp only [Numeral.scanExponent, lower, upper, ↓reduceIte]
  have fraction := Numeral.scanFraction_append numeral.fraction rest fractionChecked
    fun c first => ⟨(stop c first).1, (stop c first).2.1⟩
  have fractionStop : ∀ c,
      (Numeral.fractionChars numeral.fraction ++ rest).head? = some c → c.isDigit = false := by
    intro c first
    cases present : numeral.fraction with
    | none =>
      rw [present] at first
      exact (stop c first).1
    | some digits =>
      rw [present] at first
      have point : c = '.' := (Option.some.inj first).symm
      subst point
      decide
  have whole := Numeral.scanWhole_append numeral.whole
    (Numeral.fractionChars numeral.fraction ++ rest) wholeChecked fractionStop
  have plain : ∀ c, (numeral.whole ++ (Numeral.fractionChars numeral.fraction ++
      rest)).head? = some c → c ≠ '-' := by
    intro c first
    rcases wholeChecked with zero | ⟨nonempty, all, _⟩
    · rw [zero] at first
      have same : c = '0' := (Option.some.inj first).symm
      subst same
      decide
    · cases shape : numeral.whole with
      | nil => exact absurd shape nonempty
      | cons head others =>
        rw [shape] at first all
        have same : c = head := (Option.some.inj first).symm
        subst same
        exact (Numeral.digit_other (all c List.mem_cons_self)).1
  have minus := Numeral.scanMinus_append numeral.negative
    (numeral.whole ++ (Numeral.fractionChars numeral.fraction ++ rest)) plain
  have spelled : numeral.chars ++ rest =
      (if numeral.negative then ['-'] else []) ++
        (numeral.whole ++ (Numeral.fractionChars numeral.fraction ++ rest)) := by
    unfold Numeral.chars
    rw [bare]
    simp only [Numeral.exponentChars, List.append_nil, List.append_assoc]
  have same : numeral = ⟨numeral.negative, numeral.whole, numeral.fraction, none⟩ := by
    cases numeral
    cases bare
    rfl
  unfold Numeral.scan
  rw [spelled, minus]
  simp only [whole, Option.bind_some, fraction, exponent, Option.map_some]
  rw [← same]

/-- A formed numeral with no exponent part, at the head of a text that goes on with no
digit, point or exponent mark, is read as the number with its spelling. -/
private theorem number_append (numeral : Numeral) (formed : numeral.Formed)
    (bare : numeral.exponent = none) (rest : List Char) (stop : Stops rest) :
    number (numeral.chars ++ rest) = .ok (.number (String.ofList numeral.chars), rest) := by
  unfold number
  rw [Numeral.scan_append numeral formed bare rest stop]

/-- What follows a value in an object of a request: a comma or a closing brace. -/
private def Delimited (rest : List Char) : Prop :=
  ∃ tail, rest = ',' :: tail ∨ rest = '}' :: tail

/-- A text that starts with a comma or a brace stops a number. -/
private theorem Delimited.stops {rest : List Char} (delimited : Delimited rest) : Stops rest := by
  obtain ⟨tail, rfl | rfl⟩ := delimited <;>
    (intro c first
     cases Option.some.inj first
     decide)

/-- The text of a formed numeral starts with a minus sign or a digit. -/
private theorem Numeral.chars_head (numeral : Numeral) (formed : numeral.Formed) :
    ∃ first more, numeral.chars = first :: more ∧ (first = '-' ∨ first.isDigit = true) := by
  unfold Numeral.chars
  cases numeral.negative with
  | true => exact ⟨'-', _, rfl, .inl rfl⟩
  | false =>
    rcases formed.whole with zero | ⟨nonempty, all, _⟩
    · rw [zero]
      exact ⟨'0', _, rfl, .inr (by decide)⟩
    · cases shape : numeral.whole with
      | nil => exact absurd shape nonempty
      | cons head others =>
        rw [shape] at all
        exact ⟨head, _, rfl, .inr ((Numeral.digit_iff head).mpr (all head List.mem_cons_self))⟩

/-- A simple scalar at the head of a text that goes on with a comma or a brace is read as
its value, at any depth the parser admits and with any fuel. -/
private theorem value_scalar (scalar : Scalar) (simple : scalar.Simple) (rest : List Char)
    (delimited : Delimited rest) (fuel depth : Nat) (shallow : depth ≤ 128) :
    value (fuel + 1) depth (scalar.chars ++ rest) = .ok (scalar.value, rest) := by
  have deep : ¬depth > 128 := Nat.not_lt.mpr shallow
  cases scalar with
  | text written =>
    have opened : ws ('"' :: (written.toList ++ '"' :: rest)) =
        '"' :: (written.toList ++ '"' :: rest) := ws_cons _ _ (by decide)
    show value (fuel + 1) depth ('"' :: ((written.toList ++ ['"']) ++ rest)) = _
    rw [List.append_assoc, List.singleton_append]
    unfold value
    simp only [deep, ↓reduceIte, opened, stringValue_plain written.toList rest simple,
      String.ofList_toList]
    rfl
  | flag truth =>
    cases truth with
    | true =>
      show value (fuel + 1) depth ('t' :: 'r' :: 'u' :: 'e' :: rest) = _
      unfold value
      simp only [deep, ↓reduceIte, ws_cons 't' _ (by decide)]
      rfl
    | false =>
      show value (fuel + 1) depth ('f' :: 'a' :: 'l' :: 's' :: 'e' :: rest) = _
      unfold value
      simp only [deep, ↓reduceIte, ws_cons 'f' _ (by decide)]
      rfl
  | number numeral =>
    obtain ⟨formed, bare⟩ := simple
    obtain ⟨first, more, spelled, leading⟩ := numeral.chars_head formed
    have read := number_append numeral formed bare rest delimited.stops
    have solid : (first == ' ' || first == '\r' || first == '\n' || first == '\t') = false := by
      rcases leading with rfl | digit
      · decide
      · have other : first ≠ ' ' ∧ first ≠ '\r' ∧ first ≠ '\n' ∧ first ≠ '\t' := by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intro same <;> rw [same] at digit <;>
            exact absurd digit (by decide)
        simp [other.1, other.2.1, other.2.2.1, other.2.2.2]
    have starts : (first == '-' || first.isDigit) = true := by
      rcases leading with rfl | digit
      · decide
      · simp [digit]
    have differs : first ≠ '"' ∧ first ≠ '{' ∧ first ≠ '[' ∧ first ≠ 'n' ∧ first ≠ 't' ∧
        first ≠ 'f' := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro same <;> rw [same] at leading <;>
        exact absurd leading (by decide)
    show value (fuel + 1) depth (numeral.chars ++ rest) = _
    rw [spelled] at read ⊢
    rw [List.cons_append] at read ⊢
    unfold value
    simp only [deep, ↓reduceIte, ws_cons first _ solid]
    split
    · rename_i wrong
      exact absurd (List.cons.inj wrong).1 differs.1
    · rename_i wrong
      exact absurd (List.cons.inj wrong).1 differs.2.1
    · rename_i wrong
      exact absurd (List.cons.inj wrong).1 differs.2.2.1
    · rename_i wrong
      exact absurd (List.cons.inj wrong).1 differs.2.2.2.1
    · rename_i wrong
      exact absurd (List.cons.inj wrong).1 differs.2.2.2.2.1
    · rename_i wrong
      exact absurd (List.cons.inj wrong).1 differs.2.2.2.2.2
    · rename_i c others same
      cases (List.cons.inj same).1
      simp only [starts, ↓reduceIte]
      have valued : (Scalar.number numeral).value =
          .number (String.ofList (first :: more)) := by
        show Value.number (String.ofList numeral.chars) = _
        rw [spelled]
      rw [valued]
      exact read
    · rename_i wrong
      exact nomatch wrong

/-- A member of an object as the parser meets it: the characters of its name, the text of
its value, the value, and the fuel that reading the value needs. -/
private structure Entry where
  /-- The characters of the name. -/
  name : List Char
  /-- The text of the value. -/
  text : List Char
  /-- The value. -/
  parsed : Value
  /-- The fuel that reading the value needs. -/
  need : Nat

/-- The parser's value reader reads the text of the member as its value, before a comma or
a brace, at one depth and with the fuel the member needs. -/
private def Entry.Read (depth : Nat) (entry : Entry) : Prop :=
  ∀ fuel rest, entry.need ≤ fuel → Delimited rest →
    value fuel depth (entry.text ++ rest) = .ok (entry.parsed, rest)

/-- The text of one member: its name between quotation marks, a colon and its value. -/
private def Entry.chars (entry : Entry) : List Char :=
  '"' :: (entry.name ++ '"' :: ':' :: entry.text)

/-- The texts of the members of an object one after the other, with a comma between two. -/
def joined : List (List Char) → List Char
  | [] => []
  | [text] => text
  | text :: next :: more => text ++ ',' :: joined (next :: more)

/-- The name and the value of a member, as the parser keeps them. -/
private def Entry.field (entry : Entry) : String × Value :=
  (String.ofList entry.name, entry.parsed)

/-- The members of an object that is not empty are read in order, up to the closing brace:
for names of plain characters that differ from each other and from the members read
before, values that the value reader reads, and fuel for each member. -/
private theorem fields_entries (entries : List Entry) (depth : Nat) :
    ∀ (out : List (String × Value)) (rest : List Char) (fuel : Nat),
      entries ≠ [] →
      (∀ entry ∈ entries, ∀ c ∈ entry.name, Plain c) →
      (∀ entry ∈ entries, entry.Read depth) →
      (∀ entry ∈ entries, ∀ field ∈ out, field.1 ≠ String.ofList entry.name) →
      (entries.map fun entry => String.ofList entry.name).Nodup →
      (∀ entry ∈ entries, entry.need + entries.length ≤ fuel) →
      fields fuel depth (joined (entries.map Entry.chars) ++ '}' :: rest) out =
        .ok (.object (out ++ entries.map Entry.field), rest) := by
  induction entries with
  | nil => exact fun _ _ _ wrong => absurd rfl wrong
  | cons entry more hold =>
    intro out rest fuel _ names read fresh distinct enough
    have plain := names entry List.mem_cons_self
    have unseen : (out.any fun field => field.1 == String.ofList entry.name) = false := by
      rw [List.any_eq_false]
      intro field inside
      simpa using fresh entry List.mem_cons_self field inside
    obtain ⟨less, fueled⟩ : ∃ less, fuel = less + 1 :=
      ⟨fuel - 1, by have := enough entry List.mem_cons_self; simp at this; omega⟩
    subst fueled
    have needed : entry.need ≤ less := by
      have := enough entry List.mem_cons_self
      simp at this
      omega
    cases more with
    | nil =>
      have valued := read entry List.mem_cons_self less ('}' :: rest) needed ⟨rest, .inr rfl⟩
      show fields (less + 1) depth
        ('"' :: (entry.name ++ '"' :: ':' :: entry.text) ++ '}' :: rest) out = _
      rw [List.cons_append, List.append_assoc, List.cons_append, List.cons_append]
      unfold fields
      simp only [ws_cons '"' _ (by decide), stringValue_plain entry.name _ plain, Bind.bind,
        Except.bind, unseen, Bool.false_eq_true, ↓reduceIte, ws_cons ':' _ (by decide), require,
        beq_self_eq_true, valued, ws_cons '}' _ (by decide), pure, Except.pure, List.map_cons,
        List.map_nil]
      rfl
    | cons next others =>
      have following :
          Delimited (',' :: (joined ((next :: others).map Entry.chars) ++ '}' :: rest)) :=
        ⟨_, .inl rfl⟩
      have valued := read entry List.mem_cons_self less _ needed following
      have later := hold (out ++ [entry.field]) rest less (fun wrong => nomatch wrong)
        (fun other inside => names other (List.mem_cons_of_mem entry inside))
        (fun other inside => read other (List.mem_cons_of_mem entry inside))
        (fun other inside field held => by
          rcases List.mem_append.mp held with before | here
          · exact fresh other (List.mem_cons_of_mem entry inside) field before
          · rw [List.mem_singleton.mp here]
            intro same
            have apart := (List.nodup_cons.mp distinct).1
            exact apart (List.mem_map.mpr ⟨other, inside, same.symm⟩))
        (List.nodup_cons.mp distinct).2
        (fun other inside => by
          have := enough other (List.mem_cons_of_mem entry inside)
          simp at this ⊢
          omega)
      show fields (less + 1) depth
        (('"' :: (entry.name ++ '"' :: ':' :: entry.text) ++
          ',' :: joined ((next :: others).map Entry.chars)) ++ '}' :: rest) out = _
      rw [List.cons_append, List.cons_append, List.append_assoc, List.append_assoc,
        List.cons_append, List.cons_append, List.cons_append]
      unfold fields
      simp only [ws_cons '"' _ (by decide), stringValue_plain entry.name _ plain, Bind.bind,
        Except.bind, unseen, Bool.false_eq_true, ↓reduceIte, ws_cons ':' _ (by decide), require,
        beq_self_eq_true, valued, ws_cons ',' _ (by decide)]
      have regroup : out ++ [entry.field] ++ List.map Entry.field (next :: others) =
          out ++ List.map Entry.field (entry :: next :: others) := by
        rw [List.append_assoc]
        rfl
      rw [regroup] at later
      exact later

/-- An object with members is read as the object of their fields, whatever follows it: for
names of plain characters that differ, values that the value reader reads one level deeper,
and fuel for each member. -/
private theorem value_entries (entries : List Entry) (depth fuel : Nat) (rest : List Char)
    (shallow : depth ≤ 128) (nonempty : entries ≠ [])
    (names : ∀ entry ∈ entries, ∀ c ∈ entry.name, Plain c)
    (read : ∀ entry ∈ entries, entry.Read (depth + 1))
    (distinct : (entries.map fun entry => String.ofList entry.name).Nodup)
    (enough : ∀ entry ∈ entries, entry.need + entries.length ≤ fuel) :
    value (fuel + 1) depth ('{' :: (joined (entries.map Entry.chars) ++ '}' :: rest)) =
      .ok (.object (entries.map Entry.field), rest) := by
  have deep : ¬depth > 128 := Nat.not_lt.mpr shallow
  have inner := fields_entries entries (depth + 1) [] rest fuel nonempty names read
    (fun _ _ _ wrong => nomatch wrong) distinct enough
  rw [List.nil_append] at inner
  cases entries with
  | nil => exact absurd rfl nonempty
  | cons entry more =>
    have opened : ∃ tail, joined ((entry :: more).map Entry.chars) ++ '}' :: rest = '"' :: tail := by
      cases more with
      | nil => exact ⟨_, rfl⟩
      | cons next others => exact ⟨_, rfl⟩
    obtain ⟨tail, shape⟩ := opened
    rw [shape] at inner ⊢
    unfold value
    simp only [deep, ↓reduceIte, ws_cons '{' _ (by decide), ws_cons '"' _ (by decide)]
    exact inner

/-- The text of a scalar is not empty, and reading it needs one unit of fuel. -/
private def Scalar.entry (name : String) (scalar : Scalar) : Entry :=
  ⟨name.toList, scalar.chars, scalar.value, 1⟩

/-- A simple scalar is read at every depth the parser admits. -/
private theorem Scalar.entry_read (name : String) (scalar : Scalar) (simple : scalar.Simple)
    (depth : Nat) (shallow : depth ≤ 128) : (scalar.entry name).Read depth := by
  intro fuel rest needed delimited
  obtain ⟨less, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by
    have : 1 ≤ fuel := needed
    omega⟩
  exact value_scalar scalar simple rest delimited less depth shallow

/-- A member of a request: a scalar, or an object of scalars by their names. -/
inductive Part where
  /-- A scalar. -/
  | scalar (scalar : Scalar)
  /-- An object of scalars, each with its name. -/
  | object (members : List (String × Scalar))

/-- The text of a member with a name: the name between quotation marks, a colon and the text
of the value. -/
def member (name : String) (text : List Char) : List Char :=
  '"' :: (name.toList ++ '"' :: ':' :: text)

/-- The value of a part. -/
def Part.value : Part → Value
  | .scalar inner => inner.value
  | .object members => .object (members.map fun pair => (pair.1, pair.2.value))

/-- The text of a part. -/
def Part.chars : Part → List Char
  | .scalar inner => inner.chars
  | .object members =>
    '{' :: (joined (members.map fun pair => member pair.1 pair.2.chars) ++ ['}'])

/-- A part that the text of a request writes as it is: a simple scalar, or an object whose
names are of plain characters and differ and whose scalars are simple. -/
def Part.Simple : Part → Prop
  | .scalar inner => inner.Simple
  | .object members =>
    (∀ pair ∈ members, (∀ c ∈ pair.1.toList, Plain c) ∧ pair.2.Simple) ∧
      (members.map fun pair => pair.1).Nodup

/-- A request: the members of its object, each with its name. -/
abbrev Request := List (String × Part)

/-- The value of a request: the object of its members. -/
def Request.value (request : Request) : Value :=
  .object (request.map fun pair => (pair.1, pair.2.value))

/-- The text of a request: its members between braces, with a comma between two and no
space. -/
def Request.chars (request : Request) : List Char :=
  '{' :: (joined (request.map fun pair => member pair.1 pair.2.chars) ++ ['}'])

/-- A request that its text writes as it is: the names of its members are of plain
characters and differ, and its parts are simple. -/
def Request.Simple (request : Request) : Prop :=
  (∀ pair ∈ request, (∀ c ∈ pair.1.toList, Plain c) ∧ pair.2.Simple) ∧
    (request.map fun pair => pair.1).Nodup

/-- A text of the joined texts has, with the count of the texts, at most the length of the
whole and one. -/
private theorem joined_length (texts : List (List Char)) :
    ∀ text ∈ texts, text.length + texts.length ≤ (joined texts).length + 1 := by
  induction texts with
  | nil => exact fun _ wrong => nomatch wrong
  | cons first more hold =>
    cases more with
    | nil =>
      intro text inside
      cases List.mem_singleton.mp inside
      exact Nat.le_refl _
    | cons next others =>
      have rest := hold
      have second := rest next List.mem_cons_self
      intro text inside
      show text.length + (others.length + 1 + 1) ≤
        (first ++ ',' :: joined (next :: others)).length + 1
      rw [List.length_append, List.length_cons]
      simp only [List.length_cons] at second
      rcases List.mem_cons.mp inside with rfl | later
      · omega
      · have bound := rest text later
        simp only [List.length_cons] at bound
        omega

/-- The names of members, read back from their characters, are the names. -/
private theorem names_back {α : Type} (pairs : List (String × α)) :
    (pairs.map fun pair => String.ofList pair.1.toList) = pairs.map fun pair => pair.1 :=
  List.map_congr_left fun _ _ => String.ofList_toList

/-- The fuel that reading a part needs. -/
private def Part.need : Part → Nat
  | .scalar _ => 1
  | .object members => members.length + 2

/-- A part as a member the parser meets. -/
private def Part.entry (name : String) (part : Part) : Entry :=
  ⟨name.toList, part.chars, part.value, part.need⟩

/-- The fuel a part needs is at most the length of its text and one. -/
private theorem Part.need_le (part : Part) : part.need ≤ part.chars.length + 1 := by
  cases part with
  | scalar inner => exact Nat.succ_le_succ (Nat.zero_le _)
  | object members =>
    show members.length + 2 ≤
      ('{' :: (joined (members.map fun pair => member pair.1 pair.2.chars) ++ ['}'])).length + 1
    rw [List.length_cons, List.length_append, List.length_singleton]
    cases members with
    | nil => exact Nat.le_add_left _ _
    | cons pair more =>
      have bound := joined_length (((pair :: more).map fun pair => member pair.1 pair.2.chars))
        (member pair.1 pair.2.chars) List.mem_cons_self
      simp only [List.length_map, List.length_cons] at bound ⊢
      omega

/-- A simple part is read at every depth below the deepest the parser admits. -/
private theorem part_read (name : String) (part : Part) (simple : part.Simple)
    (depth : Nat) (shallow : depth + 1 ≤ 128) : (part.entry name).Read depth := by
  cases part with
  | scalar inner => exact inner.entry_read name simple depth (Nat.le_of_succ_le shallow)
  | object members =>
    obtain ⟨parts, distinct⟩ := simple
    intro fuel rest needed _
    obtain ⟨less, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by
      have : members.length + 2 ≤ fuel := needed
      omega⟩
    have sized : members.length + 1 ≤ less := by
      have : members.length + 2 ≤ less + 1 := needed
      omega
    show value (less + 1) depth
      ('{' :: (joined (members.map fun pair => member pair.1 pair.2.chars) ++ ['}']) ++ rest) = _
    rw [List.cons_append, List.append_assoc, List.singleton_append]
    cases members with
    | nil =>
      have deep : ¬depth > 128 := by omega
      show value (less + 1) depth ('{' :: '}' :: rest) = _
      unfold value
      simp only [deep, ↓reduceIte, ws_cons '{' _ (by decide), ws_cons '}' _ (by decide)]
      rfl
    | cons pair more =>
      have read := value_entries (((pair :: more).map fun pair => pair.2.entry pair.1)) depth less
        rest (Nat.le_of_succ_le shallow) (fun wrong => nomatch wrong)
        (fun entry inside => by
          obtain ⟨found, held, rfl⟩ := List.mem_map.mp inside
          exact (parts found held).1)
        (fun entry inside => by
          obtain ⟨found, held, rfl⟩ := List.mem_map.mp inside
          exact found.2.entry_read found.1 (parts found held).2 (depth + 1) shallow)
        (by
          rw [List.map_map]
          exact (names_back (pair :: more)).symm ▸ distinct)
        (fun entry inside => by
          obtain ⟨found, _, rfl⟩ := List.mem_map.mp inside
          show 1 + ((pair :: more).map fun pair => pair.2.entry pair.1).length ≤ less
          rw [List.length_map]
          omega)
      have fielded : ((pair :: more).map fun pair => pair.2.entry pair.1).map Entry.field =
          (pair :: more).map fun pair => (pair.1, pair.2.value) := by
        rw [List.map_map]
        exact List.map_congr_left fun found _ =>
          Prod.ext (String.ofList_toList (s := found.1)) rfl
      rw [fielded, List.map_map] at read
      exact read

/-- **The parser reads the text of a request back as its value.** For every request whose
names are of plain characters and differ at each level, whose strings are of plain
characters and whose numbers are formed numerals with no exponent part: `parse` accepts the
text, and the value it gives is the value of the request, with every member in its
place. -/
theorem parse_request (request : Request) (simple : request.Simple) :
    parse (String.ofList request.chars) = .ok request.value := by
  obtain ⟨parts, distinct⟩ := simple
  unfold parse
  rw [String.toList_ofList, String.length_ofList]
  cases request with
  | nil =>
    have read : value (['{', '}'].length + 2) 0 ['{', '}'] = .ok (.object [], []) := by
      show value (3 + 1) 0 ['{', '}'] = _
      unfold value
      simp only [Nat.not_lt.mpr (Nat.zero_le 128), ↓reduceIte, ws_cons '{' _ (by decide),
        ws_cons '}' _ (by decide)]
      rfl
    show (do
      let (v, rest) ← value (['{', '}'].length + 2) 0 ['{', '}']
      unless (ws rest).isEmpty do throw "trailing JSON input"
      return v) = _
    rw [read]
    rfl
  | cons pair more =>
    have sized : Request.chars (pair :: more) =
        '{' :: (joined ((pair :: more).map fun pair => member pair.1 pair.2.chars) ++ ['}']) :=
      rfl
    have read := value_entries ((pair :: more).map fun pair => pair.2.entry pair.1) 0
      ((Request.chars (pair :: more)).length + 1) [] (Nat.zero_le _) (fun wrong => nomatch wrong)
      (fun entry inside => by
        obtain ⟨found, held, rfl⟩ := List.mem_map.mp inside
        exact (parts found held).1)
      (fun entry inside => by
        obtain ⟨found, held, rfl⟩ := List.mem_map.mp inside
        exact part_read found.1 found.2 (parts found held).2 1 (by decide))
      (by
        rw [List.map_map]
        exact (names_back (pair :: more)).symm ▸ distinct)
      (fun entry inside => by
        obtain ⟨found, held, rfl⟩ := List.mem_map.mp inside
        have text := joined_length ((pair :: more).map fun pair => member pair.1 pair.2.chars)
          (member found.1 found.2.chars) (List.mem_map.mpr ⟨found, held, rfl⟩)
        have need := found.2.need_le
        show found.2.need + ((pair :: more).map fun pair => pair.2.entry pair.1).length ≤ _
        rw [sized]
        simp only [List.length_map, List.length_cons, List.length_append, member] at text ⊢
        omega)
    have fielded : ((pair :: more).map fun pair => pair.2.entry pair.1).map Entry.field =
        (pair :: more).map fun pair => (pair.1, pair.2.value) := by
      rw [List.map_map]
      exact List.map_congr_left fun found _ =>
        Prod.ext (String.ofList_toList (s := found.1)) rfl
    rw [fielded, List.map_map] at read
    have whole : value ((Request.chars (pair :: more)).length + 2) 0
        (Request.chars (pair :: more)) = .ok (Request.value (pair :: more), []) := read
    show (do
      let (v, rest) ← value ((Request.chars (pair :: more)).length + 2) 0
        (Request.chars (pair :: more))
      unless (ws rest).isEmpty do throw "trailing JSON input"
      return v) = _
    rw [whole]
    rfl

/-! ## The grammar of a JSON text, and the texts the parser accepts

The grammar of T. Bray (ed.), *The JavaScript Object Notation (JSON) Data Interchange
Format*, RFC 8259, 2017, sections 2 to 7, written as relations between a list of characters
and the value it denotes. The relations name no function of the parser. They keep three
restrictions of the parser, each of which the RFC permits:

* every value is at a depth of nesting of at most 128, the top-level value at depth zero and
  the values of an array or an object one deeper than it (section 9: "An implementation may
  set limits on the maximum depth of nesting");
* the names of an object differ (section 4: "The names within an object SHOULD be unique");
* a `\u` escape of a code point from `D800` to `DFFF` is half of a surrogate pair, a high
  surrogate followed by an escaped low surrogate, and the pair denotes one character beyond
  the Basic Multilingual Plane (section 7). The grammar of section 7 also admits a lone
  surrogate, whose meaning section 8.2 leaves unpredictable; the parser refuses it, because
  the characters of a Lean string are Unicode scalar values.

The text is a list of Unicode scalar values: the host decodes UTF-8 (section 8.1) before
`parse` reads it. A number denotes its spelling (`Value.number`), which section 6 leaves to
the implementation to interpret. `Grammar.Number` states section 6 character by character,
and `Grammar.number_iff` proves that its lists are the spellings (`Numeral.chars`) of the
formed numerals (`Numeral.Formed`), the numerals that the parser's scanner returns.

`parse_sound` states that every text that `parse` accepts is a JSON text of this grammar
(`Grammar.Text`), with the value that `parse` gives as a value that the grammar gives the text.
The proof follows the parser through its readers: the white space, the escapes, the body of
a string, the scanner of a number, the value reader and the loops over the members of an
object and the elements of an array, by induction on the fuel. It does not state that
`parse` accepts every text of the grammar. That the grammar gives each text at most one value
is not proved here; it follows from the completeness theorem tracked in
https://github.com/rbeauchamp/acorn/issues/163. -/

namespace Grammar

/-- White space, `ws` in section 2 of RFC 8259: a space, a horizontal tab, a line feed or a
carriage return. -/
def Space (c : Char) : Prop :=
  c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'

/-- A run of white space, possibly empty. -/
def Blank (cs : List Char) : Prop :=
  ∀ c ∈ cs, Space c

/-- A hexadecimal digit and its value, `HEXDIG` of D. Crocker and P. Overell (eds.), RFC 5234,
2008, appendix B.1, which section 7 of RFC 8259 uses in an escape. The letters are of either
case (RFC 5234, section 2.3): `0` to `9` for the values below ten, and `a` to `f` or `A` to
`F` for ten to fifteen. -/
def HexDigit (c : Char) (d : Nat) : Prop :=
  (d < 10 ∧ c.toNat = 48 + d) ∨ (10 ≤ d ∧ d < 16 ∧ (c.toNat = 87 + d ∨ c.toNat = 55 + d))

/-- Four hexadecimal digits, `4HEXDIG` in section 7, and the number they spell, the most
significant digit first. -/
def Quad (cs : List Char) (n : Nat) : Prop :=
  ∃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃, cs = [c₀, c₁, c₂, c₃] ∧ HexDigit c₀ d₀ ∧ HexDigit c₁ d₁ ∧
    HexDigit c₂ d₂ ∧ HexDigit c₃ d₃ ∧ n = 4096 * d₀ + 256 * d₁ + 16 * d₂ + d₃

/-- One character of a string, `char` in section 7, and the character it denotes. -/
inductive Character : List Char → Char → Prop
  /-- An unescaped character, `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`: every
  character from the space on, except the quotation mark and the reverse solidus. -/
  | plain (c : Char) (visible : 32 ≤ c.toNat) (unquoted : c ≠ '"') (unescaped : c ≠ '\\') :
      Character [c] c
  /-- The escaped quotation mark. -/
  | quote : Character ['\\', '"'] '"'
  /-- The escaped reverse solidus. -/
  | reverseSolidus : Character ['\\', '\\'] '\\'
  /-- The escaped solidus. -/
  | solidus : Character ['\\', '/'] '/'
  /-- The escaped backspace, `U+0008`. -/
  | backspace : Character ['\\', 'b'] '\x08'
  /-- The escaped form feed, `U+000C`. -/
  | formFeed : Character ['\\', 'f'] '\x0c'
  /-- The escaped line feed, `U+000A`. -/
  | lineFeed : Character ['\\', 'n'] '\n'
  /-- The escaped carriage return, `U+000D`. -/
  | carriageReturn : Character ['\\', 'r'] '\r'
  /-- The escaped horizontal tab, `U+0009`. -/
  | tab : Character ['\\', 't'] '\t'
  /-- A `\u` escape of a code point of the Basic Multilingual Plane that is no surrogate, and
  the character with that code point. -/
  | unit (digits : List Char) (n : Nat) (c : Char) (spelled : Quad digits n)
      (scalar : n < 0xd800 ∨ 0xdfff < n) (code : c.toNat = n) :
      Character ('\\' :: 'u' :: digits) c
  /-- Two `\u` escapes of a surrogate pair, a high surrogate and a low surrogate, and the
  character beyond the Basic Multilingual Plane that the pair encodes in UTF-16. -/
  | pair (high low : List Char) (h l : Nat) (c : Char) (first : Quad high h)
      (second : Quad low l) (leading : 0xd800 ≤ h ∧ h ≤ 0xdbff)
      (trailing : 0xdc00 ≤ l ∧ l ≤ 0xdfff)
      (code : c.toNat = 0x10000 + (h - 0xd800) * 0x400 + (l - 0xdc00)) :
      Character ('\\' :: 'u' :: (high ++ '\\' :: 'u' :: low)) c

/-- The characters of a string between its quotation marks, `*char` in section 7, and the
characters they denote. -/
inductive Characters : List Char → List Char → Prop
  /-- No character. -/
  | nil : Characters [] []
  /-- One character, then the others. -/
  | cons {cs rest : List Char} {c : Char} {decoded : List Char} (spelled : Character cs c)
      (more : Characters rest decoded) : Characters (cs ++ rest) (c :: decoded)

/-- A string, `string = quotation-mark *char quotation-mark` in section 7, and the string
it denotes. -/
def Quoted (cs : List Char) (s : String) : Prop :=
  ∃ body decoded, Characters body decoded ∧ cs = '"' :: (body ++ ['"']) ∧
    s = String.ofList decoded

/-- A decimal digit, `DIGIT = %x30-39` of RFC 5234, appendix B.1, which section 6 uses: a
character from `0` to `9`, by its code. -/
def Digit (c : Char) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- The integer part of a number, `int = zero / ( digit1-9 *DIGIT )` in section 6: a single
zero, or a digit other than zero (`digit1-9 = %x31-39`) followed by digits. -/
def IntegerPart (cs : List Char) : Prop :=
  cs = ['0'] ∨
    ∃ first more, cs = first :: more ∧ Digit first ∧ first ≠ '0' ∧ ∀ c ∈ more, Digit c

/-- The fraction part of a number, `frac = decimal-point 1*DIGIT` in section 6: a point and
at least one digit. -/
def FractionPart (cs : List Char) : Prop :=
  ∃ digits, cs = '.' :: digits ∧ digits ≠ [] ∧ ∀ c ∈ digits, Digit c

/-- The exponent part of a number, `exp = e [ minus / plus ] 1*DIGIT` with `e = %x65 / %x45`
in section 6: a mark `e` or `E`, an optional sign and at least one digit. -/
def ExponentPart (cs : List Char) : Prop :=
  ∃ mark sign digits, (mark = 'e' ∨ mark = 'E') ∧ (sign = [] ∨ sign = ['-'] ∨ sign = ['+']) ∧
    digits ≠ [] ∧ (∀ c ∈ digits, Digit c) ∧ cs = mark :: (sign ++ digits)

/-- A number, `number = [ minus ] int [ frac ] [ exp ]` in section 6: an optional minus
sign, the integer part, an optional fraction part and an optional exponent part. -/
def Number (cs : List Char) : Prop :=
  ∃ minus int frac exp, (minus = [] ∨ minus = ['-']) ∧ IntegerPart int ∧
    (frac = [] ∨ FractionPart frac) ∧ (exp = [] ∨ ExponentPart exp) ∧
    cs = minus ++ int ++ frac ++ exp

mutual

/-- A value of section 3 at a depth of nesting, and the value it denotes. It has no white
space around it. -/
inductive Value : Nat → List Char → Json.Value → Prop
  /-- The literal `null`. -/
  | null {depth : Nat} (within : depth ≤ 128) : Value depth ['n', 'u', 'l', 'l'] .null
  /-- The literal `true`. -/
  | truth {depth : Nat} (within : depth ≤ 128) : Value depth ['t', 'r', 'u', 'e'] (.bool true)
  /-- The literal `false`. -/
  | falsity {depth : Nat} (within : depth ≤ 128) :
      Value depth ['f', 'a', 'l', 's', 'e'] (.bool false)
  /-- A number of section 6, which denotes its spelling. -/
  | number {depth : Nat} {cs : List Char} (within : depth ≤ 128) (spelled : Number cs) :
      Value depth cs (.number (String.ofList cs))
  /-- A string of section 7. -/
  | string {depth : Nat} {cs : List Char} {s : String} (within : depth ≤ 128)
      (quoted : Quoted cs s) : Value depth cs (.string s)
  /-- An array of section 5 with no element: brackets with white space between them. -/
  | emptyArray {depth : Nat} {inside : List Char} (within : depth ≤ 128) (blank : Blank inside) :
      Value depth ('[' :: (inside ++ [']'])) (.array [])
  /-- An array of section 5 with elements, one level deeper. -/
  | array {depth : Nat} {inside : List Char} {values : List Json.Value} (within : depth ≤ 128)
      (items : Elements (depth + 1) inside values) :
      Value depth ('[' :: (inside ++ [']'])) (.array values)
  /-- An object of section 4 with no member: braces with white space between them. -/
  | emptyObject {depth : Nat} {inside : List Char} (within : depth ≤ 128) (blank : Blank inside) :
      Value depth ('{' :: (inside ++ ['}'])) (.object [])
  /-- An object of section 4 with members, one level deeper, whose names differ. -/
  | object {depth : Nat} {inside : List Char} {fields : List (String × Json.Value)}
      (within : depth ≤ 128) (members : Members (depth + 1) inside fields)
      (distinct : (fields.map Prod.fst).Nodup) :
      Value depth ('{' :: (inside ++ ['}'])) (.object fields)

/-- The elements of an array between its brackets, `value *( value-separator value )` in
section 5, each with the white space around it, and the values they denote in order. -/
inductive Elements : Nat → List Char → List Json.Value → Prop
  /-- The last element. -/
  | last {depth : Nat} {before cs after : List Char} {v : Json.Value} (leading : Blank before)
      (item : Value depth cs v) (trailing : Blank after) :
      Elements depth (before ++ cs ++ after) [v]
  /-- An element, a comma, and the elements after it. -/
  | cons {depth : Nat} {before cs after more : List Char} {v : Json.Value}
      {values : List Json.Value} (leading : Blank before) (item : Value depth cs v)
      (trailing : Blank after) (rest : Elements depth more values) :
      Elements depth (before ++ cs ++ after ++ ',' :: more) (v :: values)

/-- The members of an object between its braces, `member *( value-separator member )` in
section 4, with `member = string name-separator value` and the white space around each
part, and the names and values they denote in order. -/
inductive Members : Nat → List Char → List (String × Json.Value) → Prop
  /-- The last member. -/
  | last {depth : Nat} {before name between colon cs after : List Char} {key : String}
      {v : Json.Value} (leading : Blank before) (named : Quoted name key) (spaced : Blank between)
      (separated : Blank colon) (item : Value depth cs v) (trailing : Blank after) :
      Members depth (before ++ name ++ between ++ ':' :: (colon ++ cs ++ after)) [(key, v)]
  /-- A member, a comma, and the members after it. -/
  | cons {depth : Nat} {before name between colon cs after more : List Char} {key : String}
      {v : Json.Value} {fields : List (String × Json.Value)} (leading : Blank before)
      (named : Quoted name key) (spaced : Blank between) (separated : Blank colon)
      (item : Value depth cs v) (trailing : Blank after) (rest : Members depth more fields) :
      Members depth
        (before ++ name ++ between ++ ':' :: (colon ++ cs ++ after) ++ ',' :: more)
        ((key, v) :: fields)

end

/-- A JSON text, `JSON-text = ws value ws` in section 2, and the value it denotes: a value
at depth zero with white space before and after it. -/
def Text (cs : List Char) (v : Json.Value) : Prop :=
  ∃ before body after, Blank before ∧ Value 0 body v ∧ Blank after ∧
    cs = before ++ body ++ after

end Grammar

/-- The optional minus sign of the grammar is the sign of a numeral. -/
private theorem Grammar.minus_iff (cs : List Char) :
    (cs = [] ∨ cs = ['-']) ↔ ∃ negative : Bool, (if negative then ['-'] else []) = cs := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  · rintro ⟨negative, rfl⟩
    cases negative
    · exact .inl rfl
    · exact .inr rfl

/-- The integer part of the grammar is the digits before the point of a formed numeral. -/
private theorem Grammar.integerPart_iff (cs : List Char) :
    Grammar.IntegerPart cs ↔
      (cs = ['0'] ∨ (cs ≠ [] ∧ (∀ c ∈ cs, Numeral.Digit c) ∧ cs.head? ≠ some '0')) := by
  constructor
  · rintro (zero | ⟨first, more, rfl, digit, nonzero, digits⟩)
    · exact .inl zero
    · refine .inr ⟨List.cons_ne_nil _ _, ?_, ?_⟩
      · intro c inside
        rcases List.mem_cons.mp inside with same | later
        · subst same
          exact digit
        · exact digits c later
      · intro same
        rw [List.head?_cons, Option.some.injEq] at same
        exact nonzero same
  · rintro (zero | ⟨nonempty, digits, head⟩)
    · exact .inl zero
    · cases cs with
      | nil => exact absurd rfl nonempty
      | cons first more =>
        refine .inr ⟨first, more, rfl, digits first List.mem_cons_self, ?_, ?_⟩
        · intro same
          subst same
          exact head rfl
        · intro c inside
          exact digits c (List.mem_cons_of_mem _ inside)

/-- The optional fraction part of the grammar is the part after the point of a formed
numeral. -/
private theorem Grammar.fractionPart_iff (cs : List Char) :
    (cs = [] ∨ Grammar.FractionPart cs) ↔ ∃ fraction : Option (List Char),
      (∀ digits, fraction = some digits → digits ≠ [] ∧ ∀ c ∈ digits, Numeral.Digit c) ∧
        Numeral.fractionChars fraction = cs := by
  constructor
  · rintro (rfl | ⟨digits, rfl, nonempty, all⟩)
    · exact ⟨none, fun _ absent => (nomatch absent), rfl⟩
    · refine ⟨some digits, fun _ same => ?_, rfl⟩
      cases same
      exact ⟨nonempty, all⟩
  · rintro ⟨_ | digits, formed, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨digits, rfl, formed digits rfl⟩

/-- The optional exponent part of the grammar is the exponent part of a formed numeral. -/
private theorem Grammar.exponentPart_iff (cs : List Char) :
    (cs = [] ∨ Grammar.ExponentPart cs) ↔ ∃ exponent : Option Exponent,
      (∀ e, exponent = some e → e.digits ≠ [] ∧ ∀ c ∈ e.digits, Numeral.Digit c) ∧
        Numeral.exponentChars exponent = cs := by
  constructor
  · rintro (rfl | ⟨mark, sign, digits, marks, signs, nonempty, all, rfl⟩)
    · exact ⟨none, fun _ absent => (nomatch absent), rfl⟩
    · obtain ⟨upper, rfl⟩ : ∃ upper : Bool, (if upper then 'E' else 'e') = mark := by
        rcases marks with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
      obtain ⟨signed, rfl⟩ : ∃ s, Exponent.signChars s = sign := by
        rcases signs with rfl | rfl | rfl
        · exact ⟨none, rfl⟩
        · exact ⟨some true, rfl⟩
        · exact ⟨some false, rfl⟩
      refine ⟨some ⟨upper, signed, digits⟩, fun _ same => ?_, rfl⟩
      cases same
      exact ⟨nonempty, all⟩
  · rintro ⟨_ | ⟨upper, signed, digits⟩, formed, rfl⟩
    · exact .inl rfl
    · obtain ⟨nonempty, all⟩ := formed _ rfl
      refine .inr ⟨if upper then 'E' else 'e', Exponent.signChars signed, digits, ?_, ?_,
        nonempty, all, rfl⟩
      · cases upper
        · exact .inl rfl
        · exact .inr rfl
      · cases signed with
        | none => exact .inl rfl
        | some negative =>
          cases negative
          · exact .inr (.inr rfl)
          · exact .inr (.inl rfl)

/-- The numbers of the grammar are the spellings of the formed numerals: a list of
characters is a number of section 6 exactly when it is `Numeral.chars` of a numeral of
that form. -/
theorem Grammar.number_iff (cs : List Char) :
    Grammar.Number cs ↔ ∃ numeral : Numeral, numeral.Formed ∧ numeral.chars = cs := by
  constructor
  · rintro ⟨minus, int, frac, exp, signed, whole, fraction, exponent, rfl⟩
    obtain ⟨negative, rfl⟩ := (Grammar.minus_iff minus).mp signed
    obtain ⟨point, pointed, rfl⟩ := (Grammar.fractionPart_iff frac).mp fraction
    obtain ⟨power, powered, rfl⟩ := (Grammar.exponentPart_iff exp).mp exponent
    exact ⟨⟨negative, int, point, power⟩,
      ⟨(Grammar.integerPart_iff int).mp whole, pointed, powered⟩, rfl⟩
  · rintro ⟨⟨negative, whole, point, power⟩, ⟨integer, pointed, powered⟩, rfl⟩
    exact ⟨if negative then ['-'] else [], whole, Numeral.fractionChars point,
      Numeral.exponentChars power, (Grammar.minus_iff _).mpr ⟨negative, rfl⟩,
      (Grammar.integerPart_iff whole).mpr integer,
      (Grammar.fractionPart_iff _).mpr ⟨point, pointed, rfl⟩,
      (Grammar.exponentPart_iff _).mpr ⟨power, powered, rfl⟩, rfl⟩

/-- The white space that `ws` drops is white space of the grammar, and it is the head of the
list. -/
private theorem ws_blank (cs : List Char) :
    ∃ before, Grammar.Blank before ∧ cs = before ++ ws cs := by
  refine ⟨cs.takeWhile fun c => c == ' ' || c == '\r' || c == '\n' || c == '\t', ?_,
    (List.takeWhile_append_dropWhile ..).symm⟩
  intro c inside
  have spaced := List.all_eq_true.mp List.all_takeWhile c inside
  simp only [Bool.or_eq_true, beq_iff_eq] at spaced
  rcases spaced with ((same | same) | same) | same <;> subst same <;> unfold Grammar.Space <;>
    simp

/-- A run of white space before another is one run. -/
private theorem Grammar.Blank.append {first second : List Char} (one : Grammar.Blank first)
    (other : Grammar.Blank second) : Grammar.Blank (first ++ second) := by
  intro c inside
  rcases List.mem_append.mp inside with early | late
  · exact one c early
  · exact other c late

/-- `require` accepts exactly a list that starts with the character, and returns the rest. -/
private theorem require_ok {c : Char} {cs rest : List Char} (read : require c cs = .ok rest) :
    cs = c :: rest := by
  cases cs with
  | nil => exact nomatch read
  | cons head tail =>
    by_cases same : head = c
    · subst same
      simp only [require, beq_self_eq_true, ↓reduceIte, Except.ok.injEq] at read
      rw [read]
    · simp only [require, beq_iff_eq, same, ↓reduceIte] at read
      exact nomatch read

/-- A code point that is no surrogate and below `0x110000` is the code point of the character
that `Char.ofNat` gives. -/
private theorem toNat_ofNat_scalar {n : Nat} (scalar : n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dite_eq_left scalar]
  rfl

/-- The value that `quad` gives a character is below 16 only for a hexadecimal digit, and then
it is the value of that digit. -/
private theorem quad_digit (c : Char)
    (below : (if c.isDigit = true then c.toNat - 48
      else if (decide ('a' ≤ c) && decide (c ≤ 'f')) = true then c.toNat - 87
      else if (decide ('A' ≤ c) && decide (c ≤ 'F')) = true then c.toNat - 55 else 16) < 16) :
    Grammar.HexDigit c (if c.isDigit = true then c.toNat - 48
      else if (decide ('a' ≤ c) && decide (c ≤ 'f')) = true then c.toNat - 87
      else if (decide ('A' ≤ c) && decide (c ≤ 'F')) = true then c.toNat - 55 else 16) := by
  unfold Grammar.HexDigit
  split at below
  · rename_i digit
    rw [ite_eq_left digit]
    have range := (Numeral.digit_iff c).mp digit
    unfold Numeral.Digit at range
    left
    omega
  · rename_i digit
    rw [ite_eq_right digit]
    split at below
    · rename_i lower
      rw [ite_eq_left lower]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def] at lower
      have low : 97 ≤ c.toNat := lower.1
      have high : c.toNat ≤ 102 := lower.2
      right
      omega
    · rename_i lower
      rw [ite_eq_right lower]
      split at below
      · rename_i upper
        rw [ite_eq_left upper]
        simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def] at upper
        have low : 65 ≤ c.toNat := upper.1
        have high : c.toNat ≤ 70 := upper.2
        right
        omega
      · exact absurd below (Nat.lt_irrefl 16)

/-- A bind of `Except` that returns a value runs its first part to a value. -/
theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (read : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact nomatch read
  | ok a => exact ⟨a, rfl, read⟩

/-- Four steps of a loop, each of which takes one hexadecimal digit from the head of the list,
read four hexadecimal digits from its head. -/
private theorem quad_steps
    (body : Nat → List Char × Nat → Except String (ForInStep (List Char × Nat)))
    (step : ∀ i cs n r, body i (cs, n) = .ok r →
      ∃ c tail d, cs = c :: tail ∧ Grammar.HexDigit c d ∧ r = .yield (tail, n * 16 + d))
    {cs rest : List Char} {m : Nat}
    (read : (do
      let s ← forIn (List.range' 0 4 1) (cs, 0) body
      pure (s.2, s.1) : Except String (Nat × List Char)) = .ok (m, rest)) :
    ∃ digits, Grammar.Quad digits m ∧ cs = digits ++ rest := by
  simp only [List.range', List.forIn_cons, List.forIn_nil] at read
  obtain ⟨s, looped, returned⟩ := except_bind_ok read
  obtain ⟨r0, h0, k0⟩ := except_bind_ok looped
  obtain ⟨c0, t0, d0, rfl, x0, rfl⟩ := step _ _ _ _ h0
  obtain ⟨r1, h1, k1⟩ := except_bind_ok k0
  obtain ⟨c1, t1, d1, rfl, x1, rfl⟩ := step _ _ _ _ h1
  obtain ⟨r2, h2, k2⟩ := except_bind_ok k1
  obtain ⟨c2, t2, d2, rfl, x2, rfl⟩ := step _ _ _ _ h2
  obtain ⟨r3, h3, k3⟩ := except_bind_ok k2
  obtain ⟨c3, t3, d3, rfl, x3, rfl⟩ := step _ _ _ _ h3
  have last : (t3, (((0 * 16 + d0) * 16 + d1) * 16 + d2) * 16 + d3) = s := Except.ok.inj k3
  subst last
  have both : ((((0 * 16 + d0) * 16 + d1) * 16 + d2) * 16 + d3, t3) = (m, rest) :=
    Except.ok.inj returned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj both
  exact ⟨[c0, c1, c2, c3], ⟨c0, c1, c2, c3, d0, d1, d2, d3, rfl, x0, x1, x2, x3, by omega⟩, rfl⟩

private theorem quad_ok {cs rest : List Char} {n : Nat} (read : quad cs = .ok (n, rest)) :
    ∃ digits, Grammar.Quad digits n ∧ cs = digits ++ rest := by
  simp only [quad, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv] at read
  refine quad_steps _ ?_ read
  intro i cs n r stepped
  cases cs with
  | nil => exact nomatch stepped
  | cons c tail =>
    simp only at stepped
    have digit := quad_digit c
    generalize (if c.isDigit = true then c.toNat - 48
      else if (decide ('a' ≤ c) && decide (c ≤ 'f')) = true then c.toNat - 87
      else if (decide ('A' ≤ c) && decide (c ≤ 'F')) = true then c.toNat - 55 else 16) = d
      at stepped digit
    split at stepped
    · rename_i below
      exact ⟨c, tail, d, rfl, digit below, (Except.ok.inj stepped).symm⟩
    · exact nomatch stepped

/-- Four hexadecimal digits spell a number below `0x10000`. -/
private theorem Grammar.Quad.small {cs : List Char} {n : Nat} (spelled : Grammar.Quad cs n) :
    n < 0x10000 := by
  obtain ⟨_, _, _, _, d₀, d₁, d₂, d₃, -, x₀, x₁, x₂, x₃, rfl⟩ := spelled
  have b₀ : d₀ < 16 := by unfold Grammar.HexDigit at x₀; omega
  have b₁ : d₁ < 16 := by unfold Grammar.HexDigit at x₁; omega
  have b₂ : d₂ < 16 := by unfold Grammar.HexDigit at x₂; omega
  have b₃ : d₃ < 16 := by unfold Grammar.HexDigit at x₃; omega
  omega

/-- What `unicode` reads after `\u` is a `\u` escape of the grammar, and the character it
returns is the character the escape denotes. -/
private theorem unicode_ok {cs rest : List Char} {c : Char} (read : unicode cs = .ok (c, rest)) :
    ∃ escape, Grammar.Character ('\\' :: 'u' :: escape) c ∧ cs = escape ++ rest := by
  unfold unicode at read
  obtain ⟨⟨first, after⟩, quaded, continued⟩ := except_bind_ok read
  obtain ⟨high, spelled, rfl⟩ := quad_ok quaded
  have small := spelled.small
  simp only at continued
  split at continued
  · rename_i leading
    simp only [Bool.and_eq_true, decide_eq_true_eq] at leading
    obtain ⟨marked, more, afterMark⟩ := except_bind_ok continued
    obtain ⟨slashed, backslash, letter⟩ := except_bind_ok more
    have slash := require_ok backslash
    have u := require_ok letter
    subst slash u
    obtain ⟨⟨second, tail⟩, lowQuad, closing⟩ := except_bind_ok afterMark
    obtain ⟨low, lowSpelled, rfl⟩ := quad_ok lowQuad
    have lowSmall := lowSpelled.small
    simp only at closing
    split at closing
    · rename_i trailing
      simp only [Bool.and_eq_true, decide_eq_true_eq] at trailing
      obtain ⟨same, rfl⟩ := Prod.mk.inj (Except.ok.inj closing)
      subst same
      refine ⟨high ++ '\\' :: 'u' :: low,
        .pair high low first second _ spelled lowSpelled leading trailing ?_, by simp⟩
      rw [toNat_ofNat_scalar (by omega)]
      omega
    · exact nomatch closing
  · rename_i leading
    simp only [Bool.and_eq_true, decide_eq_true_eq] at leading
    split at continued
    · exact nomatch continued
    · rename_i lone
      simp only [Bool.and_eq_true, decide_eq_true_eq] at lone
      obtain ⟨same, rfl⟩ := Prod.mk.inj (Except.ok.inj continued)
      subst same
      refine ⟨high, .unit high first _ spelled (by omega) ?_, rfl⟩
      exact toNat_ofNat_scalar (by omega)

/-- Pushing one character and then appending a string appends the string of both. -/
private theorem push_ofList (out : String) (c : Char) (rest : List Char) :
    out.push c ++ String.ofList rest = out ++ String.ofList (c :: rest) := by
  rw [String.push_eq_append, String.ofList_cons, String.append_assoc]

/-- One character of the grammar before characters of the grammar and a closing quotation
mark are characters of the grammar before that mark. -/
private theorem body_cons {escape r rest body decoded : List Char} {d : Char} {out s : String}
    (spelled : Grammar.Character escape d) (chars : Grammar.Characters body decoded)
    (same : r = body ++ '"' :: rest) (value : s = out.push d ++ String.ofList decoded) :
    ∃ body decoded, Grammar.Characters body decoded ∧ escape ++ r = body ++ '"' :: rest ∧
      s = out ++ String.ofList decoded :=
  ⟨escape ++ body, d :: decoded, .cons spelled chars, by rw [same, List.append_assoc],
    by rw [value, push_ofList]⟩

/-- What `stringBody` reads up to a closing quotation mark is the characters of a string of
the grammar, and the string it returns appends the characters they denote. -/
private theorem stringBody_ok (fuel : Nat) {cs rest : List Char} {out s : String}
    (read : stringBody fuel cs out = .ok (s, rest)) :
    ∃ body decoded, Grammar.Characters body decoded ∧ cs = body ++ '"' :: rest ∧
      s = out ++ String.ofList decoded := by
  induction fuel generalizing cs out with
  | zero => exact nomatch read
  | succ fuel hold =>
    unfold stringBody at read
    split at read
    · exact nomatch read
    · obtain ⟨same, rfl⟩ := Prod.mk.inj (Except.ok.inj read)
      exact ⟨[], [], .nil, rfl, by rw [same, String.ofList_nil, String.append_empty]⟩
    · simp only at read
      split at read
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons .quote chars same value
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons .reverseSolidus chars same value
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons .solidus chars same value
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons (d := Char.ofNat 8) .backspace chars same value
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons (d := Char.ofNat 12) .formFeed chars same value
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons .lineFeed chars same value
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons .carriageReturn chars same value
      · obtain ⟨body, decoded, chars, same, value⟩ := hold read
        exact body_cons .tab chars same value
      · obtain ⟨⟨d, after⟩, escaped, next⟩ := except_bind_ok read
        obtain ⟨tail, spelled, rfl⟩ := unicode_ok escaped
        obtain ⟨body, decoded, chars, same, value⟩ := hold next
        exact body_cons spelled chars same value
      · exact nomatch read
    · exact nomatch read
    · rename_i c tail unquoted escapes ends
      split at read
      · exact nomatch read
      · rename_i visible
        obtain ⟨body, decoded, chars, same, value⟩ := hold read
        have unescaped : c ≠ '\\' := by
          intro solidus
          cases tail with
          | nil => exact ends solidus rfl
          | cons next more => exact escapes next more solidus rfl
        exact body_cons (escape := [c]) (.plain c (by omega) unquoted unescaped) chars same value

/-- What `stringValue` reads is a string of the grammar, and it returns the string that the
string of the grammar denotes. -/
private theorem stringValue_ok {cs rest : List Char} {s : String}
    (read : stringValue cs = .ok (s, rest)) :
    ∃ spelled, Grammar.Quoted spelled s ∧ cs = spelled ++ rest := by
  unfold stringValue at read
  obtain ⟨after, opened, body⟩ := except_bind_ok read
  have quoted := require_ok opened
  subst quoted
  obtain ⟨chars, decoded, spelled, rfl, rfl⟩ := stringBody_ok _ body
  exact ⟨'"' :: (chars ++ ['"']), ⟨chars, decoded, spelled, rfl, by rw [String.empty_append]⟩,
    by simp⟩

/-- What `number` reads is the spelling of a formed numeral, and it returns the number with
that spelling. -/
private theorem number_ok {cs rest : List Char} {v : Value} (read : number cs = .ok (v, rest)) :
    ∃ numeral : Numeral, numeral.Formed ∧ v = .number (String.ofList numeral.chars) ∧
      cs = numeral.chars ++ rest := by
  unfold number at read
  split at read
  · rename_i numeral after scanned
    obtain ⟨same, rfl⟩ := Prod.mk.inj (Except.ok.inj read)
    obtain ⟨formed, parts⟩ := Numeral.scan_formed scanned
    exact ⟨numeral, formed, same.symm, parts⟩
  · exact nomatch read

/-- White space before the members of an object is white space of their first member. -/
private theorem Grammar.Members.blank {depth : Nat} {space body : List Char}
    {fields : List (String × Json.Value)} (blank : Grammar.Blank space)
    (members : Grammar.Members depth body fields) :
    Grammar.Members depth (space ++ body) fields := by
  cases members with
  | last leading named spaced separated item trailing =>
    have joined := Grammar.Members.last (blank.append leading) named spaced separated item
      trailing
    simpa only [List.append_assoc, List.cons_append] using joined
  | cons leading named spaced separated item trailing rest =>
    have joined := Grammar.Members.cons (blank.append leading) named spaced separated item
      trailing rest
    simpa only [List.append_assoc, List.cons_append] using joined

/-- White space before the elements of an array is white space of their first element. -/
private theorem Grammar.Elements.blank {depth : Nat} {space body : List Char}
    {values : List Json.Value} (blank : Grammar.Blank space)
    (elements : Grammar.Elements depth body values) :
    Grammar.Elements depth (space ++ body) values := by
  cases elements with
  | last leading item trailing =>
    have joined := Grammar.Elements.last (blank.append leading) item trailing
    simpa only [List.append_assoc] using joined
  | cons leading item trailing rest =>
    have joined := Grammar.Elements.cons (blank.append leading) item trailing rest
    simpa only [List.append_assoc, List.cons_append] using joined

/-- **What the value reader, the member loop and the element loop accept is text of the
grammar.** For every fuel: an accepted value is white space and a value of the grammar at the
depth, with the value read as a value that the grammar gives it; an accepted run of members or elements is the
members or elements of the grammar before the closing brace or bracket, with the names of the
members of an object distinct. -/
private theorem read_sound (fuel : Nat) :
    (∀ depth input v rest, value fuel depth input = .ok (v, rest) →
      ∃ before cs, Grammar.Blank before ∧ Grammar.Value depth cs v ∧
        input = before ++ cs ++ rest) ∧
    (∀ depth cs out v rest, fields fuel depth cs out = .ok (v, rest) →
      (out.map Prod.fst).Nodup →
      ∃ body more, Grammar.Members depth body more ∧ ((out ++ more).map Prod.fst).Nodup ∧
        v = .object (out ++ more) ∧ cs = body ++ '}' :: rest) ∧
    (∀ depth cs out v rest, elements fuel depth cs out = .ok (v, rest) →
      ∃ body more, Grammar.Elements depth body more ∧ v = .array (out ++ more) ∧
        cs = body ++ ']' :: rest) := by
  induction fuel with
  | zero =>
    refine ⟨fun _ _ _ _ read => ?_, fun _ _ _ _ _ read => ?_, fun _ _ _ _ _ read => ?_⟩ <;>
      exact nomatch read
  | succ fuel hold =>
    obtain ⟨valued, fielded, listed⟩ := hold
    refine ⟨fun depth input v rest read => ?_, fun depth cs out v rest read distinct => ?_,
      fun depth cs out v rest read => ?_⟩
    · unfold value at read
      simp only at read
      split at read
      · exact nomatch read
      · rename_i shallow
        have within : depth ≤ 128 := Nat.not_lt.mp shallow
        obtain ⟨before, blank, shape⟩ := ws_blank input
        generalize ws input = cs at read shape
        subst shape
        split at read
        · obtain ⟨⟨s, after⟩, quoting, returned⟩ := except_bind_ok read
          obtain ⟨same, rfl⟩ := Prod.mk.inj (Except.ok.inj returned)
          subst same
          obtain ⟨spelled, quoted, written⟩ := stringValue_ok quoting
          exact ⟨before, spelled, blank, .string within quoted, by rw [written, List.append_assoc]⟩
        · rename_i opened
          obtain ⟨inside, insideBlank, insideShape⟩ := ws_blank opened
          generalize ws opened = cs at read insideShape
          subst insideShape
          split at read
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj read)
            exact ⟨before, '{' :: (inside ++ ['}']), blank, .emptyObject within insideBlank,
              by simp⟩
          · obtain ⟨body, more, members, distinct, rfl, rfl⟩ :=
              fielded _ _ _ _ _ read List.nodup_nil
            exact ⟨before, '{' :: ((inside ++ body) ++ ['}']), blank,
              .object within (members.blank insideBlank) (by simpa using distinct), by simp⟩
        · rename_i opened
          obtain ⟨inside, insideBlank, insideShape⟩ := ws_blank opened
          generalize ws opened = cs at read insideShape
          subst insideShape
          split at read
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj read)
            exact ⟨before, '[' :: (inside ++ [']']), blank, .emptyArray within insideBlank,
              by simp⟩
          · obtain ⟨body, more, items, rfl, rfl⟩ := listed _ _ _ _ _ read
            exact ⟨before, '[' :: ((inside ++ body) ++ [']']), blank,
              .array within (items.blank insideBlank), by simp⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj read)
          exact ⟨before, _, blank, .null within, by simp⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj read)
          exact ⟨before, _, blank, .truth within, by simp⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj read)
          exact ⟨before, _, blank, .falsity within, by simp⟩
        · split at read
          · obtain ⟨numeral, formed, rfl, written⟩ := number_ok read
            exact ⟨before, numeral.chars, blank,
              .number within ((Grammar.number_iff _).mpr ⟨numeral, formed, rfl⟩),
              by rw [written, List.append_assoc]⟩
          · exact nomatch read
        · exact nomatch read
    · unfold fields at read
      obtain ⟨before, blank, shape⟩ := ws_blank cs
      generalize ws cs = opened at read shape
      subst shape
      obtain ⟨⟨key, named⟩, naming, continued⟩ := except_bind_ok read
      obtain ⟨name, quoted, rfl⟩ := stringValue_ok naming
      simp only at continued
      split at continued
      · exact nomatch continued
      · rename_i repeated
        have fresh : key ∉ out.map Prod.fst := by
          intro inside
          obtain ⟨field, held, same⟩ := List.mem_map.mp inside
          exact repeated (List.any_eq_true.mpr
            ⟨field, held, by rw [same]; exact beq_self_eq_true key⟩)
        obtain ⟨afterColon, colon, valuing⟩ := except_bind_ok continued
        obtain ⟨between, betweenBlank, betweenShape⟩ := ws_blank named
        generalize ws named = marked at colon betweenShape
        subst betweenShape
        have colonShape := require_ok colon
        subst colonShape
        obtain ⟨⟨item, afterItem⟩, itemRead, closing⟩ := except_bind_ok valuing
        obtain ⟨colonBlank, itemText, colonBlankIs, itemIs, rfl⟩ :=
          valued _ _ _ _ itemRead
        have extended : ((out ++ [(key, item)]).map Prod.fst).Nodup := by
          rw [List.map_append, List.nodup_append]
          refine ⟨distinct, by simp, fun earlier inside later single same => ?_⟩
          have named : later = key := by simpa using single
          exact fresh (named ▸ same ▸ inside)
        simp only at closing
        obtain ⟨after, afterBlank, afterShape⟩ := ws_blank afterItem
        generalize ws afterItem = ending at closing afterShape
        subst afterShape
        split at closing
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj closing)
          exact ⟨before ++ name ++ between ++ ':' :: (colonBlank ++ itemText ++ after),
            [(key, item)], .last blank quoted betweenBlank colonBlankIs itemIs afterBlank,
            extended, rfl, by simp⟩
        · obtain ⟨body, more, members, nodup, rfl, rfl⟩ := fielded _ _ _ _ _ closing extended
          exact ⟨before ++ name ++ between ++ ':' :: (colonBlank ++ itemText ++ after) ++
              ',' :: body, (key, item) :: more,
            .cons blank quoted betweenBlank colonBlankIs itemIs afterBlank members,
            by simpa using nodup, by simp, by simp⟩
        · exact nomatch closing
    · unfold elements at read
      obtain ⟨⟨item, afterItem⟩, itemRead, closing⟩ := except_bind_ok read
      obtain ⟨before, itemText, blank, itemIs, rfl⟩ := valued _ _ _ _ itemRead
      simp only at closing
      obtain ⟨after, afterBlank, afterShape⟩ := ws_blank afterItem
      generalize ws afterItem = ending at closing afterShape
      subst afterShape
      split at closing
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj closing)
        exact ⟨before ++ itemText ++ after, [item], .last blank itemIs afterBlank, rfl,
          by simp⟩
      · obtain ⟨body, more, items, rfl, rfl⟩ := listed _ _ _ _ _ closing
        exact ⟨before ++ itemText ++ after ++ ',' :: body, item :: more,
          .cons blank itemIs afterBlank items, by simp, by simp⟩
      · exact nomatch closing

/-- **Every text that the parser accepts is a JSON text of the grammar, and the value the
parser gives is a value that the grammar gives the text.** For every text and value: white
space, a value at depth zero, and white space (`Grammar.Text`), with a derivation of the
grammar that gives the value. -/
theorem parse_sound (text : String) (v : Value) (parsed : parse text = .ok v) :
    Grammar.Text text.toList v := by
  unfold parse at parsed
  obtain ⟨⟨found, rest⟩, read, finished⟩ := except_bind_ok parsed
  obtain ⟨before, body, blank, item, shape⟩ := (read_sound _).1 _ _ _ _ read
  obtain ⟨after, afterBlank, afterShape⟩ := ws_blank rest
  simp only at finished
  split at finished
  · rename_i ended
    have same : found = v := Except.ok.inj finished
    subst same
    rw [List.isEmpty_iff] at ended
    rw [ended, List.append_nil] at afterShape
    exact ⟨before, body, after, blank, item, afterBlank, by rw [shape, afterShape]⟩
  · exact nomatch finished

/-! ## The numeral of a natural number -/

/-- The character of each of the ten decimal digits. -/
def Numeral.figure : Fin 10 → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'

/-- Every figure is a decimal digit, and its code less the code of `0` is its number. -/
theorem Numeral.figure_digit :
    ∀ digit : Fin 10, Numeral.Digit (Numeral.figure digit) ∧
      (Numeral.figure digit).toNat - 48 = digit.val := by
  show ∀ digit : Fin 10, (48 ≤ (Numeral.figure digit).toNat ∧
    (Numeral.figure digit).toNat ≤ 57) ∧ (Numeral.figure digit).toNat - 48 = digit.val
  decide

/-- Only the figure of zero is `0`. -/
private theorem Numeral.figure_zero :
    ∀ digit : Fin 10, Numeral.figure digit = '0' → digit.val = 0 := by
  decide

/-- The decimal digits of a natural number, the most significant first, with no leading
zero: one figure below ten, and otherwise the digits of the tenth part followed by the
figure of the rest. -/
def Numeral.digits (natural : Nat) : List Char :=
  if small : natural < 10 then [Numeral.figure ⟨natural, small⟩]
  else Numeral.digits (natural / 10) ++
    [Numeral.figure ⟨natural % 10, Nat.mod_lt natural (by decide)⟩]
termination_by natural
decreasing_by omega

/-- The numeral of a natural number: its decimal digits, with no sign, point or exponent
part. -/
def Numeral.natural (natural : Nat) : Numeral :=
  ⟨false, Numeral.digits natural, none, none⟩

/-- The digits of a natural number are decimal digits, there is at least one, and the first
is `0` only for zero. -/
private theorem Numeral.digits_shape (natural : Nat) :
    (∀ c ∈ Numeral.digits natural, Numeral.Digit c) ∧ Numeral.digits natural ≠ [] ∧
      ((Numeral.digits natural).head? = some '0' → natural = 0) := by
  induction natural using Nat.strongRecOn with
  | ind natural hold =>
    unfold Numeral.digits
    split
    · rename_i small
      refine ⟨fun c inside => ?_, fun wrong => (nomatch wrong), fun first => ?_⟩
      · rw [List.mem_singleton.mp inside]
        exact (Numeral.figure_digit ⟨natural, small⟩).1
      · exact Numeral.figure_zero ⟨natural, small⟩ (Option.some.inj first)
    · rename_i large
      obtain ⟨all, nonempty, leading⟩ := hold (natural / 10) (by omega)
      refine ⟨fun c inside => ?_, fun wrong => ?_, fun first => ?_⟩
      · rcases List.mem_append.mp inside with before | last
        · exact all c before
        · rw [List.mem_singleton.mp last]
          exact (Numeral.figure_digit _).1
      · exact nonempty (List.append_eq_nil_iff.mp wrong).1
      · cases shape : Numeral.digits (natural / 10) with
        | nil => exact absurd shape nonempty
        | cons head tail =>
          rw [shape] at first leading
          have zero := leading first
          omega

/-- **The numeral of a natural number is formed.** For every natural number. -/
theorem Numeral.natural_formed (natural : Nat) : (Numeral.natural natural).Formed := by
  obtain ⟨all, nonempty, leading⟩ := Numeral.digits_shape natural
  refine ⟨?_, fun _ wrong => (nomatch wrong), fun _ wrong => (nomatch wrong)⟩
  by_cases zero : natural = 0
  · subst zero
    exact .inl (by
      show Numeral.digits 0 = ['0']
      unfold Numeral.digits
      rfl)
  · exact .inr ⟨nonempty, all, fun first => zero (leading first)⟩

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
