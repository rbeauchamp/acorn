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
states that every number of a parsed text has a numeral: that rests on the parser building
a number in one place, from the spelling of a scanned numeral.
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
