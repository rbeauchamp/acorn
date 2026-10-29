/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Decimal digits in text

Each unsigned number on an Acorn command line, a flag of the core or an argument of a native
driver alike, is read by `natural`: an optional plus sign, then at least one digit from `0` to
`9`. `read` takes the digits alone, with the same digit rule; it reads the length of a viewer
control request, the resident memory that `ps` reports, the unsigned integers of
`Json.Value.natural`, and the line numbers that the corpus audit reads.
Neither reader accepts white space, a minus sign or a digit separator, and each returns the value
of the digits in positional notation, so leading zeros are allowed.

The numbers of the Microduck's JSON frames (`Host.Microduck.Counted`,
`Host.Microduck.Decimal.read`) are not read here: they are read through the number scanner of
`Acorn.Json`, which follows the number grammar of RFC 8259, section 6, where a leading zero is
refused.

The coordinates of the terrain diagnostic of `world-native`, which the terrain admits over
signed 64-bit integers, are the only signed numbers of an Acorn command line. They are read by
`integer`: an optional minus sign or plus sign, then the digits, with no white space, second sign
or digit separator.

`Spelled`, `Natural` and `Integer` state the three languages and their values with no executed
function. The contracts `digits_read`, `digits_natural` and `digits_integer` in
`Acorn.Decisions` prove that each reader accepts exactly the texts of its language, and
`digits_read_value`, `digits_natural_value` and `digits_integer_value` that it returns their
values.

Lean core's readers of numbers in text, such as `String.toNat?`, accept `_` between two
digits: at the pinned toolchain v4.35.0, `String.isNat_iff` in `Std/Data/String/ToNat.lean`
admits a separator between two digits, and `String.toNat?_eq_some_ofDigitChars` drops it from
the value, so `"4_2".toNat? = some 42`. The readers above therefore do not use them. A Regula
rule that refuses a reference to them is proposed in
https://github.com/rbeauchamp/regula/issues/445.
-/
namespace Acorn.Digits

/-- Decimal digits: at least one character, each a digit from `0` to `9`, read from the left,
each digit moving the value of the digits before it up one place and adding its own value. A
sign, a separator or white space refuses the text. -/
def read (text : String) : Option Nat :=
  match text.toList with
  | [] => none
  | digits@(_ :: _) => digits.foldlM (fun total c =>
      if '0' ≤ c && c ≤ '9' then some (10 * total + (c.toNat - 48)) else none) 0

/-- The unsigned number of a command line: an optional plus sign, then decimal digits
(`read`). -/
def natural (text : String) : Option Nat :=
  match text.toList with
  | '+' :: digits => read (String.ofList digits)
  | _ => read text

/-- A signed integer of a command line: an optional minus sign or plus sign, then decimal digits
(`read`), negated after a minus sign, so `-0` is zero. A second sign refuses the text. -/
def integer (text : String) : Option Int :=
  match text.toList with
  | '-' :: digits => (read (String.ofList digits)).map fun n : Nat => -(n : Int)
  | '+' :: digits => (read (String.ofList digits)).map fun n : Nat => (n : Int)
  | _ => (read text).map fun n : Nat => (n : Int)

/-- The grammar of `natural`, as the usage text of each native driver states it. -/
def usage : String :=
  "A number is the digits 0 to 9 with an optional leading +; no other sign, separator or space."

/-- Decimal digits, stated with no executed function: at least one character, each a digit from
`0` to `9`, and `n` the value of the digits in positional notation, each digit times ten to the
power of its place counted from the right. -/
def Spelled (text : String) (n : Nat) : Prop :=
  text.toList ≠ [] ∧ (∀ c ∈ text.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧
    n = (text.toList.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum

/-- The text of an unsigned number on a command line, stated with no executed function: an
optional plus sign, then at least one digit from `0` to `9`, and `n` the value of the digits in
positional notation, each digit times ten to the power of its place counted from the right.
Leading zeros are allowed; white space, a minus sign and digit separators are not. -/
def Natural (text : String) (n : Nat) : Prop :=
  ∃ sign digits : List Char, (sign = [] ∨ sign = ['+']) ∧ digits ≠ [] ∧
    (∀ c ∈ digits, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧ text.toList = sign ++ digits ∧
    n = (digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum

/-- The text of a signed integer on a command line, stated with no executed function: an
optional minus sign or plus sign, then at least one digit from `0` to `9`, and `z` the value of
the digits in positional notation, each digit times ten to the power of its place counted from
the right, negated after a minus sign. Leading zeros are allowed; white space, a second sign and
digit separators are not. -/
def Integer (text : String) (z : Int) : Prop :=
  ∃ sign digits : List Char, (sign = [] ∨ sign = ['+'] ∨ sign = ['-']) ∧ digits ≠ [] ∧
    (∀ c ∈ digits, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧ text.toList = sign ++ digits ∧
    z = (if sign = ['-'] then -1 else 1) *
      ((digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum : Nat)

end Acorn.Digits
