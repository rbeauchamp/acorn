/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Decimal digits in text

Acorn reads every number that text writes in decimal digits here. Each number on a command
line, a flag of the core or an argument of a native driver alike, is read by `natural`: an
optional plus sign, then at least one digit from `0` to `9`. The length of a viewer control
request, the unsigned integers of JSON values and the numbers that the corpus audit reads from
the documents are read by `read`, which takes the digits alone. Neither reader accepts white
space, a minus sign or a digit separator, and each returns the value of the digits in
positional notation, so leading zeros are allowed.

`Spelled` and `Natural` state the two languages and their values with no executed function.
The contracts `digits_read` and `digits_natural` in `Acorn.Decisions` prove that each reader
accepts exactly the texts of its language, and `digits_read_value` and `digits_natural_value`
that it returns their values.

Lean core's readers of numbers in text, such as `String.toNat?`, accept `_` between two
digits: at the pinned toolchain v4.34.1, `String.isNat_iff` in `Std/Data/String/ToNat.lean`
admits a separator between two digits, and `String.toNat?_eq_some_ofDigitChars` drops it from
the value, so `"4_2".toNat? = some 42`. The boundary audit refuses a reference to one of those
readers from every executing module (`AcornBoundaryAudit.coreNumberReader`).
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

end Acorn.Digits
