/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Microduck.Wire
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# What the conversion of a decimal computes

`Acorn.Host.Microduck.Decimal.fixed` converts a decimal number to an integer of a
declared scale by integer arithmetic. This module states what it computes without that
arithmetic, over the rational numbers.

- `value` is the number a `Decimal` denotes: its digits times ten to its exponent,
  negated for a minus sign. It is defined from the three fields alone.
- `Nearest x n` says that the integer `n` is nearest to the rational `x`, and that at a
  tie it is the one farther from zero: `n` is within one half of `x`, and where it is
  exactly one half away, `x` is nearer to zero than `n`. At most one integer is nearest
  to a rational (`Nearest.unique`).

`rounded_nearest` states that `Decimal.rounded` is nearest to the value times ten to the
`places`, for every decimal and number of places. `fixed_nearest` is the statement of
the conversion: for every scale and decimal, the result is the integer nearest to the
value times ten to the places of the scale, saturated to the bounds of the scale. Its
statement names `value`, `Nearest`, the bounds and the places, and no definition of the
conversion's arithmetic, so a conversion that scaled by another power of ten would not
satisfy it.

The proofs read the two natural-number bounds of the executed division
(`Decimal.magnitude_bounds`) as bounds on a quotient of rationals, and use
`Decimal.fixed_clamp` for the two cases that the conversion decides without the
division.

`written` is the rational number that the parts of a JSON numeral write. It reads a digit
from a table of the ten digits (`digit`) and a run of digits by the place of each
(`numberOf`), so it shares no arithmetic with the reader, which folds the codes of the
characters from the left (`Acorn.Host.Microduck.spelled`). `ofNumeral_value` states that
the decimal the reader builds from a formed numeral has that value, and `read_nearest`
joins it to `fixed_nearest`: the integer kept for a JSON value that is read is the
saturation of the integer nearest to what its spelling writes, in the units of the scale.
Both are for formed numerals only: for a character that is no digit the table gives zero
and the reader's arithmetic on the code can give another number, and no statement is made
about a numeral with such a character.

`kept_nearest`, `counted_numberOf` and `signed_numberOf` state the same of the three
relations on one number that the reader of a frame is specified with, which are written
with the reader's arithmetic. A word that
a scale keeps of a JSON value is the saturation of an integer that is nearest to what the
spelling writes, and `kept_nearest` gives that integer. A natural number counted from a
value is the number that its digits, which are decimal digits alone, write by their
places, and an integer is that number negated after a minus sign.

`spelling_twist` is about what a host writes: each numeral in the line of a velocity
command is formed, and it writes the integer of the action table's magnitude divided by
a thousand, exactly, for each of the four velocities.
-/
namespace AcornVerif.Decimal
open Acorn.Host.Microduck

/-- The rational number a decimal denotes: the digits times ten to the exponent, negated
for a minus sign. -/
def value (decimal : Decimal) : ℚ :=
  (if decimal.negative then -1 else 1) * (decimal.digits : ℚ) * (10 : ℚ) ^ decimal.exponent

/-- The integer is nearest to the rational, and at a tie it is the one farther from zero:
it is within one half, and where it is exactly one half away the rational is nearer to
zero than the integer. -/
def Nearest (target : ℚ) (integer : ℤ) : Prop :=
  |(integer : ℚ) - target| ≤ 1 / 2 ∧
    (|(integer : ℚ) - target| = 1 / 2 → |target| < |(integer : ℚ)|)

/-- Two integers that are both nearest to one rational are not in strict order. -/
theorem Nearest.apart {target : ℚ} {lesser greater : ℤ} (first : Nearest target lesser)
    (second : Nearest target greater) (ordered : lesser < greater) : False := by
  have step : (lesser : ℚ) + 1 ≤ greater := by exact_mod_cast ordered
  obtain ⟨_, above⟩ := abs_le.mp first.1
  obtain ⟨below, _⟩ := abs_le.mp second.1
  obtain ⟨under, _⟩ := abs_le.mp first.1
  obtain ⟨_, over⟩ := abs_le.mp second.1
  have atLesser : (lesser : ℚ) - target = -(1 / 2) := by linarith
  have atGreater : (greater : ℚ) - target = 1 / 2 := by linarith
  have tieLesser : |target| < |(lesser : ℚ)| :=
    first.2 (by rw [atLesser, abs_neg, abs_of_pos (by norm_num)])
  have tieGreater : |target| < |(greater : ℚ)| :=
    second.2 (by rw [atGreater, abs_of_pos (by norm_num)])
  rcases le_or_gt 0 lesser with natural | negative
  · have cast : (0 : ℚ) ≤ lesser := by exact_mod_cast natural
    rw [abs_of_nonneg cast, abs_of_nonneg (by linarith)] at tieLesser
    linarith
  · have cast : (lesser : ℚ) + 1 ≤ 0 := by exact_mod_cast negative
    rw [abs_of_nonpos (by linarith : (greater : ℚ) ≤ 0),
      abs_of_nonpos (by linarith : target ≤ 0)] at tieGreater
    linarith

/-- **At most one integer is nearest to a rational.** -/
theorem Nearest.unique {target : ℚ} {first second : ℤ} (one : Nearest target first)
    (other : Nearest target second) : first = second := by
  rcases lt_trichotomy first second with less | same | more
  · exact (one.apart other less).elim
  · exact same
  · exact (other.apart one more).elim

/-- Ten to an integer is ten to its positive part over ten to its negative part. -/
theorem power_split (shift : ℤ) :
    (10 : ℚ) ^ shift = (10 : ℚ) ^ shift.toNat / (10 : ℚ) ^ (-shift).toNat := by
  rcases le_or_gt 0 shift with whole | part
  · have none : (-shift).toNat = 0 := by omega
    have same : shift = (shift.toNat : ℤ) := (Int.toNat_of_nonneg whole).symm
    rw [none, pow_zero, div_one]
    conv_lhs => rw [same]
    exact zpow_natCast _ _
  · have none : shift.toNat = 0 := by omega
    have same : shift = -((-shift).toNat : ℤ) := by omega
    rw [none, pow_zero, one_div]
    conv_lhs => rw [same]
    rw [zpow_neg, zpow_natCast]

/-- **The rounding is the nearest integer, a tie away from zero.** For every decimal and
number of places, `Decimal.rounded` is nearest to the value of the decimal times ten to
the places. -/
theorem rounded_nearest (decimal : Decimal) (places : ℕ) :
    Nearest (value decimal * (10 : ℚ) ^ places) (decimal.rounded places) := by
  obtain ⟨least, greatest⟩ := decimal.magnitude_bounds places
  have unit : (0 : ℚ) < (10 : ℚ) ^ (-decimal.shift places).toNat := by positivity
  have leastCast : 2 * (decimal.magnitude places : ℚ) * (10 : ℚ) ^ (-decimal.shift places).toNat ≤
      2 * ((decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat) +
        (10 : ℚ) ^ (-decimal.shift places).toNat := by exact_mod_cast least
  have greatestCast : 2 * ((decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat) +
        (10 : ℚ) ^ (-decimal.shift places).toNat <
      2 * ((decimal.magnitude places : ℚ) + 1) * (10 : ℚ) ^ (-decimal.shift places).toNat := by
    exact_mod_cast greatest
  have sum : (10 : ℚ) ^ decimal.exponent * (10 : ℚ) ^ places =
      (10 : ℚ) ^ decimal.shift places := by
    unfold Decimal.shift
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
  have scaled : (decimal.digits : ℚ) * (10 : ℚ) ^ decimal.exponent * (10 : ℚ) ^ places =
      (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
        (10 : ℚ) ^ (-decimal.shift places).toNat := by
    rw [mul_assoc, sum, power_split, mul_div_assoc]
  have lower : (decimal.magnitude places : ℚ) - 1 / 2 ≤
      (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
        (10 : ℚ) ^ (-decimal.shift places).toNat := by
    rw [le_div_iff₀ unit]
    linarith
  have upper : (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
        (10 : ℚ) ^ (-decimal.shift places).toNat <
      (decimal.magnitude places : ℚ) + 1 / 2 := by
    rw [div_lt_iff₀ unit]
    linarith
  have natural : (0 : ℚ) ≤ (decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
      (10 : ℚ) ^ (-decimal.shift places).toNat := by positivity
  have whole : (0 : ℚ) ≤ (decimal.magnitude places : ℚ) := Nat.cast_nonneg _
  unfold Nearest value Decimal.rounded
  cases decimal.negative
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Int.cast_natCast]
    rw [scaled]
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, fun tie => ?_⟩
    rw [abs_of_nonneg natural, abs_of_nonneg whole]
    rcases (abs_eq (by norm_num : (0 : ℚ) ≤ 1 / 2)).mp tie with half | half <;> linarith
  · simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast]
    have flip : -1 * (decimal.digits : ℚ) * (10 : ℚ) ^ decimal.exponent * (10 : ℚ) ^ places =
        -((decimal.digits : ℚ) * (10 : ℚ) ^ (decimal.shift places).toNat /
          (10 : ℚ) ^ (-decimal.shift places).toNat) := by
      rw [← scaled]
      ring
    rw [flip]
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, fun tie => ?_⟩
    rw [abs_neg, abs_neg, abs_of_nonneg natural, abs_of_nonneg whole]
    rcases (abs_eq (by norm_num : (0 : ℚ) ≤ 1 / 2)).mp tie with half | half <;> linarith

/-- **The conversion gives the nearest integer to the value in the units of the scale, a
tie away from zero, saturated to the bounds of the scale.** For every scale, every
decimal with an exponent of any size, and the integer that is nearest to the value of the
decimal times ten to the places of the scale. -/
theorem fixed_nearest (scale : Scale) (decimal : Decimal) (nearest : ℤ)
    (near : Nearest (value decimal * (10 : ℚ) ^ scale.places) nearest) :
    (decimal.fixed scale).val = max scale.low (min scale.high nearest) := by
  rw [Decimal.fixed_clamp, Scale.clamp_value,
    (rounded_nearest decimal scale.places).unique near]

/-- The value of a decimal digit, by a table of the ten digits. Every other character has
the value zero; a formed numeral has no other character. -/
def digit : Char → ℕ
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | '9' => 9
  | _ => 0

/-- The natural number that a run of digits writes, by the place of each digit: a digit
counts its value times ten to the count of the digits after it. -/
def numberOf : List Char → ℕ
  | [] => 0
  | head :: tail => digit head * 10 ^ tail.length + numberOf tail

/-- The exponent that an exponent part writes: the number of its digits, negated after a
minus sign, and zero where there is no exponent part. -/
def exponentOf : Option Acorn.Json.Exponent → ℤ
  | none => 0
  | some ⟨_, some true, digits⟩ => -(numberOf digits : ℤ)
  | some ⟨_, _, digits⟩ => numberOf digits

/-- The rational number that a numeral writes: the digits before the point, plus the
digits after it over ten to their count, times ten to the exponent, negated for a minus
sign. It is stated with `digit`, `numberOf` and `exponentOf` of this module, and with no
definition of the executing library except the fields of a numeral. -/
def written (numeral : Acorn.Json.Numeral) : ℚ :=
  (if numeral.negative then -1 else 1) *
    ((numberOf numeral.whole : ℚ) +
      (numberOf (numeral.fraction.getD []) : ℚ) /
        (10 : ℚ) ^ (numeral.fraction.getD []).length) *
    (10 : ℚ) ^ exponentOf numeral.exponent

/-- The code of a decimal digit, less the code of `0`, is its value in the table. -/
theorem digit_code (c : Char) (decimal : Acorn.Json.Numeral.Digit c) :
    c.toNat - 48 = digit c := by
  obtain ⟨low, high⟩ := decimal
  have same : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
  have code : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨
      c.toNat = 53 ∨ c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
  rcases code with at_ | at_ | at_ | at_ | at_ | at_ | at_ | at_ | at_ | at_ <;>
    (rw [same, at_]; rfl)

/-- **The left fold of the reader and the places of the specification give one number.**
For every run of decimal digits, `spelled` is `numberOf`. -/
theorem spelled_numberOf (digits : List Char)
    (decimal : ∀ c ∈ digits, Acorn.Json.Numeral.Digit c) : spelled digits = numberOf digits := by
  induction digits with
  | nil => rfl
  | cons head tail hold =>
    have first := digit_code head (decimal head List.mem_cons_self)
    have rest := hold fun c inside => decimal c (List.mem_cons_of_mem head inside)
    have moved := spelled_from (10 * 0 + (head.toNat - 48)) tail
    unfold spelled at moved ⊢
    rw [List.foldl_cons, moved]
    unfold spelled at rest
    rw [rest, first, Nat.mul_zero, Nat.zero_add]
    rfl

/-- Every digit before the point of a formed numeral is a decimal digit. -/
theorem formed_whole {numeral : Acorn.Json.Numeral} (formed : numeral.Formed) :
    ∀ c ∈ numeral.whole, Acorn.Json.Numeral.Digit c := by
  rcases formed.whole with zero | ⟨_, decimal, _⟩
  · intro c inside
    rw [zero, List.mem_singleton] at inside
    rw [inside]
    exact ⟨by decide, by decide⟩
  · exact decimal

/-- Every digit after the point of a formed numeral is a decimal digit. -/
theorem formed_fraction {numeral : Acorn.Json.Numeral} (formed : numeral.Formed) :
    ∀ c ∈ numeral.fraction.getD [], Acorn.Json.Numeral.Digit c := by
  cases part : numeral.fraction with
  | none => exact fun _ inside => nomatch inside
  | some digits => exact (formed.fraction digits part).2

/-- **The exponent the reader takes is the exponent the numeral writes.** For every formed
numeral. -/
theorem power_exponentOf {numeral : Acorn.Json.Numeral} (formed : numeral.Formed) :
    power numeral.exponent = exponentOf numeral.exponent := by
  cases part : numeral.exponent with
  | none => rfl
  | some exponent =>
    obtain ⟨upper, sign, digits⟩ := exponent
    have same := spelled_numberOf digits (formed.exponent _ part).2
    unfold power exponentOf
    rcases sign with _ | _ | _ <;> simp [same]

/-- **The decimal of a formed numeral has the value that the numeral writes.** The reader
takes the digits with the point removed, as one number by a left fold on the codes of the
characters, times ten to the exponent lowered by the count of the digits after the point.
For every formed numeral that is the whole part plus the fraction, times ten to the
exponent, each read by the place of its digits. -/
theorem ofNumeral_value (numeral : Acorn.Json.Numeral) (formed : numeral.Formed) :
    value (Decimal.ofNumeral numeral) = written numeral := by
  have positive : (10 : ℚ) ^ (numeral.fraction.getD []).length ≠ 0 := by positivity
  have whole := spelled_numberOf numeral.whole (formed_whole formed)
  have fraction := spelled_numberOf (numeral.fraction.getD []) (formed_fraction formed)
  unfold value written Decimal.ofNumeral
  simp only [spelled_append]
  rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast, power_exponentOf formed, whole,
    fraction]
  push_cast
  field_simp

/-- **The integer kept for a JSON number is the nearest to the number its spelling writes,
in the units of the scale, a tie away from zero, saturated to the bounds of the scale.**
For every scale and every JSON value that the reader gives a decimal for: the value is a
number with the spelling of a formed numeral, and the conversion of the decimal is the
saturation of the integer nearest to what that numeral writes times ten to the places of
the scale. The statement names the spelling, `written`, `Nearest`, the bounds and the
places. -/
theorem read_nearest (scale : Scale) (json : Acorn.Json.Value) (decimal : Decimal)
    (read : Decimal.read json = some decimal) :
    ∃ numeral : Acorn.Json.Numeral, numeral.Formed ∧
      json = .number (String.ofList numeral.chars) ∧
        ∀ nearest : ℤ, Nearest (written numeral * (10 : ℚ) ^ scale.places) nearest →
          (decimal.fixed scale).val = max scale.low (min scale.high nearest) := by
  obtain ⟨numeral, formed, same, rfl⟩ := (Decimal.read_iff json decimal).mp read
  refine ⟨numeral, formed, same, fun nearest near => ?_⟩
  rw [← ofNumeral_value numeral formed] at near
  exact fixed_nearest scale _ nearest near

/-- **A kept word is the nearest to the number the spelling writes, in the units of the
scale, a tie away from zero, saturated to the bounds of the scale.** For every scale,
JSON value and word that the scale keeps of the value: the value is a number with the
spelling of a formed numeral, an integer is nearest to what that numeral writes times ten
to the places of the scale, and the word is the saturation of that integer. At most one
integer is nearest (`Nearest.unique`). -/
theorem kept_nearest (scale : Scale) (json : Acorn.Json.Value) (word : scale.Word)
    (kept : scale.Kept json word) :
    ∃ numeral : Acorn.Json.Numeral, numeral.Formed ∧
      json = .number (String.ofList numeral.chars) ∧
        ∃ nearest : ℤ, Nearest (written numeral * (10 : ℚ) ^ scale.places) nearest ∧
          word.val = max scale.low (min scale.high nearest) := by
  obtain ⟨numeral, formed, same, rfl⟩ := kept
  refine ⟨numeral, formed, same, (Decimal.ofNumeral numeral).rounded scale.places, ?_, ?_⟩
  · rw [← ofNumeral_value numeral formed]
    exact rounded_nearest _ _
  · rw [Decimal.fixed_clamp, Scale.clamp_value]

/-- **A counted number is the number that its digits write by their places.** For every
JSON value and natural number counted from it: the value is a number whose spelling is
decimal digits alone, and those digits write the number. -/
theorem counted_numberOf (json : Acorn.Json.Value) (natural : ℕ)
    (counted : Counted json natural) :
    ∃ digits : List Char, (∀ c ∈ digits, Acorn.Json.Numeral.Digit c) ∧
      json = .number (String.ofList digits) ∧ numberOf digits = natural := by
  obtain ⟨digits, formed, same, rfl⟩ := counted
  exact ⟨digits, formed_whole formed, same,
    (spelled_numberOf digits (formed_whole formed)).symm⟩

/-- **A signed integer is the number that its digits write by their places, negated after
a minus sign.** For every JSON value and integer that it spells: the value is the number
spelled by a sign and decimal digits, with no point and no exponent, and the integer is
the number those digits write, negated when the sign is negative. -/
theorem signed_numberOf (json : Acorn.Json.Value) (integer : ℤ)
    (signed : Signed json integer) :
    ∃ (negative : Bool) (digits : List Char), (∀ c ∈ digits, Acorn.Json.Numeral.Digit c) ∧
      json =
        .number (String.ofList (⟨negative, digits, none, none⟩ : Acorn.Json.Numeral).chars) ∧
        (if negative then -(numberOf digits : ℤ) else numberOf digits) = integer := by
  obtain ⟨negative, digits, formed, same, rfl⟩ := signed
  refine ⟨negative, digits, formed_whole formed, same, ?_⟩
  rw [spelled_numberOf digits (formed_whole formed)]

/-- **Each magnitude of a velocity is written as its thousandths over a thousand.** For
each of the four velocities of the table and each of its three magnitudes: the numeral
that a command's line writes is formed, and the number it writes is the integer of
`Velocity.twist` divided by a thousand. So the line of a velocity asks for exactly the
magnitudes of the table: zero, 0.3 m/s forward, or 1.5 rad/s of turn to one side. Each
numeral is formed because the scanner gives it back from its own spelling
(`Acorn.Json.Numeral.scan_formed`). -/
theorem spelling_twist (velocity : Velocity) :
    (velocity.spelling.forward.Formed ∧
        written velocity.spelling.forward = (velocity.twist.forward : ℚ) / 1000) ∧
      (velocity.spelling.left.Formed ∧
        written velocity.spelling.left = (velocity.twist.left : ℚ) / 1000) ∧
      (velocity.spelling.turn.Formed ∧
        written velocity.spelling.turn = (velocity.twist.turn : ℚ) / 1000) := by
  have formed : ∀ numeral : Acorn.Json.Numeral,
      Acorn.Json.Numeral.scan numeral.chars = some (numeral, []) → numeral.Formed :=
    fun _ scanned => (Acorn.Json.Numeral.scan_formed scanned).1
  cases velocity <;>
    refine ⟨⟨formed _ (by decide), ?_⟩, ⟨formed _ (by decide), ?_⟩,
      ⟨formed _ (by decide), ?_⟩⟩ <;>
    norm_num [written, numberOf, digit, exponentOf, Velocity.spelling, nought,
      Velocity.twist]

end AcornVerif.Decimal
