/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Json

/-!
# A decimal number, kept as a bounded integer

The Microduck's control daemon reports a measured quantity as the decimal text of a JSON
number. This module is where such a number becomes an integer of a declared range. It
has two types, one conversion and one reader of a JSON number.

A `Decimal` is a number as a JSON text spells one: a sign, the digits as one natural
number, and a power of ten. Its value is the digits times ten to the exponent, negated
when the sign says so. Every sign, natural number and integer exponent is a `Decimal`:
the type refuses nothing. No float is involved: the conversion is integer arithmetic on
those three parts.

A `Scale` declares how a field is kept: the number of decimal places, and the least and
the greatest value. A `Scale.Word` is an integer with the proof that it lies between
them, so the bounds of a result are part of its type and no theorem states them.

`Decimal.fixed` is the conversion. What it computes is stated in
`AcornVerif.Decimal`, over the rational value of the decimal and with none of this
module's arithmetic: the result is the integer nearest to the value times ten to the
`places`, at a tie the one farther from zero, saturated to the bounds of the scale
(`AcornVerif.Decimal.fixed_nearest`).

**How it computes.** `Decimal.rounded` is that nearest integer by direct arithmetic,
which raises ten to the size of the exponent, and `Scale.clamp` is the saturation. The
conversion equals the one after the other for every decimal and every scale
(`Decimal.fixed_clamp`), and it runs `Decimal.rounded` only between two comparisons.
Write `shift` for the exponent plus the places. The two comparisons, of integers only,
decide the outer cases:

- **It rounds to zero** when there are no digits, or when the width of the digits plus
  the shift is negative. The digits are less than ten to their width (`width_bound`), so
  the magnitude is then under a tenth of a unit, and the rounded magnitude is zero
  (`Decimal.magnitude_vanishes`).
- **It saturates** when there are digits and the shift is at least the width of the
  scale, which is the width of its larger bound. The rounded magnitude is
  then at least ten to that width (`Decimal.magnitude_beyond`), which is above both
  bounds (`Scale.width_bound`), and the result is the least value for a decimal with a
  minus sign and the greatest for one without.
- **Between the two** it does the arithmetic, which forms two powers of ten: one that
  multiplies the digits and one that divides. Write `w` for the width of the scale and
  `d` for the width of the digits of the decimal. The exponent of the first is below
  `w`, and the exponent of the second is at most `d` (`Decimal.shift_between`): the
  largest powers are ten to the `w - 1` in the numerator and ten to the `d` in the
  denominator. So what the conversion forms is bounded by the scale and by the length
  of the digits, and not by the size of the exponent. With thousandths in sixteen bits,
  `w` is 5: `1e1` forms ten to the 4, and `1000000000e-13` forms ten to the 10. The cost
  of the conversion is not otherwise stated.

`width` is the count of the octal digits of a natural number, and one for zero: one more
than a third of its binary logarithm, rounded down. A number is less than eight to that
count, and so less than ten to it (`width_bound`). The comparisons use it where the count
of the decimal digits would serve, because it is read from the binary length of the
number and divides nothing, and a count of decimal digits divides the number by ten once
for each digit. Ten decimal digits are about eleven octal digits, so `d` is about a tenth
more than the count of the decimal digits.

**Reading a number.** `Decimal.read` gives the decimal of a JSON value. It reads the
spelling that `Acorn.Json.parse` keeps in a number through `Acorn.Json.Value.numeral`,
which is the scanner of that parser and no second reader of numbers, and takes
`Decimal.ofNumeral` of the numeral: the sign, the digits before and after the point as
one natural number (`spelled`), and the exponent lowered by the count of the digits after
the point. A value is read exactly when it is a number with the spelling of a formed
numeral (`Decimal.read_iff`): an optional minus sign, a single zero or digits with no
leading zero, an optional point with at least one digit after it, and an optional
exponent with an optional sign and at least one digit. So `1.` and `1e` have no decimal,
and negative zero has one. The decimal of a formed numeral has the value that the numeral
spells (`AcornVerif.Decimal.ofNumeral_value`), where that value is stated in the proof
library by the place of each digit and with a table of the ten digits, and with neither
`spelled` nor the code of a character. So the integer kept for a value that is read is the
nearest to the number its spelling writes, in the units of the scale, a tie away from
zero, saturated to the bounds of the scale (`AcornVerif.Decimal.read_nearest`).

Three relations state what a reader of a frame keeps of one number, for
`Acorn.Host.Microduck.Wire`. `Scale.Kept` is the word of a scale: the conversion of the
decimal of a formed numeral that spells the value (`AcornVerif.Decimal.kept_nearest`
states it as the nearest integer to what the numeral writes). `Counted` is a natural
number: the value is spelled by digits alone, with no sign, point or exponent, and the
digits spell the number (`AcornVerif.Decimal.counted_numberOf`). `Signed` is an integer:
the value is spelled by digits with an optional minus sign, with no point or exponent,
and the digits with their sign spell the integer (`AcornVerif.Decimal.signed_numberOf`).

No theorem compares two decimals by their values, so that the conversion keeps their
order is not stated.
-/
namespace Acorn.Host.Microduck

/-- The count of the octal digits of a natural number, and one for zero: one more than a
third of its binary logarithm, rounded down. It is read from the binary length of the
number, with no division of the number. -/
def width (value : Nat) : Nat :=
  value.log2 / 3 + 1

/-- **A natural number is less than ten to its width.** It is less than two to its binary
length, which is at most eight to the width. -/
theorem width_bound (value : Nat) : value < 10 ^ width value := by
  have binary : value < 2 ^ (value.log2 + 1) := Nat.lt_log2_self
  have octal : 2 ^ (value.log2 + 1) ≤ (2 ^ 3) ^ width value := by
    rw [← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by unfold width; omega)
  have ten : (2 ^ 3) ^ width value ≤ 10 ^ width value :=
    Nat.pow_le_pow_left (by decide) _
  exact Nat.lt_of_lt_of_le binary (Nat.le_trans octal ten)

/-- The width of every natural number is at least one. -/
theorem width_positive (value : Nat) : 0 < width value := by
  unfold width
  omega

/-- A number as a JSON text spells one. Its value is `digits` times ten to the
`exponent`, negated when `negative`. -/
structure Decimal where
  /-- Whether the text has a minus sign. -/
  negative : Bool
  /-- The digits of the text, with the point removed, as one natural number. -/
  digits : Nat
  /-- The power of ten that the digits are multiplied by. -/
  exponent : Int

/-- How a field is kept as an integer. -/
structure Scale where
  /-- The number of decimal places kept: the unit is ten to the minus `places`. -/
  places : Nat
  /-- The least value. -/
  low : Int
  /-- The greatest value. -/
  high : Int
  /-- The least value is not above the greatest. -/
  ordered : low ≤ high

/-- A value of a scale: an integer between the least and the greatest value. -/
abbrev Scale.Word (scale : Scale) : Type :=
  { value : Int // scale.low ≤ value ∧ value ≤ scale.high }

/-- The width of the larger of the two bounds of a scale, by distance from zero. -/
def Scale.width (scale : Scale) : Nat :=
  Microduck.width (max scale.low.natAbs scale.high.natAbs)

/-- **Both bounds of a scale are within ten to its width of zero.** -/
theorem Scale.width_bound (scale : Scale) :
    scale.low.natAbs < 10 ^ scale.width ∧ scale.high.natAbs < 10 ^ scale.width := by
  have larger := Microduck.width_bound (max scale.low.natAbs scale.high.natAbs)
  have left := Nat.le_max_left scale.low.natAbs scale.high.natAbs
  have right := Nat.le_max_right scale.low.natAbs scale.high.natAbs
  unfold Scale.width
  constructor <;> omega

/-- Saturation: an integer below the scale gives its least value, one above gives its
greatest, and one inside is kept. -/
def Scale.clamp (scale : Scale) (value : Int) : scale.Word :=
  if below : value < scale.low then ⟨scale.low, Int.le_refl _, scale.ordered⟩
  else if above : scale.high < value then ⟨scale.high, scale.ordered, Int.le_refl _⟩
  else ⟨value, Int.not_lt.mp below, Int.not_lt.mp above⟩

/-- **Saturation is the greater of the least value and the lesser of the greatest value
and the integer.** For every scale and integer. -/
theorem Scale.clamp_value (scale : Scale) (value : Int) :
    (scale.clamp value).val = max scale.low (min scale.high value) := by
  have ordered := scale.ordered
  unfold Scale.clamp
  split
  · show scale.low = _
    omega
  · split
    · show scale.high = _
      omega
    · show value = _
      omega

/-- The power of ten that takes a decimal to units of ten to the minus `places`. -/
def Decimal.shift (decimal : Decimal) (places : Nat) : Int :=
  decimal.exponent + places

/-- The magnitude of a decimal in units of ten to the minus `places`, rounded to the
nearest natural number, a tie away from zero. It raises ten to the size of the shift. -/
def Decimal.magnitude (decimal : Decimal) (places : Nat) : Nat :=
  (2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
      10 ^ (-decimal.shift places).toNat) /
    (2 * 10 ^ (-decimal.shift places).toNat)

/-- The two bounds of the division in `Decimal.magnitude`, in natural numbers: twice the
magnitude times the divisor is at most twice the scaled digits plus the divisor, which is
less than twice the next natural number times the divisor. `AcornVerif.Decimal` reads
them as the rounding of the decimal's value. -/
theorem Decimal.magnitude_bounds (decimal : Decimal) (places : Nat) :
    2 * decimal.magnitude places * 10 ^ (-decimal.shift places).toNat ≤
        2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
          10 ^ (-decimal.shift places).toNat ∧
      2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
          10 ^ (-decimal.shift places).toNat <
        2 * (decimal.magnitude places + 1) * 10 ^ (-decimal.shift places).toNat := by
  have unit : 0 < 2 * 10 ^ (-decimal.shift places).toNat :=
    Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have lower := Nat.div_mul_le_self
    (2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
      10 ^ (-decimal.shift places).toNat) (2 * 10 ^ (-decimal.shift places).toNat)
  have upper := Nat.lt_mul_div_succ
    (2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
      10 ^ (-decimal.shift places).toNat) unit
  unfold Decimal.magnitude
  constructor
  · rw [Nat.mul_comm 2, Nat.mul_assoc]
    exact lower
  · rw [Nat.mul_right_comm]
    exact upper

/-- **No digits, or a width of the digits below the negated shift, is zero.** For every
decimal and number of places: with no digits, or with the width of the digits plus the
shift negative, the magnitude is zero. -/
theorem Decimal.magnitude_vanishes (decimal : Decimal) (places : Nat)
    (small : decimal.digits = 0 ∨
      (width decimal.digits : Int) + decimal.shift places < 0) :
    decimal.magnitude places = 0 := by
  have unit : 0 < 10 ^ (-decimal.shift places).toNat := Nat.pow_pos (by decide)
  unfold Decimal.magnitude
  apply Nat.div_eq_of_lt
  rcases small with none | far
  · rw [none]
    omega
  · have count := width_bound decimal.digits
    have whole : (decimal.shift places).toNat = 0 := by omega
    have grows : 10 ^ (width decimal.digits + 1) ≤ 10 ^ (-decimal.shift places).toNat :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at grows
    rw [whole, Nat.pow_zero, Nat.mul_one]
    omega

/-- **Digits and a shift of at least a bound give at least ten to that bound.** For every
decimal with digits, number of places and bound: when the shift is at least the bound,
the magnitude is at least ten to the bound. -/
theorem Decimal.magnitude_beyond (decimal : Decimal) (places bound : Nat)
    (present : decimal.digits ≠ 0) (far : (bound : Int) ≤ decimal.shift places) :
    10 ^ bound ≤ decimal.magnitude places := by
  have none : (-decimal.shift places).toNat = 0 := by omega
  have grows : 10 ^ bound ≤ 10 ^ (decimal.shift places).toNat :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have scaled : 10 ^ (decimal.shift places).toNat ≤
      decimal.digits * 10 ^ (decimal.shift places).toNat :=
    Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero present)
  unfold Decimal.magnitude
  rw [none, Nat.pow_zero, Nat.mul_one]
  omega

/-- A decimal in units of ten to the minus `places`, rounded to the nearest integer, a
tie away from zero: the rounded magnitude with the sign of the decimal. It raises ten to
the size of the shift, and `Decimal.fixed` calls it between its two comparisons only. -/
def Decimal.rounded (decimal : Decimal) (places : Nat) : Int :=
  if decimal.negative then -(decimal.magnitude places : Int) else decimal.magnitude places

/-- The conversion of a decimal to a word of a scale: zero saturated when the decimal
rounds to zero by the width of its digits, a bound of the scale when its shift alone
puts it beyond both, and `Decimal.rounded` saturated between the two. -/
def Decimal.fixed (scale : Scale) (decimal : Decimal) : scale.Word :=
  if decimal.digits = 0 ∨
      (width decimal.digits : Int) + decimal.shift scale.places < 0 then
    scale.clamp 0
  else if (scale.width : Int) ≤ decimal.shift scale.places then
    if decimal.negative then ⟨scale.low, Int.le_refl _, scale.ordered⟩
    else ⟨scale.high, scale.ordered, Int.le_refl _⟩
  else scale.clamp (decimal.rounded scale.places)

/-- **The conversion is the rounding followed by the saturation.** For every scale and
every decimal, with an exponent of any size. -/
theorem Decimal.fixed_clamp (scale : Scale) (decimal : Decimal) :
    decimal.fixed scale = scale.clamp (decimal.rounded scale.places) := by
  have ordered := scale.ordered
  have reach := scale.width_bound
  unfold Decimal.fixed
  split
  · rename_i small
    have zero := decimal.magnitude_vanishes scale.places small
    unfold Decimal.rounded
    rw [zero]
    cases decimal.negative <;> rfl
  · rename_i large
    split
    · rename_i far
      have present : decimal.digits ≠ 0 := fun none => large (Or.inl none)
      have beyond := decimal.magnitude_beyond scale.places scale.width present far
      split
      · rename_i minus
        apply Subtype.ext
        rw [Scale.clamp_value]
        unfold Decimal.rounded
        simp only [minus, ↓reduceIte]
        omega
      · rename_i plus
        apply Subtype.ext
        rw [Scale.clamp_value]
        unfold Decimal.rounded
        simp only [plus, Bool.false_eq_true, ↓reduceIte]
        omega
    · rfl

/-- **Between the two comparisons each power of ten has its bound.** For every scale and
decimal that the conversion neither rounds to zero by the width of the digits nor
saturates by the shift: the exponent of the power of ten that multiplies the digits in
`Decimal.magnitude` is below the width of the scale, and the exponent of the power that
divides is at most the width of the digits of the decimal. -/
theorem Decimal.shift_between (scale : Scale) (decimal : Decimal)
    (large : ¬(decimal.digits = 0 ∨
      (width decimal.digits : Int) + decimal.shift scale.places < 0))
    (near : ¬(scale.width : Int) ≤ decimal.shift scale.places) :
    (decimal.shift scale.places).toNat < scale.width ∧
      (-decimal.shift scale.places).toNat ≤ width decimal.digits := by
  have count : ¬(width decimal.digits : Int) + decimal.shift scale.places < 0 :=
    fun far => large (Or.inr far)
  have some := width_positive (max scale.low.natAbs scale.high.natAbs)
  unfold Scale.width at near ⊢
  constructor <;> omega

/-- The natural number that a run of digits spells: each digit adds its value to ten times
what the digits before it spell. -/
def spelled (digits : List Char) : Nat :=
  digits.foldl (fun total c => 10 * total + (c.toNat - 48)) 0

/-- The digits of a run, read from an earlier total: the total moves up by one place for
each digit. -/
theorem spelled_from (total : Nat) (digits : List Char) :
    digits.foldl (fun total c => 10 * total + (c.toNat - 48)) total =
      total * 10 ^ digits.length + spelled digits := by
  unfold spelled
  induction digits generalizing total with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  | cons head tail hold =>
    have move : total * (10 ^ tail.length * 10) = 10 * total * 10 ^ tail.length := by
      rw [Nat.mul_comm (10 ^ tail.length) 10, ← Nat.mul_assoc, Nat.mul_comm total 10]
    rw [List.foldl_cons, List.foldl_cons, hold (10 * total + (head.toNat - 48)),
      hold (10 * 0 + (head.toNat - 48)), List.length_cons, Nat.pow_succ, move, Nat.mul_zero,
      Nat.zero_add, Nat.add_mul, Nat.add_assoc]

/-- **Two runs of digits one after the other spell the first moved up by the length of the
second, plus the second.** -/
theorem spelled_append (first second : List Char) :
    spelled (first ++ second) = spelled first * 10 ^ second.length + spelled second := by
  unfold spelled
  rw [List.foldl_append]
  exact spelled_from _ second

/-- The exponent that an exponent part spells, and zero without one. -/
def power : Option Json.Exponent → Int
  | none => 0
  | some part =>
    if part.sign = some true then -(spelled part.digits : Int) else spelled part.digits

/-- The decimal of a numeral: its sign, the digits before and after the point as one
natural number, and its exponent lowered by the count of the digits after the point. -/
def Decimal.ofNumeral (numeral : Json.Numeral) : Decimal :=
  ⟨numeral.negative, spelled (numeral.whole ++ numeral.fraction.getD []),
    power numeral.exponent - (numeral.fraction.getD []).length⟩

/-- The decimal of a JSON value: the decimal of its numeral, for a number whose kept
spelling is the whole spelling of a JSON number, and nothing for every other value. -/
def Decimal.read (value : Json.Value) : Option Decimal :=
  value.numeral.map Decimal.ofNumeral

/-- **A value is read as a decimal exactly when it is a number with the spelling of a
formed numeral, and the decimal is that numeral's.** -/
theorem Decimal.read_iff (value : Json.Value) (decimal : Decimal) :
    Decimal.read value = some decimal ↔
      ∃ numeral : Json.Numeral, numeral.Formed ∧
        value = .number (String.ofList numeral.chars) ∧
          Decimal.ofNumeral numeral = decimal := by
  unfold Decimal.read
  constructor
  · intro found
    cases scanned : value.numeral with
    | none =>
      rw [scanned] at found
      exact nomatch found
    | some numeral =>
      rw [scanned] at found
      obtain ⟨formed, same⟩ := (Json.Value.numeral_iff value numeral).mp scanned
      exact ⟨numeral, formed, same, Option.some.inj found⟩
  · rintro ⟨numeral, formed, same, rfl⟩
    rw [(Json.Value.numeral_iff value numeral).mpr ⟨formed, same⟩]
    rfl

/-- The word is what the scale keeps of the value: the value is a number with the spelling
of a formed numeral, and the word is the conversion of that numeral's decimal. -/
def Scale.Kept (scale : Scale) (json : Json.Value) (word : scale.Word) : Prop :=
  ∃ numeral : Json.Numeral, numeral.Formed ∧
    json = .number (String.ofList numeral.chars) ∧
      (Decimal.ofNumeral numeral).fixed scale = word

/-- The value is a number spelled by digits alone, a single zero or digits with no leading
zero, and the digits spell the natural number. -/
def Counted (json : Json.Value) (natural : Nat) : Prop :=
  ∃ digits : List Char, (⟨false, digits, none, none⟩ : Json.Numeral).Formed ∧
    json = .number (String.ofList digits) ∧ spelled digits = natural

/-- The value is a number spelled by digits with an optional minus sign, a single zero or
digits with no leading zero, with no point and no exponent, and the digits with their sign
spell the integer. -/
def Signed (json : Json.Value) (integer : Int) : Prop :=
  ∃ (negative : Bool) (digits : List Char),
    (⟨negative, digits, none, none⟩ : Json.Numeral).Formed ∧
      json = .number (String.ofList (⟨negative, digits, none, none⟩ : Json.Numeral).chars) ∧
        (if negative then -(spelled digits : Int) else spelled digits) = integer

/-- **The decimal digits of a natural number spell it.** For every natural number. -/
theorem spelled_digits (natural : Nat) : spelled (Json.Numeral.digits natural) = natural := by
  have single : ∀ digit : Fin 10, spelled [Json.Numeral.figure digit] = digit.val := fun digit => by
    show 10 * 0 + ((Json.Numeral.figure digit).toNat - 48) = digit.val
    rw [(Json.Numeral.figure_digit digit).2, Nat.mul_zero, Nat.zero_add]
  induction natural using Nat.strongRecOn with
  | ind natural hold =>
    unfold Json.Numeral.digits
    split
    · exact single _
    · rename_i large
      rw [spelled_append, hold (natural / 10) (by omega), single]
      show natural / 10 * 10 ^ 1 + natural % 10 = natural
      omega

/-- **A natural number is counted from its own numeral.** For every natural number: the
JSON number with the spelling of its decimal digits is spelled by digits alone, and they
spell the number. -/
theorem counted_natural (natural : Nat) :
    Counted (.number (String.ofList (Json.Numeral.natural natural).chars)) natural :=
  ⟨Json.Numeral.digits natural, Json.Numeral.natural_formed natural, by
    simp [Json.Numeral.natural, Json.Numeral.chars, Json.Numeral.fractionChars,
      Json.Numeral.exponentChars], spelled_digits natural⟩

end Acorn.Host.Microduck
