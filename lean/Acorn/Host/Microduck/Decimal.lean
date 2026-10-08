/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# A decimal number, kept as a bounded integer

The Microduck's control daemon reports a measured quantity as the decimal text of a JSON
number. This module is where such a number becomes an integer of a declared range. It
has two types and one conversion.

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

- **It rounds to zero** when there are no digits, or when the count of the digits plus
  the shift is negative. The digits are less than ten to their count (`width_bound`), so
  the magnitude is then under a tenth of a unit, and the rounded magnitude is zero
  (`Decimal.magnitude_vanishes`).
- **It saturates** when there are digits and the shift is at least the width of the
  scale, which is the count of the digits of its larger bound. The rounded magnitude is
  then at least ten to that width (`Decimal.magnitude_beyond`), which is above both
  bounds (`Scale.width_bound`), and the result is the least value for a decimal with a
  minus sign and the greatest for one without.
- **Between the two** it does the arithmetic, which forms two powers of ten: one that
  multiplies the digits and one that divides. Write `w` for the width of the scale and
  `d` for the count of the digits of the decimal. The exponent of the first is below
  `w`, and the exponent of the second is at most `d` (`Decimal.shift_between`): the
  largest powers are ten to the `w - 1` in the numerator and ten to the `d` in the
  denominator. So what the conversion forms is bounded by the scale and by the length
  of the digits, and not by the size of the exponent. With thousandths in sixteen bits,
  `w` is 5: `1e1` forms ten to the 4, and `1000000000e-13` forms ten to the 10. The cost
  of the conversion is not otherwise stated.

`width` is the count of the decimal digits of a natural number.

**The boundary.** The function that reads the spelling of a number into a `Decimal` is
not built; it belongs with the reader of the daemon's text. The spelling it will read is
the one `Acorn.Json.parse` keeps in `Acorn.Json.Value.number`: an optional minus sign,
digits, an optional point with digits after it, and an optional exponent with an
optional sign and digits. That reader refuses a spelling with no digit after a point or
after an exponent mark, such as `1.` and `1e`. Every spelling it admits has a sign,
digits that are one natural number and an integer exponent, and so has a `Decimal`,
negative zero among them; this conversion is total over them. That the function which
is not built gives the `Decimal` of the spelling is no theorem here.

No theorem compares two decimals by their values, so that the conversion keeps their
order is not stated.
-/
namespace Acorn.Host.Microduck

/-- The count of the decimal digits of a natural number, and one for zero. -/
def width (value : Nat) : Nat :=
  if small : value < 10 then 1 else width (value / 10) + 1
termination_by value
decreasing_by omega

/-- **A natural number is less than ten to the count of its digits.** -/
theorem width_bound (value : Nat) : value < 10 ^ width value := by
  induction value using Nat.strongRecOn with
  | ind value smaller =>
    unfold width
    split
    · rename_i small
      rw [Nat.pow_one]
      exact small
    · have inner := smaller (value / 10) (by omega)
      rw [Nat.pow_succ]
      omega

/-- Every natural number has at least one digit. -/
theorem width_positive (value : Nat) : 0 < width value := by
  unfold width
  split <;> omega

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

/-- The count of the digits of the larger of the two bounds of a scale, by distance
from zero. -/
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

/-- **No digits, or a count of digits below the negated shift, is zero.** For every
decimal and number of places: with no digits, or with the count of the digits plus the
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
rounds to zero by the count of its digits, a bound of the scale when its shift alone
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
decimal that the conversion neither rounds to zero by the count of the digits nor
saturates by the shift: the exponent of the power of ten that multiplies the digits in
`Decimal.magnitude` is below the width of the scale, and the exponent of the power that
divides is at most the count of the digits of the decimal. -/
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

end Acorn.Host.Microduck
