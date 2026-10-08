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
when the sign says so. No float is involved: the conversion is integer arithmetic on
those three parts.

A `Scale` declares how a field is kept: the number of decimal places, and the least and
the greatest value. `Decimal.fixed` is the conversion, in two steps.

- **Scaling and rounding** give `Decimal.rounded`, an integer. The magnitude is taken in
  units of ten to the minus `places` and rounded to the nearest natural number, a tie
  away from zero. `Decimal.magnitude_nearest` states that, and `Decimal.magnitude_unique`
  that no other natural number has the property. Where the power of ten that takes the
  decimal to those units is not negative, the magnitude is the digits times that power,
  and nothing is rounded (`Decimal.magnitude_exact`). A magnitude under half a unit gives
  zero (`Decimal.magnitude_zero`), so a residue such as `1e-323` is zero in thousandths.
  The rounded value is the rounded magnitude, negated for a decimal with a minus sign: it
  is not positive for such a decimal, and not negative for a decimal without one
  (`Decimal.rounded_sign`).
- **Saturation** gives the result. A rounded value below the least value of the scale
  gives the least value, one above the greatest gives the greatest, and one between them
  is kept (`Decimal.fixed_below`, `Decimal.fixed_above`, `Decimal.fixed_inside`). The
  result of a scale that does not contain zero can have the other sign than the decimal.

The result is a `Scale.Word`, an integer with the proof that it lies between the least
and the greatest value of its scale. The bounds are part of the type, so no theorem
states them.

**What is bounded.** The exponent of a `Decimal` lies within `Decimal.reach`, 400, of
zero. So of the two powers of ten that a conversion forms, one has an exponent of at
most the reach plus the places of the scale, and the other of at most the reach
(`Decimal.shift_bounded`). The places of a `Scale` and the digits of a `Decimal` are not
bounded by their types.

The reach is a declaration, and this is its reason. Take a text whose digits, from the
first that is not zero to the last, number at most 17, and whose first such digit stands
at a power of ten between -324 and 308. With the point removed its exponent is between
-340 and 308, because removing the point lowers the exponent by at most 16. The finite
binary64 numbers that are not zero have magnitudes from about 4.94 times ten to the -324
to about 1.80 times ten to the 308, which is that range of powers. This is argued here
and not machine-checked. That the daemon writes every number as such a text is an
assumption. The function that reads a text into a `Decimal` is not built; it owes the
refusal of an exponent outside the reach, and a limit on the digits.

No theorem here compares two decimals by their values, so that the conversion keeps
their order is not stated.
-/
namespace Acorn.Host.Microduck

/-- The distance from zero within which the exponent of a `Decimal` lies. -/
def Decimal.reach : Nat := 400

/-- A number as a JSON text spells one. Its value is `digits` times ten to the
`exponent`, negated when `negative`. -/
structure Decimal where
  /-- Whether the text has a minus sign. -/
  negative : Bool
  /-- The digits of the text, with the point removed, as one natural number. -/
  digits : Nat
  /-- The power of ten that the digits are multiplied by. -/
  exponent : Int
  /-- The exponent lies within the reach of zero. -/
  bounded : exponent.natAbs ≤ Decimal.reach

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

/-- The power of ten that takes a decimal to units of ten to the minus `places`. -/
def Decimal.shift (decimal : Decimal) (places : Nat) : Int :=
  decimal.exponent + places

/-- The magnitude of a decimal in units of ten to the minus `places`, rounded to the
nearest natural number, a tie away from zero (`Decimal.magnitude_nearest`). -/
def Decimal.magnitude (decimal : Decimal) (places : Nat) : Nat :=
  (2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
      10 ^ (-decimal.shift places).toNat) /
    (2 * 10 ^ (-decimal.shift places).toNat)

/-- **The powers of ten a conversion forms are bounded by the reach and the places.** For
every decimal and number of places, of the two exponents that `Decimal.magnitude` raises
ten to, one is at most the reach plus the places and the other at most the reach. -/
theorem Decimal.shift_bounded (decimal : Decimal) (places : Nat) :
    (decimal.shift places).toNat ≤ Decimal.reach + places ∧
      (-decimal.shift places).toNat ≤ Decimal.reach := by
  have bounded := decimal.bounded
  unfold Decimal.shift
  constructor <;> omega

/-- **The magnitude is the nearest natural number, a tie away from zero.** For every
decimal and number of places, write `scaled` for the digits times ten to the shift where
the shift is positive, and `unit` for ten to the minus shift where it is negative, so
that the magnitude of the decimal in the units of the scale is `scaled / unit`. Then
twice the rounded magnitude times the unit is at most twice `scaled` plus the unit, which
is less than twice the next natural number times the unit: the rounded magnitude differs
from `scaled / unit` by at most one half, and at exactly one half it is the greater. -/
theorem Decimal.magnitude_nearest (decimal : Decimal) (places : Nat) :
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

/-- **A shift that is not negative rounds nothing.** For every decimal and number of
places whose shift is not negative, the magnitude is the digits times ten to the shift. -/
theorem Decimal.magnitude_exact (decimal : Decimal) (places : Nat)
    (whole : 0 ≤ decimal.shift places) :
    decimal.magnitude places = decimal.digits * 10 ^ (decimal.shift places).toNat := by
  have none : (-decimal.shift places).toNat = 0 := by omega
  unfold Decimal.magnitude
  rw [none, Nat.pow_zero, Nat.mul_one]
  omega

/-- **No other natural number is nearest.** For every decimal and number of places, a
natural number with the two bounds of `Decimal.magnitude_nearest` is the magnitude. -/
theorem Decimal.magnitude_unique (decimal : Decimal) (places value : Nat)
    (least : 2 * value * 10 ^ (-decimal.shift places).toNat ≤
      2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
        10 ^ (-decimal.shift places).toNat)
    (greatest : 2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) +
        10 ^ (-decimal.shift places).toNat <
      2 * (value + 1) * 10 ^ (-decimal.shift places).toNat) :
    decimal.magnitude places = value := by
  rw [Nat.mul_comm 2, Nat.mul_assoc] at least
  rw [Nat.mul_comm 2 (value + 1), Nat.mul_assoc] at greatest
  exact Nat.div_eq_of_lt_le least greatest

/-- **Less than half a unit is zero.** For every decimal and number of places: when twice
the scaled digits are less than the unit, the magnitude is zero. -/
theorem Decimal.magnitude_zero (decimal : Decimal) (places : Nat)
    (small : 2 * (decimal.digits * 10 ^ (decimal.shift places).toNat) <
      10 ^ (-decimal.shift places).toNat) :
    decimal.magnitude places = 0 := by
  unfold Decimal.magnitude
  exact Nat.div_eq_of_lt (by omega)

/-- A decimal in units of ten to the minus `places`, rounded to the nearest integer, a
tie away from zero: the rounded magnitude with the sign of the decimal. -/
def Decimal.rounded (decimal : Decimal) (places : Nat) : Int :=
  if decimal.negative then -(decimal.magnitude places : Int) else decimal.magnitude places

/-- **The rounded value is the rounded magnitude with the sign of the decimal.** Its
distance from zero is the rounded magnitude; it is not positive for a decimal with a
minus sign, and not negative for a decimal without one. It is zero for both when the
magnitude rounds to zero. -/
theorem Decimal.rounded_sign (decimal : Decimal) (places : Nat) :
    (decimal.rounded places).natAbs = decimal.magnitude places ∧
      (decimal.negative = true → decimal.rounded places ≤ 0) ∧
      (decimal.negative = false → 0 ≤ decimal.rounded places) := by
  unfold Decimal.rounded
  cases decimal.negative
  · exact ⟨Int.natAbs_natCast _, fun wrong => absurd wrong Bool.false_ne_true,
      fun _ => Int.natCast_nonneg _⟩
  · exact ⟨(Int.natAbs_neg _).trans (Int.natAbs_natCast _),
      fun _ => Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _),
      fun wrong => absurd wrong.symm Bool.false_ne_true⟩

/-- The conversion of a decimal to a word of a scale: scaled and rounded
(`Decimal.rounded`), then saturated to the bounds of the scale. -/
def Decimal.fixed (scale : Scale) (decimal : Decimal) : scale.Word :=
  if below : decimal.rounded scale.places < scale.low then
    ⟨scale.low, Int.le_refl _, scale.ordered⟩
  else if above : scale.high < decimal.rounded scale.places then
    ⟨scale.high, scale.ordered, Int.le_refl _⟩
  else ⟨decimal.rounded scale.places, Int.not_lt.mp below, Int.not_lt.mp above⟩

/-- **A rounded value below the scale gives its least value.** -/
theorem Decimal.fixed_below (scale : Scale) (decimal : Decimal)
    (below : decimal.rounded scale.places < scale.low) :
    (decimal.fixed scale).val = scale.low := by
  simp only [Decimal.fixed, below, ↓reduceDIte]

/-- **A rounded value above the scale gives its greatest value.** -/
theorem Decimal.fixed_above (scale : Scale) (decimal : Decimal)
    (above : scale.high < decimal.rounded scale.places) :
    (decimal.fixed scale).val = scale.high := by
  have ordered := scale.ordered
  have least : ¬decimal.rounded scale.places < scale.low := by omega
  simp only [Decimal.fixed, least, above, ↓reduceDIte]

/-- **A rounded value inside the scale is kept.** -/
theorem Decimal.fixed_inside (scale : Scale) (decimal : Decimal)
    (least : scale.low ≤ decimal.rounded scale.places)
    (greatest : decimal.rounded scale.places ≤ scale.high) :
    (decimal.fixed scale).val = decimal.rounded scale.places := by
  have least : ¬decimal.rounded scale.places < scale.low := by omega
  have greatest : ¬scale.high < decimal.rounded scale.places := by omega
  simp only [Decimal.fixed, least, greatest, ↓reduceDIte]

end Acorn.Host.Microduck
