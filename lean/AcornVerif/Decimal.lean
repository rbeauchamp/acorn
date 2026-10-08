/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Microduck.Decimal
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.Order
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

end AcornVerif.Decimal
