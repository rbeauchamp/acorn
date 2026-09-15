/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Integer quotient rounding

Nearest-even rounding is stated as an integer-distance contract. The proof
uses quotient/remainder decomposition, not enumeration of machine encodings.
It isolates a reusable obligation for significand narrowing and integer casts.
-/

namespace Acorn.Rounding

/-- Quotient rounded to nearest, choosing the even integer at an exact tie.
Division by zero remains total with the underlying Nat division convention. -/
def nearestEven (numerator denominator : Nat) : Nat :=
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  if denominator < 2 * remainder ∨
      (denominator = 2 * remainder ∧ quotient % 2 = 1) then quotient + 1 else quotient

/-- The rounded multiple lies within half a denominator of the numerator.
Both sides use naturals so no subtraction can silently truncate an error. -/
theorem nearestEven_distance (numerator denominator : Nat) (h : 0 < denominator) :
    2 * numerator ≤ 2 * (nearestEven numerator denominator * denominator) + denominator ∧
      2 * (nearestEven numerator denominator * denominator) ≤ 2 * numerator + denominator := by
  have hdecomp := Nat.div_add_mod' numerator denominator
  have hrem := Nat.mod_lt numerator h
  simp only [nearestEven]
  split
  · rename_i hup
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  · rename_i hdown
    omega

/-- Exact rescaling preserves the nearest-quotient error bound. This connects
integer significand decisions to decoded dyadic values without rounding again. -/
theorem nearestEven_scaled_distance (numerator denominator scale : Nat) (h : 0 < denominator) :
    2 * (numerator * scale) ≤
        2 * (nearestEven numerator denominator * denominator * scale) + denominator * scale ∧
      2 * (nearestEven numerator denominator * denominator * scale) ≤
        2 * (numerator * scale) + denominator * scale := by
  have bounds := nearestEven_distance numerator denominator h
  constructor
  · simpa only [Nat.add_mul, Nat.mul_assoc] using Nat.mul_le_mul_right scale bounds.1
  · simpa only [Nat.add_mul, Nat.mul_assoc] using Nat.mul_le_mul_right scale bounds.2

/-- At a halfway numerator, the executing quotient decision always selects even. -/
theorem nearestEven_tie (numerator denominator : Nat)
    (htie : denominator = 2 * (numerator % denominator)) :
    nearestEven numerator denominator % 2 = 0 := by
  have hmod := Nat.mod_lt (numerator / denominator) (by decide : 0 < 2)
  dsimp only [nearestEven]
  split <;> omega

/-- Exact integer multiples require no rounding and are retained. -/
theorem nearestEven_exact (quotient denominator : Nat) (h : 0 < denominator) :
    nearestEven (quotient * denominator) denominator = quotient := by
  simp [nearestEven, Nat.mul_div_cancel _ h, Nat.ne_of_gt h]

/-- Rounding division by a positive integer cannot increase a natural input.
This closes the machine-word conversion boundary without a wrapping assumption. -/
theorem nearestEven_le_input (numerator denominator : Nat) (h : 0 < denominator) :
    nearestEven numerator denominator ≤ numerator := by
  by_cases hn : numerator = 0
  · simp [nearestEven, hn, Nat.ne_of_gt h]
  by_cases hd : denominator = 1
  · simp [nearestEven, hd, Nat.mod_one]
  have hq : numerator / denominator < numerator := Nat.div_lt_self (by omega) (by omega)
  dsimp only [nearestEven]
  split <;> omega

/-- Nearest rounding chooses either the floor quotient or its successor. -/
theorem nearestEven_bracket (numerator denominator : Nat) :
    numerator / denominator ≤ nearestEven numerator denominator ∧
      nearestEven numerator denominator ≤ numerator / denominator + 1 := by
  dsimp only [nearestEven]
  split <;> omega

/-- A shift beyond the word width puts every word strictly below half a rounding unit. -/
theorem nearestEven_word_large_shift (word : UInt64) (shift : Nat) (large : 64 < shift) :
    nearestEven word.toNat (2 ^ shift) = 0 := by
  have power : 2 ^ 65 ≤ 2 ^ shift := Nat.pow_le_pow_right (by decide) (by omega)
  have width := word.toNat_lt
  have half : 2 * word.toNat < 2 ^ shift := by omega
  have small : word.toNat < 2 ^ shift := by omega
  simp only [nearestEven, Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small]
  have below : ¬ 2 ^ shift < 2 * word.toNat := by omega
  have untied : ¬ 2 ^ shift = 2 * word.toNat := by omega
  simp only [below, untied, false_and, or_self, ↓reduceIte]

/-- Rounded word division compares the remainder with its complement, avoiding
an overflowing doubled remainder. The denominator is positive at admission. -/
def nearestEvenWord (word denominator : UInt64) : UInt64 :=
  let quotient := word / denominator
  let remainder := word % denominator
  let complement := denominator - remainder
  if complement < remainder ∨ (complement = remainder ∧ quotient % 2 = 1)
  then quotient + 1 else quotient

/-- Word quotient rounding implements the unbounded integer specification
for every nonzero denominator, without arithmetic wrap. -/
theorem nearestEvenWord_exact (word denominator : UInt64) (positive : 0 < denominator.toNat) :
    (nearestEvenWord word denominator).toNat = nearestEven word.toNat denominator.toNat := by
  have rem := Nat.mod_lt word.toNat positive
  have complement : (denominator - word % denominator).toNat =
      denominator.toNat - word.toNat % denominator.toNat := by
    rw [UInt64.toNat_sub_of_le]
    · simp
    · change word.toNat % denominator.toNat ≤ denominator.toNat
      omega
  have choice : (denominator - word % denominator < word % denominator ∨
      (denominator - word % denominator = word % denominator ∧ word / denominator % 2 = 1)) ↔
      (denominator.toNat < 2 * (word.toNat % denominator.toNat) ∨
      (denominator.toNat = 2 * (word.toNat % denominator.toNat) ∧
        word.toNat / denominator.toNat % 2 = 1)) := by
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, complement,
      UInt64.toNat_mod, UInt64.toNat_div, UInt64.toNat_ofNat]
    simp only [Nat.reducePow, Nat.reduceMod]
    omega
  dsimp only [nearestEvenWord, nearestEven]
  simp only [choice]
  split
  · rename_i up
    have bound := nearestEven_le_input word.toNat denominator.toNat positive
    simp only [nearestEven, if_pos up] at bound
    rw [UInt64.toNat_add, UInt64.toNat_div]
    change (word.toNat / denominator.toNat + 1) % 2^64 = _
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt bound word.toNat_lt)
  · exact UInt64.toNat_div _ _

/-- Shift-and-mask quotient rounding needs no machine division. Its caller
admits a shift below the word width before constructing the low-bit mask. -/
def nearestEvenShift (word shift : UInt64) : UInt64 :=
  let denominator := (1 : UInt64) <<< shift
  let quotient := word >>> shift
  let remainder := word &&& (denominator - 1)
  let complement := denominator - remainder
  if complement < remainder ∨ (complement = remainder ∧ quotient % 2 = 1)
  then quotient + 1 else quotient

/-- A bounded machine shift constructs the exact positive power of two. -/
theorem shiftDenominator_exact (shift : UInt64) (bounded : shift.toNat < 64) :
    ((1 : UInt64) <<< shift).toNat = 2 ^ shift.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt bounded, Nat.shiftLeft_eq]
  change (1 * 2 ^ shift.toNat) % 2^64 = _
  rw [Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) bounded)]

/-- A bounded right shift is exactly division by the constructed power of two. -/
theorem shiftQuotient_exact (word shift : UInt64) (bounded : shift.toNat < 64) :
    word >>> shift = word / ((1 : UInt64) <<< shift) := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt bounded, Nat.shiftRight_eq_div_pow,
    UInt64.toNat_div, shiftDenominator_exact shift bounded]

/-- A low-bit mask is exactly remainder modulo the constructed power of two. -/
theorem maskRemainder_exact (word shift : UInt64) (bounded : shift.toNat < 64) :
    word &&& (((1 : UInt64) <<< shift) - 1) = word % ((1 : UInt64) <<< shift) := by
  have denominator := shiftDenominator_exact shift bounded
  apply UInt64.toNat.inj
  rw [UInt64.toNat_and, UInt64.toNat_sub_of_le, UInt64.toNat_mod, denominator]
  · change word.toNat &&& (2 ^ shift.toNat - 1) = word.toNat % 2 ^ shift.toNat
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  · change 1 ≤ ((1 : UInt64) <<< shift).toNat
    rw [denominator]
    exact Nat.two_pow_pos _

/-- Binary quotient/remainder decomposition agrees with word division for
all admitted shifts. The rounding decision and carry are shared exactly. -/
theorem nearestEvenShift_eq (word shift : UInt64) (bounded : shift.toNat < 64) :
    nearestEvenShift word shift = nearestEvenWord word ((1 : UInt64) <<< shift) := by
  simp only [nearestEvenShift, nearestEvenWord, shiftQuotient_exact word shift bounded,
    maskRemainder_exact word shift bounded]

/-- Fixed-width shift rounding handles the word-width boundary explicitly;
shifts above 64 cannot reach half a unit, while shift 64 can round to one. -/
def wordShift64 (word shift : UInt64) : UInt64 :=
  if 64 < shift then 0
  else if shift = 64 then if (0x8000000000000000 : UInt64) < word then 1 else 0
  else nearestEvenShift word shift

/-- The fixed-width rounding path agrees with integer nearest-even rounding. -/
theorem wordShift64_exact (word shift : UInt64) :
    (wordShift64 word shift).toNat = nearestEven word.toNat (2 ^ shift.toNat) := by
  unfold wordShift64
  split
  · rename_i large
    exact (nearestEven_word_large_shift word shift.toNat large).symm
  · rename_i small
    split
    · rename_i equal
      subst shift
      have width := word.toNat_lt
      have quotient : word.toNat / 2^64 = 0 := Nat.div_eq_of_lt width
      have remainder : word.toNat % 2^64 = word.toNat := Nat.mod_eq_of_lt width
      change (if (0x8000000000000000 : UInt64) < word then (1 : UInt64) else 0).toNat =
        nearestEven word.toNat (2^64)
      simp only [nearestEven, quotient, remainder]
      split <;> split <;> simp_all only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat] <;> omega
    · rename_i unequal
      have shiftBound : shift.toNat < 64 := by
        change ¬ 64 < shift.toNat at small
        have : shift.toNat ≠ 64 := by intro h; exact unequal (UInt64.toNat.inj h)
        omega
      rw [nearestEvenShift_eq word shift shiftBound,
        nearestEvenWord_exact word _ (by rw [shiftDenominator_exact shift shiftBound]; exact Nat.two_pow_pos _),
        shiftDenominator_exact shift shiftBound]

/-- The general API admits its bounded shift to the fixed-width implementation.
Large natural shifts return zero without constructing a denominator. -/
def wordShift (word : UInt64) (shift : Nat) : UInt64 :=
  if 64 < shift then 0 else wordShift64 word shift.toUInt64

/-- The executing word conversion retains the full rounded quotient exactly. -/
theorem wordShift_exact (word : UInt64) (shift : Nat) :
    (wordShift word shift).toNat = nearestEven word.toNat (2 ^ shift) := by
  unfold wordShift
  split
  · rename_i large
    exact (nearestEven_word_large_shift word shift large).symm
  · rename_i small
    rw [wordShift64_exact]
    have bound : shift < 2^64 := by omega
    rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' bound]

/-- The word-facing and general APIs share the same rounding specification. -/
theorem wordShift64_eq_wordShift (word shift : UInt64) :
    wordShift64 word shift = wordShift word shift.toNat := by
  apply UInt64.toNat.inj
  rw [wordShift64_exact, wordShift_exact]

/-- The actual word-valued significand rounding is within half of one discarded
unit for every source word and shift, including shifts beyond the word width. -/
theorem wordShift_distance (word : UInt64) (shift : Nat) :
    2 * word.toNat ≤ 2 * ((wordShift word shift).toNat * 2 ^ shift) + 2 ^ shift ∧
      2 * ((wordShift word shift).toNat * 2 ^ shift) ≤ 2 * word.toNat + 2 ^ shift := by
  rw [wordShift_exact]
  exact nearestEven_distance _ _ (Nat.two_pow_pos shift)

/-- Rounding a bounded significand can carry at most one bit into the exponent.
This is the guard used by the actual normal-target narrowing path. -/
theorem wordShift_carry_bound (word : UInt64) (kept shift : Nat)
    (h : word.toNat < 2 ^ (kept + shift)) :
    (wordShift word shift).toNat ≤ 2 ^ kept := by
  rw [wordShift_exact]
  have hq : word.toNat / 2 ^ shift < 2 ^ kept := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mpr
    simpa only [Nat.pow_add] using h
  have := (nearestEven_bracket word.toNat (2 ^ shift)).2
  omega

/-- The retained leading bit cannot disappear during normal-significand
rounding; carry normalization is the only possible width change. -/
theorem wordShift_leading_bit (word : UInt64) (kept shift : Nat)
    (h : 2 ^ (kept + shift) ≤ word.toNat) :
    2 ^ kept ≤ (wordShift word shift).toNat := by
  rw [wordShift_exact]
  have hq : 2 ^ kept ≤ word.toNat / 2 ^ shift := by
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos shift)).mpr
    simpa only [Nat.pow_add] using h
  exact Nat.le_trans hq (nearestEven_bracket word.toNat (2 ^ shift)).1

/-- Discarding any number of bits from zero yields exactly zero. -/
theorem wordShift_zero (shift : Nat) : wordShift 0 shift = 0 := by
  apply UInt64.toNat.inj
  rw [wordShift_exact]
  have bound := nearestEven_le_input 0 (2^shift) (Nat.two_pow_pos shift)
  change nearestEven 0 (2^shift) = 0
  omega
end Acorn.Rounding
