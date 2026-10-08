/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Payload-preserving machine encodings

Raw words own storage and admission. In particular, they do not pass through
`Float32.ofBits` or `Float.ofBits`, whose logical models canonicalize NaNs.
The order key below orders magnitudes, not real numerical distances. It gives
both zero encodings the same key and reverses magnitude order for negative
encodings. NaNs remain unordered through the separate classification guard.

Native UInt operations, Lean's compiler/runtime and the target machine are
trusted infrastructure. No floating arithmetic or native override is introduced
here. Raw comparison keeps arbitrary bound encodings on the total branch path
without importing a historical evaluator or a second expression language.
-/

namespace Acorn

/-- A raw binary32 encoding, including every NaN payload and both zero signs. -/
structure Binary32 where
  /-- The exact stored word. -/
  bits : UInt32
  deriving DecidableEq, Repr

/-- A raw binary64 encoding; no admission canonicalizes its payload. -/
structure Binary64 where
  /-- The exact stored word. -/
  bits : UInt64
  deriving DecidableEq, Repr

namespace Binary32

/-- Unsigned exponent/significand field, without the sign bit. -/
def magnitude (x : Binary32) : Nat := (x.bits &&& 0x7fffffff).toNat

/-- Sign-bit classification, including negative zero and signed NaNs. -/
def negative (x : Binary32) : Bool := x.bits &&& 0x80000000 != 0

/-- A word with its sign bit set: read as an unsigned number, it is at least `2 ^ 31`.
Negative zero and the NaNs with that bit are such words. -/
def Negative (x : Binary32) : Prop := 2 ^ 31 ≤ x.bits.toNat

/-- The sign test accepts exactly the words with the sign bit set. -/
theorem negative_iff (x : Binary32) : x.negative = true ↔ x.Negative := by
  have bound := x.bits.toNat_lt
  have quotient : (x.bits.toNat &&& 2 ^ 31) / 2 ^ 31 = x.bits.toNat / 2 ^ 31 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos 31), Nat.and_one_is_mod,
      Nat.mod_eq_of_lt (by omega)]
  have remainder : (x.bits.toNat &&& 2 ^ 31) % 2 ^ 31 = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  simp only [negative, Negative, bne_iff_ne, ne_eq, ← UInt32.toNat_inj, UInt32.toNat_and]
  change ¬x.bits.toNat &&& 2 ^ 31 = 0 ↔ _
  constructor
  · intro set
    omega
  · intro high clear
    omega

/-- The sign test decides the sign bit, so a function that decides `Negative` runs that test. -/
instance (x : Binary32) : Decidable x.Negative := decidable_of_iff _ (negative_iff x)

/-- The decision of the sign bit is the verdict of the sign test. -/
theorem decide_negative (x : Binary32) : decide x.Negative = x.negative := by
  simp only [← negative_iff, Bool.decide_eq_true]

/-- Ordered magnitude key; equal signed zeros have key zero. -/
def key (x : Binary32) : Int :=
  if x.Negative then -(x.magnitude : Int) else x.magnitude

/-- The key, with the sign test in the place of the sign bit. -/
theorem key_eq_negative (x : Binary32) :
    x.key = if x.negative then -(x.magnitude : Int) else x.magnitude := by
  unfold key
  simp only [← negative_iff]

/-- All and only encodings whose magnitude exceeds infinity. -/
def isNaN (x : Binary32) : Bool := (x.bits &&& 0x7fffffff) > (0x7f800000 : UInt32)

/-- Word NaN classification has the same exact magnitude specification. -/
theorem isNaN_eq_magnitude (x : Binary32) : x.isNaN = decide (x.magnitude > 0x7f800000) := rfl

/-- The magnitude field has 31 bits. -/
theorem magnitude_lt (x : Binary32) : x.magnitude < 2 ^ 31 := by
  unfold magnitude
  rw [UInt32.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- A NaN encoding: the eight bits of the exponent field are all ones, and the fraction field
of 23 bits is not zero. -/
def IsNaN (x : Binary32) : Prop := x.magnitude / 2 ^ 23 = 255 ∧ x.magnitude % 2 ^ 23 ≠ 0

/-- The NaN test accepts exactly the NaN encodings. -/
theorem isNaN_iff (x : Binary32) : x.isNaN = true ↔ x.IsNaN := by
  have bound := x.magnitude_lt
  rw [isNaN_eq_magnitude, decide_eq_true_iff]
  unfold IsNaN
  constructor
  · intro above
    exact ⟨by omega, by omega⟩
  · intro ⟨exponent, fraction⟩
    omega

/-- The NaN test decides the NaN encodings, so a function that decides `IsNaN` runs that
test. -/
instance (x : Binary32) : Decidable x.IsNaN := decidable_of_iff _ (isNaN_iff x)

/-- Equality against a stored magnitude constant stays in fixed-width storage. -/
def magnitudeEq (x : Binary32) (word : UInt32) : Bool := x.bits &&& 0x7fffffff == word

/-- Word magnitude equality implements its natural-number specification. -/
theorem magnitudeEq_exact (x : Binary32) (word : UInt32) :
    x.magnitudeEq word = (x.magnitude == word.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [magnitudeEq, magnitude, beq_iff_eq, UInt32.toNat_inj]

/-- Finite representation predicate, excluding infinity and every NaN encoding. -/
def Finite (x : Binary32) : Prop := x.magnitude < 0x7f800000

instance (x : Binary32) : Decidable x.Finite :=
  inferInstanceAs (Decidable (x.bits &&& 0x7fffffff < (0x7f800000 : UInt32)))

/-- Strict comparison keeps NaNs unordered without translating their words. -/
def less (left right : Binary32) : Bool :=
  let lm := left.bits &&& 0x7fffffff
  let rm := right.bits &&& 0x7fffffff
  let ln := left.bits &&& 0x80000000 != 0
  let rn := right.bits &&& 0x80000000 != 0
  !left.isNaN && !right.isNaN &&
    (if ln then if rn then rm < lm else lm != 0 || rm != 0
     else if rn then false else lm < rm)

/-- Word comparison agrees with the signed-magnitude specification for every
encoding, including unordered NaNs and the two equal zero encodings. -/
theorem less_eq_key (left right : Binary32) :
    left.less right = (!left.isNaN && !right.isNaN && decide (left.key < right.key)) := by
  have order (a b : Binary32) :
      a.bits &&& 0x7fffffff < b.bits &&& 0x7fffffff ↔ a.magnitude < b.magnitude :=
    UInt32.lt_iff_toNat_lt
  have zero (a : Binary32) : a.bits &&& 0x7fffffff = 0 ↔ a.magnitude = 0 := by
    rw [← UInt32.toNat_inj]
    exact Iff.rfl
  unfold less
  rw [key_eq_negative, key_eq_negative]
  change (!left.isNaN && !right.isNaN &&
    (if left.negative then
      if right.negative then decide (right.bits &&& 0x7fffffff < left.bits &&& 0x7fffffff)
      else (left.bits &&& 0x7fffffff != 0 || right.bits &&& 0x7fffffff != 0)
    else if right.negative then false
    else decide (left.bits &&& 0x7fffffff < right.bits &&& 0x7fffffff))) = _
  congr 1
  cases left.negative <;> cases right.negative <;>
    simp only [↓reduceIte, Bool.false_eq_true] <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, order, zero,
      Bool.false_eq_true, false_iff]
  · constructor <;> intro _ <;> omega
  · intro _
    omega
  · constructor
    · intro _
      omega
    · intro below
      by_cases none : left.magnitude = 0
      · exact .inr (by omega)
      · exact .inl none
  · constructor <;> intro _ <;> omega

/-- Strict numeric order of two words: neither is a NaN, and the signed keys are in strict
order. The two zero encodings have one key, so neither is below the other. -/
def Less (left right : Binary32) : Prop := ¬left.IsNaN ∧ ¬right.IsNaN ∧ left.key < right.key

/-- Strict word comparison accepts exactly the pairs in strict numeric order. -/
theorem less_iff (left right : Binary32) : left.less right = true ↔ left.Less right := by
  rw [less_eq_key]
  simp only [Less, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, ← isNaN_iff,
    Bool.not_eq_true, and_assoc]

/-- Strict word comparison decides the strict numeric order, so a function that decides `Less`
runs that comparison. -/
instance (left right : Binary32) : Decidable (left.Less right) :=
  decidable_of_iff _ (less_iff left right)

/-- Positive zero's exact stored encoding. -/
def zero : Binary32 := ⟨0⟩

/-- Sign change on raw storage preserves every payload bit. -/
def negate (x : Binary32) : Binary32 := ⟨x.bits ^^^ 0x80000000⟩

/-- Total raw saturation in low-before-high order, even for unordered bounds.
Only a finite ordered interval justifies a range guarantee. -/
def saturate (value lower upper : Binary32) : Binary32 :=
  if value.IsNaN then lower
  else if value.Less lower then lower
  else if upper.Less value then upper
  else value

/-- Saturation, with the NaN test and the word comparison in the place of the propositions
that they decide. -/
theorem saturate_eq_less (value lower upper : Binary32) :
    saturate value lower upper =
      if value.isNaN || value.less lower then lower
      else if upper.less value then upper
      else value := by
  unfold saturate
  simp only [← isNaN_iff, ← less_iff]
  cases value.isNaN <;> rfl

/-- Symmetric raw projection; NaNs select positive zero before either bound. -/
def project (value bound : Binary32) : Binary32 :=
  if value.isNaN then zero
  else if bound.less value then bound
  else if value.less bound.negate then bound.negate
  else value

/-- Nonnegative raw projection, preserving the source's negative-zero identity. -/
def projectNonnegative (value bound : Binary32) : Binary32 :=
  if value.isNaN || value.less zero then zero
  else if bound.less value then bound
  else value

/-- Strict positivity of a signed magnitude key needs only sign and zero fields. -/
def keyPositive (x : Binary32) : Bool := !x.negative && x.bits &&& 0x7fffffff != 0

/-- The word positivity predicate is the stored key's exact integer order. -/
theorem keyPositive_exact (x : Binary32) : x.keyPositive = true ↔ 0 < x.key := by
  simp only [keyPositive, Bool.and_eq_true, bne_iff_ne, ne_eq,
    ← UInt32.toNat_inj, UInt32.toNat_zero]
  rw [key_eq_negative]
  cases hn : x.negative <;> simp_all [magnitude] <;> omega

/-- A word decision procedure for positive numerical state. -/
def positiveDecidable (x : Binary32) : Decidable (0 < x.key) :=
  decidable_of_iff (x.keyPositive = true) (keyPositive_exact x)

/-- Finite encodings cannot be classified as NaN. -/
theorem finite_not_nan (x : Binary32) (h : x.Finite) : x.isNaN = false := by
  change decide (x.magnitude > 0x7f800000) = false
  rw [decide_eq_false_iff_not]
  exact Nat.not_lt_of_ge (Nat.le_of_lt h)

/-- Comparison between finite operands is exactly their signed magnitude order. -/
theorem less_finite (x y : Binary32) (hx : x.Finite) (hy : y.Finite) :
    x.less y = decide (x.key < y.key) := by
  simp [less_eq_key, finite_not_nan x hx, finite_not_nan y hy]

end Binary32

namespace Binary64

/-- Raw binary64 magnitude field. -/
def magnitude (x : Binary64) : Nat := (x.bits &&& 0x7fffffffffffffff).toNat

/-- Every binary64 NaN encoding, without payload canonicalization. -/
def isNaN (x : Binary64) : Bool := (x.bits &&& 0x7fffffffffffffff) > (0x7ff0000000000000 : UInt64)

/-- The magnitude field has 63 bits. -/
theorem magnitude_lt (x : Binary64) : x.magnitude < 2 ^ 63 := by
  unfold magnitude
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- A NaN encoding: the eleven bits of the exponent field are all ones, and the fraction field
of 52 bits is not zero. -/
def IsNaN (x : Binary64) : Prop := x.magnitude / 2 ^ 52 = 2047 ∧ x.magnitude % 2 ^ 52 ≠ 0

/-- The NaN test accepts exactly the NaN encodings. -/
theorem isNaN_iff (x : Binary64) : x.isNaN = true ↔ x.IsNaN := by
  have bound := x.magnitude_lt
  have classified : x.isNaN = decide (x.magnitude > 0x7ff0000000000000) := rfl
  rw [classified, decide_eq_true_iff]
  unfold IsNaN
  constructor
  · intro above
    exact ⟨by omega, by omega⟩
  · intro ⟨exponent, fraction⟩
    omega

/-- The NaN test decides the NaN encodings, so a function that decides `IsNaN` runs that
test. -/
instance (x : Binary64) : Decidable x.IsNaN := decidable_of_iff _ (isNaN_iff x)

/-- Finite binary64 encoding, excluding infinity and every NaN payload. -/
def Finite (x : Binary64) : Prop := x.magnitude < 0x7ff0000000000000

instance (x : Binary64) : Decidable x.Finite :=
  inferInstanceAs (Decidable (x.bits &&& 0x7fffffffffffffff < (0x7ff0000000000000 : UInt64)))

end Binary64
end Acorn
