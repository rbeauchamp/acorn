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

/-- Ordered magnitude key; equal signed zeros have key zero. -/
def key (x : Binary32) : Int :=
  if x.negative then -(x.magnitude : Int) else x.magnitude

/-- All and only encodings whose magnitude exceeds infinity. -/
def isNaN (x : Binary32) : Bool := (x.bits &&& 0x7fffffff) > (0x7f800000 : UInt32)

/-- Word NaN classification has the same exact magnitude specification. -/
theorem isNaN_eq_magnitude (x : Binary32) : x.isNaN = decide (x.magnitude > 0x7f800000) := rfl

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
  unfold less key negative
  split <;> split <;> simp_all [magnitude, UInt32.lt_iff_toNat_lt]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq]
  have lz : left.bits &&& 0x7fffffff = 0 ↔
      left.bits.toNat &&& 0x7fffffff = 0 := by
    rw [← UInt32.toNat_inj]; rfl
  have rz : right.bits &&& 0x7fffffff = 0 ↔
      right.bits.toNat &&& 0x7fffffff = 0 := by
    rw [← UInt32.toNat_inj]; rfl
  simp only [ne_eq, lz, rz]
  omega


/-- Positive zero's exact stored encoding. -/
def zero : Binary32 := ⟨0⟩

/-- Sign change on raw storage preserves every payload bit. -/
def negate (x : Binary32) : Binary32 := ⟨x.bits ^^^ 0x80000000⟩

/-- Total raw saturation in low-before-high order, even for unordered bounds.
Only a finite ordered interval justifies a range guarantee. -/
def saturate (value lower upper : Binary32) : Binary32 :=
  if value.isNaN || value.less lower then lower
  else if upper.less value then upper
  else value

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
  unfold key
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

/-- Finite binary64 encoding, excluding infinity and every NaN payload. -/
def Finite (x : Binary64) : Prop := x.magnitude < 0x7ff0000000000000

instance (x : Binary64) : Decidable x.Finite :=
  inferInstanceAs (Decidable (x.bits &&& 0x7fffffffffffffff < (0x7ff0000000000000 : UInt64)))

end Binary64
end Acorn
