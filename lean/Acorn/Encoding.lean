import Init

namespace Acorn

structure Binary32 where
  bits : UInt32
  deriving DecidableEq, Repr

structure Binary64 where
  bits : UInt64
  deriving DecidableEq, Repr

namespace Binary32

def magnitude (x : Binary32) : Nat := (x.bits &&& 0x7fffffff).toNat

def negative (x : Binary32) : Bool := x.bits &&& 0x80000000 != 0

def Negative (x : Binary32) : Prop := 2 ^ 31 ≤ x.bits.toNat

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

instance (x : Binary32) : Decidable x.Negative := decidable_of_iff _ (negative_iff x)

theorem decide_negative (x : Binary32) : decide x.Negative = x.negative := by
  simp only [← negative_iff, Bool.decide_eq_true]

def key (x : Binary32) : Int :=
  if x.Negative then -(x.magnitude : Int) else x.magnitude

theorem key_eq_negative (x : Binary32) :
    x.key = if x.negative then -(x.magnitude : Int) else x.magnitude := by
  unfold key
  simp only [← negative_iff]

def isNaN (x : Binary32) : Bool := (x.bits &&& 0x7fffffff) > (0x7f800000 : UInt32)

theorem isNaN_eq_magnitude (x : Binary32) : x.isNaN = decide (x.magnitude > 0x7f800000) := rfl

theorem magnitude_lt (x : Binary32) : x.magnitude < 2 ^ 31 := by
  unfold magnitude
  rw [UInt32.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

def IsNaN (x : Binary32) : Prop := x.magnitude / 2 ^ 23 = 255 ∧ x.magnitude % 2 ^ 23 ≠ 0

theorem isNaN_iff (x : Binary32) : x.isNaN = true ↔ x.IsNaN := by
  have bound := x.magnitude_lt
  rw [isNaN_eq_magnitude, decide_eq_true_iff]
  unfold IsNaN
  constructor
  · intro above
    exact ⟨by omega, by omega⟩
  · intro ⟨exponent, fraction⟩
    omega

instance (x : Binary32) : Decidable x.IsNaN := decidable_of_iff _ (isNaN_iff x)

def magnitudeEq (x : Binary32) (word : UInt32) : Bool := x.bits &&& 0x7fffffff == word

theorem magnitudeEq_exact (x : Binary32) (word : UInt32) :
    x.magnitudeEq word = (x.magnitude == word.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [magnitudeEq, magnitude, beq_iff_eq, UInt32.toNat_inj]

def Finite (x : Binary32) : Prop := x.magnitude < 0x7f800000

instance (x : Binary32) : Decidable x.Finite :=
  UInt32.decLt (x.bits &&& 0x7fffffff) 0x7f800000

def less (left right : Binary32) : Bool :=
  let lm := left.bits &&& 0x7fffffff
  let rm := right.bits &&& 0x7fffffff
  let ln := left.bits &&& 0x80000000 != 0
  let rn := right.bits &&& 0x80000000 != 0
  !left.isNaN && !right.isNaN &&
    (if ln then if rn then rm < lm else lm != 0 || rm != 0
     else if rn then false else lm < rm)

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

def Less (left right : Binary32) : Prop := ¬left.IsNaN ∧ ¬right.IsNaN ∧ left.key < right.key

theorem less_iff (left right : Binary32) : left.less right = true ↔ left.Less right := by
  rw [less_eq_key]
  simp only [Less, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, ← isNaN_iff,
    Bool.not_eq_true, and_assoc]

instance (left right : Binary32) : Decidable (left.Less right) :=
  decidable_of_iff _ (less_iff left right)

def zero : Binary32 := ⟨0⟩

def negate (x : Binary32) : Binary32 := ⟨x.bits ^^^ 0x80000000⟩

def saturate (value lower upper : Binary32) : Binary32 :=
  if value.IsNaN then lower
  else if value.Less lower then lower
  else if upper.Less value then upper
  else value

theorem saturate_eq_less (value lower upper : Binary32) :
    saturate value lower upper =
      if value.isNaN || value.less lower then lower
      else if upper.less value then upper
      else value := by
  unfold saturate
  simp only [← isNaN_iff, ← less_iff]
  cases value.isNaN <;> rfl

def project (value bound : Binary32) : Binary32 :=
  if value.isNaN then zero
  else if bound.less value then bound
  else if value.less bound.negate then bound.negate
  else value

def projectNonnegative (value bound : Binary32) : Binary32 :=
  if value.isNaN || value.less zero then zero
  else if bound.less value then bound
  else value

def keyPositive (x : Binary32) : Bool := !x.negative && x.bits &&& 0x7fffffff != 0

theorem keyPositive_exact (x : Binary32) : x.keyPositive = true ↔ 0 < x.key := by
  simp only [keyPositive, Bool.and_eq_true, bne_iff_ne, ne_eq,
    ← UInt32.toNat_inj, UInt32.toNat_zero]
  rw [key_eq_negative]
  cases hn : x.negative <;> simp_all [magnitude] <;> omega

def positiveDecidable (x : Binary32) : Decidable (0 < x.key) :=
  decidable_of_iff (x.keyPositive = true) (keyPositive_exact x)

theorem finite_not_nan (x : Binary32) (h : x.Finite) : x.isNaN = false := by
  change decide (x.magnitude > 0x7f800000) = false
  rw [decide_eq_false_iff_not]
  exact Nat.not_lt_of_ge (Nat.le_of_lt h)

theorem less_finite (x y : Binary32) (hx : x.Finite) (hy : y.Finite) :
    x.less y = decide (x.key < y.key) := by
  simp [less_eq_key, finite_not_nan x hx, finite_not_nan y hy]

end Binary32

namespace Binary64

def magnitude (x : Binary64) : Nat := (x.bits &&& 0x7fffffffffffffff).toNat

def isNaN (x : Binary64) : Bool := (x.bits &&& 0x7fffffffffffffff) > (0x7ff0000000000000 : UInt64)

theorem magnitude_lt (x : Binary64) : x.magnitude < 2 ^ 63 := by
  unfold magnitude
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

def IsNaN (x : Binary64) : Prop := x.magnitude / 2 ^ 52 = 2047 ∧ x.magnitude % 2 ^ 52 ≠ 0

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

instance (x : Binary64) : Decidable x.IsNaN := decidable_of_iff _ (isNaN_iff x)

def Finite (x : Binary64) : Prop := x.magnitude < 0x7ff0000000000000

instance (x : Binary64) : Decidable x.Finite :=
  UInt64.decLt (x.bits &&& 0x7fffffffffffffff) 0x7ff0000000000000

end Binary64
end Acorn
