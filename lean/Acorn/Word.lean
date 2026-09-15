/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# Executable word operations

Four UInt64 limb products implement the complete high product. The general
128-bit interface is retained as a specification, with a universal bridge.
Proofs account for both carries and every discarded word modulus without
enumerating inputs. Native UInt primitives and compiler/runtime are trusted.
-/

namespace Acorn.Word

/-- Multiplication by a word with a right inverse loses no input information. -/
theorem multiplier_injective (multiplier inverse : UInt64)
    (unit : multiplier * inverse = 1) (left right : UInt64)
    (h : left * multiplier = right * multiplier) : left = right := by
  have hc := congrArg (fun word => word * inverse) h
  simpa only [UInt64.mul_assoc, unit, UInt64.mul_one] using hc

/-- Xor with a fixed word is injective over all machine encodings. -/
theorem xor_word_injective (left right mask : UInt64)
    (h : left ^^^ mask = right ^^^ mask) : left = right := by
  apply UInt64.toBitVec_inj.mp
  have hb := congrArg UInt64.toBitVec h
  exact (BitVec.xor_left_inj mask.toBitVec).mp hb

/-- High word of the full unsigned 128-bit product, with explicit widening. -/
def multiplyHighSpec (left right : UInt64) : UInt64 :=
  UInt64.ofBitVec
    (((left.toBitVec.setWidth 128 * right.toBitVec.setWidth 128) >>> 64).setWidth 64)

/-- The product of two words fits in the declared widened domain. -/
theorem product_fits (left right : UInt64) : left.toNat * right.toNat < 2 ^ 128 := by
  have hl := left.toNat_lt
  have hr := right.toNat_lt
  calc
    left.toNat * right.toNat ≤ left.toNat * 2 ^ 64 :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt hr)
    _ < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right hl (by decide)
    _ = 2 ^ 128 := by decide

/-- The full-product high quotient itself fits in one word. -/
theorem high_fits (left right : UInt64) : left.toNat * right.toNat / 2 ^ 64 < 2 ^ 64 := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < (2 : Nat) ^ 64)).2
  exact product_fits left right

/-- Exact connection from the executing widened-word definition to its quotient. -/
theorem multiplyHighSpec_exact (left right : UInt64) :
    (multiplyHighSpec left right).toNat = left.toNat * right.toNat / 2 ^ 64 := by
  have hl : left.toNat < 2 ^ 128 := Nat.lt_trans left.toNat_lt (by decide)
  have hr : right.toNat < 2 ^ 128 := Nat.lt_trans right.toNat_lt (by decide)
  simp only [multiplyHighSpec, UInt64.toNat_ofBitVec, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_mul, UInt64.toNat_toBitVec,
    Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (product_fits left right),
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (high_fits left right)]

/-- The low 32-bit limb occupies a full word without general arithmetic. -/
def lowLimb (word : UInt64) : UInt64 := word &&& 0xffffffff

/-- The high 32-bit limb is a fixed native shift. -/
def highLimb (word : UInt64) : UInt64 := word >>> 32

/-- Masking is the exact low-limb remainder. -/
theorem lowLimb_exact (word : UInt64) : (lowLimb word).toNat = word.toNat % 2^32 := by
  change word.toNat &&& (2^32 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- Shifting is the exact high-limb quotient. -/
theorem highLimb_exact (word : UInt64) : (highLimb word).toNat = word.toNat / 2^32 := by
  rw [highLimb, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

/-- Four bounded limb products and their low-column carry recover the high word.
Every multiplication and addition is performed in UInt64. -/
def multiplyHigh (left right : UInt64) : UInt64 :=
  let p00 := lowLimb left * lowLimb right
  let p01 := lowLimb left * highLimb right
  let p10 := highLimb left * lowLimb right
  let p11 := highLimb left * highLimb right
  let carry := highLimb p00 + lowLimb p01 + lowLimb p10
  p11 + highLimb p01 + highLimb p10 + highLimb carry

/-- The four-column decomposition is an arithmetic identity, including both carries. -/
theorem limb_high_identity (a0 a1 b0 b1 : Nat) :
    ((a0 + 2^32*a1)*(b0 + 2^32*b1)) / 2^64 =
      a1*b1 + (a0*b1)/2^32 + (a1*b0)/2^32 +
        ((a0*b0)/2^32 + (a0*b1)%2^32 + (a1*b0)%2^32)/2^32 := by
  have expanded : (a0 + 2^32*a1)*(b0 + 2^32*b1) =
      a0*b0 + 2^32*(a0*b1) + 2^32*(a1*b0) + 2^64*(a1*b1) := by
    change (a0 + 2^32*a1)*(b0 + 2^32*b1) =
      a0*b0 + 2^32*(a0*b1) + 2^32*(a1*b0) + (2^32*2^32)*(a1*b1)
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  rw [expanded]
  have p00 := Nat.mod_add_div (a0*b0) (2^32)
  have p01 := Nat.mod_add_div (a0*b1) (2^32)
  have p10 := Nat.mod_add_div (a1*b0) (2^32)
  have r00 := Nat.mod_lt (a0*b0) (show 0 < 2^32 by decide)
  have carry := Nat.mod_add_div ((a0*b0)/2^32 + (a0*b1)%2^32 + (a1*b0)%2^32) (2^32)
  have cr := Nat.mod_lt ((a0*b0)/2^32 + (a0*b1)%2^32 + (a1*b0)%2^32) (show 0 < 2^32 by decide)
  omega

/-- A limb product fits in a word with enough headroom for the low-column carry. -/
theorem limb_product_bound (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    a*b ≤ 18446744065119617025 := by
  exact Nat.mul_le_mul (show a ≤ 4294967295 by omega) (show b ≤ 4294967295 by omega)

/-- The executing word algorithm equals the complete product's high quotient. -/
theorem multiplyHigh_exact (left right : UInt64) :
    (multiplyHigh left right).toNat = left.toNat * right.toNat / 2^64 := by
  let a0 := left.toNat % 2^32
  let a1 := left.toNat / 2^32
  let b0 := right.toNat % 2^32
  let b1 := right.toNat / 2^32
  have ha0 : a0 < 2^32 := Nat.mod_lt _ (by decide)
  have hb0 : b0 < 2^32 := Nat.mod_lt _ (by decide)
  have ha1 : a1 < 2^32 := by have := left.toNat_lt; dsimp only [a1]; omega
  have hb1 : b1 < 2^32 := by have := right.toNat_lt; dsimp only [b1]; omega
  have h00 := limb_product_bound a0 b0 ha0 hb0
  have h01 := limb_product_bound a0 b1 ha0 hb1
  have h10 := limb_product_bound a1 b0 ha1 hb0
  have h11 := limb_product_bound a1 b1 ha1 hb1
  have decomposed := limb_high_identity a0 a1 b0 b1
  have leftParts : a0 + 2^32*a1 = left.toNat := Nat.mod_add_div _ _
  have rightParts : b0 + 2^32*b1 = right.toNat := Nat.mod_add_div _ _
  rw [leftParts, rightParts] at decomposed
  have finalBound := high_fits left right
  have r01 := Nat.mod_lt (a0*b1) (show 0 < 2^32 by decide)
  have r10 := Nat.mod_lt (a1*b0) (show 0 < 2^32 by decide)
  have p00 : (lowLimb left * lowLimb right).toNat = a0*b0 := by
    rw [UInt64.toNat_mul, lowLimb_exact, lowLimb_exact]
    change (a0*b0) % 2^64 = a0*b0
    exact Nat.mod_eq_of_lt (by omega)
  have p01 : (lowLimb left * highLimb right).toNat = a0*b1 := by
    rw [UInt64.toNat_mul, lowLimb_exact, highLimb_exact]
    change (a0*b1) % 2^64 = a0*b1
    exact Nat.mod_eq_of_lt (by omega)
  have p10 : (highLimb left * lowLimb right).toNat = a1*b0 := by
    rw [UInt64.toNat_mul, highLimb_exact, lowLimb_exact]
    change (a1*b0) % 2^64 = a1*b0
    exact Nat.mod_eq_of_lt (by omega)
  have p11 : (highLimb left * highLimb right).toNat = a1*b1 := by
    rw [UInt64.toNat_mul, highLimb_exact, highLimb_exact]
    change (a1*b1) % 2^64 = a1*b1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [multiplyHigh, UInt64.toNat_add, highLimb_exact, lowLimb_exact, p00, p01, p10, p11]
  omega

/-- The word recipe retains the general widened-product interface exactly. -/
theorem multiplyHigh_eq_spec (left right : UInt64) :
    multiplyHigh left right = multiplyHighSpec left right := by
  apply UInt64.toNat.inj
  rw [multiplyHigh_exact, multiplyHighSpec_exact]

/-- A nonzero machine count; every constructor carries the same positive bound. -/
structure Count where
  /-- The actual receiving word. -/
  word : UInt64
  /-- Range selection has an inhabitant only for a positive count. -/
  positive : 0 < word.toNat

/-- The existing total count conversion maps zero to one. -/
def Count.ofWord (word : UInt64) : Count :=
  if h : 0 < word.toNat then ⟨word, h⟩ else ⟨1, by decide⟩

/-- Multiply-high is below every admitted receiving count, for every source word. -/
theorem multiplyHigh_below (input : UInt64) (count : Count) :
    (multiplyHigh input count.word).toNat < count.word.toNat := by
  rw [multiplyHigh_exact]
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < (2 : Nat) ^ 64)).2
  have h := Nat.mul_lt_mul_of_pos_right input.toNat_lt count.positive
  simpa only [Nat.mul_comm] using h

/-- Return a machine word carrying the actual range-selection proof. -/
def below (input : UInt64) (count : Count) :
    { word : UInt64 // word.toNat < count.word.toNat } :=
  ⟨multiplyHigh input count.word, multiplyHigh_below input count⟩

/-- Checked advancement refuses before overflowing the fixed-width clock. -/
def advanceClock (clock amount : UInt64) : Option UInt64 :=
  if clock.toNat + amount.toNat < 2 ^ 64 then some (clock + amount) else none

/-- An accepted clock advance retains its full natural sum; it never wraps. -/
theorem clock_advance_exact (clock amount next : UInt64)
    (h : advanceClock clock amount = some next) :
    next.toNat = clock.toNat + amount.toNat := by
  unfold advanceClock at h
  split at h
  · rename_i fits
    cases h
    simp only [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  · contradiction

/-- Clock refusal is exactly exhaustion of the available word range. -/
theorem clock_advance_refuses (clock amount : UInt64) :
    advanceClock clock amount = none ↔ 2 ^ 64 ≤ clock.toNat + amount.toNat := by
  simp [advanceClock]

/-- Positive left xor shifts are injective by induction from the low bit. -/
theorem xor_shiftLeft_injective {width shift : Nat} (positive : 0 < shift)
    (left right : BitVec width) (h : left ^^^ (left <<< shift) = right ^^^ (right <<< shift)) :
    left = right := by
  have bits : ∀ i, left.getLsbD i = right.getLsbD i := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      have hi := congrArg (fun word : BitVec width => word.getLsbD i) h
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft] at hi
      by_cases hs : i < shift
      · simpa [hs] using hi
      · have smaller := ih (i - shift) (by omega)
        simpa [smaller] using hi
  exact BitVec.eq_of_getLsbD_eq (fun i _ => bits i)

/-- Rotation merely reindexes the finite bit positions. -/
theorem rotate_injective {width rotation : Nat} (hr : rotation < width)
    (left right : BitVec width) (h : left.rotateLeft rotation = right.rotateLeft rotation) :
    left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hw : i + rotation < width
  · have hb := congrArg (fun word : BitVec width => word.getLsbD (i + rotation)) h
    simpa [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hr, hw, hi,
      show ¬ i + rotation < rotation by omega] using hb
  · have hb := congrArg (fun word : BitVec width => word.getLsbD (i + rotation - width)) h
    simpa [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hr,
      show i + rotation - width < rotation by omega,
      show width - rotation + (i + rotation - width) = i by omega] using hb
/-- Positive right xor shifts are injective by induction from the high bit. -/
theorem xor_shiftRight_injective {width shift : Nat} (positive : 0 < shift)
    (left right : BitVec width) (h : left ^^^ (left >>> shift) = right ^^^ (right >>> shift)) :
    left = right := by
  have bits (remaining : Nat) : ∀ i, width - i = remaining → left.getLsbD i = right.getLsbD i := by
    induction remaining using Nat.strongRecOn with
    | ind remaining ih =>
      intro i hi
      by_cases hw : i < width
      · have smaller := ih (width - (i + shift)) (by omega) (i + shift) rfl
        have hb := congrArg (fun word : BitVec width => word.getLsbD i) h
        simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight] at hb
        rw [Nat.add_comm shift i, smaller] at hb
        exact Bool.xor_left_inj.mp hb
      · simp [BitVec.getLsbD_of_ge, show width ≤ i by omega]
  exact BitVec.eq_of_getLsbD_eq (fun i _ => bits (width - i) i rfl)
end Acorn.Word
