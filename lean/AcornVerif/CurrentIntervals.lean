/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentDivision
/-!
# Numerical interval consequences

These contracts compose the actual standard-model arithmetic and conversion
connections. Signed multiplication preserves its numerical direction. The
spacing immediately above one, combined with the derived rounding radius,
proves the closed upper endpoint for addition. Raw-word order then supplies
finite narrowing on a containing local domain. Exceptional numerical values
remain excluded and native primitive/compiler correspondence stays trusted.
-/
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder AcornVerif.CurrentOperations AcornVerif.CurrentDivision
namespace AcornVerif.CurrentIntervals

/-- Subtracting positive zero preserves every unpacked constructor and sign in the standard model.
-/
theorem model_sub_positive_zero (spec : Format) (value : UnpackedFloat) :
    UnpackedFloat.sub spec value (.zero .positive) = value := by
  cases value with
  | zero sign => cases sign <;> rfl
  | notANumber => rfl
  | infinity sign => rfl
  | finite sign m e hp => rfl

/-- The actual finite binary64 subtraction of positive zero preserves its numerical value and
finiteness, including signed zero. -/
theorem binary64_sub_zero_value (value : Binary64) (finite : value.Finite) :
    (value.sub ⟨0⟩).Finite ∧ numerical64 (value.sub ⟨0⟩) = numerical64 value := by
  have normal := model_unpack_format Format.binary64 (by decide) value.bits.toBitVec
    ((model_decoded64_finite value).mpr finite)
  have zero : decoded64 ⟨0⟩=.zero .positive := rfl
  have identity : UnpackedFloat.sub Format.binary64 (decoded64 value) (decoded64 ⟨0⟩)=
      decoded64 value := by rw [zero,model_sub_positive_zero]
  have decoded := model_sub64_decoded value ⟨0⟩ finite (by decide)
    (by rw [identity]; exact normal.1) (by rw [identity]; exact normal.2)
  rw [identity] at decoded
  constructor
  · apply (model_decoded64_finite _).mp
    rw [decoded]
    exact (model_decoded64_finite _).mpr finite
  · simp only [numerical64,decoded]

/-- The actual finite normalized model multiplication preserves a nonpositive product sign through
residual rounding. -/
theorem model_mul_nonpositive (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (direction : unpackedValue left * unpackedValue right ≤ 0) :
    unpackedValue (UnpackedFloat.mul spec left right) ≤ 0 := by
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero other => exact le_refl 0
    | finite s m e hp => exact le_refl 0
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero sign => exact le_refl 0
    | finite rightSign rm re rp =>
      have identity : unpackedValue (.finite leftSign lm le lp)*
          unpackedValue (.finite rightSign rm re rp) =
          signCoefficient (leftSign*rightSign)*(lm*rm:Nat)*(2:ℚ)^(le+re) := by
        rw [model_sign_product_value,zpow_add₀ (by norm_num : (2:ℚ)≠0)]
        simp only [unpackedValue,Nat.cast_mul]
        ring
      have positive : (0:ℚ)<(lm*rm:Nat)*(2:ℚ)^(le+re) :=
        mul_pos (by exact_mod_cast Nat.mul_pos lp rp) (zpow_pos (by norm_num) _)
      have signNonpositive : signCoefficient (leftSign*rightSign)≤0 := by
        rw [identity,mul_assoc] at direction
        exact nonpos_of_mul_nonpos_left direction positive
      simp only [UnpackedFloat.mul]
      rw [model_round_accuracy_value]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg signNonpositive (Nat.cast_nonneg _))
        (le_of_lt (zpow_pos (by norm_num : (0:ℚ)<2) _))

/-- Actual binary64 multiplication with exact product magnitude at most 2^16 stays finite and
preserves a nonpositive numerical direction. -/
theorem binary64_mul_nonpositive (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (bound : |numerical64 left * numerical64 right| ≤ 65536)
    (direction : numerical64 left * numerical64 right ≤ 0) :
    (left.mul right).Finite ∧ numerical64 (left.mul right) ≤ 0 := by
  have ln := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rn := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have power : (2:ℚ)^(16:Int)=65536 := by norm_num
  have localProof := model_mul_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    ln rn 16 (by simpa only [numerical64,power] using bound)
  have radius : (2:ℚ)^(max ((16:Int)+1-Format.binary64.mantissaBits)
      Format.binary64.minExponent)/2=1/137438953472 := by
    norm_num [Format.mantissaBits,Format.minExponent]
  have error : |unpackedValue (UnpackedFloat.mul Format.binary64 (decoded64 left)
      (decoded64 right))-(numerical64 left*numerical64 right)|≤1/137438953472 := by
    simpa only [numerical64,radius] using localProof.2
  have fits := model_local64_fits _ _ localProof.1 bound error
  have decoded := model_mul64_decoded left right leftFinite rightFinite localProof.1 fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ localProof.1
  · simpa only [numerical64,decoded] using
      model_mul_nonpositive Format.binary64 (decoded64 left) (decoded64 right) ln rn direction

/-- Every finite binary64 value strictly above one is separated from one by at least 2^-52, as
derived from the actual raw key order. -/
theorem numerical64_above_one_gap (value : Binary64) (finite : value.Finite)
    (above : 1 < numerical64 value) :
    1 + 1 / 4503599627370496 ≤ numerical64 value := by
  let unit : Binary64 := ⟨0x3ff0000000000000⟩
  let next : Binary64 := ⟨0x3ff0000000000001⟩
  have unitFinite : unit.Finite := by decide
  have nextFinite : next.Finite := by decide
  have unitValue : numerical64 unit=1 := by
    dsimp only [unit]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-52:Int)=1
    norm_num
  have nextValue : numerical64 next=1+1/4503599627370496 := by
    dsimp only [next]
    change (1:ℚ)*4503599627370497*(2:ℚ)^(-52:Int)=_
    norm_num
  have key := (numerical64_strict_order unit value unitFinite finite).mp
    (by simpa [unitValue] using above)
  have nextKey : next.key≤value.key := by
    have uk : unit.key=(0x3ff0000000000000:Int) := by dsimp only [unit]; rfl
    have nk : next.key=(0x3ff0000000000001:Int) := by dsimp only [next]; rfl
    rw [uk] at key
    rw [nk]
    omega
  have order := (numerical64_order next value nextFinite finite).mpr nextKey
  simpa only [nextValue] using order

/-- Actual binary64 addition with exact sum magnitude at most one stays finite and cannot cross
the upper endpoint one. -/
theorem binary64_add_unit_upper (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) (bound : |numerical64 left + numerical64 right| ≤ 1) :
    (left.add right).Finite ∧ numerical64 (left.add right) ≤ 1 := by
  have ln := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rn := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have localProof := model_add_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    ln rn 0 (by simpa only [numerical64,zpow_zero] using bound)
  have radius : (2:ℚ)^(max ((0:Int)+1-Format.binary64.mantissaBits)
      Format.binary64.minExponent)/2=1/9007199254740992 := by
    norm_num [Format.mantissaBits,Format.minExponent]
  have error : |unpackedValue (UnpackedFloat.add Format.binary64 (decoded64 left)
      (decoded64 right))-(numerical64 left+numerical64 right)|≤1/9007199254740992 := by
    simpa only [numerical64,radius] using localProof.2
  have fits : ModelFits Format.binary64 (UnpackedFloat.add Format.binary64
      (decoded64 left) (decoded64 right)) := by
    apply model_fits_of_value_bound Format.binary64 _
      (model_normalized_finite _ _ localProof.1) 1 (by decide)
    have ht := abs_add_le
      (unpackedValue (UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64 right))-
        (numerical64 left+numerical64 right)) (numerical64 left+numerical64 right)
    rw [sub_add_cancel] at ht
    norm_num only [zpow_one]
    linarith only [ht,error,bound]
  have decoded := model_add64_decoded left right leftFinite rightFinite localProof.1 fits
  have finite : (left.add right).Finite := by
    apply (model_decoded64_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ localProof.1
  have observedError : |numerical64 (left.add right)-(numerical64 left+numerical64 right)|≤
      1/9007199254740992 := by simpa only [numerical64,decoded] using error
  refine ⟨finite,?_⟩
  by_contra above
  have gap := numerical64_above_one_gap (left.add right) finite (by linarith only [above])
  have upper := (abs_le.mp observedError).2
  have limit := (abs_le.mp bound).2
  linarith only [gap,upper,limit]

/-- Every raw word below the sign bit has a key equal to its unsigned word value. -/
theorem binary64_key_nonnegative_word (value : Binary64) (bound : value.bits.toNat < 2 ^ 63) :
    value.key = (value.bits.toNat : Int) := by
  have mask : value.bits &&& 0x8000000000000000=0 := by
    apply UInt64.toNat.inj
    rw [word64_sign_exact]
    change (value.bits.toNat/2^63)*2^63=0
    rw [Nat.div_eq_of_lt bound,Nat.zero_mul]
  have magnitude : value.magnitude=value.bits.toNat := by
    change value.bits.toNat &&& (2^63-1)=_
    rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt bound]
  simp only [Binary64.key,mask,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,magnitude]

/-- A strictly positive raw key implies an unset sign bit and equals the unsigned stored word. -/
theorem binary64_positive_key_word (value : Binary64) (positive : 0 < value.key) :
    value.bits.toNat < 2 ^ 63 ∧ value.key = (value.bits.toNat : Int) := by
  have mask : value.bits &&& 0x8000000000000000=0 := by
    by_contra nonzero
    have sign : (value.bits &&& 0x8000000000000000 != 0)=true := by simpa using nonzero
    simp only [Binary64.key,sign,↓reduceIte] at positive
    omega
  have sign := congrArg UInt64.toNat mask
  rw [word64_sign_exact] at sign
  change (value.bits.toNat/2^63)*2^63=0 at sign
  have bound : value.bits.toNat<2^63 := by omega
  exact ⟨bound,binary64_key_nonnegative_word value bound⟩

/-- Actual narrowing stays finite for every finite binary64 value of magnitude at most 2^16. -/
theorem narrow_finite_local (value : Binary64) (finite : value.Finite)
    (bound : |numerical64 value| ≤ 65536) : (Conversion.narrow value).Finite := by
  let limit : Binary64 := ⟨0x40f0000000000000⟩
  have limitFinite : limit.Finite := by decide
  have limitValue : numerical64 limit=65536 := by
    dsimp only [limit]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-36:Int)=65536
    norm_num
  have magnitude := (numerical64_magnitude_order value limit finite limitFinite).mp
    (by rw [limitValue]; norm_num only [abs_of_pos (by norm_num : (0:ℚ)<65536)]; exact bound)
  have limitMagnitude : limit.magnitude=0x40f0000000000000 := by dsimp only [limit]; rfl
  rw [limitMagnitude] at magnitude
  have fields := Conversion.fields64_decomposition value
  have exponent : (((value.bits >>> 52) &&& 0x7ff):UInt64).toNat≤1039 := by omega
  apply (Conversion.narrow_finite_iff value finite).mpr
  rw [Conversion.normalExponent_exact _ _ (by omega)]
  split <;> omega

end AcornVerif.CurrentIntervals
