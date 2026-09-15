/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentFloat
import Acorn.Portable
/-!
# Machine unit-interval multiplication and integer power

These results unfold the pinned Lean 4.33.0 standard model in
`Init/Data/Float/Model/Unpacked/{Round,Pack/Basic,Operations/Mul}.lean`.
They bound the two actual rounding stages, including carry and subnormal
results, then connect those stages to `Binary64.mul` and `Portable.powLoop`.
The loop proof quantifies over every natural exponent; it does not unroll or
sample a selected exponent domain. The signed interval includes negative zero, whose output sign is characterized
by exponent parity. Widening and narrowing preserve the unit bound, connecting
the induction to the public binary32 power for every UInt32 exponent. Native
primitive/compiler correspondence remains trusted.
-/

namespace AcornVerif.CurrentPower
open AcornVerif.CurrentFloat
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat

/-- Every finite shift retains exactly the integer quotient, regardless of residual bits. -/
theorem model_shift_mantissa (mantissa : ExtendedMantissa) (shift : Nat) :
    (mantissa >>> shift).mantissa = mantissa.mantissa / 2^shift := by
  induction shift with
  | zero => simp; rfl
  | succ shift ih =>
    change (ExtendedMantissa.shiftRightOne (mantissa >>> shift)).mantissa = _
    simp only [ExtendedMantissa.shiftRightOne, ih]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- Nearest-even rounding increases the retained integer by at most one. -/
theorem model_round_mantissa_ceiling (mantissa : ExtendedMantissa) :
    mantissa.roundedMantissa ≤ mantissa.mantissa + 1 := by
  unfold ExtendedMantissa.roundedMantissa
  cases h : mantissa.accuracy with
  | exact => simp [Accuracy.roundToNearestEven]
  | inexact order => cases order <;> simp [Accuracy.roundToNearestEven] <;> omega

/-- The actual target-exponent shift leaves fewer than 53 retained bits. -/
theorem model_first_mantissa_bound (mantissa : Nat) (exponent : Int) :
    (shiftToTargetExponent Format.binary64 mantissa exponent .exact).1.mantissa < 2^53 := by
  unfold shiftToTargetExponent shiftToExponent
  rw [model_shift_mantissa]
  change mantissa / 2^((Format.binary64.targetExponent (totalExponent mantissa exponent)-exponent).toNat) < 2^53
  by_cases hz : mantissa = 0
  · simp [hz]
  · let shift := (Format.binary64.targetExponent (totalExponent mantissa exponent)-exponent).toNat
    have hlo : mantissa.log2+1 ≤ 53+shift := by
      simp only [shift, Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
      omega
    have hm := ((Nat.log2_eq_iff hz).mp rfl).2
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mpr
    rw [← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hlo)
/-- Positive finite components with exponent at most -53 pack below one. -/
theorem model_pack_below_one (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa)
    (he : exponent ≤ -53) :
    (Float.Model.pack (.finite .positive mantissa exponent positive)).toBits.toNat < 0x3ff0000000000000 := by
  have hb : (exponent+1075).toNat ≤ 1022 := by omega
  have hn : ¬ 2 ^ Format.binary64.exponentBits ≤
      (exponent + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    change ¬ 2048 ≤ (exponent + 1023 + 52).toNat + 1
    omega
  change (pack Format.binary64 (.finite .positive mantissa exponent positive)).toNat < _
  simp only [pack, if_neg hn]
  split
  · change (0#1 ++ BitVec.ofNat 11 (exponent+1023+52).toNat ++ BitVec.ofNat 52 mantissa).toNat < _
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    change ((0 * 2^11 ||| ((exponent+1023+52).toNat % 2048))*2^52 ||| (mantissa % 2^52)) < _
    have heq : (exponent+1023+52).toNat % 2048 = (exponent+1075).toNat := by omega
    rw [Nat.zero_mul, Nat.zero_or, heq, Nat.mul_comm,
      ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt mantissa (Nat.two_pow_pos 52))]
    have hf := Nat.mod_lt mantissa (Nat.two_pow_pos 52)
    omega
  · change (0#1 ++ 0#11 ++ BitVec.ofNat 52 mantissa).toNat < _
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    change ((0 * 2^11 ||| 0)*2^52 ||| (mantissa % 2^52)) < _
    have hf := Nat.mod_lt mantissa (Nat.two_pow_pos 52)
    simp only [Nat.zero_mul, Nat.zero_or]
    omega
/-- The second normalization stage shifts once exactly on the significand carry. -/
theorem model_second_shift_exact (mantissa : Nat) (exponent : Int) (hm : mantissa ≤ 2^53)
    (he : -1074 ≤ exponent) :
    shiftToTargetExponent Format.binary64 mantissa exponent .exact =
      if mantissa = 2^53 then (ExtendedMantissa.ofMantissaAndAccuracy (2^52) .exact, exponent+1)
      else (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact, exponent) := by
  by_cases htop : mantissa = 2^53
  · rw [if_pos htop, htop]
    have hl : (2^53 : Nat).log2 = 53 := by decide
    have ht : Format.binary64.targetExponent (totalExponent (2^53) exponent) = exponent+1 := by
      simp only [Format.targetExponent, totalExponent, hl, Format.mantissaBits, Format.minExponent]
      omega
    simp only [shiftToTargetExponent, ht, shiftToExponent]
    have hd : (exponent+1-exponent).toNat = 1 := by omega
    rw [hd]
    have hshift : ExtendedMantissa.ofMantissaAndAccuracy (2^53) .exact >>> (1 : Nat) =
        ExtendedMantissa.ofMantissaAndAccuracy (2^52) .exact := by
      exact model_shift_exact (2^52) 1
    rw [hshift]
    rfl
  · rw [if_neg htop]
    have hl : mantissa.log2 ≤ 52 := by
      by_cases hz : mantissa = 0
      · simp [hz]
      · have h := (Nat.log2_lt hz).mpr (show mantissa < 2^53 by omega)
        omega
    have ht : Format.binary64.targetExponent (totalExponent mantissa exponent) ≤ exponent := by
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
      omega
    simp only [shiftToTargetExponent, shiftToExponent]
    have hd : (Format.binary64.targetExponent (totalExponent mantissa exponent)-exponent).toNat = 0 := by omega
    rw [hd]
    simp
    rfl
/-- The actual rounding and packing stages preserve the unit bound on the product domain. -/
theorem model_round_product_unit (mantissa : Nat) (exponent : Int) (hm : mantissa < 2^106)
    (he : exponent ≤ -106) :
    (Float.Model.pack (roundWithAccuracy Format.binary64 .positive mantissa exponent .exact)).toBits.toNat ≤
      0x3ff0000000000000 := by
  let first := shiftToTargetExponent Format.binary64 mantissa exponent .exact
  let rounded := first.1.roundedMantissa
  have hr : rounded ≤ 2^53 := by
    have hfirst : first.1.mantissa < 2^53 := model_first_mantissa_bound mantissa exponent
    have hr := model_round_mantissa_ceiling first.1
    omega
  have hl : mantissa.log2 ≤ 105 := by
    by_cases hz : mantissa = 0
    · simp [hz]
    · have h := (Nat.log2_lt hz).mpr hm
      omega
  have ht : -1074 ≤ Format.binary64.targetExponent (totalExponent mantissa exponent) ∧
      Format.binary64.targetExponent (totalExponent mantissa exponent) ≤ -53 := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have he1 : -1074 ≤ first.2 ∧ first.2 ≤ -53 := by
    dsimp only [first, shiftToTargetExponent, shiftToExponent]
    omega
  rw [roundWithAccuracy]
  change (Float.Model.pack (let final := shiftToTargetExponent Format.binary64 rounded first.2 .exact
    if h : final.1.mantissa = 0 then .zero .positive
    else .finite .positive final.1.mantissa final.2 (Nat.pos_of_ne_zero h))).toBits.toNat ≤ _
  rw [model_second_shift_exact rounded first.2 hr he1.1]
  split
  · change (Float.Model.pack (.finite .positive (2^52) (first.2+1) (by decide))).toBits.toNat ≤ _
    rw [model_pack_word _ _ (by omega) (by decide) (by omega) (by omega)]
    have hbi : (first.2+1+1075).toNat ≤ 1023 := by omega
    simp only [Nat.mod_self]
    omega
  · change (Float.Model.pack (if h : rounded = 0 then .zero .positive
      else .finite .positive rounded first.2 (Nat.pos_of_ne_zero h))).toBits.toNat ≤ _
    split
    · decide
    · exact Nat.le_of_lt (model_pack_below_one _ _ _ he1.2)
/-- Multiplication by a power of two shifts every positive integer leading-bit index. -/
theorem model_log2_scaled_positive (m shift : Nat) (hm : 0 < m) :
    (m*2^shift).log2 = m.log2+shift := by
  have hp : m*2^shift ≠ 0 := by
    have := Nat.mul_pos hm (Nat.two_pow_pos shift)
    omega
  have hb := (Nat.log2_eq_iff (Nat.ne_of_gt hm)).mp rfl
  apply (Nat.log2_eq_iff hp).mpr
  have hl := Nat.mul_le_mul_right (2^shift) hb.1
  have hh := Nat.mul_lt_mul_of_pos_right hb.2 (Nat.two_pow_pos shift)
  rw [← Nat.pow_add] at hl hh
  have h : m.log2+shift+1 = m.log2+1+shift := by omega
  simpa only [h] using And.intro hl hh

/-- A zero-filled scale is exact for every normalized value, including subnormals. -/
theorem model_round_scaled_normalized (m shift : Nat) (e : Int) (hm : 0 < m)
    (ht : Format.binary64.targetExponent (totalExponent m e) = e) :
    roundWithAccuracy Format.binary64 .positive (m*2^shift) (e-shift) .exact =
      .finite .positive m e hm := by
  have hl := model_log2_scaled_positive m shift hm
  have htotal : totalExponent (m*2^shift) (e-shift) = totalExponent m e := by
    simp only [totalExponent, hl]
    omega
  have hs : shiftToTargetExponent Format.binary64 (m*2^shift) (e-shift) .exact =
      (ExtendedMantissa.ofMantissaAndAccuracy m .exact, e) := by
    simp only [shiftToTargetExponent, htotal, ht, shiftToExponent]
    have hdelta : (e-(e-shift)).toNat = shift := by omega
    rw [hdelta, model_shift_exact]
    congr 1
    omega
  have hshift (a : ExtendedMantissa) : a >>> (0 : Nat) = a := rfl
  rw [roundWithAccuracy, hs]
  simp [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, shiftToTargetExponent,
    ht, shiftToExponent, hshift, Nat.ne_of_gt hm]

/-- A positive subnormal retains its exact components through packing and unpacking. -/
theorem model_unpack_pack_subnormal (m : Nat) (positive : 0 < m) (bound : m < 2^52) :
    unpack Format.binary64 (pack Format.binary64 (.finite .positive m (-1074) positive)) =
      .finite .positive m (-1074) positive := by
  have hlog : m.log2 < 52 := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound
  have hn : ¬m.log2+1 = Format.binary64.mantissaBits := by
    change ¬m.log2+1 = 53
    omega
  simp only [pack]
  rw [if_neg (show ¬2 ^ Format.binary64.exponentBits ≤
    ((-1074 : Int) + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 by decide)]
  rw [if_neg hn]
  simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents]
  have hs : unpackSign (packComponents Format.binary64 .positive 0#11 (BitVec.ofNat 52 m)) = 0#1 := by
    change (0#1 ++ 0#11 ++ BitVec.ofNat 52 m).extractLsb' 63 1 = 0#1
    rw [BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_of_le (by decide)]
    rfl
  rw [hs]
  have hm : (BitVec.ofNat 52 m).toNat = m := Nat.mod_eq_of_lt bound
  have hnz : BitVec.ofNat 52 m ≠ 0#52 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [hm] at this
    change m = 0 at this
    omega
  simp [hnz, hm, Sign.ofBitVec, Format.exponentBias]
/-- Decoded positive-sign unit values, with separate normal, subnormal and exact-one conditions. -/
def ModelUnit : UnpackedFloat → Prop
  | .zero sign => sign = .positive
  | .finite sign m e _ => sign = .positive ∧ m < 2^53 ∧ -1074 ≤ e ∧ e ≤ -52 ∧
      (e = -52 → m = 2^52) ∧ (e = -1074 ∨ 2^52 ≤ m)
  | _ => False

/-- Every raw positive-sign word at or below one decodes into the complete unit domain. -/
theorem model_unpack_unit (word : UInt64) (bound : word.toNat ≤ 0x3ff0000000000000) :
    ModelUnit (unpack Format.binary64 word.toBitVec) := by
  let ev := unpackExponent (spec := Format.binary64) word.toBitVec
  let mv := unpackMantissa (spec := Format.binary64) word.toBitVec
  have he : ev.toNat = word.toNat / 2^52 := by
    change (word.toNat >>> 52) % 2^11 = word.toNat / 2^52
    rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show word.toNat / 2^52 < 2^11 by omega)]
  have hm : mv.toNat = word.toNat % 2^52 := by
    change (word.toNat >>> 0) % 2^52 = _
    rw [Nat.shiftRight_zero]
  have hs : unpackSign (spec := Format.binary64) word.toBitVec = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    change (word.toNat >>> 63) % 2 = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (show word.toNat < 2^63 by omega)]
  have hsize : mv.toNat < 2^52 := by rw [hm]; exact Nat.mod_lt _ (Nat.two_pow_pos 52)
  have hfields : word.toNat = ev.toNat * 2^52 + mv.toNat := by rw [he, hm]; omega
  have hhigh : ev.toNat ≤ 1023 := by omega
  have hnotinf : ev ≠ -1#11 := by
    intro h
    have := congrArg BitVec.toNat h
    change ev.toNat = 2047 at this
    omega
  have hsig : (1#1 ++ mv).toNat = 2^52 + mv.toNat := by
    change 2^52 ||| mv.toNat = _
    rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt hsize, Nat.add_comm]
  unfold unpack
  change ModelUnit (if ev = -1#11 then _ else if ev = 0#11 then _ else _)
  rw [if_neg hnotinf]
  by_cases hz : ev = 0#11
  · rw [if_pos hz]
    split
    · simp [ModelUnit, hs, Sign.ofBitVec]
    · simp [ModelUnit, hs, Sign.ofBitVec]
      have he0 : ev.toNat = 0 := congrArg BitVec.toNat hz
      change mv.toNat < 2^53 ∧ -1074 ≤ (ev.toNat : Int)-1075+1 ∧
        (ev.toNat : Int)-1075+1 ≤ -52 ∧
        ((ev.toNat : Int)-1075+1 = -52 → mv.toNat = 2^52) ∧
        ((ev.toNat : Int)-1075+1 = -1074 ∨ 2^52 ≤ mv.toNat)
      omega
  · rw [if_neg hz]
    have hepos : 0 < ev.toNat := by
      by_cases h : ev.toNat = 0
      · have hw : ev = 0#11 := BitVec.eq_of_toNat_eq h
        exact False.elim (hz hw)
      · omega
    simp [ModelUnit, hs, Sign.ofBitVec]
    change (1#1 ++ mv).toNat < 2^53 ∧ -1074 ≤ (ev.toNat : Int)-1075 ∧
      (ev.toNat : Int)-1075 ≤ -52 ∧
      ((ev.toNat : Int)-1075 = -52 → (1#1 ++ mv).toNat = 2^52) ∧
      ((ev.toNat : Int)-1075 = -1074 ∨ 2^52 ≤ (1#1 ++ mv).toNat)
    rw [hsig]
    omega
/-- The decoded unit domain already has the exponent required by the rounding model. -/
theorem model_unit_round_target (sign : Sign) (m : Nat) (e : Int) (positive : 0 < m)
    (unit : ModelUnit (.finite sign m e positive)) :
    Format.binary64.targetExponent (totalExponent m e) = e := by
  rcases unit with ⟨hs, hm, he, he', ht, hn⟩
  cases hn with
  | inl h =>
    subst e
    have hl : m.log2 ≤ 52 := by
      have h := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr hm
      omega
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  | inr h => exact model_normal_target m e (model_mantissa_log m h hm) he

/-- Repacking preserves every decoded unit value, including zero and subnormals. -/
theorem model_unit_unpack_pack (value : UnpackedFloat) (unit : ModelUnit value) :
    unpack Format.binary64 (pack Format.binary64 value) = value := by
  cases value with
  | zero sign => simp only [ModelUnit] at unit; subst sign; rfl
  | finite sign m e positive =>
    rcases unit with ⟨hs, hm, he, he', ht, hn⟩
    subst sign
    by_cases hnormal : 2^52 ≤ m
    · exact model_unpack_pack_normal .positive m e hnormal hm he (by omega)
    · have hexp : e = -1074 := by cases hn <;> omega
      subst e
      exact model_unpack_pack_subnormal m positive (by omega)
  | infinity sign => contradiction
  | notANumber => contradiction

/-- Every admitted decoded unit value packs at or below the raw encoding of one. -/
theorem model_unit_pack_bound (value : UnpackedFloat) (unit : ModelUnit value) :
    (Float.Model.pack value).toBits.toNat ≤ 0x3ff0000000000000 := by
  cases value with
  | zero sign => simp only [ModelUnit] at unit; subst sign; decide
  | finite sign m e positive =>
    rcases unit with ⟨hs, hm, he, he', ht, hn⟩
    subst sign
    by_cases htop : e = -52
    · have hm := ht htop
      subst e
      subst m
      change (0x3ff0000000000000 : Nat) ≤ 0x3ff0000000000000
      exact Nat.le_refl _
    · exact Nat.le_of_lt (model_pack_below_one m e positive (by omega))
  | infinity sign => contradiction
  | notANumber => contradiction

/-- The actual bit-reinterpretation model preserves the complete positive-sign unit domain. -/
theorem model_ofBits_unit (word : UInt64) (bound : word.toNat ≤ 0x3ff0000000000000) :
    ModelUnit (Float.Model.ofBits word).unpack := by
  have h := model_unpack_unit word bound
  change ModelUnit (unpack Format.binary64 (pack Format.binary64 (unpack Format.binary64 word.toBitVec)))
  rw [model_unit_unpack_pack _ h]
  exact h

/-- The standard decoded multiplication and rounding preserve the positive-sign unit bound. -/
theorem model_mul_unit (first second : UnpackedFloat) (hu : ModelUnit first) (hv : ModelUnit second) :
    (Float.Model.pack (mul Format.binary64 first second)).toBits.toNat ≤ 0x3ff0000000000000 := by
  cases first <;> cases second <;> simp only [ModelUnit] at hu hv
  all_goals try contradiction
  · rename_i sign₁ sign₂
    subst sign₁
    subst sign₂
    change (0 : Nat) ≤ 0x3ff0000000000000
    omega
  · rename_i sign₁ sign₂ m e positive
    subst sign₁
    rcases hv with ⟨hs, _⟩
    subst sign₂
    change (0 : Nat) ≤ 0x3ff0000000000000
    omega
  · rename_i sign₁ m e positive sign₂
    rcases hu with ⟨hs, _⟩
    subst sign₁
    subst sign₂
    change (0 : Nat) ≤ 0x3ff0000000000000
    omega
  · rename_i sign₁ m₁ e₁ positive₁ sign₂ m₂ e₂ positive₂
    have htarget₁ := model_unit_round_target sign₁ m₁ e₁ positive₁ hu
    have htarget₂ := model_unit_round_target sign₂ m₂ e₂ positive₂ hv
    rcases hu with ⟨hs₁, hm₁, he₁, he₁', ht₁, hn₁⟩
    rcases hv with ⟨hs₂, hm₂, he₂, he₂', ht₂, hn₂⟩
    subst sign₁
    subst sign₂
    change (Float.Model.pack (roundWithAccuracy Format.binary64 .positive (m₁*m₂) (e₁+e₂) .exact)).toBits.toNat ≤ _
    by_cases htop₁ : e₁ = -52
    · have hm := ht₁ htop₁
      subst e₁
      subst m₁
      rw [Nat.mul_comm (2^52)]
      have heq : (-52 : Int)+e₂ = e₂-(52 : Nat) := by omega
      rw [heq, model_round_scaled_normalized m₂ 52 e₂ positive₂ htarget₂]
      exact model_unit_pack_bound _ ⟨rfl, hm₂, he₂, he₂', ht₂, hn₂⟩
    · by_cases htop₂ : e₂ = -52
      · have hm := ht₂ htop₂
        subst e₂
        subst m₂
        have heq : e₁+(-52) = e₁-(52 : Nat) := by omega
        rw [heq, model_round_scaled_normalized m₁ 52 e₁ positive₁ htarget₁]
        exact model_unit_pack_bound _ ⟨rfl, hm₁, he₁, he₁', ht₁, hn₁⟩
      · apply model_round_product_unit
        · have h₁ := Nat.mul_lt_mul_of_pos_right hm₁ positive₂
          have h₂ := Nat.mul_lt_mul_of_pos_left hm₂ (Nat.two_pow_pos 53)
          have hh := Nat.lt_trans h₁ h₂
          exact hh
        · omega
/-- The executing binary64 multiplication preserves the raw positive-sign unit interval. -/
theorem binary64_mul_unit (first second : Binary64)
    (hu : first.bits.toNat ≤ 0x3ff0000000000000)
    (hv : second.bits.toNat ≤ 0x3ff0000000000000) :
    (first.mul second).bits.toNat ≤ 0x3ff0000000000000 := by
  change (Float.Model.mul (Float.Model.ofBits first.bits) (Float.Model.ofBits second.bits)).toBits.toNat ≤ _
  exact model_mul_unit _ _ (model_ofBits_unit first.bits hu) (model_ofBits_unit second.bits hv)

/-- The executing square-and-multiply loop preserves the unit bound for every natural exponent. -/
theorem powLoop_unit (accumulator squared : Binary64) (remaining : Nat)
    (ha : accumulator.bits.toNat ≤ 0x3ff0000000000000)
    (hs : squared.bits.toNat ≤ 0x3ff0000000000000) :
    (Portable.powLoop accumulator squared remaining).bits.toNat ≤ 0x3ff0000000000000 := by
  induction remaining using Nat.strongRecOn generalizing accumulator squared with
  | ind remaining ih =>
    by_cases hz : remaining = 0
    · rw [hz, Portable.powLoop_zero]
      exact ha
    · rw [Portable.powLoop_step _ _ _ hz]
      apply ih (remaining/2) (Nat.div_lt_self (by omega) (by omega))
      · split
        · exact binary64_mul_unit _ _ ha hs
        · exact ha
      · exact binary64_mul_unit _ _ hs hs
/-- The public machine power preserves the positive-sign unit interval for every UInt32 exponent. -/
theorem pow_word_unit (value : Binary32) (exponent : UInt32)
    (bound : value.bits.toNat ≤ 0x3f800000) :
    (Portable.pow value exponent).bits.toNat ≤ 0x3f800000 := by
  rw [Portable.pow_eq]
  apply Conversion.narrow_word_unit
  apply powLoop_unit
  · change (0x3ff0000000000000 : Nat) ≤ 0x3ff0000000000000
    exact Nat.le_refl _
  · exact Conversion.widen_word_unit value bound

/-- The public zero exponent gives exactly one for every raw base, including every NaN payload. -/
theorem pow_zero_word (value : Binary32) : Portable.pow value 0 = ⟨0x3f800000⟩ := by
  rw [Portable.pow_eq]
  rw [show (0 : UInt32).toNat = 0 from rfl, Portable.powLoop_zero]
  rfl

/-- Multiplying binary64 signed zeros retains exactly the exclusive-or sign. -/
theorem mul_signed_zeros (left right : Bool) :
    (Binary64.mk (if left then 0x8000000000000000 else 0)).mul
      ⟨if right then 0x8000000000000000 else 0⟩ =
        ⟨if left != right then 0x8000000000000000 else 0⟩ := by
  cases left <;> cases right <;> rfl

/-- Multiplication by binary64 one preserves either zero sign. -/
theorem mul_one_signed_zero (sign : Bool) :
    (Binary64.ofUInt64 1).mul ⟨if sign then 0x8000000000000000 else 0⟩ =
      ⟨if sign then 0x8000000000000000 else 0⟩ := by
  cases sign <;> rfl

/-- A signed-zero accumulator and positive-zero square retain the accumulator sign through any loop length. -/
theorem powLoop_zero_accumulator (sign : Bool) (remaining : Nat) :
    Portable.powLoop ⟨if sign then 0x8000000000000000 else 0⟩ ⟨0⟩ remaining =
      ⟨if sign then 0x8000000000000000 else 0⟩ := by
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    by_cases hz : remaining = 0
    · rw [hz, Portable.powLoop_zero]
    · rw [Portable.powLoop_step _ _ _ hz]
      have hs := mul_signed_zeros false false
      change (Binary64.mk 0).mul ⟨0⟩ = ⟨0⟩ at hs
      rw [hs]
      have ha := mul_signed_zeros sign false
      simp at ha
      rw [ha]
      simp only [ite_self]
      exact ih (remaining/2) (Nat.div_lt_self (by omega) (by omega))

/-- A positive power of positive zero reaches its absorbing zero state for any natural exponent. -/
theorem powLoop_positive_zero (remaining : Nat) (positive : remaining ≠ 0) :
    Portable.powLoop (Binary64.ofUInt64 1) ⟨0⟩ remaining = ⟨0⟩ := by
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    rw [Portable.powLoop_step _ _ _ positive]
    have hs := mul_signed_zeros false false
    change (Binary64.mk 0).mul ⟨0⟩ = ⟨0⟩ at hs
    rw [hs]
    split
    · have ha := mul_one_signed_zero false
      change (Binary64.ofUInt64 1).mul ⟨0⟩ = ⟨0⟩ at ha
      rw [ha]
      exact powLoop_zero_accumulator false _
    · rename_i even
      apply ih (remaining/2) (Nat.div_lt_self (by omega) (by omega))
      omega

/-- Powers of negative zero retain its sign exactly for odd positive exponents. -/
theorem pow_negative_zero (exponent : UInt32) :
    Portable.pow ⟨0x80000000⟩ exponent =
      if exponent.toNat = 0 then ⟨0x3f800000⟩
      else if exponent.toNat % 2 = 1 then ⟨0x80000000⟩ else ⟨0⟩ := by
  by_cases hz : exponent.toNat = 0
  · have he : exponent = 0 := UInt32.toNat.inj hz
    rw [he, pow_zero_word]
    rfl
  · rw [if_neg hz]
    rw [Portable.pow_eq]
    change Conversion.narrow (Portable.powLoop (Binary64.ofUInt64 1) ⟨0x8000000000000000⟩ exponent.toNat) = _
    rw [Portable.powLoop_step _ _ _ hz]
    have hs := mul_signed_zeros true true
    change (Binary64.mk 0x8000000000000000).mul ⟨0x8000000000000000⟩ = ⟨0⟩ at hs
    rw [hs]
    split
    · rename_i odd
      have ha := mul_one_signed_zero true
      change (Binary64.ofUInt64 1).mul ⟨0x8000000000000000⟩ = ⟨0x8000000000000000⟩ at ha
      have hzacc := powLoop_zero_accumulator true (exponent.toNat/2)
      change Portable.powLoop ⟨0x8000000000000000⟩ ⟨0⟩ (exponent.toNat/2) = ⟨0x8000000000000000⟩ at hzacc
      rw [ha, hzacc]
      exact Conversion.narrow_signed_zero true
    · rename_i even
      rw [powLoop_positive_zero _ (by omega)]
      exact Conversion.narrow_signed_zero false
/-- The signed order interval from zero to one includes every positive-sign unit word and negative zero. -/
theorem key_unit_cases (value : Binary32) (lo : 0 ≤ value.key) (hi : value.key ≤ 0x3f800000) :
    value.bits.toNat ≤ 0x3f800000 ∨ value.bits = 0x80000000 := by
  have hm : value.magnitude = value.bits.toNat % 2^31 := by
    change value.bits.toNat &&& (2^31-1) = _
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have hw := value.bits.toNat_lt
  by_cases hs : value.negative = true
  · have hmag : value.magnitude = 0 := by
      simp only [Binary32.key, hs, ↓reduceIte] at lo
      omega
    by_cases hz : value.bits.toNat = 0
    · exact Or.inl (by omega)
    · right
      apply UInt32.toNat.inj
      change value.bits.toNat = 2^31
      omega
  · have hn : value.bits &&& 0x80000000 = 0 := by
      simpa [Binary32.negative] using hs
    have hraw : value.magnitude = value.bits.toNat := by
      have hjoin : (value.bits.toNat &&& (2^31-1)) ||| (value.bits.toNat &&& 2^31) = value.bits.toNat := by
        rw [← Nat.and_or_distrib_left]
        change value.bits.toNat &&& (2^32-1) = value.bits.toNat
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hw]
      have high : value.bits.toNat &&& 2^31 = 0 := congrArg UInt32.toNat hn
      rw [high, Nat.or_zero] at hjoin
      exact hjoin
    simp [Binary32.key, hs] at hi
    exact Or.inl (by omega)

/-- The public power returns a finite value in the signed unit interval for every admitted base and UInt32 exponent. -/
theorem pow_unit (value : Binary32) (exponent : UInt32)
    (lo : 0 ≤ value.key) (hi : value.key ≤ 0x3f800000) :
    (Portable.pow value exponent).Finite ∧
      0 ≤ (Portable.pow value exponent).key ∧ (Portable.pow value exponent).key ≤ 0x3f800000 := by
  rcases key_unit_cases value lo hi with h | h
  · have hb := pow_word_unit value exponent h
    have hm : (Portable.pow value exponent).magnitude = (Portable.pow value exponent).bits.toNat := by
      change (Portable.pow value exponent).bits.toNat &&& (2^31-1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    have hn : (Portable.pow value exponent).negative = false := by
      unfold Binary32.negative
      have hsmall : (Portable.pow value exponent).bits.toNat < 2^31 := by omega
      have high : (Portable.pow value exponent).bits &&& 0x80000000 = 0 := by
        apply UInt32.toNat.inj
        change (Portable.pow value exponent).bits.toNat &&& 2^31 = 0
        apply Nat.eq_of_testBit_eq
        intro index
        simp only [Nat.testBit_and, Nat.testBit_two_pow]
        by_cases he : index = 31
        · subst index
          simp [Nat.testBit_lt_two_pow hsmall]
        · simp [Ne.symm he]
      simp [high]
    simp only [Binary32.Finite, Binary32.key, hn, Bool.false_eq_true, ↓reduceIte, hm]
    omega
  · have hv : value = ⟨0x80000000⟩ := by cases value; simp_all
    rw [hv, pow_negative_zero]
    split
    · decide
    · split <;> decide
/-- Packing the three extracted binary64 fields reconstructs every original word. -/
theorem model_packComponents_unpack (word : UInt64) :
    packComponents Format.binary64 (Sign.ofBitVec (unpackSign (spec := Format.binary64) word.toBitVec))
      (unpackExponent (spec := Format.binary64) word.toBitVec) (unpackMantissa (spec := Format.binary64) word.toBitVec) = word.toBitVec := by
  have hs (bit : BitVec 1) : (Sign.ofBitVec bit).toBitVec = bit := by
    have hb := bit.isLt
    by_cases hz : bit = 0#1
    · rw [hz]
      rfl
    · have ho : bit = 1#1 := by
        apply BitVec.eq_of_toNat_eq
        have hp : bit.toNat ≠ 0 := by intro h; exact hz (BitVec.eq_of_toNat_eq h)
        change bit.toNat = 1
        omega
      rw [ho]
      rfl
  unfold packComponents
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  have hb := word.toNat_lt
  have hsign : (unpackSign (spec := Format.binary64) word.toBitVec).toNat = word.toNat / 2^63 := by
    change (word.toNat >>> 63) % 2 = _
    rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  have hexp : (unpackExponent (spec := Format.binary64) word.toBitVec).toNat = word.toNat / 2^52 % 2^11 := by
    change (word.toNat >>> 52) % 2^11 = _
    rw [Nat.shiftRight_eq_div_pow]
  have hfrac : (unpackMantissa (spec := Format.binary64) word.toBitVec).toNat = word.toNat % 2^52 := by
    change (word.toNat >>> 0) % 2^52 = _
    rw [Nat.shiftRight_zero]
  rw [BitVec.toNat_append, BitVec.toNat_append, hsign, hexp, hfrac]
  simp only [Nat.shiftLeft_eq]
  have he := Nat.mod_lt (word.toNat / 2^52) (Nat.two_pow_pos 11)
  have hf := Nat.mod_lt word.toNat (Nat.two_pow_pos 52)
  rw [Nat.mul_comm _ (2^11), ← Nat.two_pow_add_eq_or_of_lt he]
  rw [Nat.mul_comm _ (2^52), ← Nat.two_pow_add_eq_or_of_lt hf]
  change 2^52 * (2^11 * (word.toNat / 2^63) + word.toNat / 2^52 % 2^11) + word.toNat % 2^52 = word.toNat
  have hq : word.toNat / 2^52 / 2^11 = word.toNat / 2^63 := by rw [Nat.div_div_eq_div_mul]
  omega

/-- A raw normal binary64 word decodes to its exact sign, significand and exponent fields. -/
theorem model_unpack_normal_fields (word : UInt64)
    (lo : 0 < (unpackExponent (spec := Format.binary64) word.toBitVec).toNat)
    (hi : (unpackExponent (spec := Format.binary64) word.toBitVec).toNat < 2047) :
    unpack Format.binary64 word.toBitVec =
      .finite (Sign.ofBitVec (unpackSign (spec := Format.binary64) word.toBitVec))
        (2^52+(unpackMantissa (spec := Format.binary64) word.toBitVec).toNat)
        ((unpackExponent (spec := Format.binary64) word.toBitVec).toNat-1075)
        (by omega) := by
  let ev := unpackExponent (spec := Format.binary64) word.toBitVec
  let mv := unpackMantissa (spec := Format.binary64) word.toBitVec
  have hn : ev ≠ -1#11 := by
    intro h
    have ht := congrArg BitVec.toNat h
    change ev.toNat = 2047 at ht
    change ev.toNat < 2047 at hi
    omega
  have hz : ev ≠ 0#11 := by
    intro h
    have ht := congrArg BitVec.toNat h
    change ev.toNat = 0 at ht
    change 0 < ev.toNat at lo
    omega
  have hm : (1#1 ++ mv).toNat = 2^52+mv.toNat := by
    change 2^52 ||| mv.toNat = _
    rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt mv.isLt, Nat.add_comm]
  unfold unpack
  change (if ev = -1#11 then _ else if ev = 0#11 then _ else _) = _
  rw [if_neg hn, if_neg hz]
  congr 1

/-- Packing the decoded normal model preserves the complete source word. -/
theorem model_pack_unpack_normal_word (word : UInt64)
    (lo : 0 < (unpackExponent (spec := Format.binary64) word.toBitVec).toNat)
    (hi : (unpackExponent (spec := Format.binary64) word.toBitVec).toNat < 2047) :
    pack Format.binary64 (unpack Format.binary64 word.toBitVec) = word.toBitVec := by
  rw [model_unpack_normal_fields word lo hi]
  let ev := unpackExponent (spec := Format.binary64) word.toBitVec
  let mv := unpackMantissa (spec := Format.binary64) word.toBitVec
  have hm : 2^52+mv.toNat < 2^53 := by have h : mv.toNat < 2^52 := mv.isLt; omega
  have hl := model_mantissa_log (2^52+mv.toNat) (by omega) hm
  have hbiased : (((ev.toNat : Int)-1075)+Format.binary64.exponentBias+Format.binary64.mantissaBitsWithoutImplicit).toNat = ev.toNat := by
    change (((ev.toNat : Int)-1075)+1023+52).toNat = _
    omega
  change pack Format.binary64 (.finite _ (2^52+mv.toNat) ((ev.toNat : Int)-1075) _) = _
  unfold pack
  rw [hl, hbiased, if_neg (show ¬ 2^Format.binary64.exponentBits ≤ ev.toNat+1 by change ev.toNat < 2047 at hi; change ¬2048 ≤ ev.toNat+1; omega)]
  rw [if_pos (show 52+1 = Format.binary64.mantissaBits from rfl)]
  have heq : BitVec.ofNat 11 ev.toNat = ev := by apply BitVec.eq_of_toNat_eq; exact Nat.mod_eq_of_lt ev.isLt
  have mf : BitVec.ofNat 52 (2^52+mv.toNat) = mv := by
    apply BitVec.eq_of_toNat_eq
    change (2^52+mv.toNat) % 2^52 = mv.toNat
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt mv.isLt]
  rw [heq, mf]
  exact model_packComponents_unpack word

/-- Multiplying one by a normal model value preserves all significand and sign bits. -/
theorem binary64_one_mul_normal_model (sign : Sign) (m : Nat) (e : Int)
    (lo : 2^52 ≤ m) (hi : m < 2^53) (he : -1074 ≤ e) (he' : e ≤ 971) :
    (Binary64.ofUInt64 1).mul
      ⟨(Float.Model.pack (.finite sign m e (by omega))).toBits⟩ =
        ⟨(Float.Model.pack (.finite sign m e (by omega))).toBits⟩ := by
  have reencode : Float.Model.ofBits (Float.Model.pack (.finite sign m e (by omega))).toBits =
      Float.Model.pack (.finite sign m e (by omega)) := by
    change Float.Model.pack (unpack Format.binary64 (pack Format.binary64 _)) = _
    rw [model_unpack_pack_normal sign m e lo hi he he']
  have hu : (Float.Model.pack (.finite sign m e (by omega))).unpack = .finite sign m e (by omega) :=
    model_unpack_pack_normal sign m e lo hi he he'
  have hone : (Float.Model.ofBits (Float.Model.ofUInt64 1).toBits).unpack =
      .finite .positive (2^52) (-52) (by decide) := rfl
  change Binary64.mk (Float.Model.mul (Float.Model.ofBits (Float.Model.ofUInt64 1).toBits)
    (Float.Model.ofBits (Float.Model.pack (.finite sign m e _)).toBits)).toBits = _
  rw [reencode, Float.Model.mul, hu, hone]
  have hs : (Sign.positive*sign) = sign := by cases sign <;> rfl
  change Binary64.mk (Float.Model.pack (roundWithAccuracy Format.binary64 (.positive*sign) (2^52*m) (-52+e) .exact)).toBits = _
  rw [hs, Nat.mul_comm (2^52), show (-52:Int)+e = e-(52:Nat) by omega,
    model_round_scaled_exact sign m 52 e lo hi he]

/-- The actual native-boundary multiplication by one preserves every raw normal binary64 word. -/
theorem binary64_one_mul_normal (value : Binary64)
    (lo : 0 < (unpackExponent (spec := Format.binary64) value.bits.toBitVec).toNat)
    (hi : (unpackExponent (spec := Format.binary64) value.bits.toBitVec).toNat < 2047) :
    (Binary64.ofUInt64 1).mul value = value := by
  have hp := model_pack_unpack_normal_word value.bits lo hi
  rw [model_unpack_normal_fields value.bits lo hi] at hp
  have hbits : (Float.Model.pack (.finite (Sign.ofBitVec (unpackSign (spec := Format.binary64) value.bits.toBitVec))
    (2^52+(unpackMantissa (spec := Format.binary64) value.bits.toBitVec).toNat)
    ((unpackExponent (spec := Format.binary64) value.bits.toBitVec).toNat-1075) (by omega))).toBits = value.bits := by
    exact UInt64.toBitVec_inj.mp hp
  have hm : (unpackMantissa (spec := Format.binary64) value.bits.toBitVec).toNat < 2^52 :=
    (unpackMantissa (spec := Format.binary64) value.bits.toBitVec).isLt
  have result := binary64_one_mul_normal_model
    (Sign.ofBitVec (unpackSign (spec := Format.binary64) value.bits.toBitVec))
    (2^52+(unpackMantissa (spec := Format.binary64) value.bits.toBitVec).toNat)
    ((unpackExponent (spec := Format.binary64) value.bits.toBitVec).toNat-1075) (by omega) (by omega) (by omega) (by omega)
  rw [hbits] at result
  exact result
/-- The standard model and current raw recipe extract the same binary64 exponent bits. -/
theorem model_exponent_word (word : UInt64) :
    (unpackExponent (spec := Format.binary64) word.toBitVec).toNat = ((word >>> 52) &&& 0x7ff : UInt64).toNat := by
  change (word.toNat >>> 52) % 2^11 = (word.toNat >>> 52) &&& (2^11-1)
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- Actual multiplication by one preserves the widened word of every non-NaN binary32 source. -/
theorem binary64_one_mul_widen (value : Binary32) (notNan : value.isNaN = false) :
    (Binary64.ofUInt64 1).mul (Conversion.widen value) = Conversion.widen value := by
  by_cases finite : value.Finite
  · have hwide := Conversion.widen_finite value finite
    rcases Conversion.widen_normal_or_zero value finite with hz | hn
    · have hb := (Conversion.widen value).bits.toNat_lt
      change (Conversion.widen value).bits.toNat &&& (2^63-1) = 0 at hz
      rw [Nat.and_two_pow_sub_one_eq_mod] at hz
      have hc : (Conversion.widen value).bits.toNat = 0 ∨ (Conversion.widen value).bits.toNat = 2^63 := by omega
      rcases hc with h | h
      · have he : Conversion.widen value = ⟨0⟩ := congrArg Binary64.mk (UInt64.toNat.inj h)
        rw [he]
        exact mul_one_signed_zero false
      · have he : Conversion.widen value = ⟨0x8000000000000000⟩ := congrArg Binary64.mk (UInt64.toNat.inj h)
        rw [he]
        exact mul_one_signed_zero true
    · have hd := Conversion.fields64_decomposition (Conversion.widen value)
      have hf := Conversion.fraction64_bound (Conversion.widen value).bits
      change (Conversion.widen value).magnitude < 0x7ff0000000000000 at hwide
      apply binary64_one_mul_normal
      · rw [model_exponent_word]
        omega
      · rw [model_exponent_word]
        omega
  · have hm : value.magnitude = 0x7f800000 := by
      simp only [Binary32.isNaN_eq_magnitude, decide_eq_false_iff_not] at notNan
      unfold Binary32.Finite at finite
      omega
    have hw := value.bits.toNat_lt
    change value.bits.toNat &&& (2^31-1) = 0x7f800000 at hm
    rw [Nat.and_two_pow_sub_one_eq_mod] at hm
    have hc : value.bits.toNat = 0x7f800000 ∨ value.bits.toNat = 0xff800000 := by omega
    rcases hc with h | h
    · have he : value = ⟨0x7f800000⟩ := congrArg Binary32.mk (UInt32.toNat.inj h)
      rw [he]
      rfl
    · have he : value = ⟨0xff800000⟩ := congrArg Binary32.mk (UInt32.toNat.inj h)
      rw [he]
      rfl

/-- The public exponent-one power is bit-exactly the identity on every non-NaN binary32 word. -/
theorem pow_one_word (value : Binary32) (notNan : value.isNaN = false) :
    Portable.pow value 1 = value := by
  rw [Portable.pow_eq]
  change Conversion.narrow (Portable.powLoop (Binary64.ofUInt64 1) (Conversion.widen value) 1) = value
  rw [Portable.powLoop_step _ _ _ (by decide)]
  change Conversion.narrow (Portable.powLoop ((Binary64.ofUInt64 1).mul (Conversion.widen value)) _ 0) = value
  rw [Portable.powLoop_zero, binary64_one_mul_widen value notNan, Conversion.narrow_widen_nonNaN value notNan]
end AcornVerif.CurrentPower
