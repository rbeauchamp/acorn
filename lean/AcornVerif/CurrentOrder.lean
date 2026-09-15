/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentArithmetic
/-!
# Numerical interpretation and machine order

The pinned Lean 4.33.0 standard `UnpackedFloat` decoder defines the finite
numerical reading. A strictly increasing integer significand scale connects
that reading to the executing raw keys and comparisons, including signed zero.
Existing assembled conversion theorems supply exact widening and integer-value
links. Numerical claims require finite inputs; no exceptional payload or native
compiler correspondence is inferred from the total rational extension.
-/
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic

namespace AcornVerif.CurrentOrder

/-- Unsigned field interpretation in least-subnormal units, with the implicit bit derived from the
exponent field. -/
def fieldUnits (precision magnitude : Nat) : Nat :=
  let exponent := magnitude / 2^precision
  let fraction := magnitude % 2^precision
  if exponent = 0 then fraction else (2^precision+fraction)*2^(exponent-1)

/-- The unsigned interpretation sends zero to zero at every precision. -/
theorem fieldUnits_zero (precision : Nat) : fieldUnits precision 0 = 0 := by
  simp [fieldUnits]

/-- Unsigned encoding order is strictly preserved by the derived significand scale. -/
theorem fieldUnits_strict (precision left right : Nat) (ordered : left < right) :
    fieldUnits precision left < fieldUnits precision right := by
  let unit := 2^precision
  let le := left/unit
  let re := right/unit
  let lf := left%unit
  let rf := right%unit
  have positive : 0 < unit := Nat.two_pow_pos precision
  have lfBound : lf < unit := Nat.mod_lt _ positive
  have rfBound : rf < unit := Nat.mod_lt _ positive
  have ld : le*unit+lf=left := Nat.div_add_mod' left unit
  have rd : re*unit+rf=right := Nat.div_add_mod' right unit
  have exponents : le ≤ re := Nat.div_le_div_right (Nat.le_of_lt ordered)
  change (if le=0 then lf else (unit+lf)*2^(le-1)) <
    (if re=0 then rf else (unit+rf)*2^(re-1))
  by_cases same : le = re
  · rw [← same]
    rw [← same] at rd
    have fractions : lf < rf := by omega
    by_cases zero : le=0
    · simp only [zero, ↓reduceIte]
      exact fractions
    · simp only [if_neg zero]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
  · have gap : le < re := by omega
    have rnz : re ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) gap)
    rw [if_neg rnz]
    by_cases zero : le=0
    · rw [if_pos zero]
      calc
        lf < unit := lfBound
        _ ≤ unit+rf := Nat.le_add_right _ _
        _ ≤ (unit+rf)*2^(re-1) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    · rw [if_neg zero]
      have scale : 2^le ≤ 2^(re-1) := Nat.pow_le_pow_right (by decide) (by omega)
      have shift : 2^le = 2^(le-1)*2 := by
        have he : le = le-1+1 := by
          have hpositive : 0 < le := Nat.pos_of_ne_zero zero
          omega
        conv_lhs => rw [he, Nat.pow_succ]
      calc
        (unit+lf)*2^(le-1) < (2*unit)*2^(le-1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
        _ = unit*2^le := by rw [shift]; ring
        _ ≤ unit*2^(re-1) := Nat.mul_le_mul_left _ scale
        _ ≤ (unit+rf)*2^(re-1) := Nat.mul_le_mul_right _ (by omega)

/-- Unsigned numerical units and encoding magnitudes have exactly the same non-strict order. -/
theorem fieldUnits_order (precision left right : Nat) :
    fieldUnits precision left ≤ fieldUnits precision right ↔ left ≤ right := by
  exact (show StrictMono (fieldUnits precision) from
    fun _ _ h => fieldUnits_strict precision _ _ h).le_iff_le

/-- Positive encodings denote positive units, and zero is the only zero magnitude. -/
theorem fieldUnits_positive (precision magnitude : Nat) :
    0 < fieldUnits precision magnitude ↔ 0 < magnitude := by
  constructor
  · intro h
    by_cases hz : magnitude=0
    · rw [hz,fieldUnits_zero] at h
      omega
    · omega
  · intro h
    simpa only [fieldUnits_zero] using fieldUnits_strict precision 0 magnitude h

/-- The actual standard decoder agrees with the signed dyadic reading of finite exponent and
fraction fields. -/
theorem model_finite_fields_value (spec : Format) (bits : BitVec spec.numBits)
    (finite : (unpack spec bits).isFinite = true) :
    unpackedValue (unpack spec bits) =
      signCoefficient (Sign.ofBitVec (unpackSign bits)) *
      if (unpackExponent bits).toNat = 0 then
        (unpackMantissa bits).toNat * (2 : ℚ) ^ spec.minExponent
      else (2 ^ spec.mantissaBitsWithoutImplicit + (unpackMantissa bits).toNat : Nat) *
        (2 : ℚ) ^ ((unpackExponent bits).toNat - (spec.exponentBias +
          spec.mantissaBitsWithoutImplicit) : Int) := by
  let ev := unpackExponent bits
  let mv := unpackMantissa bits
  let sv := Sign.ofBitVec (unpackSign bits)
  have inf : ev ≠ -1#_ := by
    rw [model_unpack_finite_exponent, decide_eq_true_eq] at finite
    intro h
    change ev.toNat < _ at finite
    rw [h] at finite
    simp only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, Nat.lt_irrefl] at finite
  have unpackEq : unpack spec bits =
      (if ev=0#_ then if h : mv=0#_ then .zero sv else
        .finite sv mv.toNat (ev.toNat-(spec.exponentBias+spec.mantissaBitsWithoutImplicit)+1)
          (by simpa [BitVec.toNat_pos, BitVec.pos_iff_ne_zero])
      else .finite sv (1#1 ++ mv).toNat
        (ev.toNat-(spec.exponentBias+spec.mantissaBitsWithoutImplicit)) (by simp)) := by
    unfold unpack
    rw [if_neg inf]
  rw [unpackEq]
  change unpackedValue _ = signCoefficient sv *
    (if ev.toNat=0 then mv.toNat*(2:ℚ)^spec.minExponent
    else (2^spec.mantissaBitsWithoutImplicit+mv.toNat:Nat) *
      (2:ℚ)^(ev.toNat-(spec.exponentBias+spec.mantissaBitsWithoutImplicit):Int))
  by_cases ez : ev=0#_
  · have en : ev.toNat=0 := congrArg BitVec.toNat ez
    rw [if_pos ez, if_pos en]
    have exponent : (ev.toNat:Int)-(spec.exponentBias+spec.mantissaBitsWithoutImplicit)+1 =
        spec.minExponent := by
      have hb := model_format_min_bias spec
      rw [en]
      omega
    by_cases mz : mv=0#_
    · rw [dif_pos mz]
      have mn : mv.toNat=0 := congrArg BitVec.toNat mz
      simp only [unpackedValue,mn,Nat.cast_zero,zero_mul,mul_zero]
    · rw [dif_neg mz]
      simp only [unpackedValue,exponent]
      ring
  · have en : ev.toNat ≠ 0 := by
      intro h
      exact ez (BitVec.eq_of_toNat_eq h)
    rw [if_neg ez, if_neg en]
    have mantissa : (1#1 ++ mv).toNat=2^spec.mantissaBitsWithoutImplicit+mv.toNat := by
      simp only [BitVec.toNat_append, show (1#1).toNat=1 from rfl, Nat.shiftLeft_eq,Nat.one_mul]
      rw [Nat.or_comm,Nat.or_two_pow_eq_add_of_lt mv.isLt,Nat.add_comm]
    simp only [unpackedValue,mantissa]
    ring


/-- Assembling bounded fields recovers their exact unsigned unit interpretation. -/
theorem fieldUnits_fields (precision exponent fraction : Nat) (bound : fraction < 2 ^ precision) :
    fieldUnits precision (exponent * 2 ^ precision + fraction) =
      if exponent=0 then fraction else (2 ^ precision + fraction) * 2 ^ (exponent - 1) := by
  have positive := Nat.two_pow_pos precision
  have quotient : (exponent*2^precision+fraction)/2^precision=exponent := by
    simp [Nat.add_div,Nat.div_eq_of_lt bound,Nat.mod_lt _ positive]
  have remainder : (exponent*2^precision+fraction)%2^precision=fraction := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt bound]
  simp only [fieldUnits,quotient,remainder]

/-- The actual finite standard-model reading equals the integer field scale times the format
subnormal unit. -/
theorem model_finite_fieldUnits_value (spec : Format) (bits : BitVec spec.numBits)
    (finite : (unpack spec bits).isFinite = true) :
    unpackedValue (unpack spec bits) =
      signCoefficient (Sign.ofBitVec (unpackSign bits)) *
        (fieldUnits spec.mantissaBitsWithoutImplicit
          ((unpackExponent bits).toNat * 2 ^ spec.mantissaBitsWithoutImplicit +
            (unpackMantissa bits).toNat) : ℚ) * (2 : ℚ) ^ spec.minExponent := by
  rw [model_finite_fields_value spec bits finite]
  rw [fieldUnits_fields _ _ _ (unpackMantissa bits).isLt]
  by_cases zero : (unpackExponent bits).toNat=0
  · rw [if_pos zero,if_pos zero]
    ring
  · rw [if_neg zero,if_neg zero]
    have exponent : ((unpackExponent bits).toNat:Int)-
        (spec.exponentBias+spec.mantissaBitsWithoutImplicit) =
        spec.minExponent + (((unpackExponent bits).toNat-1:Nat):Int) := by
      have hb := model_format_min_bias spec
      omega
    rw [exponent,zpow_add₀ (by norm_num : (2:ℚ) ≠ 0),zpow_natCast]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring

/-- Every finite binary64 word has the exact signed rational value determined by its magnitude
fields. -/
theorem numerical64_fieldUnits (value : Binary64) (finite : value.Finite) :
    numerical64 value = signCoefficient (Sign.ofBitVec (unpackSign
      (spec := Format.binary64) value.bits.toBitVec)) *
      (fieldUnits 52 value.magnitude : ℚ) * (2:ℚ)^(-1074:Int) := by
  have proof := model_finite_fieldUnits_value Format.binary64 value.bits.toBitVec
    ((model_decoded64_finite value).mpr finite)
  have frac : (unpackMantissa (spec := Format.binary64) value.bits.toBitVec).toNat =
      (value.bits &&& 0xfffffffffffff).toNat := by
    change (value.bits.toNat >>> 0)%2^52 = value.bits.toNat &&& (2^52-1)
    rw [Nat.shiftRight_zero,Nat.and_two_pow_sub_one_eq_mod]
  rw [model_exponent_word,frac,←Conversion.fields64_decomposition value] at proof
  exact proof

/-- Every finite binary32 word has the exact signed rational value determined by its magnitude
fields. -/
theorem numerical32_fieldUnits (value : Binary32) (finite : value.Finite) :
    numerical32 value = signCoefficient (Sign.ofBitVec (unpackSign
      (spec := Format.binary32) value.bits.toBitVec)) *
      (fieldUnits 23 value.magnitude : ℚ) * (2:ℚ)^(-149:Int) := by
  have proof := model_finite_fieldUnits_value Format.binary32 value.bits.toBitVec
    ((model_decoded32_finite value).mpr finite)
  have exp : (unpackExponent (spec := Format.binary32) value.bits.toBitVec).toNat =
      ((value.bits >>> 23) &&& 0xff).toNat := by
    change (value.bits.toNat >>> 23)%2^8 = (value.bits.toNat >>> 23) &&& (2^8-1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have frac : (unpackMantissa (spec := Format.binary32) value.bits.toBitVec).toNat =
      (value.bits &&& 0x7fffff).toNat := by
    change (value.bits.toNat >>> 0)%2^23 = value.bits.toNat &&& (2^23-1)
    rw [Nat.shiftRight_zero,Nat.and_two_pow_sub_one_eq_mod]
  rw [exp,frac,←Conversion.fields32_decomposition value] at proof
  exact proof


/-- Signed extension of the strictly increasing magnitude scale, identifying both zero encodings.
-/
def signedFieldUnits (precision : Nat) (key : Int) : Int :=
  if key < 0 then -(fieldUnits precision key.natAbs : Int)
  else fieldUnits precision key.toNat

/-- The signed scale commutes with attaching either sign to any magnitude, including zero. -/
theorem signedFieldUnits_sign (precision magnitude : Nat) (negative : Bool) :
    signedFieldUnits precision (if negative then - (magnitude : Int) else magnitude) =
      if negative then - (fieldUnits precision magnitude : Int) else fieldUnits precision
        magnitude := by
  cases negative with
  | false => simp [signedFieldUnits]
  | true =>
    by_cases hz : magnitude=0
    · simp [hz,signedFieldUnits,fieldUnits_zero]
    · have hn : -(magnitude:Int) < 0 := by omega
      change (if -(magnitude:Int)<0 then -(fieldUnits precision (-(magnitude:Int)).natAbs:Int)
        else fieldUnits precision (-(magnitude:Int)).toNat) = -(fieldUnits precision magnitude:Int)
      rw [if_pos hn]
      simp only [Int.natAbs_neg,Int.natAbs_natCast]

/-- The signed unit interpretation is strictly increasing over every integer key. -/
theorem signedFieldUnits_strict (precision : Nat) (left right : Int) (ordered : left < right) :
    signedFieldUnits precision left < signedFieldUnits precision right := by
  cases left with
  | ofNat left =>
    cases right with
    | ofNat right =>
      change (left:Int) < right at ordered
      have ho : left < right := by omega
      simpa [signedFieldUnits,Int.ofNat_eq_natCast,
        not_lt_of_ge (Int.natCast_nonneg left), not_lt_of_ge (Int.natCast_nonneg right)] using
          (show (fieldUnits precision left : Int) <
        fieldUnits precision right from by exact_mod_cast fieldUnits_strict precision left right ho)
    | negSucc right =>
      change (left:Int) < -(right+1:Int) at ordered
      omega
  | negSucc left =>
    cases right with
    | ofNat right =>
      have positive : 0 < fieldUnits precision (left+1) :=
        (fieldUnits_positive precision (left+1)).mpr (by omega)
      have nonnegative : 0 ≤ (fieldUnits precision right : Int) := Int.natCast_nonneg _
      simpa [signedFieldUnits,Int.ofNat_eq_natCast,not_lt_of_ge (Int.natCast_nonneg right)] using
        (show -(fieldUnits precision (left+1):Int) < fieldUnits precision right from by omega)
    | negSucc right =>
      have ho : right+1 < left+1 := by omega
      have h := fieldUnits_strict precision (right+1) (left+1) ho
      simpa [signedFieldUnits,Int.ofNat_eq_natCast] using
        (show -(fieldUnits precision (left+1):Int) <
          -(fieldUnits precision (right+1):Int) from by omega)

/-- Signed units and raw signed keys induce the same non-strict order. -/
theorem signedFieldUnits_order (precision : Nat) (left right : Int) :
    signedFieldUnits precision left ≤ signedFieldUnits precision right ↔ left ≤ right := by
  exact (show StrictMono (signedFieldUnits precision) from
    fun _ _ h => signedFieldUnits_strict precision _ _ h).le_iff_le

/-- The standard binary64 sign decoder agrees with the executing raw sign mask. -/
theorem model_word64_sign (word : UInt64) :
    Sign.ofBitVec (unpackSign (spec := Format.binary64) word.toBitVec) =
      if word &&& 0x8000000000000000 != 0 then .negative else .positive := by
  have hs := word64_sign_exact word
  have high : (unpackSign (spec := Format.binary64) word.toBitVec).toNat = word.toNat/2^63 := by
    have hb := word.toNat_lt
    change (word.toNat >>> 63)%2 = word.toNat/2^63
    rw [Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt (by omega)]
  by_cases zero : word &&& 0x8000000000000000 = 0
  · have hn := congrArg UInt64.toNat zero
    rw [hs] at hn
    change (word.toNat/2^63)*2^63=0 at hn
    have hv : unpackSign (spec := Format.binary64) word.toBitVec=0#1 := by
      apply BitVec.eq_of_toNat_eq
      rw [high]
      change word.toNat/2^63=0
      omega
    simp [Sign.ofBitVec,hv,zero]
  · have hv : unpackSign (spec := Format.binary64) word.toBitVec ≠ 0#1 := by
      intro h
      have hn := congrArg BitVec.toNat h
      rw [high] at hn
      have hzero : word &&& 0x8000000000000000 = 0 := by
        apply UInt64.toNat.inj
        rw [hs]
        change (word.toNat/2^63)*2^63=0
        change word.toNat/2^63=0 at hn
        simp only [hn,Nat.zero_mul]
      contradiction
    simp [Sign.ofBitVec,hv,zero]

/-- Every finite binary64 numerical reading is the signed key interpretation at the exact
subnormal scale. -/
theorem numerical64_key_units (value : Binary64) (finite : value.Finite) :
    numerical64 value = (signedFieldUnits 52 value.key : ℚ) * (2 : ℚ) ^ ( - 1074 : Int) := by
  rw [numerical64_fieldUnits value finite,model_word64_sign]
  unfold Binary64.key
  rw [signedFieldUnits_sign]
  cases h : value.bits &&& 0x8000000000000000 != 0 <;>
    simp only [Bool.false_eq_true,↓reduceIte,signCoefficient,Int.cast_natCast,Int.cast_neg]
  · ring
  · ring

/-- Numerical and executing key order agree for every pair of finite binary64 words. -/
theorem numerical64_order (left right : Binary64) (leftFinite : left.Finite) (rightFinite :
  right.Finite) :
    numerical64 left ≤ numerical64 right ↔ left.key ≤ right.key := by
  rw [numerical64_key_units left leftFinite,numerical64_key_units right rightFinite]
  rw [mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0:ℚ)<2) _)]
  rw [Int.cast_le,signedFieldUnits_order]


/-- The binary32 sign mask extracts exactly the top bit as a word magnitude. -/
theorem word32_sign_exact (word : UInt32) :
    ((word &&& 0x80000000) : UInt32).toNat=(word.toNat / 2 ^ 31) * 2 ^ 31 := by
  have hb := word.toNat_lt
  change word.toNat &&& 2^31 = _
  have hq : word.toNat/2^31 < 2 := by omega
  have hd : (word.toNat &&& 2^31)/2^31=word.toNat/2^31 := by
    rw [Nat.and_div_two_pow,Nat.div_self (Nat.two_pow_pos 31)]
    change word.toNat/2^31 &&& (2^1-1)=_
    rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt hq]
  have hm : (word.toNat &&& 2^31)%2^31=0 := by
    rw [Nat.and_mod_two_pow,Nat.mod_self,Nat.and_zero]
  omega

/-- The standard binary32 sign decoder agrees with the executing raw sign mask. -/
theorem model_word32_sign (word : UInt32) :
    Sign.ofBitVec (unpackSign (spec := Format.binary32) word.toBitVec) =
      if word &&& 0x80000000 != 0 then .negative else .positive := by
  have hs := word32_sign_exact word
  have high : (unpackSign (spec := Format.binary32) word.toBitVec).toNat = word.toNat/2^31 := by
    have hb := word.toNat_lt
    change (word.toNat >>> 31)%2 = word.toNat/2^31
    rw [Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt (by omega)]
  by_cases zero : word &&& 0x80000000 = 0
  · have hn := congrArg UInt32.toNat zero
    rw [hs] at hn
    change (word.toNat/2^31)*2^31=0 at hn
    have hv : unpackSign (spec := Format.binary32) word.toBitVec=0#1 := by
      apply BitVec.eq_of_toNat_eq
      rw [high]
      change word.toNat/2^31=0
      omega
    simp [Sign.ofBitVec,hv,zero]
  · have hv : unpackSign (spec := Format.binary32) word.toBitVec ≠ 0#1 := by
      intro h
      have hn := congrArg BitVec.toNat h
      rw [high] at hn
      have hzero : word &&& 0x80000000 = 0 := by
        apply UInt32.toNat.inj
        rw [hs]
        change (word.toNat/2^31)*2^31=0
        change word.toNat/2^31=0 at hn
        simp only [hn,Nat.zero_mul]
      contradiction
    simp [Sign.ofBitVec,hv,zero]

/-- Every finite binary32 numerical reading is the signed key interpretation at the exact
subnormal scale. -/
theorem numerical32_key_units (value : Binary32) (finite : value.Finite) :
    numerical32 value = (signedFieldUnits 23 value.key : ℚ) * (2 : ℚ) ^ ( - 149 : Int) := by
  rw [numerical32_fieldUnits value finite,model_word32_sign]
  unfold Binary32.key
  rw [signedFieldUnits_sign]
  change _ = (if value.bits &&& 0x80000000 != 0 then -(fieldUnits 23 value.magnitude:Int)
    else fieldUnits 23 value.magnitude)*(2:ℚ)^(-149:Int)
  cases h : value.bits &&& 0x80000000 != 0 <;>
    simp only [Bool.false_eq_true,↓reduceIte,signCoefficient,Int.cast_natCast,Int.cast_neg]
  · ring
  · ring

/-- Numerical and executing key order agree for every pair of finite binary32 words. -/
theorem numerical32_order (left right : Binary32) (leftFinite : left.Finite) (rightFinite :
  right.Finite) :
    numerical32 left ≤ numerical32 right ↔ left.key ≤ right.key := by
  rw [numerical32_key_units left leftFinite,numerical32_key_units right rightFinite]
  rw [mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0:ℚ)<2) _)]
  rw [Int.cast_le,signedFieldUnits_order]

/-- Finite binary64 strict numerical order agrees with the raw key comparison. -/
theorem numerical64_strict_order (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) : numerical64 left < numerical64 right ↔ left.key < right.key := by
  rw [←not_le,←not_le,(numerical64_order right left rightFinite leftFinite)]

/-- Finite binary32 strict numerical order agrees with the raw key comparison. -/
theorem numerical32_strict_order (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) : numerical32 left < numerical32 right ↔ left.key < right.key := by
  rw [←not_le,←not_le,(numerical32_order right left rightFinite leftFinite)]

/-- The actual binary64 comparison computes strict numerical order on all finite encodings. -/
theorem numerical64_less (left right : Binary64) (leftFinite : left.Finite) (rightFinite :
  right.Finite) :
    left.less right = decide (numerical64 left < numerical64 right) := by
  have ln : left.isNaN=false := by
    change decide (0x7ff0000000000000<left.magnitude)=false
    change left.magnitude<0x7ff0000000000000 at leftFinite
    simp only [decide_eq_false_iff_not]
    omega
  have rn : right.isNaN=false := by
    change decide (0x7ff0000000000000<right.magnitude)=false
    change right.magnitude<0x7ff0000000000000 at rightFinite
    simp only [decide_eq_false_iff_not]
    omega
  simp only [Binary64.less_eq_key,ln,rn,Bool.not_false,Bool.true_and]
  simp only [numerical64_strict_order left right leftFinite rightFinite]

/-- The actual binary32 comparison computes strict numerical order on all finite encodings. -/
theorem numerical32_less (left right : Binary32) (leftFinite : left.Finite) (rightFinite :
  right.Finite) :
    left.less right = decide (numerical32 left < numerical32 right) := by
  simp only [Binary32.less_eq_key,Binary32.finite_not_nan left leftFinite,
    Binary32.finite_not_nan right rightFinite,Bool.not_false,Bool.true_and]
  simp only [numerical32_strict_order left right leftFinite rightFinite]


set_option exponentiation.threshold 2048 in
/-- The shared conversion scale is exactly the binary32 least-subnormal scale multiplied by 2^925.
-/
theorem magnitudeUnits32_fieldUnits (value : Binary32) :
    Conversion.magnitudeUnits32 value = fieldUnits 23 value.magnitude * 2 ^ 925 := by
  dsimp only [Conversion.magnitudeUnits32,fieldUnits]
  split
  · rfl
  · rename_i nonzero
    have exponent : value.magnitude/2^23+924 = value.magnitude/2^23-1+925 := by omega
    rw [exponent,Nat.pow_add,Nat.mul_assoc]

/-- The finite binary64 reading agrees with the conversion module integer magnitude units and
exact sign. -/
theorem numerical64_units (value : Binary64) (finite : value.Finite) :
    numerical64 value = signCoefficient (Sign.ofBitVec (unpackSign
      (spec := Format.binary64) value.bits.toBitVec)) *
      (Conversion.magnitudeUnits64 value : ℚ) * (2:ℚ)^(-1074:Int) :=
  numerical64_fieldUnits value finite

/-- The finite binary32 reading agrees with the conversion module shared integer units and exact
sign. -/
theorem numerical32_units (value : Binary32) (finite : value.Finite) :
    numerical32 value = signCoefficient (Sign.ofBitVec (unpackSign
      (spec := Format.binary32) value.bits.toBitVec)) *
      (Conversion.magnitudeUnits32 value : ℚ) * (2:ℚ)^(-1074:Int) := by
  rw [numerical32_fieldUnits value finite,magnitudeUnits32_fieldUnits]
  have power : (2:ℚ)^925*(2:ℚ)^(-1074:Int)=(2:ℚ)^(-149:Int) := by
    rw [←zpow_natCast,←zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
    congr 1
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  simp only [mul_assoc,power]

/-- Actual widening preserves the complete finite signed dyadic value, including either zero sign.
-/
theorem numerical_widen_exact (value : Binary32) (finite : value.Finite) :
    numerical64 (Conversion.widen value)=numerical32 value := by
  rw [numerical64_units _ (Conversion.widen_finite value finite),numerical32_units value finite,
    Conversion.widen_magnitude_exact value finite]
  have signs : unpackSign (spec := Format.binary64) (Conversion.widen value).bits.toBitVec =
      unpackSign (spec := Format.binary32) value.bits.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    change ((Conversion.widen value).bits.toNat >>> 63)%2=(value.bits.toNat >>> 31)%2
    simp only [Nat.shiftRight_eq_div_pow]
    rw [Conversion.widen_sign value finite]
  rw [signs]

/-- Either sign has the same nonnegative dyadic magnitude, including a zero significand. -/
theorem sign_dyadic_abs (sign : Sign) (mantissa : Nat) (exponent : Int) :
    |signCoefficient sign * mantissa * (2 : ℚ) ^ exponent| = mantissa * (2 : ℚ) ^ exponent := by
  have positive : (0:ℚ) ≤ (mantissa:ℚ)*(2:ℚ)^exponent :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _))
  cases sign <;> simp only [signCoefficient,one_mul,neg_mul,abs_neg] <;>
    exact abs_of_nonneg positive

/-- Finite binary64 absolute value is exactly its unsigned magnitude scale. -/
theorem numerical64_abs_units (value : Binary64) (finite : value.Finite) :
    |numerical64 value|=(fieldUnits 52 value.magnitude : ℚ) * (2 : ℚ) ^ ( - 1074 : Int) := by
  rw [numerical64_fieldUnits value finite]
  exact sign_dyadic_abs _ _ _

/-- Finite binary32 absolute value is exactly its unsigned magnitude scale. -/
theorem numerical32_abs_units (value : Binary32) (finite : value.Finite) :
    |numerical32 value|=(fieldUnits 23 value.magnitude : ℚ) * (2 : ℚ) ^ ( - 149 : Int) := by
  rw [numerical32_fieldUnits value finite]
  exact sign_dyadic_abs _ _ _

/-- Absolute numerical order agrees with raw magnitude order for finite binary64 encodings. -/
theorem numerical64_magnitude_order (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    |numerical64 left| ≤ |numerical64 right| ↔ left.magnitude ≤ right.magnitude := by
  rw [numerical64_abs_units left leftFinite,numerical64_abs_units right rightFinite]
  rw [mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0:ℚ)<2) _),Nat.cast_le,fieldUnits_order]

/-- Absolute numerical order agrees with raw magnitude order for finite binary32 encodings. -/
theorem numerical32_magnitude_order (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite) :
    |numerical32 left| ≤ |numerical32 right| ↔ left.magnitude ≤ right.magnitude := by
  rw [numerical32_abs_units left leftFinite,numerical32_abs_units right rightFinite]
  rw [mul_le_mul_iff_left₀ (zpow_pos (by norm_num : (0:ℚ)<2) _),Nat.cast_le,fieldUnits_order]

/-- The actual signed conversion denotes the exact source integer throughout the 53-bit magnitude
domain. -/
theorem numerical64_ofInt (value : Int) (bound : value.natAbs < 2 ^ 53) :
    numerical64 (Conversion.ofInt value) = value := by
  rw [numerical64_units _ (ofInt_finite value bound),ofInt_magnitude_exact value bound,
    model_word64_sign,ofInt_sign value bound]
  have power : (2:ℚ)^1074*(2:ℚ)^(-1074:Int)=1 := by
    rw [←zpow_natCast,←zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
    rfl
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [mul_assoc,mul_assoc,power,mul_one]
  by_cases negative : value<0
  · simp only [negative,decide_true,↓reduceIte,signCoefficient]
    have habs : (value.natAbs:Int) = -value := (Int.ofNat_natAbs_of_nonpos (by omega))
    have hcast : (value.natAbs:ℚ)=-(value:ℚ) := by
      have hc := congrArg (fun n:Int => (n:ℚ)) habs
      simpa only [Int.cast_natCast,Int.cast_neg] using hc
    rw [hcast]
    ring
  · simp only [negative,decide_false,Bool.false_eq_true,↓reduceIte,signCoefficient,one_mul]
    have hc := congrArg (fun n:Int => (n:ℚ)) (Int.natAbs_of_nonneg (by omega : 0 ≤ value))
    simpa only [Int.cast_natCast] using hc

/-- The actual unsigned conversion denotes the exact source integer throughout the 53-bit domain.
-/
theorem numerical64_ofUInt64 (word : UInt64) (bound : word.toNat < 2 ^ 53) :
    numerical64 (Binary64.ofUInt64 word) = word.toNat := by
  have signed : Conversion.ofInt (word.toNat:Int)=Binary64.ofUInt64 word := by
    simp [Conversion.ofInt,not_lt_of_ge (Int.natCast_nonneg word.toNat),Binary64.ofUInt64]
  have hp := numerical64_ofInt (word.toNat:Int) (by simpa using bound)
  rw [signed] at hp
  exact hp
end AcornVerif.CurrentOrder
