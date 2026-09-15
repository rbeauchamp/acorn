/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Rng
import Acorn.Conversion
/-!
# Exact small-integer conversions and floating RNG observations

The proofs unfold the standard logical definitions in Lean 4.33.0's
`Init/Data/Float/Model/{Float,Unpacked/Round,Unpacked/Pack/Basic}.lean` and
`Unpacked/Operations/{OfNat,Mul}.lean`. Normalization, zero-filled shifts and
field packing are proved algebraically, without enumerating machine inputs.
The final theorems concern the actual `Acorn.Rng.Fraction53.toBinary64` and
`Xoshiro256.nextF64` definitions, including their standard conversion/multiply.
Unsigned and signed small-integer conversions share those exact normalization
lemmas. The signed-32-bit conversion pair is proved exact throughout its full
admitted domain. Native primitive/compiler correspondence remains the arithmetic layer's trust
boundary; the kernel proof does not verify C or establish an IID RNG law.
-/

namespace AcornVerif.CurrentFloat
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
/-- A normal binary64 significand has leading-bit index 52. -/
theorem model_mantissa_log (mantissa : Nat) (lower : 2^52 ≤ mantissa) (upper : mantissa < 2^53) :
    mantissa.log2 = 52 := (Nat.log2_eq_iff (by omega)).mpr ⟨lower, upper⟩
/-- A normalized significand above the subnormal floor keeps its exponent. -/
theorem model_normal_target (mantissa : Nat) (exponent : Int) (hlog : mantissa.log2 = 52)
    (he : -1074 ≤ exponent) : Format.binary64.targetExponent (totalExponent mantissa exponent) = exponent := by
  simp only [Format.targetExponent, totalExponent, hlog, Format.mantissaBits,
    Format.minExponent]
  omega
/-- The executing rounding model preserves an already normalized exact input. -/
theorem model_round_fixed (sign : Sign) (mantissa : Nat) (exponent : Int) (hpos : 0 < mantissa)
    (ht : Format.binary64.targetExponent (totalExponent mantissa exponent) = exponent) :
    roundWithAccuracy Format.binary64 sign mantissa exponent .exact =
      .finite sign mantissa exponent hpos := by
  have hshift (m : ExtendedMantissa) : m >>> (0 : Nat) = m := rfl
  simp [hshift, roundWithAccuracy, shiftToTargetExponent, ht, shiftToExponent,
    ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, Nat.ne_of_gt hpos]
/-- Left normalization fills the 53-bit significand without discarding bits. -/
theorem model_scaled_mantissa (n k : Nat) (lo : 2^k ≤ n) (hi : n < 2^(k+1))
    (hk : k ≤ 52) :
    2^52 ≤ n * 2^(52-k) ∧ n * 2^(52-k) < 2^53 := by
  have hlo := Nat.mul_le_mul_right (2^(52-k)) lo
  have hhi := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos (52-k))
  rw [← Nat.pow_add] at hlo hhi
  have ha : k + (52-k) = 52 := by omega
  have hb : k+1+(52-k) = 53 := by omega
  simpa only [ha, hb] using And.intro hlo hhi
/-- Every positive integer of at most 53 bits normalizes exactly. -/
theorem model_round_small_nat (n k : Nat) (lo : 2^k ≤ n) (hi : n < 2^(k+1)) (hk : k ≤ 52) :
    round Format.binary64 .positive n 0 =
      .finite .positive (n * 2^(52-k)) ((k : Int)-52)
        (by have := (model_scaled_mantissa n k lo hi hk).1; omega) := by
  have hpos : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos k) lo
  have hl : n.log2 = k := (Nat.log2_eq_iff (by omega)).mpr ⟨lo, hi⟩
  have ht : Format.binary64.targetExponent (totalExponent n 0) = (k : Int)-52 := by
    simp only [Format.targetExponent, totalExponent, hl, Format.mantissaBits, Format.minExponent]
    omega
  have hshift : (0 - ((k : Int)-52)).toNat = 52-k := by omega
  have hnext : (0 : Int) - ↑(52-k) = (k : Int)-52 := by omega
  simp only [round, ht, decreaseExponent, hshift, hnext]
  rw [Nat.shiftLeft_eq]
  apply model_round_fixed .positive
  apply model_normal_target
  · exact model_mantissa_log _ (model_scaled_mantissa n k lo hi hk).1
      (model_scaled_mantissa n k lo hi hk).2
  · omega
/-- Packing and unpacking a finite normal value preserves its exact components. -/
theorem model_unpack_pack_normal (sign : Sign) (m : Nat) (e : Int) (lo : 2^52 ≤ m) (hi : m < 2^53)
    (he : -1074 ≤ e) (he' : e ≤ 971) :
    unpack Format.binary64 (pack Format.binary64 (.finite sign m e (by omega))) =
      .finite sign m e (by omega) := by
  have hl := model_mantissa_log m lo hi
  have hb : 0 < (e+1075).toNat ∧ (e+1075).toNat < 2047 := by omega
  have hn : ¬ 2 ^ Format.binary64.exponentBits ≤
      (e + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    change ¬ 2048 ≤ (e + 1023 + 52).toNat + 1
    omega
  simp only [pack, if_neg hn, hl]
  rw [if_pos (show 52 + 1 = Format.binary64.mantissaBits from rfl)]
  simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents]
  have hsign (ee : BitVec 11) (mm : BitVec 52) :
      unpackSign (packComponents Format.binary64 sign ee mm) = sign.toBitVec := by
    change (sign.toBitVec ++ ee ++ mm).extractLsb' 63 1 = sign.toBitVec
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    cases sign <;> rfl
  rw [hsign]
  have hbe : (BitVec.ofNat 11 (e + ↑Format.binary64.exponentBias + ↑52).toNat).toNat =
      (e+1075).toNat := by
    change (e+1023+52).toNat % 2048 = (e+1075).toNat
    omega
  have hne : BitVec.ofNat 11 (e + ↑Format.binary64.exponentBias + ↑52).toNat ≠ 2047#11 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [hbe] at this
    change (e+1075).toNat = 2047 at this
    omega
  have hnz : BitVec.ofNat 11 (e + ↑Format.binary64.exponentBias + ↑52).toNat ≠ 0#11 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [hbe] at this
    change (e+1075).toNat = 0 at this
    omega
  have hm : (1#1 ++ BitVec.ofNat 52 m).toNat = m := by
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    change 2^52 ||| (m % 2^52) = m
    rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt m (Nat.two_pow_pos 52))]
    omega
  have heq2 : max (e+1075) 0 - (↑Format.binary64.exponentBias + 52) = e := by
    change max (e+1075) 0 - (1023+52) = e
    omega
  have hs : Sign.ofBitVec sign.toBitVec = sign := by cases sign <;> rfl
  simp [hne, hnz, hbe, hm, heq2, hs]
/-- Any finite number of zero-filled right shifts is exact, including residual bits. -/
theorem model_shift_exact (m shift : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy (m*2^shift) .exact >>> shift) =
      ExtendedMantissa.ofMantissaAndAccuracy m .exact := by
  induction shift generalizing m with
  | zero => simp [ExtendedMantissa.ofMantissaAndAccuracy]; rfl
  | succ shift ih =>
    change Nat.repeat ExtendedMantissa.shiftRightOne (shift+1) _ = _
    rw [Nat.repeat]
    change ExtendedMantissa.shiftRightOne
      (ExtendedMantissa.ofMantissaAndAccuracy (m*2^(shift+1)) .exact >>> shift) = _
    have hp : m*2^(shift+1) = (m*2)*2^shift := by
      rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_assoc]
    rw [hp, ih]
    simp [ExtendedMantissa.shiftRightOne, ExtendedMantissa.ofMantissaAndAccuracy]
/-- Multiplication by a power of two shifts the leading-bit index by that exponent. -/
theorem model_log2_scaled (m shift : Nat) (lo : 2^52 ≤ m) (hi : m < 2^53) :
    (m*2^shift).log2 = 52+shift := by
  have hpos : m*2^shift ≠ 0 := by
    have := Nat.mul_pos (show 0 < m by omega) (Nat.two_pow_pos shift)
    omega
  apply (Nat.log2_eq_iff hpos).mpr
  have hl := Nat.mul_le_mul_right (2^shift) lo
  have hh := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos shift)
  rw [← Nat.pow_add] at hl hh
  have h : 52+shift+1 = 53+shift := by omega
  simpa only [h] using And.intro hl hh
/-- The actual rounding model drops a zero-filled scale without rounding error. -/
theorem model_round_scaled_exact (sign : Sign) (m shift : Nat) (e : Int) (lo : 2^52 ≤ m) (hi : m < 2^53)
    (he : -1074 ≤ e) :
    roundWithAccuracy Format.binary64 sign (m*2^shift) (e-shift) .exact =
      .finite sign m e (by omega) := by
  have hl := model_log2_scaled m shift lo hi
  have ht : Format.binary64.targetExponent (totalExponent (m*2^shift) (e-shift)) = e := by
    simp only [Format.targetExponent, totalExponent, hl, Format.mantissaBits, Format.minExponent]
    omega
  have hs : shiftToTargetExponent Format.binary64 (m*2^shift) (e-shift) .exact =
      (ExtendedMantissa.ofMantissaAndAccuracy m .exact, e) := by
    simp only [shiftToTargetExponent, ht, shiftToExponent]
    have hdelta : (e-(e-shift)).toNat = shift := by omega
    rw [hdelta, model_shift_exact]
    congr 1
    omega
  have htarget := model_normal_target m e (model_mantissa_log m lo hi) he
  have hshift (a : ExtendedMantissa) : a >>> (0 : Nat) = a := rfl
  rw [roundWithAccuracy, hs]
  simp [ExtendedMantissa.ofMantissaAndAccuracy,
    ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
    Accuracy.roundToNearestEven, shiftToTargetExponent, htarget, shiftToExponent,
    hshift, show m ≠ 0 by omega]
/-- The standard UInt64 conversion has exact normal components below 2^53. -/
theorem model_ofUInt64_small (word : UInt64) (k : Nat) (lo : 2^k ≤ word.toNat)
    (hi : word.toNat < 2^(k+1)) (hk : k ≤ 52) :
    Float.Model.ofUInt64 word = Float.Model.pack
      (.finite .positive (word.toNat * 2^(52-k)) ((k : Int)-52)
        (by have := (model_scaled_mantissa word.toNat k lo hi hk).1; omega)) := by
  have hpos : 0 < word.toNat := Nat.lt_of_lt_of_le (Nat.two_pow_pos k) lo
  have hc : compare (word.toNat : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  simp only [Float.Model.ofUInt64, ofUInt64, ofNat, ofInt, normalize, hc, Int.toNat_natCast]
  rw [model_round_small_nat word.toNat k lo hi hk]
/-- Bit reinterpretation preserves every admitted normal model word. -/
theorem model_reencode_normal (m : Nat) (e : Int) (lo : 2^52 ≤ m) (hi : m < 2^53)
    (he : -1074 ≤ e) (he' : e ≤ 971) :
    Float.Model.ofBits (Float.Model.pack (.finite .positive m e (by omega))).toBits =
      Float.Model.pack (.finite .positive m e (by omega)) := by
  change Float.Model.pack (unpack Format.binary64 (pack Format.binary64 _)) = _
  rw [model_unpack_pack_normal .positive m e lo hi he he']
/-- The actual binary64 multiplication by 2^-53 is exact on the stated normal domain. -/
theorem model_mul_fraction_scale (m : Nat) (e : Int) (lo : 2^52 ≤ m) (hi : m < 2^53)
    (he : -1021 ≤ e) (he' : e ≤ 971) :
    Float.Model.mul (Float.Model.pack (.finite .positive m e (by omega)))
      (Float.Model.ofBits 0x3ca0000000000000) =
      Float.Model.pack (.finite .positive m (e-53) (by omega)) := by
  have hu : (Float.Model.pack (.finite .positive m e (by omega))).unpack =
      .finite .positive m e (by omega) :=
    model_unpack_pack_normal .positive m e lo hi (by omega) he'
  have hc : (Float.Model.ofBits 0x3ca0000000000000).unpack =
      .finite .positive (2^52) (-105) (by decide) := by rfl
  rw [Float.Model.mul, hu, hc]
  change Float.Model.pack (roundWithAccuracy Format.binary64 .positive (m*2^52)
    (e + (-105)) .exact) = _
  have heq : e + (-105) = (e-53) - (52 : Nat) := by omega
  rw [heq, model_round_scaled_exact .positive m 52 (e-53) lo hi (by omega)]
/-- The RNG observation has the exact normalized components of its retained numerator. -/
theorem fraction_model_word (fraction : Rng.Fraction53) (k : Nat) (lo : 2^k ≤ fraction.numerator.toNat)
    (hi : fraction.numerator.toNat < 2^(k+1)) (hk : k ≤ 52) :
    fraction.toBinary64.bits = (Float.Model.pack
      (.finite .positive (fraction.numerator.toNat * 2^(52-k)) ((k : Int)-105)
        (by have := (model_scaled_mantissa fraction.numerator.toNat k lo hi hk).1; omega))).toBits := by
  simp only [Rng.Fraction53.toBinary64, Binary64.mul, Binary64.ofUInt64, UInt64.toFloat,
    Float.toBits, Float.ofBits, Float.mul]
  rw [model_ofUInt64_small fraction.numerator k lo hi hk]
  have hb := model_scaled_mantissa fraction.numerator.toNat k lo hi hk
  rw [model_reencode_normal _ _ hb.1 hb.2 (by omega) (by omega)]
  change (Float.Model.mul _ _).toBits = _
  rw [model_mul_fraction_scale _ _ hb.1 hb.2 (by omega) (by omega)]
  have heq : (k : Int)-52-53 = k-105 := by omega
  rw [heq]
/-- A positive normal model value packs into nonoverlapping exponent and fraction fields. -/
theorem model_pack_word (m : Nat) (e : Int) (lo : 2^52 ≤ m) (hi : m < 2^53)
    (he : -1074 ≤ e) (he' : e ≤ 971) :
    (Float.Model.pack (.finite .positive m e (by omega))).toBits.toNat =
      (e+1075).toNat * 2^52 + m % 2^52 := by
  have hl := model_mantissa_log m lo hi
  have hb : 0 < (e+1075).toNat ∧ (e+1075).toNat < 2047 := by omega
  have hn : ¬ 2 ^ Format.binary64.exponentBits ≤
      (e + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat + 1 := by
    change ¬ 2048 ≤ (e + 1023 + 52).toNat + 1
    omega
  change (pack Format.binary64 (.finite .positive m e (by omega))).toNat = _
  simp only [pack, if_neg hn, hl]
  rw [if_pos (show 52 + 1 = Format.binary64.mantissaBits from rfl)]
  change (0#1 ++ BitVec.ofNat 11 (e+1023+52).toNat ++ BitVec.ofNat 52 m).toNat = _
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hm : m % 2^52 < 2^52 := Nat.mod_lt m (Nat.two_pow_pos 52)
  have heq : (e+1023+52).toNat % 2048 = (e+1075).toNat := by omega
  change ((0 * 2^11 ||| ((e+1023+52).toNat % 2048))*2^52 ||| (m % 2^52)) = _
  rw [Nat.zero_mul, Nat.zero_or, heq, Nat.mul_comm]
  exact (Nat.two_pow_add_eq_or_of_lt hm _).symm
/-- The packed normal word denotes its exact dyadic value in binary64-subnormal units. -/
theorem model_pack_units (m : Nat) (e : Int) (lo : 2^52 ≤ m) (hi : m < 2^53)
    (he : -1074 ≤ e) (he' : e ≤ 971) :
    Conversion.magnitudeUnits64 ⟨(Float.Model.pack (.finite .positive m e (by omega))).toBits⟩ =
      m * 2 ^ (e+1074).toNat := by
  let raw : Binary64 := ⟨(Float.Model.pack (.finite .positive m e (by omega))).toBits⟩
  have hw : raw.bits.toNat = (e+1075).toNat * 2^52 + m % 2^52 := model_pack_word m e lo hi he he'
  have hb : 0 < (e+1075).toNat ∧ (e+1075).toNat < 2047 := by omega
  have hf : m % 2^52 < 2^52 := Nat.mod_lt m (Nat.two_pow_pos 52)
  have hraw : raw.bits.toNat < 2^63 := by omega
  have hm : raw.magnitude = (e+1075).toNat * 2^52 + m % 2^52 := by
    change raw.bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hraw, hw]
  change Conversion.magnitudeUnits64 raw = _
  unfold Conversion.magnitudeUnits64
  rw [hm]
  have hdiv : ((e+1075).toNat * 2^52 + m % 2^52) / 2^52 = (e+1075).toNat := by omega
  have hmod : ((e+1075).toNat * 2^52 + m % 2^52) % 2^52 = m % 2^52 := by omega
  rw [hdiv, hmod, if_neg (show (e+1075).toNat ≠ 0 by omega)]
  have hmvalue : 2^52 + m % 2^52 = m := by omega
  have hevalue : (e+1075).toNat-1 = (e+1074).toNat := by omega
  rw [hmvalue, hevalue]
set_option exponentiation.threshold 2048 in
/-- Every admitted 53-bit fraction executes to numerator / 2^53 exactly, including zero. -/
theorem fraction_value_exact (fraction : Rng.Fraction53) :
    Conversion.magnitudeUnits64 fraction.toBinary64 = fraction.numerator.toNat * 2^1021 := by
  by_cases hz : fraction.numerator.toNat = 0
  · have hw : fraction.numerator = 0 := UInt64.toNat_inj.mp hz
    rw [hz, Nat.zero_mul]
    simp only [Rng.Fraction53.toBinary64, hw]
    rfl
  · let k := fraction.numerator.toNat.log2
    have hlohi : 2^k ≤ fraction.numerator.toNat ∧ fraction.numerator.toNat < 2^(k+1) :=
      (Nat.log2_eq_iff hz).mp rfl
    have hk : k ≤ 52 := by
      have h := (Nat.log2_lt hz).mpr fraction.bounded
      omega
    have hb := model_scaled_mantissa fraction.numerator.toNat k hlohi.1 hlohi.2 hk
    change Conversion.magnitudeUnits64 ⟨fraction.toBinary64.bits⟩ = _
    rw [fraction_model_word fraction k hlohi.1 hlohi.2 hk]
    rw [model_pack_units _ _ hb.1 hb.2 (by omega) (by omega)]
    have he : ((k : Int)-105+1074).toNat = k+969 := by omega
    rw [he, Nat.mul_assoc, ← Nat.pow_add]
    have hsum : 52-k+(k+969) = 1021 := by omega
    rw [hsum]
/-- Every executed fraction word is nonnegative and strictly below the encoding of one. -/
theorem fraction_word_lt_one (fraction : Rng.Fraction53) : fraction.toBinary64.bits.toNat < 0x3ff0000000000000 := by
  by_cases hz : fraction.numerator.toNat = 0
  · have hw : fraction.numerator = 0 := UInt64.toNat_inj.mp hz
    simp only [Rng.Fraction53.toBinary64, hw]
    decide
  · let k := fraction.numerator.toNat.log2
    have hlohi : 2^k ≤ fraction.numerator.toNat ∧ fraction.numerator.toNat < 2^(k+1) :=
      (Nat.log2_eq_iff hz).mp rfl
    have hk : k ≤ 52 := by
      have h := (Nat.log2_lt hz).mpr fraction.bounded
      omega
    have hb := model_scaled_mantissa fraction.numerator.toNat k hlohi.1 hlohi.2 hk
    rw [fraction_model_word fraction k hlohi.1 hlohi.2 hk]
    rw [model_pack_word _ _ hb.1 hb.2 (by omega) (by omega)]
    have he : ((k : Int)-105+1075).toNat = k+970 := by omega
    rw [he]
    have hf := Nat.mod_lt (fraction.numerator.toNat * 2^(52-k)) (Nat.two_pow_pos 52)
    omega
/-- The actual floating fraction result is finite for every admitted numerator. -/
theorem fraction_finite (fraction : Rng.Fraction53) : fraction.toBinary64.Finite := by
  have h := fraction_word_lt_one fraction
  change fraction.toBinary64.bits.toNat &&& (2^63-1) < 0x7ff0000000000000
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by omega)
/-- The actual RNG draw returns its shifted word divided by 2^53 exactly. -/
theorem nextF64_value_exact (stream : Rng.Xoshiro256) :
    Conversion.magnitudeUnits64 stream.nextF64.1 = (stream.next.1 >>> 11).toNat * 2^1021 :=
  fraction_value_exact (Rng.Fraction53.ofWord stream.next.1)
/-- Every actual floating RNG draw has a nonnegative encoding strictly below one. -/
theorem nextF64_word_lt_one (stream : Rng.Xoshiro256) : stream.nextF64.1.bits.toNat < 0x3ff0000000000000 :=
  fraction_word_lt_one (Rng.Fraction53.ofWord stream.next.1)
set_option exponentiation.threshold 2048 in
/-- The actual unsigned conversion is dyadically exact for every integer below 2^53. -/
theorem ofUInt64_value_exact (word : UInt64) (bound : word.toNat < 2^53) :
    Conversion.magnitudeUnits64 (Binary64.ofUInt64 word) = word.toNat * 2^1074 := by
  by_cases hz : word.toNat = 0
  · have hw : word = 0 := UInt64.toNat.inj hz
    rw [hw]
    rfl
  · let k := word.toNat.log2
    have hlohi : 2^k ≤ word.toNat ∧ word.toNat < 2^(k+1) := (Nat.log2_eq_iff hz).mp rfl
    have hk : k ≤ 52 := by have := (Nat.log2_lt hz).mpr bound; omega
    have hm := model_scaled_mantissa word.toNat k hlohi.1 hlohi.2 hk
    change Conversion.magnitudeUnits64 ⟨(Float.Model.ofUInt64 word).toBits⟩ = _
    rw [model_ofUInt64_small word k hlohi.1 hlohi.2 hk]
    rw [model_pack_units _ _ hm.1 hm.2 (by omega) (by omega)]
    have he : ((k:Int)-52+1074).toNat = k+1022 := by omega
    rw [he, Nat.mul_assoc, ← Nat.pow_add, show 52-k+(k+1022) = 1074 by omega]

/-- The exact small-integer conversion has a positive-sign finite normal or zero encoding. -/
theorem ofUInt64_word_bound (word : UInt64) (bound : word.toNat < 2^53) :
    (Binary64.ofUInt64 word).bits.toNat < 0x7ff0000000000000 := by
  by_cases hz : word.toNat = 0
  · have hw : word = 0 := UInt64.toNat.inj hz
    rw [hw]
    decide
  · let k := word.toNat.log2
    have hlohi : 2^k ≤ word.toNat ∧ word.toNat < 2^(k+1) := (Nat.log2_eq_iff hz).mp rfl
    have hk : k ≤ 52 := by have := (Nat.log2_lt hz).mpr bound; omega
    have hm := model_scaled_mantissa word.toNat k hlohi.1 hlohi.2 hk
    change (Float.Model.ofUInt64 word).toBits.toNat < _
    rw [model_ofUInt64_small word k hlohi.1 hlohi.2 hk, model_pack_word _ _ hm.1 hm.2 (by omega) (by omega)]
    have he : ((k:Int)-52+1075).toNat = k+1023 := by omega
    rw [he]
    have hf := Nat.mod_lt (word.toNat * 2^(52-k)) (Nat.two_pow_pos 52)
    omega

/-- The binary64 sign mask extracts exactly the high bit, as a word value. -/
theorem word64_sign_exact (word : UInt64) :
    ((word &&& 0x8000000000000000) : UInt64).toNat = (word.toNat / 2^63)*2^63 := by
  have hb := word.toNat_lt
  change word.toNat &&& 2^63 = _
  have hq : word.toNat / 2^63 < 2 := by omega
  have hd : (word.toNat &&& 2^63) / 2^63 = word.toNat / 2^63 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos 63)]
    change word.toNat / 2^63 &&& (2^1-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hq]
  have hm : (word.toNat &&& 2^63) % 2^63 = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  omega

/-- Raw sign negation preserves every magnitude bit. -/
theorem negate_magnitude (value : Binary64) : value.negate.magnitude = value.magnitude := by
  change (value.bits.toNat ^^^ 2^63) &&& (2^63-1) = value.bits.toNat &&& (2^63-1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]

/-- Sign negation preserves the exact magnitude interpretation. -/
theorem negate_magnitude_units (value : Binary64) :
    Conversion.magnitudeUnits64 value.negate = Conversion.magnitudeUnits64 value := by
  simp only [Conversion.magnitudeUnits64, negate_magnitude]

/-- The executing signed conversion preserves magnitude exactly throughout the 53-bit integer domain. -/
theorem ofInt_magnitude_exact (value : Int) (bound : value.natAbs < 2^53) :
    Conversion.magnitudeUnits64 (Conversion.ofInt value) = value.natAbs*2^1074 := by
  have hword : value.natAbs.toUInt64.toNat = value.natAbs := by
    change value.natAbs % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hn := ofUInt64_value_exact value.natAbs.toUInt64 (by rw [hword]; exact bound)
  rw [hword] at hn
  unfold Conversion.ofInt
  split
  · change Conversion.magnitudeUnits64 (Binary64.ofUInt64 value.natAbs.toUInt64).negate = _
    rw [negate_magnitude_units]
    exact hn
  · exact hn

/-- Signed small-integer conversion remains finite for either source sign. -/
theorem ofInt_finite (value : Int) (bound : value.natAbs < 2^53) :
    (Conversion.ofInt value).Finite := by
  have hword : value.natAbs.toUInt64.toNat = value.natAbs := by
    change value.natAbs % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hb := ofUInt64_word_bound value.natAbs.toUInt64 (by rw [hword]; exact bound)
  have hf : (Binary64.ofUInt64 value.natAbs.toUInt64).Finite := by
    change (Binary64.ofUInt64 value.natAbs.toUInt64).bits.toNat &&& (2^63-1) < _
    exact Nat.lt_of_le_of_lt Nat.and_le_left hb
  unfold Conversion.ofInt
  split
  · change (Binary64.ofUInt64 value.natAbs.toUInt64).negate.magnitude < _
    rw [negate_magnitude]
    exact hf
  · exact hf

/-- The signed conversion installs the source sign without crossing any magnitude bits. -/
theorem ofInt_sign (value : Int) (bound : value.natAbs < 2^53) :
    ((Conversion.ofInt value).bits &&& 0x8000000000000000 != 0) = decide (value < 0) := by
  have hword : value.natAbs.toUInt64.toNat = value.natAbs := by
    change value.natAbs % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hb := ofUInt64_word_bound value.natAbs.toUInt64 (by rw [hword]; exact bound)
  let word := (Binary64.ofUInt64 value.natAbs.toUInt64).bits
  have hw : word.toNat < 2^63 := by change (Binary64.ofUInt64 value.natAbs.toUInt64).bits.toNat < _; omega
  have hs := word64_sign_exact word
  rw [Nat.div_eq_of_lt hw, Nat.zero_mul] at hs
  have hz : word &&& 0x8000000000000000 = 0 := UInt64.toNat.inj hs
  have hn : (word ^^^ 0x8000000000000000) &&& 0x8000000000000000 ≠ 0 := by
    intro h
    have hn := word64_sign_exact (word ^^^ 0x8000000000000000)
    rw [h] at hn
    change 0 = ((word.toNat ^^^ 2^63)/2^63)*2^63 at hn
    rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt hw, Nat.div_self (Nat.two_pow_pos 63), Nat.zero_xor] at hn
    contradiction
  unfold Conversion.ofInt
  change ((if value < 0 then Binary64.mk (word ^^^ 0x8000000000000000) else ⟨word⟩).bits &&& 0x8000000000000000 != 0) = _
  by_cases negative : value < 0
  · simp [negative, hn]
  · simp [negative, hz]

/-- Truncation recovers every integer admitted by the exact signed conversion. -/
theorem trunc64_ofInt (value : Int) (bound : value.natAbs < 2^53) :
    Conversion.trunc64 (Conversion.ofInt value) = value := by
  rw [Conversion.trunc64_signed_exact, ofInt_sign value bound, ofInt_magnitude_exact value bound,
    Nat.mul_div_cancel _ (Nat.two_pow_pos 1074)]
  by_cases hn : value < 0
  · simp only [hn, decide_true, ↓reduceIte]
    exact (Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hn)).symm
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact Int.natAbs_of_nonneg (by omega)

/-- The actual signed-32-bit conversion pair is exact throughout the complete admitted integer domain. -/
theorem toI32_ofInt (value : Int) (lo : -(2^31) ≤ value) (hi : value < 2^31) :
    Conversion.toI32 (Conversion.ofInt value) = value := by
  have hb : value.natAbs < 2^53 := by omega
  rw [Conversion.toI32_eq_signedCast, Conversion.signedCast_finite _ _ (ofInt_finite value hb), trunc64_ofInt value hb]
  unfold Conversion.clampInt
  omega
end AcornVerif.CurrentFloat
