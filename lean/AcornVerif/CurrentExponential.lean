/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentPower
/-!
# Executing exponential classification and scaling

The current definitions in `Acorn.Portable` own every operation. These proofs
unfold the pinned Lean 4.33.0 standard floating model, as documented in
`CurrentFloat.lean` and `CurrentPower.lean`, to establish exact normal exponent
scaling and the actual finite-width narrowing behavior.

The polynomial domain [1/2, 3/2] contains the retained component contract's
[0.7, 1.42] interval. The scale bounds include subnormal binary32 results,
underflow to zero, and permitted overflow at the upper exponents. Saturation
admits only the finite strict interior of its generated thresholds. Reduction
and the series require their own component proofs; this module does not infer
ideal transcendental accuracy or compiler/runtime correctness.
-/
namespace AcornVerif.CurrentExponential
open Acorn
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower
/-- The raw power-of-two construction writes the exact admitted normal exponent field. -/
theorem powerOfTwo_word (exponent : Int) (lo : -1022 ≤ exponent) (hi : exponent ≤ 1023) :
    (Portable.powerOfTwo exponent).bits.toNat = (exponent+1023).toNat*2^52 := by
  have hn : 0 ≤ exponent+1023 := by omega
  have hh : exponent+1023 < (2^64:Int) := by omega
  have hm : (exponent+1023) % (2^64) = exponent+1023 := Int.emod_eq_of_lt hn hh
  have hc : (exponent+1023).toNat < 2^64 := by omega
  have hw : (exponent+1023).toNat.toUInt64.toNat = (exponent+1023).toNat := by
    change (exponent+1023).toNat % 2^64 = _
    exact Nat.mod_eq_of_lt hc
  have hp : (exponent+1023).toNat*2^52 < 2^64 := by omega
  unfold Portable.powerOfTwo
  rw [hm]
  simp only [UInt64.toNat_shiftLeft, hw, UInt64.toNat_ofNat, Nat.shiftLeft_eq]
  change (exponent+1023).toNat*2^52 % (2^64) = _
  exact Nat.mod_eq_of_lt hp

/-- The same power-of-two word is the normalized standard binary64 model with unit significand. -/
theorem powerOfTwo_model (exponent : Int) (lo : -1022 ≤ exponent) (hi : exponent ≤ 1023) :
    Portable.powerOfTwo exponent =
      ⟨(Float.Model.pack (.finite .positive (2^52) (exponent-52) (by decide))).toBits⟩ := by
  have hp := powerOfTwo_word exponent lo hi
  have hm := model_pack_word (2^52) (exponent-52) (by omega) (by decide) (by omega) (by omega)
  have he : exponent-52+1075 = exponent+1023 := by omega
  rw [he] at hm
  simp only [Nat.mod_self, Nat.add_zero] at hm
  exact congrArg Binary64.mk (UInt64.toNat.inj (hp.trans hm.symm))

/-- Scaling a normal model by an admitted power of two shifts its exponent exactly above the subnormal floor; packing owns overflow. -/
theorem binary64_scale_normal_model (m : Nat) (e exponent : Int)
    (lo : 2^52 ≤ m) (hi : m < 2^53) (he : -1074 ≤ e) (he' : e ≤ 971)
    (hk : -1022 ≤ exponent) (hk' : exponent ≤ 1023)
    (resultLo : -1074 ≤ e+exponent) :
    (Binary64.mk (Float.Model.pack (.finite .positive m e (by omega))).toBits).mul
      (Portable.powerOfTwo exponent) =
        ⟨(Float.Model.pack (.finite .positive m (e+exponent) (by omega))).toBits⟩ := by
  rw [powerOfTwo_model exponent hk hk']
  have re₁ : Float.Model.ofBits (Float.Model.pack (.finite .positive m e (by omega))).toBits =
      Float.Model.pack (.finite .positive m e (by omega)) := by
    change Float.Model.pack (unpack Format.binary64 (pack Format.binary64 _)) = _
    rw [model_unpack_pack_normal .positive m e lo hi he he']
  have re₂ : Float.Model.ofBits (Float.Model.pack (.finite .positive (2^52) (exponent-52) (by decide))).toBits =
      Float.Model.pack (.finite .positive (2^52) (exponent-52) (by decide)) := by
    change Float.Model.pack (unpack Format.binary64 (pack Format.binary64 _)) = _
    rw [model_unpack_pack_normal .positive (2^52) (exponent-52) (by omega) (by decide) (by omega) (by omega)]
  have u₁ : (Float.Model.pack (.finite .positive m e (by omega))).unpack = .finite .positive m e (by omega) :=
    model_unpack_pack_normal .positive m e lo hi he he'
  have u₂ : (Float.Model.pack (.finite .positive (2^52) (exponent-52) (by decide))).unpack =
      .finite .positive (2^52) (exponent-52) (by decide) :=
    model_unpack_pack_normal .positive (2^52) (exponent-52) (by omega) (by decide) (by omega) (by omega)
  change Binary64.mk (Float.Model.mul (Float.Model.ofBits _) (Float.Model.ofBits _)).toBits = _
  rw [re₁, re₂, Float.Model.mul, u₁, u₂]
  change Binary64.mk (Float.Model.pack (roundWithAccuracy Format.binary64 .positive (m*2^52) (e+(exponent-52)) .exact)).toBits = _
  rw [show e+(exponent-52) = (e+exponent)-(52:Nat) by omega,
    model_round_scaled_exact .positive m 52 (e+exponent) lo hi resultLo]

/-- Every positive-sign normal word is exactly its decoded normalized model. -/
theorem model_positive_normal_word (value : Binary64) (positive : value.bits.toNat < 2^63)
    (lo : 0 < ((value.bits >>> 52) &&& 0x7ff : UInt64).toNat)
    (hi : ((value.bits >>> 52) &&& 0x7ff : UInt64).toNat < 2047) :
    value = ⟨(Float.Model.pack (.finite .positive
      (2^52+((value.bits &&& 0xfffffffffffff : UInt64).toNat))
      ((((value.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int)-1075) (by omega))).toBits⟩ := by
  have hp := model_pack_unpack_normal_word value.bits (by rw [model_exponent_word]; exact lo)
    (by rw [model_exponent_word]; exact hi)
  rw [model_unpack_normal_fields value.bits (by rw [model_exponent_word]; exact lo)
    (by rw [model_exponent_word]; exact hi)] at hp
  have hs : unpackSign (spec := Format.binary64) value.bits.toBitVec = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    change (value.bits.toNat >>> 63) % 2 = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt positive]
  have hf : (unpackMantissa (spec := Format.binary64) value.bits.toBitVec).toNat =
      ((value.bits &&& 0xfffffffffffff : UInt64).toNat) := by
    change (value.bits.toNat >>> 0) % 2^52 = value.bits.toNat &&& (2^52-1)
    rw [Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod]
  simp only [hs, Sign.ofBitVec, ↓reduceIte] at hp
  have he := model_exponent_word value.bits
  have hbits : (Float.Model.pack (.finite .positive
      (2^52+((value.bits &&& 0xfffffffffffff : UInt64).toNat))
      ((((value.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int)-1075) (by omega))).toBits = value.bits := by
    apply UInt64.toBitVec_inj.mp
    change pack Format.binary64 (.finite .positive (2^52+((value.bits &&& 0xfffffffffffff : UInt64).toNat))
      ((((value.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int)-1075) (by omega)) = _
    simp only [he, hf] at hp
    exact hp
  exact (congrArg Binary64.mk hbits).symm
/-- The executing exponential scale keeps the significand and shifts the biased exponent exactly on a containing dyadic domain. -/
theorem expScale_wide_word (polynomial : Binary64) (exponent : Int)
    (lo : 0x3fe0000000000000 ≤ polynomial.bits.toNat) (hi : polynomial.bits.toNat ≤ 0x3ff8000000000000)
    (hk : -151 ≤ exponent) (hk' : exponent ≤ 129) :
    (polynomial.mul (Portable.powerOfTwo exponent)).bits.toNat =
      ((((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int)+exponent).toNat*2^52 +
        ((polynomial.bits &&& 0xfffffffffffff : UInt64).toNat) := by
  let ev : UInt64 := (polynomial.bits >>> 52) &&& 0x7ff
  let fv : UInt64 := polynomial.bits &&& 0xfffffffffffff
  have hmag : polynomial.magnitude = polynomial.bits.toNat := by
    change polynomial.bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hd : polynomial.bits.toNat = ev.toNat*2^52+fv.toNat := by
    have h := Conversion.fields64_decomposition polynomial
    rw [hmag] at h
    exact h
  have hf : fv.toNat < 2^52 := Conversion.fraction64_bound polynomial.bits
  have hev : 1022 ≤ ev.toNat ∧ ev.toNat ≤ 1023 := by omega
  have hpoly := model_positive_normal_word polynomial (by omega) (by change 0 < ev.toNat; omega)
    (by change ev.toNat < 2047; omega)
  change polynomial = ⟨(Float.Model.pack (.finite .positive (2^52+fv.toNat) ((ev.toNat:Int)-1075) (by omega))).toBits⟩ at hpoly
  have hs := binary64_scale_normal_model (2^52+fv.toNat) ((ev.toNat:Int)-1075) exponent
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [← hpoly] at hs
  have hw := congrArg (fun v : Binary64 => v.bits.toNat) hs
  change (polynomial.mul (Portable.powerOfTwo exponent)).bits.toNat = _ at hw
  rw [model_pack_word _ _ (by omega) (by omega) (by omega) (by omega)] at hw
  have heq : (ev.toNat:Int)-1075+exponent+1075 = ev.toNat+exponent := by omega
  have hfrac : (2^52+fv.toNat) % 2^52 = fv.toNat := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hf]
  rw [heq, hfrac] at hw
  exact hw

/-- The scaled result retains exactly the source fraction and its shifted normal exponent. -/
theorem expScale_wide_components (polynomial : Binary64) (exponent : Int)
    (lo : 0x3fe0000000000000 ≤ polynomial.bits.toNat) (hi : polynomial.bits.toNat ≤ 0x3ff8000000000000)
    (hk : -151 ≤ exponent) (hk' : exponent ≤ 129) :
    let result := polynomial.mul (Portable.powerOfTwo exponent)
    let sourceExponent := (((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int)
    result.bits.toNat < 0x7ff0000000000000 ∧
      (((result.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int) = sourceExponent+exponent ∧
      (result.bits &&& 0xfffffffffffff : UInt64) = (polynomial.bits &&& 0xfffffffffffff) := by
  dsimp only
  have hpoly := Conversion.fields64_decomposition polynomial
  have hpfrac := Conversion.fraction64_bound polynomial.bits
  have hpmag : polynomial.magnitude = polynomial.bits.toNat := by
    change polynomial.bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hpmag] at hpoly
  have he : 1022 ≤ (((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat) ∧
      (((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat) ≤ 1023 := by omega
  have hw := expScale_wide_word polynomial exponent lo hi hk hk'
  have hbound : (polynomial.mul (Portable.powerOfTwo exponent)).bits.toNat < 0x7ff0000000000000 := by omega
  have hmag : (polynomial.mul (Portable.powerOfTwo exponent)).magnitude =
      (polynomial.mul (Portable.powerOfTwo exponent)).bits.toNat := by
    change (polynomial.mul (Portable.powerOfTwo exponent)).bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hd := Conversion.fields64_decomposition (polynomial.mul (Portable.powerOfTwo exponent))
  have hf := Conversion.fraction64_bound (polynomial.mul (Portable.powerOfTwo exponent)).bits
  rw [hmag, hw] at hd
  refine ⟨hbound, by omega, ?_⟩
  apply UInt64.toNat.inj
  omega

/-- Scaling and final narrowing always produce a positive-sign finite or infinite word, never NaN. -/
theorem expScale_nonnegative (polynomial : Binary64) (exponent : Int)
    (lo : 0x3fe0000000000000 ≤ polynomial.bits.toNat) (hi : polynomial.bits.toNat ≤ 0x3ff8000000000000)
    (hk : -151 ≤ exponent) (hk' : exponent ≤ 129) :
    (Portable.expScale polynomial exponent).bits.toNat ≤ 0x7f800000 := by
  have components := expScale_wide_components polynomial exponent lo hi hk hk'
  let wide := polynomial.mul (Portable.powerOfTwo exponent)
  have hfinite : wide.Finite := by
    change wide.bits.toNat &&& (2^63-1) < _
    exact Nat.lt_of_le_of_lt Nat.and_le_left components.1
  have he : (((wide.bits >>> 52) &&& 0x7ff : UInt64).toNat) < 2047 := by
    have hd := Conversion.fields64_decomposition wide
    change wide.magnitude < 0x7ff0000000000000 at hfinite
    omega
  have hm := Conversion.narrow_finite_input_bound wide he
  have hs := Conversion.narrow_sign wide hfinite
  change (Conversion.narrow wide).bits.toNat &&& (2^31-1) ≤ _ at hm
  rw [Nat.and_two_pow_sub_one_eq_mod] at hm
  have hbound : wide.bits.toNat < 0x7ff0000000000000 := components.1
  change (Conversion.narrow wide).bits.toNat ≤ _
  omega

/-- Every strictly negative scaling exponent produces a result in the positive-sign unit interval. -/
theorem expScale_negative_unit (polynomial : Binary64) (exponent : Int)
    (lo : 0x3fe0000000000000 ≤ polynomial.bits.toNat) (hi : polynomial.bits.toNat ≤ 0x3ff8000000000000)
    (hk : -151 ≤ exponent) (negative : exponent < 0) :
    (Portable.expScale polynomial exponent).bits.toNat ≤ 0x3f800000 := by
  have hpoly := Conversion.fields64_decomposition polynomial
  have hf := Conversion.fraction64_bound polynomial.bits
  have hm : polynomial.magnitude = polynomial.bits.toNat := by
    change polynomial.bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hm] at hpoly
  have hw := expScale_wide_word polynomial exponent lo hi hk (by omega)
  apply Conversion.narrow_word_unit
  omega

/-- At exponent zero, every unit-bounded polynomial remains unit-bounded after the actual scale and narrowing. -/
theorem expScale_zero_unit (polynomial : Binary64)
    (lo : 0x3fe0000000000000 ≤ polynomial.bits.toNat) (hi : polynomial.bits.toNat ≤ 0x3ff0000000000000) :
    (Portable.expScale polynomial 0).bits.toNat ≤ 0x3f800000 := by
  have hm : polynomial.magnitude = polynomial.bits.toNat := by
    change polynomial.bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hp := Conversion.fields64_decomposition polynomial
  rw [hm] at hp
  have hw := expScale_wide_word polynomial 0 lo (by omega) (by omega) (by omega)
  apply Conversion.narrow_word_unit
  omega
/-- A significand no larger than one and a half cannot carry into the next exponent when narrowed. -/
theorem normalExponent_no_carry (word exponent : UInt64)
    (bound : ((word &&& 0xfffffffffffff : UInt64).toNat) ≤ 2^51) :
    Conversion.normalExponent word exponent = exponent := by
  have hm := Conversion.normalSignificand_value word
  have hr := (Rounding.nearestEven_bracket (Conversion.normalSignificand word).toNat (2^29)).2
  have hx : (Conversion.roundedNormal word).toNat =
      Rounding.nearestEven (Conversion.normalSignificand word).toNat (2^29) := by
    rw [Conversion.roundedNormal_eq]
    exact Rounding.wordShift_exact _ _
  have hn : (Conversion.roundedNormal word == ((1:UInt64) <<< 24)) = false := by
    simp only [beq_eq_false_iff_ne]
    intro h
    have hnat := congrArg UInt64.toNat h
    change (Conversion.roundedNormal word).toNat = 2^24 at hnat
    omega
  simp only [Conversion.normalExponent, hn, Bool.false_eq_true, ↓reduceIte]

/-- The actual scaled/narrowed result is finite through exponent 127 on the containing half-to-three-halves polynomial domain. -/
theorem expScale_finite (polynomial : Binary64) (exponent : Int)
    (lo : 0x3fe0000000000000 ≤ polynomial.bits.toNat) (hi : polynomial.bits.toNat ≤ 0x3ff8000000000000)
    (hk : -151 ≤ exponent) (hk' : exponent ≤ 127) :
    (Portable.expScale polynomial exponent).Finite := by
  have components := expScale_wide_components polynomial exponent lo hi hk (by omega)
  let wide := polynomial.mul (Portable.powerOfTwo exponent)
  have hbound : wide.bits.toNat < 0x7ff0000000000000 := components.1
  have hfinite : wide.Finite := by
    change wide.bits.toNat &&& (2^63-1) < _
    exact Nat.lt_of_le_of_lt Nat.and_le_left hbound
  have hpoly := Conversion.fields64_decomposition polynomial
  have hf := Conversion.fraction64_bound polynomial.bits
  have hm : polynomial.magnitude = polynomial.bits.toNat := by
    change polynomial.bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hm] at hpoly
  have he : 1022 ≤ (((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat) ∧
      (((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat) ≤ 1023 := by omega
  have hshift : (((wide.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int) =
      (((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat : Int)+exponent := components.2.1
  have hew : (((wide.bits >>> 52) &&& 0x7ff : UInt64).toNat) ≤ 1150 := by omega
  change (Conversion.narrow wide).Finite
  apply (Conversion.narrow_finite_iff wide hfinite).mpr
  by_cases top : (((wide.bits >>> 52) &&& 0x7ff : UInt64).toNat) = 1150
  · have hsource : (((polynomial.bits >>> 52) &&& 0x7ff : UInt64).toNat) = 1023 := by omega
    have hfrac : ((wide.bits &&& 0xfffffffffffff : UInt64).toNat) ≤ 2^51 := by
      have hh : (wide.bits &&& 0xfffffffffffff : UInt64) = (polynomial.bits &&& 0xfffffffffffff) := components.2.2
      rw [hh]
      omega
    rw [normalExponent_no_carry _ _ hfrac]
    exact hew
  · rw [Conversion.normalExponent_exact _ _ (by omega)]
    split <;> omega
/-- The actual exponential classifier preserves exceptional words and admits only its finite strict interior. -/
theorem expSaturation_ends (value : Binary32) :
    match Portable.expSaturation value with
    | some result =>
      if value.isNaN then result = value
      else if !value.less ⟨Acorn.Constants.expOverflowBits⟩ then result = ⟨0x7f800000⟩
      else !(Binary32.mk Acorn.Constants.expUnderflowBits).less value ∧ result = .zero
    | none => value.Finite ∧
        (Binary32.mk Acorn.Constants.expUnderflowBits).less value = true ∧
        value.less ⟨Acorn.Constants.expOverflowBits⟩ = true := by
  by_cases nan : value.isNaN = true
  · simp [Portable.expSaturation, nan]
  · by_cases high : (!value.less ⟨Acorn.Constants.expOverflowBits⟩) = true
    · simp [Portable.expSaturation, nan, high]
    · by_cases low : (!(Binary32.mk Acorn.Constants.expUnderflowBits).less value) = true
      · simp [Portable.expSaturation, nan, high, low]
      · simp only [Portable.expSaturation, nan, high, low]
        have hn : value.isNaN = false := by simpa using nan
        have hh : value.less ⟨Acorn.Constants.expOverflowBits⟩ = true := by simpa using high
        have hl : (Binary32.mk Acorn.Constants.expUnderflowBits).less value = true := by simpa using low
        refine ⟨?_, hl, hh⟩
        have hhn : (Binary32.mk Acorn.Constants.expOverflowBits).isNaN = false := rfl
        have hln : (Binary32.mk Acorn.Constants.expUnderflowBits).isNaN = false := rfl
        have hhk : (Binary32.mk Acorn.Constants.expOverflowBits).key = 0x42b20000 := rfl
        have hlk : (Binary32.mk Acorn.Constants.expUnderflowBits).key = -0x42d00000 := rfl
        simp only [Binary32.less_eq_key, hn, hhn, Bool.not_false, Bool.true_and, decide_eq_true_eq] at hh
        simp only [Binary32.less_eq_key, hn, hln, Bool.not_false, Bool.true_and, decide_eq_true_eq] at hl
        rw [hhk] at hh
        rw [hlk] at hl
        change value.magnitude < 0x7f800000
        by_cases hs : value.negative = true
        · simp only [Binary32.key, hs, ↓reduceIte] at hh hl
          omega
        · simp only [Binary32.key, hs] at hh hl
          omega
end AcornVerif.CurrentExponential
