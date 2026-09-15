/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Terrain
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact executing raw binary32 floor

Finite values are interpreted in the existing exact binary64-subnormal units.
An integral result and a one-unit half-open enclosure characterize floor
uniquely. Field arithmetic establishes that characterization without native
reflection, input enumeration or a trusted floating floor primitive.
-/
set_option exponentiation.threshold 2048
set_option maxRecDepth 2048

namespace AcornVerif.CurrentFloor
open Acorn Acorn.Host

/-- Extracting the binary32 high bit is exact unsigned division. -/
theorem word32_sign_exact (word : UInt32) :
    ((word &&& 0x80000000) : UInt32).toNat = (word.toNat / 2 ^ 31)*2 ^ 31 := by
  have hb := word.toNat_lt
  change word.toNat &&& 2 ^ 31 = _
  have hq : word.toNat / 2 ^ 31 < 2 := by omega
  have hd : (word.toNat &&& 2 ^ 31) / 2 ^ 31 = word.toNat / 2 ^ 31 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos 31)]
    change word.toNat / 2 ^ 31 &&& (2 ^ 1-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hq]
  have hm : (word.toNat &&& 2 ^ 31) % 2 ^ 31 = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  omega

/-- Assembly neither wraps the word nor lets magnitude bits reach the sign. -/
theorem assemble_fields (negative : Bool) (exponent fraction : Nat)
    (hfit : exponent * 2 ^ 23 + fraction < 2 ^ 31) :
    (assemble32 negative exponent fraction).magnitude = exponent * 2 ^ 23 + fraction ∧
    (assemble32 negative exponent fraction).negative = negative := by
  have hword : (assemble32 negative exponent fraction).bits.toNat =
      (if negative then 2 ^ 31 else 0) + exponent * 2 ^ 23 + fraction := by
    apply UInt32.toNat_ofNat_of_lt'
    change _ < (4294967296 : Nat)
    have hsign : (if negative then 2 ^ 31 else 0 : Nat) ≤ 2 ^ 31 := by split <;> omega
    omega
  constructor
  · change (assemble32 negative exponent fraction).bits.toNat &&& (2 ^ 31-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, hword]
    cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · have hs := word32_sign_exact (assemble32 negative exponent fraction).bits
    rw [hword] at hs
    cases negative with
    | false =>
      have hz : (assemble32 false exponent fraction).bits &&& 0x80000000 = 0 :=
        UInt32.toNat.inj (by
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hs
          rw [Nat.div_eq_of_lt hfit] at hs
          exact hs)
      simp [Binary32.negative, hz]
    | true =>
      have hn : (assemble32 true exponent fraction).bits &&& 0x80000000 ≠ 0 := by
        intro hz
        rw [hz] at hs
        simp only [↓reduceIte] at hs
        have hdiv : (2 ^ 31 + exponent * 2 ^ 23 + fraction) / 2 ^ 31 = 1 := by omega
        rw [hdiv] at hs
        norm_num at hs
      simpa [Binary32.negative] using hn

/-- Field assembly permits the one exponent carry made by integral rounding. -/
theorem assemble_units (negative : Bool) (exponent fraction : Nat)
    (he : 0 < exponent) (hemax : exponent < 254) (hf : fraction ≤ 2 ^ 23) :
    Conversion.magnitudeUnits32 (assemble32 negative exponent fraction) =
      (2 ^ 23 + fraction) * 2 ^ (exponent + 924) := by
  have hm := (assemble_fields negative exponent fraction (by omega)).1
  unfold Conversion.magnitudeUnits32
  rw [hm]
  by_cases hcarry : fraction = 2 ^ 23
  · subst fraction
    have hd : (exponent * 2 ^ 23 + 2 ^ 23) / 2 ^ 23 = exponent + 1 := by omega
    have hr : (exponent * 2 ^ 23 + 2 ^ 23) % 2 ^ 23 = 0 := by omega
    rw [hd, hr, if_neg (by omega)]
    have hp : exponent + 1 + 924 = (exponent + 924) + 1 := by omega
    rw [hp, Nat.pow_succ]
    omega
  · have hd : (exponent * 2 ^ 23 + fraction) / 2 ^ 23 = exponent := by omega
    have hr : (exponent * 2 ^ 23 + fraction) % 2 ^ 23 = fraction := by omega
    rw [hd, hr, if_neg (by omega)]

/-- Rounding to a divisor of the significand width needs at most one carry. -/
theorem fraction_bound (negative : Bool) (fraction divisor : Nat)
    (hf : fraction < 2 ^ 23) (hd : 0 < divisor) (hdiv : divisor ∣ 2 ^ 23) :
    floorFraction negative fraction divisor ≤ 2 ^ 23 := by
  obtain ⟨multiple, hm⟩ := hdiv
  have hm' : multiple * divisor = 2 ^ 23 := by simpa [Nat.mul_comm] using hm.symm
  have hq : fraction / divisor < multiple := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    rw [hm']
    exact hf
  unfold floorFraction
  split
  · calc
      (fraction / divisor + 1) * divisor ≤ multiple * divisor :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 23 := hm'
  · simp only [Nat.add_zero]
    calc fraction / divisor * divisor ≤ fraction := Nat.div_mul_le_self _ _
         _ ≤ 2 ^ 23 := by omega

/-- The actual fraction has no residual fractional lattice units. -/
theorem fraction_divisible (negative : Bool) (fraction divisor : Nat) :
    divisor ∣ floorFraction negative fraction divisor := by
  unfold floorFraction
  exact dvd_mul_left _ _

/-- Fraction rounding brackets the original fraction within one integral lattice step. -/
theorem fraction_enclosure (negative : Bool) (fraction divisor : Nat) (hd : 0 < divisor) :
    if negative then
      fraction ≤ floorFraction negative fraction divisor ∧
        floorFraction negative fraction divisor < fraction + divisor
    else floorFraction negative fraction divisor ≤ fraction ∧
      fraction < floorFraction negative fraction divisor + divisor := by
  have hm := Nat.mod_lt fraction hd
  have he := Nat.div_add_mod fraction divisor
  rw [Nat.mul_comm] at he
  cases negative with
  | false => simp [floorFraction]; omega
  | true =>
    by_cases hr : fraction % divisor = 0
    · simp [floorFraction, hr]; omega
    · simp [floorFraction, hr, Nat.add_mul]; omega

/-- The raw magnitude always fits below the sign bit. -/
theorem magnitude_bound (value : Binary32) : value.magnitude < 2 ^ 31 := by
  change (value.bits.toNat &&& (2 ^ 31 - 1)) < 2 ^ 31
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Every finite subunit magnitude is strictly below one exact integer unit. -/
theorem subunit_bound (value : Binary32) (he : value.magnitude / 2 ^ 23 < 127) :
    Conversion.magnitudeUnits32 value < 2 ^ 1074 := by
  let e := value.magnitude / 2 ^ 23
  let f := value.magnitude % 2 ^ 23
  have hf : f < 2 ^ 23 := Nat.mod_lt _ (Nat.two_pow_pos _)
  change (if e = 0 then f * 2 ^ 925 else (2 ^ 23 + f) * 2 ^ (e + 924)) < _
  split
  · calc
      f * 2 ^ 925 < 2 ^ 23 * 2 ^ 925 := Nat.mul_lt_mul_of_pos_right hf (Nat.two_pow_pos _)
      _ = 2 ^ 948 := by rw [← Nat.pow_add]
      _ ≤ 2 ^ 1074 := Nat.pow_le_pow_right (by decide) (by decide)
  · calc
      (2 ^ 23 + f) * 2 ^ (e + 924) < 2 ^ 24 * 2 ^ (e + 924) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ ≤ 2 ^ 24 * 2 ^ 1050 := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega))
      _ = 2 ^ 1074 := by rw [← Nat.pow_add]

/-- A nonzero raw magnitude has strictly positive dyadic magnitude units. -/
theorem units_positive (value : Binary32) (h : value.magnitude ≠ 0) :
    0 < Conversion.magnitudeUnits32 value := by
  unfold Conversion.magnitudeUnits32
  dsimp only
  split
  · rename_i he
    have hf : 0 < value.magnitude % 2 ^ 23 := by omega
    exact Nat.mul_pos hf (Nat.two_pow_pos _)
  · exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)

/-- Zero field assembly preserves the sign and has zero numerical magnitude. -/
theorem zero_fields (negative : Bool) :
    (assemble32 negative 0 0).Finite ∧
    (assemble32 negative 0 0).negative = negative ∧
    Conversion.magnitudeUnits32 (assemble32 negative 0 0) = 0 := by
  have hf := assemble_fields negative 0 0 (by decide)
  refine ⟨?_, hf.2, ?_⟩
  · unfold Binary32.Finite
    rw [hf.1]
    decide
  · simp [Conversion.magnitudeUnits32, hf.1]

/-- The negative unit encoding has the exact integral magnitude and sign. -/
theorem negative_one_fields :
    (Binary32.mk 0xbf800000).Finite ∧ (Binary32.mk 0xbf800000).negative = true ∧
    Conversion.magnitudeUnits32 (Binary32.mk 0xbf800000) = 2 ^ 1074 := by
  refine ⟨by decide, by decide, ?_⟩
  change 2 ^ 23 * 2 ^ 1051 = 2 ^ 1074
  rw [← Nat.pow_add]

/-- Normal subintegral exponents round onto the exact integer lattice. -/
theorem middle_magnitude (negative : Bool) (exponent fraction : Nat)
    (hlow : 127 ≤ exponent) (hhigh : exponent < 150) (hf : fraction < 2 ^ 23) :
    let result := assemble32 negative exponent
      (floorFraction negative fraction (2 ^ (150 - exponent)))
    result.Finite ∧ result.negative = negative ∧
    2 ^ 1074 ∣ Conversion.magnitudeUnits32 result ∧
    if negative then
      (2 ^ 23 + fraction) * 2 ^ (exponent + 924) ≤ Conversion.magnitudeUnits32 result ∧
      Conversion.magnitudeUnits32 result < (2 ^ 23 + fraction) * 2 ^ (exponent + 924) + 2 ^ 1074
    else Conversion.magnitudeUnits32 result ≤ (2 ^ 23 + fraction) * 2 ^ (exponent + 924) ∧
      (2 ^ 23 + fraction) * 2 ^ (exponent + 924) <
        Conversion.magnitudeUnits32 result + 2 ^ 1074 := by
  let divisor := 2 ^ (150 - exponent)
  let scale := 2 ^ (exponent + 924)
  let rounded := floorFraction negative fraction divisor
  have hd : 0 < divisor := Nat.two_pow_pos _
  have hb : 0 < scale := Nat.two_pow_pos _
  have hdiv : divisor ∣ 2 ^ 23 := Nat.pow_dvd_pow _ (by omega)
  have hr : rounded ≤ 2 ^ 23 := fraction_bound negative fraction divisor hf hd hdiv
  have hscale : divisor * scale = 2 ^ 1074 := by
    dsimp [divisor, scale]
    rw [← Nat.pow_add, show 150 - exponent + (exponent + 924) = 1074 by omega]
  have ha := assemble_fields negative exponent rounded (by omega)
  have hu := assemble_units negative exponent rounded (by omega) (by omega) hr
  dsimp only
  change (assemble32 negative exponent rounded).Finite ∧
    (assemble32 negative exponent rounded).negative = negative ∧ _
  refine ⟨?_, ha.2, ?_, ?_⟩
  · unfold Binary32.Finite
    rw [ha.1]
    omega
  · rw [hu]
    have hadd : divisor ∣ 2 ^ 23 + rounded :=
      Nat.dvd_add hdiv (fraction_divisible negative fraction divisor)
    obtain ⟨factor, heq⟩ := hadd
    refine ⟨factor, ?_⟩
    change (2 ^ 23 + rounded) * scale = 2 ^ 1074 * factor
    rw [heq, ← hscale]
    rw [Nat.mul_assoc, Nat.mul_comm factor scale, ← Nat.mul_assoc]
  · rw [hu]
    have he := fraction_enclosure negative fraction divisor hd
    cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    all_goals
      constructor
      · exact Nat.mul_le_mul_right scale (Nat.add_le_add_left he.1 _)
      · have h := Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_left he.2 (2 ^ 23)) hb
        simpa only [← Nat.add_assoc, Nat.add_mul, hscale] using h

/-- Every finite input produces a finite integral magnitude within one unit of the input. -/
theorem floor_magnitude (value : Binary32) (finite : value.Finite) :
    (floor32 value).Finite ∧ (floor32 value).negative = value.negative ∧
    2 ^ 1074 ∣ Conversion.magnitudeUnits32 (floor32 value) ∧
    if value.negative then
      Conversion.magnitudeUnits32 value ≤ Conversion.magnitudeUnits32 (floor32 value) ∧
      Conversion.magnitudeUnits32 (floor32 value) < Conversion.magnitudeUnits32 value + 2 ^ 1074
    else Conversion.magnitudeUnits32 (floor32 value) ≤ Conversion.magnitudeUnits32 value ∧
      Conversion.magnitudeUnits32 value <
        Conversion.magnitudeUnits32 (floor32 value) + 2 ^ 1074 := by
  let exponent := value.magnitude / 2 ^ 23
  let fraction := value.magnitude % 2 ^ 23
  have hf : fraction < 2 ^ 23 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have he : exponent < 255 := by
    unfold Binary32.Finite at finite
    dsimp [exponent]
    omega
  have hnormal (hn : exponent ≠ 0) :
      Conversion.magnitudeUnits32 value = (2 ^ 23 + fraction) * 2 ^ (exponent + 924) := by
    exact if_neg hn
  simp only [floor32_eq_spec]
  unfold floor32Spec
  change (if exponent = 255 then value else if exponent ≥ 150 then value
    else if exponent < 127 then
      if value.negative && value.magnitude != 0 then ⟨0xbf800000⟩
      else assemble32 value.negative 0 0
    else assemble32 value.negative exponent
      (floorFraction value.negative fraction (2 ^ (150 - exponent)))).Finite ∧ _
  rw [if_neg (by omega)]
  by_cases hlarge : exponent ≥ 150
  · rw [if_pos hlarge]
    refine ⟨finite, rfl, ?_, ?_⟩
    · rw [hnormal (by omega)]
      exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
    · have hp := Nat.two_pow_pos 1074
      split <;> omega
  · rw [if_neg hlarge]
    by_cases hsmall : exponent < 127
    · rw [if_pos hsmall]
      have hb := subunit_bound value hsmall
      by_cases hs : (value.negative && value.magnitude != 0) = true
      · rw [if_pos hs]
        have hn : value.negative = true := (Bool.and_eq_true_iff.mp hs).1
        have hz : value.magnitude ≠ 0 := by simpa using (Bool.and_eq_true_iff.mp hs).2
        have hp := units_positive value hz
        have ho := negative_one_fields
        refine ⟨ho.1, ho.2.1.trans hn.symm, ?_, ?_⟩
        · rw [ho.2.2]
        · rw [hn, if_pos rfl, ho.2.2]
          omega
      · rw [if_neg hs]
        have hz := zero_fields value.negative
        refine ⟨hz.1, hz.2.1, ?_, ?_⟩
        · rw [hz.2.2]; exact dvd_zero _
        · rw [hz.2.2]
          cases hn : value.negative with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
          | true =>
            have hm : value.magnitude = 0 := by simpa [hn] using hs
            have hu : Conversion.magnitudeUnits32 value = 0 := by
              simp [Conversion.magnitudeUnits32, hm]
            simp only [↓reduceIte, hu]
            exact ⟨Nat.le_refl _, by simp⟩
    · rw [if_neg hsmall]
      rw [hnormal (by omega)]
      exact middle_magnitude value.negative exponent fraction (by omega) (by omega) hf

/-- Exact signed dyadic interpretation; exceptional words are classified separately. -/
def signedUnits (value : Binary32) : Int :=
  if value.negative then -(Conversion.magnitudeUnits32 value : Int)
  else Conversion.magnitudeUnits32 value

/-- Universal floor semantics on the actual finite binary32 domain.
The result is integral and lies below the input by strictly less than one;
zero signs are preserved separately, and exceptional words use the identity theorem. -/
theorem floor32_spec (value : Binary32) (finite : value.Finite) :
    (floor32 value).Finite ∧ (floor32 value).negative = value.negative ∧
    (2 ^ 1074 : Int) ∣ signedUnits (floor32 value) ∧
    signedUnits (floor32 value) ≤ signedUnits value ∧
      signedUnits value < signedUnits (floor32 value) + 2 ^ 1074 := by
  have h := floor_magnitude value finite
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · have hd : (2 ^ 1074 : Int) ∣ (Conversion.magnitudeUnits32 (floor32 value) : Int) := by
      exact_mod_cast h.2.2.1
    unfold signedUnits
    split
    · obtain ⟨factor, heq⟩ := hd
      exact ⟨-factor, by rw [heq, Int.mul_neg]⟩
    · exact hd
  · have hb := h.2.2.2
    unfold signedUnits
    rw [h.2.1]
    cases hn : value.negative <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    · exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
    · have hl : (Conversion.magnitudeUnits32 value : Int) ≤
          (Conversion.magnitudeUnits32 (floor32 value) : Int) := by exact_mod_cast hb.1
      have hr : (Conversion.magnitudeUnits32 (floor32 value) : Int) <
          (Conversion.magnitudeUnits32 value : Int) + 2 ^ 1074 := by exact_mod_cast hb.2
      omega

end AcornVerif.CurrentFloor
