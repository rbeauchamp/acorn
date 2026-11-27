import Acorn.Encoding
import Acorn.Rounding

namespace Acorn.Conversion

def normalSignificand (bits : UInt64) : UInt64 :=
  ((1 : UInt64) <<< 52) ||| (bits &&& 0xfffffffffffff)

theorem normalSignificand_bounds (bits : UInt64) :
    2 ^ 52 ≤ (normalSignificand bits).toNat ∧
      (normalSignificand bits).toNat < 2 ^ 53 := by
  change 2 ^ 52 ≤ (2 ^ 52 ||| (bits.toNat &&& (2 ^ 52 - 1))) ∧
    (2 ^ 52 ||| (bits.toNat &&& (2 ^ 52 - 1))) < 2 ^ 53
  exact ⟨Nat.left_le_or,
    Nat.or_lt_two_pow (by decide) (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))⟩

def roundedNormal (bits : UInt64) : UInt64 :=
  Rounding.wordShift64 (normalSignificand bits) 29

theorem roundedNormal_eq (bits : UInt64) :
    roundedNormal bits = Rounding.wordShift (normalSignificand bits) 29 := by
  exact Rounding.wordShift64_eq_wordShift _ 29

theorem roundedNormal_bounds (bits : UInt64) :
    2 ^ 23 ≤ (roundedNormal bits).toNat ∧ (roundedNormal bits).toNat ≤ 2 ^ 24 := by
  rw [roundedNormal_eq]
  exact ⟨Rounding.wordShift_leading_bit _ 23 29 (normalSignificand_bounds bits).1,
    Rounding.wordShift_carry_bound _ 24 29 (normalSignificand_bounds bits).2⟩

def normalizedNormal (bits : UInt64) : UInt64 :=
  let rounded := roundedNormal bits
  if rounded == ((1 : UInt64) <<< 24) then ((1 : UInt64) <<< 23) else rounded

theorem normalizedNormal_bounds (bits : UInt64) :
    2 ^ 23 ≤ (normalizedNormal bits).toNat ∧
      (normalizedNormal bits).toNat < 2 ^ 24 := by
  have bounds := roundedNormal_bounds bits
  dsimp only [normalizedNormal]
  split
  · decide
  · rename_i h
    have hn : (roundedNormal bits).toNat ≠ 2 ^ 24 := by
      intro heq
      have hw : roundedNormal bits = ((1 : UInt64) <<< 24) := UInt64.toNat.inj heq
      simp [hw] at h
    omega

theorem normalizedNormal_value (bits : UInt64) :
    (normalizedNormal bits).toNat *
      (if roundedNormal bits == ((1 : UInt64) <<< 24) then 2 else 1) =
        (roundedNormal bits).toNat := by
  dsimp only [normalizedNormal]
  split
  · rename_i h
    have hw : roundedNormal bits = ((1 : UInt64) <<< 24) := by simpa using h
    simp [hw]
  · simp_all

def normalFraction (bits : UInt64) : UInt32 :=
  (normalizedNormal bits).toUInt32 - ((1 : UInt32) <<< 23)

theorem normalFraction_exact (bits : UInt64) :
    (normalFraction bits).toNat + 2 ^ 23 = (normalizedNormal bits).toNat ∧
      (normalFraction bits).toNat < 2 ^ 23 := by
  have bounds := normalizedNormal_bounds bits
  have hfit : (normalizedNormal bits).toNat < 2 ^ 32 := by omega
  have hw : (normalizedNormal bits).toUInt32.toNat = (normalizedNormal bits).toNat := by
    rw [UInt64.toNat_toUInt32]
    exact Nat.mod_eq_of_lt hfit
  have hle : ((1 : UInt32) <<< 23) ≤ (normalizedNormal bits).toUInt32 := by
    rw [UInt32.le_iff_toNat_le, hw]
    exact bounds.1
  have hf : (normalFraction bits).toNat = (normalizedNormal bits).toNat - 2 ^ 23 := by
    unfold normalFraction
    rw [UInt32.toNat_sub_of_le _ _ hle, hw]
    rfl
  rw [hf]
  omega

theorem normalFraction_distance (bits : UInt64) :
    let source := (normalSignificand bits).toNat
    let decoded := ((normalFraction bits).toNat + 2 ^ 23) *
      (if roundedNormal bits == ((1 : UInt64) <<< 24) then 2 else 1) * 2 ^ 29
    2 * source ≤ 2 * decoded + 2 ^ 29 ∧ 2 * decoded ≤ 2 * source + 2 ^ 29 := by
  dsimp only
  rw [(normalFraction_exact bits).1, normalizedNormal_value]
  rw [roundedNormal_eq]
  exact Rounding.wordShift_distance (normalSignificand bits) 29

theorem normalFraction_tie (bits : UInt64)
    (htie : 2 ^ 29 = 2 * ((normalSignificand bits).toNat % 2 ^ 29)) :
    (normalFraction bits).toNat % 2 = 0 := by
  have hrounded : (roundedNormal bits).toNat % 2 = 0 := by
    rw [roundedNormal_eq, Rounding.wordShift_exact]
    exact Rounding.nearestEven_tie _ _ htie
  have hf := (normalFraction_exact bits).1
  dsimp only [normalizedNormal] at hf
  split at hf
  · change (normalFraction bits).toNat + 2 ^ 23 = 2 ^ 23 at hf
    omega
  · omega

def subnormalSignificand (bits : UInt64) : UInt64 :=
  if (bits >>> 52) &&& 0x7ff == 0 then bits &&& 0xfffffffffffff
  else normalSignificand bits

def subnormalShift (exponent : Nat) : Nat := if exponent = 0 then 925 else 926 - exponent

theorem subnormalShift_lower (exponent : Nat) (h : exponent < 897) :
    30 ≤ subnormalShift exponent := by
  unfold subnormalShift
  split <;> omega

theorem subnormalSignificand_upper (bits : UInt64) :
    (subnormalSignificand bits).toNat < 2 ^ 53 := by
  unfold subnormalSignificand
  split
  · change bits.toNat &&& (2 ^ 52 - 1) < 2 ^ 53
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · exact (normalSignificand_bounds bits).2

def subnormalFraction (bits : UInt64) (exponent : Nat) : UInt32 :=
  (Rounding.wordShift (subnormalSignificand bits) (subnormalShift exponent)).toUInt32

def subnormalFractionWord (bits exponent : UInt64) : UInt32 :=
  let shift := if exponent = 0 then 925 else if 926 < exponent then 0 else 926 - exponent
  (Rounding.wordShift64 (subnormalSignificand bits) shift).toUInt32

theorem subnormalFractionWord_eq (bits exponent : UInt64) :
    subnormalFractionWord bits exponent = subnormalFraction bits exponent.toNat := by
  have shiftValue : (if exponent = 0 then (925 : UInt64)
      else if 926 < exponent then 0 else 926 - exponent).toNat = subnormalShift exponent.toNat := by
    unfold subnormalShift
    split
    · rename_i zero
      have h : exponent.toNat = 0 := by rw [zero]; rfl
      simp only [h, ↓reduceIte]
      rfl
    · rename_i nonzero
      have h : exponent.toNat ≠ 0 := by intro h; exact nonzero (UInt64.toNat.inj h)
      simp only [h, ↓reduceIte]
      split
      · rename_i large
        change 926 < exponent.toNat at large
        change 0 = 926 - exponent.toNat
        omega
      · rename_i small
        rw [UInt64.toNat_sub_of_le]
        · rfl
        · change exponent.toNat ≤ 926
          change ¬ 926 < exponent.toNat at small
          omega
  dsimp only [subnormalFractionWord, subnormalFraction]
  congr 1
  apply UInt64.toNat.inj
  rw [Rounding.wordShift64_exact, Rounding.wordShift_exact, shiftValue]

theorem subnormalFraction_exact (bits : UInt64) (exponent : Nat) (h : exponent < 897) :
    (subnormalFraction bits exponent).toNat =
      Rounding.nearestEven (subnormalSignificand bits).toNat (2 ^ subnormalShift exponent) ∧
    (subnormalFraction bits exponent).toNat ≤ 2 ^ 23 := by
  have hs := subnormalShift_lower exponent h
  have hpow : 2 ^ 53 ≤ 2 ^ (23 + subnormalShift exponent) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hb := Rounding.wordShift_carry_bound (subnormalSignificand bits) 23
    (subnormalShift exponent) (Nat.lt_of_lt_of_le (subnormalSignificand_upper bits) hpow)
  have hfit : (Rounding.wordShift (subnormalSignificand bits) (subnormalShift exponent)).toNat <
      2 ^ 32 := by omega
  have hw : (subnormalFraction bits exponent).toNat =
      (Rounding.wordShift (subnormalSignificand bits) (subnormalShift exponent)).toNat := by
    change _ % (2 ^ 32) = _
    exact Nat.mod_eq_of_lt hfit
  exact ⟨hw.trans (Rounding.wordShift_exact _ _), hw ▸ hb⟩

theorem subnormalFraction_distance (bits : UInt64) (exponent : Nat) (h : exponent < 897) :
    let source := (subnormalSignificand bits).toNat
    let unit := 2 ^ subnormalShift exponent
    2 * source ≤ 2 * ((subnormalFraction bits exponent).toNat * unit) + unit ∧
      2 * ((subnormalFraction bits exponent).toNat * unit) ≤ 2 * source + unit := by
  dsimp only
  rw [(subnormalFraction_exact bits exponent h).1]
  exact Rounding.nearestEven_distance _ _ (Nat.two_pow_pos _)

theorem subnormalFraction_tie (bits : UInt64) (exponent : Nat) (h : exponent < 897)
    (htie : 2 ^ subnormalShift exponent =
      2 * ((subnormalSignificand bits).toNat % 2 ^ subnormalShift exponent)) :
    (subnormalFraction bits exponent).toNat % 2 = 0 := by
  rw [(subnormalFraction_exact bits exponent h).1]
  exact Rounding.nearestEven_tie _ _ htie

theorem normalFields_exact (exponent fraction : UInt32)
    (he : exponent.toNat < 256) (hf : fraction.toNat < 2 ^ 23) :
    ((exponent <<< 23) ||| fraction).toNat = exponent.toNat * 2 ^ 23 + fraction.toNat := by
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat, Nat.shiftLeft_eq]
  have hmul : exponent.toNat * 2 ^ 23 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hmul]
  simpa only [Nat.mul_comm] using (Nat.two_pow_add_eq_or_of_lt hf exponent.toNat).symm

def narrowSign (bits : UInt64) : UInt32 := ((bits >>> 63).toUInt32) <<< 31

theorem narrowSign_exact (bits : UInt64) :
    (narrowSign bits).toNat = (bits.toNat / 2 ^ 63) * 2 ^ 31 := by
  have hb := bits.toNat_lt
  simp only [narrowSign, UInt32.toNat_shiftLeft, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hq : bits.toNat / 2 ^ 63 < 2 := by omega
  have hm : bits.toNat / 2 ^ 63 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hm]
  change ((bits.toNat / 2 ^ 63) * 2 ^ 31) % (2 ^ 32) = _
  exact Nat.mod_eq_of_lt (by omega)

theorem narrowSign_magnitude (bits : UInt64) (magnitude : UInt32)
    (h : magnitude.toNat < 2 ^ 31) :
    (Binary32.mk (narrowSign bits ||| magnitude)).magnitude = magnitude.toNat := by
  change ((narrowSign bits).toNat ||| magnitude.toNat) &&& (2 ^ 31 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.or_mod_two_pow, narrowSign_exact]
  simp only [Nat.mul_mod_left, Nat.mod_eq_of_lt h, Nat.zero_or]

theorem narrowSign_highBit (bits : UInt64) (magnitude : UInt32)
    (h : magnitude.toNat < 2 ^ 31) :
    (narrowSign bits ||| magnitude).toNat / 2 ^ 31 = bits.toNat / 2 ^ 63 := by
  rw [UInt32.toNat_or, Nat.or_div_two_pow, narrowSign_exact,
    Nat.mul_div_cancel _ (Nat.two_pow_pos 31), Nat.div_eq_of_lt h, Nat.or_zero]

def normalExponent (bits : UInt64) (exponent : UInt64) : UInt64 :=
  if roundedNormal bits == ((1 : UInt64) <<< 24) then exponent + 1 else exponent

theorem normalExponent_bounds (bits exponent : UInt64)
    (hlo : 897 ≤ exponent.toNat) (hhi : exponent.toNat < 2047) :
    897 ≤ (normalExponent bits exponent).toNat ∧
      (normalExponent bits exponent).toNat ≤ 2047 := by
  unfold normalExponent
  split
  · simp only [UInt64.toNat_add, UInt64.toNat_ofNat]
    change 897 ≤ (exponent.toNat + 1) % (2 ^ 64) ∧
      (exponent.toNat + 1) % (2 ^ 64) ≤ 2047
    rw [Nat.mod_eq_of_lt (show exponent.toNat + 1 < 2 ^ 64 by omega)]
    omega
  · omega

theorem normalExponent_exact (bits exponent : UInt64) (h : exponent.toNat < 2048) :
    (normalExponent bits exponent).toNat = exponent.toNat +
      (if roundedNormal bits == ((1 : UInt64) <<< 24) then 1 else 0) := by
  unfold normalExponent
  split
  · simp only [UInt64.toNat_add, UInt64.toNat_ofNat]
    change (exponent.toNat + 1) % (2 ^ 64) = exponent.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [Nat.add_zero]

def normalMagnitude (bits exponent : UInt64) : UInt32 :=
  let rounded := roundedNormal bits
  let carry := rounded == ((1 : UInt64) <<< 24)
  let adjusted := if carry then exponent + 1 else exponent
  if adjusted > 1150 then 0x7f800000
  else
    let normalized := if carry then ((1 : UInt64) <<< 23) else rounded
    ((adjusted - 896).toUInt32 <<< 23) ||| (normalized.toUInt32 - ((1 : UInt32) <<< 23))

theorem normalMagnitude_components (bits exponent : UInt64) :
    normalMagnitude bits exponent =
      (if normalExponent bits exponent > 1150 then (0x7f800000 : UInt32)
      else ((normalExponent bits exponent - 896).toUInt32 <<< 23) ||| normalFraction bits) := by
  rfl

theorem normalMagnitude_finite_iff (bits exponent : UInt64)
    (hlo : 897 ≤ exponent.toNat) (hhi : exponent.toNat < 2047) :
    (normalMagnitude bits exponent).toNat < 0x7f800000 ↔
      (normalExponent bits exponent).toNat ≤ 1150 := by
  have hb := normalExponent_bounds bits exponent hlo hhi
  rw [normalMagnitude_components]
  split
  · rename_i h
    change 1150 < (normalExponent bits exponent).toNat at h
    change 0x7f800000 < 0x7f800000 ↔ _
    omega
  · rename_i h
    have hupper : (normalExponent bits exponent).toNat ≤ 1150 := by
      change ¬ (1150 < (normalExponent bits exponent).toNat) at h
      omega
    have hsub : (normalExponent bits exponent - 896).toNat =
        (normalExponent bits exponent).toNat - 896 := by
      rw [UInt64.toNat_sub_of_le]
      · rfl
      · change 896 ≤ (normalExponent bits exponent).toNat
        omega
    have hcast : (normalExponent bits exponent - 896).toUInt32.toNat =
        (normalExponent bits exponent).toNat - 896 := by
      rw [UInt64.toNat_toUInt32, hsub, Nat.mod_eq_of_lt (by omega)]
    rw [normalFields_exact _ _ (by rw [hcast]; omega) (normalFraction_exact bits).2, hcast]
    have hf := (normalFraction_exact bits).2
    omega

theorem normalMagnitude_bound (bits exponent : UInt64)
    (hlo : 897 ≤ exponent.toNat) (hhi : exponent.toNat < 2047) :
    (normalMagnitude bits exponent).toNat ≤ 0x7f800000 := by
  by_cases h : (normalExponent bits exponent).toNat ≤ 1150
  · exact Nat.le_of_lt
      ((normalMagnitude_finite_iff bits exponent hlo hhi).mpr h)
  · have hover : normalExponent bits exponent > 1150 := by
      change 1150 < (normalExponent bits exponent).toNat
      omega
    simp only [normalMagnitude_components, ite_eq_left hover]
    decide

theorem wordLog2_exact (word : UInt64) : word.log2.toNat = word.toNat.log2 := rfl

def widenSubnormalFraction (fraction : UInt64) : UInt64 :=
  let leading := fraction.log2
  let shift := if leading ≤ 52 then 52 - leading else 0
  (fraction - ((1 : UInt64) <<< leading)) <<< shift

theorem widenSubnormalFraction_def (fraction : UInt64) :
    widenSubnormalFraction fraction =
      (fraction - ((1 : UInt64) <<< fraction.toNat.log2.toUInt64)) <<<
        (52 - fraction.toNat.log2).toUInt64 := by
  have leading : fraction.log2 = fraction.toNat.log2.toUInt64 := by
    apply UInt64.toNat.inj
    rw [wordLog2_exact]
    symm
    exact UInt64.toNat_ofNat_of_lt' (by rw [← wordLog2_exact]; exact UInt64.toNat_lt _)
  have shift : (if fraction.log2 ≤ 52 then 52 - fraction.log2 else 0) =
      (52 - fraction.toNat.log2).toUInt64 := by
    apply UInt64.toNat.inj
    have fit : 52 - fraction.toNat.log2 < 2^64 := by omega
    rw [show (52 - fraction.toNat.log2).toUInt64.toNat = 52 - fraction.toNat.log2 from
      UInt64.toNat_ofNat_of_lt' fit]
    split
    · rename_i small
      rw [UInt64.toNat_sub_of_le _ _ small, wordLog2_exact]
      rfl
    · rename_i large
      have h : ¬ fraction.log2.toNat ≤ 52 := large
      rw [wordLog2_exact] at h
      change 0 = 52 - fraction.toNat.log2
      omega
  dsimp only [widenSubnormalFraction]
  rw [shift, leading]

def widenSubnormalExponent (fraction : UInt64) : UInt64 := fraction.log2 + 874

theorem widenSubnormalExponent_eq (fraction : UInt64) :
    widenSubnormalExponent fraction = (fraction.toNat.log2 + 874).toUInt64 := by
  apply UInt64.toNat.inj
  simp only [widenSubnormalExponent, UInt64.toNat_add, wordLog2_exact]
  rfl

theorem widenSubnormalFraction_exact (fraction : UInt64) (positive : 0 < fraction.toNat) (width : fraction.toNat < 2 ^ 23) :
    (widenSubnormalFraction fraction).toNat =
      (fraction.toNat - 2 ^ fraction.toNat.log2) * 2 ^ (52 - fraction.toNat.log2) := by
  have hn : fraction.toNat ≠ 0 := by omega
  have hl : fraction.toNat.log2 < 23 := (Nat.log2_lt hn).mpr width
  have hlead : 2 ^ fraction.toNat.log2 ≤ fraction.toNat := (Nat.log2_eq_iff hn).mp rfl |>.1
  have hpow : 2 ^ fraction.toNat.log2 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hone : (((1 : UInt64) <<< fraction.toNat.log2.toUInt64)).toNat = 2 ^ fraction.toNat.log2 := by
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, Nat.toUInt64, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
    have hfit : fraction.toNat.log2 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt (show fraction.toNat.log2 < 64 by omega)]
    simpa using Nat.mod_eq_of_lt hpow
  have hs : fraction.toNat.log2 ≤ 52 := by omega
  have hproduct : 2 ^ fraction.toNat.log2 * 2 ^ (52 - fraction.toNat.log2) = 2 ^ 52 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hs]
  have hsmall : fraction.toNat - 2 ^ fraction.toNat.log2 < 2 ^ fraction.toNat.log2 := by
    have hnupper := (Nat.log2_eq_iff hn).mp rfl |>.2
    rw [Nat.pow_succ] at hnupper
    omega
  have hshift : (fraction.toNat - 2 ^ fraction.toNat.log2) * 2 ^ (52 - fraction.toNat.log2) < 2 ^ 52 := by
    have hm := Nat.mul_lt_mul_of_pos_right hsmall (Nat.two_pow_pos (52 - fraction.toNat.log2))
    rwa [hproduct] at hm
  have hle : ((1 : UInt64) <<< fraction.toNat.log2.toUInt64) ≤ fraction := by
    change (((1 : UInt64) <<< fraction.toNat.log2.toUInt64)).toNat ≤ fraction.toNat
    rwa [hone]
  simp only [widenSubnormalFraction_def, UInt64.toNat_shiftLeft, UInt64.toNat_sub_of_le _ _ hle,
    hone, Nat.toUInt64, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show 52 - fraction.toNat.log2 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 52 - fraction.toNat.log2 < 64 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem widenSubnormalFraction_value (fraction : UInt64)
    (positive : 0 < fraction.toNat) (width : fraction.toNat < 2 ^ 23) :
    2 ^ 52 + (widenSubnormalFraction fraction).toNat =
      fraction.toNat * 2 ^ (52 - fraction.toNat.log2) := by
  have hn : fraction.toNat ≠ 0 := by omega
  have hl : fraction.toNat.log2 < 23 := (Nat.log2_lt hn).mpr width
  have hlead : 2 ^ fraction.toNat.log2 ≤ fraction.toNat := (Nat.log2_eq_iff hn).mp rfl |>.1
  have hproduct : 2 ^ fraction.toNat.log2 * 2 ^ (52 - fraction.toNat.log2) = 2 ^ 52 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (show fraction.toNat.log2 ≤ 52 by omega)]
  have hscaled := Nat.mul_le_mul_right (2 ^ (52 - fraction.toNat.log2)) hlead
  rw [hproduct] at hscaled
  rw [widenSubnormalFraction_exact fraction positive width, Nat.sub_mul, hproduct]
  omega

theorem widenSubnormalFraction_bound (fraction : UInt64)
    (positive : 0 < fraction.toNat) (width : fraction.toNat < 2 ^ 23) :
    (widenSubnormalFraction fraction).toNat < 2 ^ 52 := by
  have hn : fraction.toNat ≠ 0 := by omega
  have hl : fraction.toNat.log2 < 23 := (Nat.log2_lt hn).mpr width
  have hsmall : fraction.toNat - 2 ^ fraction.toNat.log2 < 2 ^ fraction.toNat.log2 := by
    have hupper := (Nat.log2_eq_iff hn).mp rfl |>.2
    rw [Nat.pow_succ] at hupper
    omega
  have hproduct : 2 ^ fraction.toNat.log2 * 2 ^ (52 - fraction.toNat.log2) = 2 ^ 52 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (show fraction.toNat.log2 ≤ 52 by omega)]
  rw [widenSubnormalFraction_exact fraction positive width]
  have hm := Nat.mul_lt_mul_of_pos_right hsmall (Nat.two_pow_pos (52 - fraction.toNat.log2))
  rwa [hproduct] at hm

def widenFraction (fraction : UInt64) : UInt64 := fraction <<< 29

theorem widenFraction_exact (fraction : UInt64) (width : fraction.toNat < 2 ^ 23) :
    (widenFraction fraction).toNat = fraction.toNat * 2 ^ 29 ∧
      (widenFraction fraction).toNat < 2 ^ 52 := by
  have hproduct : fraction.toNat * 2 ^ 29 < 2 ^ 52 := by omega
  simp only [widenFraction, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, Nat.shiftLeft_eq]
  change fraction.toNat * 2 ^ 29 % (2 ^ 64) = fraction.toNat * 2 ^ 29 ∧
    fraction.toNat * 2 ^ 29 % (2 ^ 64) < 2 ^ 52
  rw [Nat.mod_eq_of_lt (show fraction.toNat * 2 ^ 29 < 2 ^ 64 by omega)]
  exact ⟨rfl, hproduct⟩

theorem wideFields_exact (exponent fraction : UInt64)
    (he : exponent.toNat < 2048) (hf : fraction.toNat < 2 ^ 52) :
    ((exponent <<< 52) ||| fraction).toNat = exponent.toNat * 2 ^ 52 + fraction.toNat := by
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, Nat.shiftLeft_eq]
  change (exponent.toNat * 2 ^ 52 % (2 ^ 64)) ||| fraction.toNat = _
  have hmul : exponent.toNat * 2 ^ 52 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hmul]
  simpa only [Nat.mul_comm] using (Nat.two_pow_add_eq_or_of_lt hf exponent.toNat).symm

def widenSign (bits : UInt32) : UInt64 := (bits.toUInt64 >>> 31) <<< 63

theorem widenSign_exact (bits : UInt32) :
    (widenSign bits).toNat = (bits.toNat / 2 ^ 31) * 2 ^ 63 := by
  have hb := bits.toNat_lt
  simp only [widenSign, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    UInt32.toNat_toUInt64, UInt64.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change ((bits.toNat / 2 ^ 31) * 2 ^ 63) % (2 ^ 64) = _
  have hq : bits.toNat / 2 ^ 31 < 2 := by omega
  exact Nat.mod_eq_of_lt (by omega)

theorem widenSign_magnitude (bits : UInt32) (magnitude : UInt64)
    (h : magnitude.toNat < 2 ^ 63) :
    (Binary64.mk (widenSign bits ||| magnitude)).magnitude = magnitude.toNat := by
  change ((widenSign bits).toNat ||| magnitude.toNat) &&& (2 ^ 63 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.or_mod_two_pow, widenSign_exact]
  simp only [Nat.mul_mod_left, Nat.mod_eq_of_lt h, Nat.zero_or]

theorem widenSign_highBit (bits : UInt32) (magnitude : UInt64)
    (h : magnitude.toNat < 2 ^ 63) :
    (widenSign bits ||| magnitude).toNat / 2 ^ 63 = bits.toNat / 2 ^ 31 := by
  rw [UInt64.toNat_or, Nat.or_div_two_pow, widenSign_exact,
    Nat.mul_div_cancel _ (Nat.two_pow_pos 63), Nat.div_eq_of_lt h, Nat.or_zero]

def magnitudeUnits64 (value : Binary64) : Nat :=
  let exponent := value.magnitude / 2 ^ 52
  let fraction := value.magnitude % 2 ^ 52
  if exponent = 0 then fraction else (2 ^ 52 + fraction) * 2 ^ (exponent - 1)

def magnitudeUnits32 (value : Binary32) : Nat :=
  let exponent := value.magnitude / 2 ^ 23
  let fraction := value.magnitude % 2 ^ 23
  if exponent = 0 then fraction * 2 ^ 925
  else (2 ^ 23 + fraction) * 2 ^ (exponent + 924)

theorem fields32_decomposition (value : Binary32) :
    value.magnitude =
      (((value.bits >>> 23) &&& 0xff) : UInt32).toNat * 2 ^ 23 +
      ((value.bits &&& 0x7fffff) : UInt32).toNat := by
  simp only [Binary32.magnitude, UInt32.toNat_and, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  change value.bits.toNat &&& (2 ^ 31 - 1) =
    ((value.bits.toNat / 2 ^ 23) &&& (2 ^ 8 - 1)) * 2 ^ 23 +
      (value.bits.toNat &&& (2 ^ 23 - 1))
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem fields32_bounds (value : Binary32) :
    (((value.bits >>> 23) &&& 0xff) : UInt32).toNat < 256 ∧
      ((value.bits &&& 0x7fffff) : UInt32).toNat < 2 ^ 23 := by
  constructor
  · change ((value.bits >>> 23).toNat &&& 255) < 256
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · change (value.bits.toNat &&& (2 ^ 23 - 1)) < 2 ^ 23
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem fields32_units (value : Binary32) :
    magnitudeUnits32 value =
      let exponent := (((value.bits >>> 23) &&& 0xff) : UInt32).toNat
      let fraction := ((value.bits &&& 0x7fffff) : UInt32).toNat
      if exponent = 0 then fraction * 2 ^ 925
      else (2 ^ 23 + fraction) * 2 ^ (exponent + 924) := by
  have hf := (fields32_bounds value).2
  dsimp only [magnitudeUnits32]
  rw [fields32_decomposition]
  have hdiv : ((((value.bits >>> 23) &&& 0xff) : UInt32).toNat * 2 ^ 23 +
      ((value.bits &&& 0x7fffff) : UInt32).toNat) / 2 ^ 23 =
      (((value.bits >>> 23) &&& 0xff) : UInt32).toNat := by omega
  have hmod : ((((value.bits >>> 23) &&& 0xff) : UInt32).toNat * 2 ^ 23 +
      ((value.bits &&& 0x7fffff) : UInt32).toNat) % 2 ^ 23 =
      ((value.bits &&& 0x7fffff) : UInt32).toNat := by omega
  rw [hdiv, hmod]

theorem wideFields_units (bits : UInt32) (exponent fraction : UInt64)
    (he : 0 < exponent.toNat) (hemax : exponent.toNat < 2048)
    (hf : fraction.toNat < 2 ^ 52) :
    magnitudeUnits64 ⟨widenSign bits ||| ((exponent <<< 52) ||| fraction)⟩ =
      (2 ^ 52 + fraction.toNat) * 2 ^ (exponent.toNat - 1) := by
  have hfields := wideFields_exact exponent fraction hemax hf
  have hfit : ((exponent <<< 52) ||| fraction).toNat < 2 ^ 63 := by rw [hfields]; omega
  have hm := widenSign_magnitude bits _ hfit
  rw [hfields] at hm
  have hdiv : (exponent.toNat * 2 ^ 52 + fraction.toNat) / 2 ^ 52 = exponent.toNat := by omega
  have hmod : (exponent.toNat * 2 ^ 52 + fraction.toNat) % 2 ^ 52 = fraction.toNat := by omega
  simp only [magnitudeUnits64, hm, hdiv, hmod, Nat.ne_of_gt he, ↓reduceIte]

theorem wideFields_finite (bits : UInt32) (exponent fraction : UInt64)
    (he : exponent.toNat < 2047) (hf : fraction.toNat < 2 ^ 52) :
    (Binary64.mk (widenSign bits ||| ((exponent <<< 52) ||| fraction))).Finite := by
  have hfields := wideFields_exact exponent fraction (by omega) hf
  have hfit : ((exponent <<< 52) ||| fraction).toNat < 2 ^ 63 := by rw [hfields]; omega
  change (Binary64.mk (widenSign bits ||| ((exponent <<< 52) ||| fraction))).magnitude < _
  rw [widenSign_magnitude bits _ hfit, hfields]
  omega

theorem wideFields_sign (bits : UInt32) (exponent fraction : UInt64)
    (he : exponent.toNat < 2048) (hf : fraction.toNat < 2 ^ 52) :
    (widenSign bits ||| ((exponent <<< 52) ||| fraction)).toNat / 2 ^ 63 =
      bits.toNat / 2 ^ 31 := by
  have hfields := wideFields_exact exponent fraction he hf
  have hfit : ((exponent <<< 52) ||| fraction).toNat < 2 ^ 63 := by rw [hfields]; omega
  exact widenSign_highBit bits _ hfit

theorem narrowFields_units (bits : UInt64) (exponent fraction : UInt32)
    (he : 0 < exponent.toNat) (hemax : exponent.toNat < 256)
    (hf : fraction.toNat < 2 ^ 23) :
    magnitudeUnits32 ⟨narrowSign bits ||| ((exponent <<< 23) ||| fraction)⟩ =
      (2 ^ 23 + fraction.toNat) * 2 ^ (exponent.toNat + 924) := by
  have hfields := normalFields_exact exponent fraction hemax hf
  have hfit : ((exponent <<< 23) ||| fraction).toNat < 2 ^ 31 := by rw [hfields]; omega
  have hm := narrowSign_magnitude bits _ hfit
  rw [hfields] at hm
  have hdiv : (exponent.toNat * 2 ^ 23 + fraction.toNat) / 2 ^ 23 = exponent.toNat := by omega
  have hmod : (exponent.toNat * 2 ^ 23 + fraction.toNat) % 2 ^ 23 = fraction.toNat := by omega
  simp only [magnitudeUnits32, hm, hdiv, hmod, Nat.ne_of_gt he, ↓reduceIte]

set_option exponentiation.threshold 1024 in
theorem subnormalFields_units (bits : UInt64) (magnitude : UInt32)
    (h : magnitude.toNat ≤ 2 ^ 23) :
    magnitudeUnits32 ⟨narrowSign bits ||| magnitude⟩ = magnitude.toNat * 2 ^ 925 := by
  have hm := narrowSign_magnitude bits magnitude (by omega)
  simp only [magnitudeUnits32, hm]
  by_cases hsmall : magnitude.toNat < 2 ^ 23
  · rw [Nat.div_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall]
    rfl
  · have heq : magnitude.toNat = 2 ^ 23 := by omega
    rw [heq]
    rw [Nat.div_self (by decide : 0 < 2 ^ 23), Nat.mod_self, ite_eq_right (by decide : ¬ 1 = 0), Nat.add_zero]

theorem fields64_decomposition (value : Binary64) :
    value.magnitude =
      (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat * 2 ^ 52 +
      ((value.bits &&& 0xfffffffffffff) : UInt64).toNat := by
  simp only [Binary64.magnitude, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  change value.bits.toNat &&& (2 ^ 63 - 1) =
    ((value.bits.toNat / 2 ^ 52) &&& (2 ^ 11 - 1)) * 2 ^ 52 +
      (value.bits.toNat &&& (2 ^ 52 - 1))
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem fraction64_bound (bits : UInt64) :
    ((bits &&& 0xfffffffffffff) : UInt64).toNat < 2 ^ 52 := by
  change (bits.toNat &&& (2 ^ 52 - 1)) < 2 ^ 52
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem normalSignificand_value (bits : UInt64) :
    (normalSignificand bits).toNat = 2 ^ 52 + ((bits &&& 0xfffffffffffff) : UInt64).toNat := by
  change 2 ^ 52 ||| (bits.toNat &&& (2 ^ 52 - 1)) = 2 ^ 52 + (bits.toNat &&& (2 ^ 52 - 1))
  have hf : bits.toNat &&& (2 ^ 52 - 1) < 2 ^ 52 := fraction64_bound bits
  rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt hf, Nat.add_comm]

theorem fields64_units (value : Binary64) :
    magnitudeUnits64 value =
      let exponent := (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat
      let fraction := ((value.bits &&& 0xfffffffffffff) : UInt64).toNat
      if exponent = 0 then fraction else (2 ^ 52 + fraction) * 2 ^ (exponent - 1) := by
  have hf := fraction64_bound value.bits
  dsimp only [magnitudeUnits64]
  rw [fields64_decomposition]
  have hdiv : ((((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat * 2 ^ 52 +
      ((value.bits &&& 0xfffffffffffff) : UInt64).toNat) / 2 ^ 52 =
      (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := by omega
  have hmod : ((((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat * 2 ^ 52 +
      ((value.bits &&& 0xfffffffffffff) : UInt64).toNat) % 2 ^ 52 =
      ((value.bits &&& 0xfffffffffffff) : UInt64).toNat := by omega
  rw [hdiv, hmod]

def sourceScale64 (exponent : Nat) : Nat := if exponent = 0 then 1 else 2 ^ (exponent - 1)

theorem fields64_scaled_units (value : Binary64) :
    magnitudeUnits64 value = (subnormalSignificand value.bits).toNat *
      sourceScale64 (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := by
  rw [fields64_units]
  dsimp only
  by_cases hz : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat = 0
  · have hw : ((value.bits >>> 52) &&& 0x7ff : UInt64) = 0 := UInt64.toNat.inj hz
    simp only [sourceScale64, subnormalSignificand, hw, UInt64.toNat_zero,
      BEq.rfl, ↓reduceIte, Nat.mul_one]
  · have hw : ((value.bits >>> 52) &&& 0x7ff : UInt64) ≠ 0 := by
      intro h
      exact hz (congrArg UInt64.toNat h)
    have hb : (((value.bits >>> 52) &&& 0x7ff : UInt64) == 0) = false := by simpa using hw
    simp only [sourceScale64, subnormalSignificand, hz, hb, Bool.false_eq_true,
      ↓reduceIte, normalSignificand_value]

set_option exponentiation.threshold 1024 in
theorem subnormalScale_exact (exponent : Nat) (h : exponent < 897) :
    2 ^ subnormalShift exponent * sourceScale64 exponent = 2 ^ 925 := by
  unfold subnormalShift sourceScale64
  split
  · rw [Nat.mul_one]
  · rename_i hnonzero
    rw [← Nat.pow_add, show 926 - exponent + (exponent - 1) = 925 by omega]

theorem normalMagnitude_units (bits exponent : UInt64) (hlo : 897 ≤ exponent.toNat) (hhi : exponent.toNat < 2047)
    (hfinite : (normalExponent bits exponent).toNat ≤ 1150) :
    magnitudeUnits32 ⟨narrowSign bits ||| normalMagnitude bits exponent⟩ =
      (normalizedNormal bits).toNat * 2 ^ ((normalExponent bits exponent).toNat + 28) := by
  have hb := normalExponent_bounds bits exponent hlo hhi
  have hnot : ¬ normalExponent bits exponent > 1150 := by
    change ¬ 1150 < (normalExponent bits exponent).toNat
    omega
  have hsub : (normalExponent bits exponent - 896).toNat =
      (normalExponent bits exponent).toNat - 896 := by
    rw [UInt64.toNat_sub_of_le]
    · rfl
    · change 896 ≤ (normalExponent bits exponent).toNat
      omega
  have hcast : (normalExponent bits exponent - 896).toUInt32.toNat =
      (normalExponent bits exponent).toNat - 896 := by
    rw [UInt64.toNat_toUInt32, hsub, Nat.mod_eq_of_lt (by omega)]
  rw [normalMagnitude_components]
  rw [ite_eq_right hnot, narrowFields_units bits _ _ (by rw [hcast]; omega)
    (by rw [hcast]; omega) (normalFraction_exact bits).2, hcast]
  rw [Nat.add_comm (2 ^ 23), (normalFraction_exact bits).1]
  rw [show (normalExponent bits exponent).toNat - 896 + 924 =
    (normalExponent bits exponent).toNat + 28 by omega]

theorem normalExponent_scale (bits exponent : UInt64) (hhi : exponent.toNat < 2047) :
    2 ^ ((normalExponent bits exponent).toNat + 28) =
      (if roundedNormal bits == ((1 : UInt64) <<< 24) then 2 else 1) *
        2 ^ (exponent.toNat + 28) := by
  unfold normalExponent
  split
  · simp only [UInt64.toNat_add, UInt64.toNat_ofNat]
    change 2 ^ ((exponent.toNat + 1) % (2 ^ 64) + 28) = 2 * 2 ^ (exponent.toNat + 28)
    rw [Nat.mod_eq_of_lt (show exponent.toNat + 1 < 2 ^ 64 by omega)]
    rw [show exponent.toNat + 1 + 28 = exponent.toNat + 28 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  · simp

theorem normalMagnitude_rounded_units (bits exponent : UInt64)
    (hlo : 897 ≤ exponent.toNat) (hhi : exponent.toNat < 2047)
    (hfinite : (normalExponent bits exponent).toNat ≤ 1150) :
    magnitudeUnits32 ⟨narrowSign bits ||| normalMagnitude bits exponent⟩ =
      (roundedNormal bits).toNat * 2 ^ (exponent.toNat + 28) := by
  rw [normalMagnitude_units bits exponent hlo hhi hfinite, normalExponent_scale bits exponent hhi,
    ← Nat.mul_assoc, normalizedNormal_value]

theorem normalMagnitude_distance (value : Binary64)
    (hlo : 897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat)
    (hhi : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 2047)
    (hfinite : (normalExponent value.bits ((value.bits >>> 52) &&& 0x7ff)).toNat ≤ 1150) :
    let exponent := ((value.bits >>> 52) &&& 0x7ff : UInt64)
    let result := Binary32.mk (narrowSign value.bits ||| normalMagnitude value.bits exponent)
    2 * magnitudeUnits64 value ≤ 2 * magnitudeUnits32 result + 2 ^ (exponent.toNat + 28) ∧
      2 * magnitudeUnits32 result ≤ 2 * magnitudeUnits64 value + 2 ^ (exponent.toNat + 28) := by
  let exponent : UInt64 := (value.bits >>> 52) &&& 0x7ff
  have hsource : magnitudeUnits64 value =
      (normalSignificand value.bits).toNat * 2 ^ (exponent.toNat - 1) := by
    rw [fields64_units]
    dsimp only
    rw [ite_eq_right (show ¬ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat = 0 by omega)]
    rw [← normalSignificand_value]
  have hscale : 2 ^ 29 * 2 ^ (exponent.toNat - 1) = 2 ^ (exponent.toNat + 28) := by
    rw [← Nat.pow_add]
    have hpos : 0 < exponent.toNat := by exact Nat.lt_of_lt_of_le (by decide) hlo
    rw [show 29 + (exponent.toNat - 1) = exponent.toNat + 28 by omega]
  have hrounded : (roundedNormal value.bits).toNat =
      Rounding.nearestEven (normalSignificand value.bits).toNat (2 ^ 29) :=
    by rw [roundedNormal_eq, Rounding.wordShift_exact]
  dsimp only
  rw [hsource, normalMagnitude_rounded_units value.bits exponent hlo hhi hfinite, hrounded]
  have hd := Rounding.nearestEven_scaled_distance (normalSignificand value.bits).toNat
    (2 ^ 29) (2 ^ (exponent.toNat - 1)) (Nat.two_pow_pos 29)
  simpa only [Nat.mul_assoc, hscale] using hd

set_option exponentiation.threshold 1024 in
theorem subnormalMagnitude_distance (value : Binary64)
    (h : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 897) :
    let exponent := (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat
    let result := Binary32.mk (narrowSign value.bits ||| subnormalFraction value.bits exponent)
    2 * magnitudeUnits64 value ≤ 2 * magnitudeUnits32 result + 2 ^ 925 ∧
      2 * magnitudeUnits32 result ≤ 2 * magnitudeUnits64 value + 2 ^ 925 := by
  let exponent := (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat
  dsimp only
  rw [subnormalFields_units value.bits _ (subnormalFraction_exact value.bits exponent h).2,
    (subnormalFraction_exact value.bits exponent h).1, fields64_scaled_units]
  have hd := Rounding.nearestEven_scaled_distance (subnormalSignificand value.bits).toNat
    (2 ^ subnormalShift exponent) (sourceScale64 exponent) (Nat.two_pow_pos _)
  simpa only [Nat.mul_assoc, subnormalScale_exact exponent h] using hd

def widenNaN (value : Binary32) : Binary64 :=
  ⟨(Float32.ofBits value.bits).toFloat.toBits⟩

def narrowNaN (value : Binary64) : Binary32 :=
  ⟨(Float.ofBits value.bits).toFloat32.toBits⟩

def widen (x : Binary32) : Binary64 :=
  let b := x.bits
  let sign := widenSign b
  let e : UInt32 := (b >>> 23) &&& 0xFF
  let f : UInt64 := (b &&& 0x7FFFFF).toUInt64
  if e == 0xFF then
    if f == 0 then Binary64.mk (sign ||| ((0x7FF : UInt64) <<< 52))
    else widenNaN x
  else if e == 0 then
    if f == 0 then Binary64.mk sign
    else
      let e64 := widenSubnormalExponent f
      let frac64 := widenSubnormalFraction f
      Binary64.mk (sign ||| ((e64 <<< 52) ||| frac64))
  else
    Binary64.mk (sign ||| (((e.toUInt64 + 896) <<< 52) ||| widenFraction f))

theorem widen_def (x : Binary32) : widen x =
  let b := x.bits
  let sign := widenSign b
  let e : UInt32 := (b >>> 23) &&& 0xFF
  let f : UInt64 := (b &&& 0x7FFFFF).toUInt64
  if e == 0xFF then
    if f == 0 then Binary64.mk (sign ||| ((0x7FF : UInt64) <<< 52))
    else widenNaN x
  else if e == 0 then
    if f == 0 then Binary64.mk sign
    else
      let L := f.toNat.log2
      let e64 : UInt64 := (L + 874).toUInt64
      let frac64 := widenSubnormalFraction f
      Binary64.mk (sign ||| ((e64 <<< 52) ||| frac64))
  else
    Binary64.mk (sign ||| (((e.toUInt64 + 896) <<< 52) ||| widenFraction f)) := by
  unfold widen
  simp only [widenSubnormalExponent_eq]

theorem widen_magnitude_exact (value : Binary32) (finite : value.Finite) :
    magnitudeUnits64 (widen value) = magnitudeUnits32 value := by
  let e : UInt32 := (value.bits >>> 23) &&& 0xff
  let f : UInt64 := (value.bits &&& 0x7fffff).toUInt64
  have hfields : value.magnitude = e.toNat * 2 ^ 23 + f.toNat := fields32_decomposition value
  have hwidth : f.toNat < 2 ^ 23 := (fields32_bounds value).2
  have hewidth : e.toNat < 255 := by
    change value.magnitude < 0x7f800000 at finite
    omega
  have hsource : magnitudeUnits32 value =
      if e.toNat = 0 then f.toNat * 2 ^ 925
      else (2 ^ 23 + f.toNat) * 2 ^ (e.toNat + 924) := fields32_units value
  have hexcept : (e == 0xff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  rw [hsource]
  simp only [widen_def]
  change magnitudeUnits64 (if e == 0xff then _ else if e == 0 then _ else _) = _
  rw [hexcept]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change magnitudeUnits64 (if e == 0 then
    if f == 0 then ⟨widenSign value.bits⟩ else
      ⟨widenSign value.bits ||| (((f.toNat.log2 + 874).toUInt64 <<< 52) ||| widenSubnormalFraction f)⟩
    else ⟨widenSign value.bits ||| (((e.toUInt64 + 896) <<< 52) ||| widenFraction f)⟩) = _
  by_cases ezero : e = 0
  · simp only [ezero, BEq.rfl, ↓reduceIte, UInt32.toNat_zero]
    by_cases fzero : f = 0
    · simp only [fzero, BEq.rfl, ↓reduceIte, UInt64.toNat_zero, Nat.zero_mul]
      have hm := widenSign_magnitude value.bits 0 (by decide)
      simp only [UInt64.or_zero, UInt64.toNat_zero] at hm
      simp only [magnitudeUnits64, hm, Nat.zero_div, Nat.zero_mod, ↓reduceIte]
    · have hfpositive : 0 < f.toNat := by
        have : f.toNat ≠ 0 := by intro h; exact fzero (UInt64.toNat.inj h)
        omega
      have hfb : (f == 0) = false := by simpa using fzero
      simp only [hfb, Bool.false_eq_true, ↓reduceIte]
      have hl : f.toNat.log2 < 23 := (Nat.log2_lt (by omega)).mpr hwidth
      have hecast : (f.toNat.log2 + 874).toUInt64.toNat = f.toNat.log2 + 874 := by
        change (f.toNat.log2 + 874) % (2 ^ 64) = _
        exact Nat.mod_eq_of_lt (by omega)
      rw [wideFields_units value.bits _ _ (by rw [hecast]; omega)
        (by rw [hecast]; omega) (widenSubnormalFraction_bound f hfpositive hwidth), hecast,
        widenSubnormalFraction_value f hfpositive hwidth, Nat.mul_assoc, ← Nat.pow_add]
      rw [show 52 - f.toNat.log2 + (f.toNat.log2 + 874 - 1) = 925 by omega]
  · have heb : (e == 0) = false := by simpa using ezero
    have henat : e.toNat ≠ 0 := by intro h; exact ezero (UInt32.toNat.inj h)
    simp only [heb, Bool.false_eq_true, ↓reduceIte, henat]
    have hecast : (e.toUInt64 + 896).toNat = e.toNat + 896 := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
      change (e.toNat + 896) % (2 ^ 64) = _
      exact Nat.mod_eq_of_lt (by omega)
    rw [wideFields_units value.bits _ _ (by rw [hecast]; omega)
      (by rw [hecast]; omega) (widenFraction_exact f hwidth).2, hecast,
      (widenFraction_exact f hwidth).1]
    have hfactor : 2 ^ 52 + f.toNat * 2 ^ 29 = (2 ^ 23 + f.toNat) * 2 ^ 29 := by
      rw [Nat.add_mul]
    rw [hfactor, Nat.mul_assoc, ← Nat.pow_add]
    rw [show 29 + (e.toNat + 896 - 1) = e.toNat + 924 by omega]

theorem widen_finite (value : Binary32) (finite : value.Finite) : (widen value).Finite := by
  let e : UInt32 := (value.bits >>> 23) &&& 0xff
  let f : UInt64 := (value.bits &&& 0x7fffff).toUInt64
  have hfields : value.magnitude = e.toNat * 2 ^ 23 + f.toNat := fields32_decomposition value
  have hwidth : f.toNat < 2 ^ 23 := (fields32_bounds value).2
  have hewidth : e.toNat < 255 := by
    change value.magnitude < 0x7f800000 at finite
    omega
  have hexcept : (e == 0xff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  simp only [widen_def]
  change Binary64.Finite (if e == 0xff then _ else if e == 0 then _ else _)
  rw [hexcept]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if e == 0 then
    if f == 0 then Binary64.mk (widenSign value.bits) else
      ⟨widenSign value.bits ||| (((f.toNat.log2 + 874).toUInt64 <<< 52) ||| widenSubnormalFraction f)⟩
    else ⟨widenSign value.bits ||| (((e.toUInt64 + 896) <<< 52) ||| widenFraction f)⟩).Finite
  split
  · split
    · have hm := widenSign_magnitude value.bits 0 (by decide)
      simp only [UInt64.or_zero, UInt64.toNat_zero] at hm
      change (Binary64.mk (widenSign value.bits)).magnitude < _
      rw [hm]
      decide
    · rename_i hfzero
      have hfpositive : 0 < f.toNat := by
        have hfneq : f ≠ 0 := by simpa using hfzero
        have : f.toNat ≠ 0 := by intro h; exact hfneq (UInt64.toNat.inj h)
        omega
      have hl : f.toNat.log2 < 23 := (Nat.log2_lt (by omega)).mpr hwidth
      have hecast : (f.toNat.log2 + 874).toUInt64.toNat = f.toNat.log2 + 874 := by
        change (f.toNat.log2 + 874) % (2 ^ 64) = _
        exact Nat.mod_eq_of_lt (by omega)
      exact wideFields_finite value.bits _ _ (by rw [hecast]; omega)
        (widenSubnormalFraction_bound f hfpositive hwidth)
  · have hecast : (e.toUInt64 + 896).toNat = e.toNat + 896 := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
      change (e.toNat + 896) % (2 ^ 64) = _
      exact Nat.mod_eq_of_lt (by omega)
    exact wideFields_finite value.bits _ _ (by rw [hecast]; omega) (widenFraction_exact f hwidth).2

def narrow (y : Binary64) : Binary32 :=
  let b := y.bits
  let sign32 := narrowSign b
  let e : UInt64 := (b >>> 52) &&& 0x7FF
  let f : UInt64 := b &&& 0xFFFFFFFFFFFFF
  if e == 0x7FF then
    if f == 0 then Binary32.mk (sign32 ||| 0x7f800000)
    else narrowNaN y
  else if e ≥ 897 then
    Binary32.mk (sign32 ||| normalMagnitude b e)
  else
    Binary32.mk (sign32 ||| subnormalFractionWord b e)

theorem narrow_def (y : Binary64) : narrow y =
  let b := y.bits
  let sign32 := narrowSign b
  let e : UInt64 := (b >>> 52) &&& 0x7FF
  let f : UInt64 := b &&& 0xFFFFFFFFFFFFF
  if e == 0x7FF then
    if f == 0 then Binary32.mk (sign32 ||| 0x7f800000)
    else narrowNaN y
  else if e ≥ 897 then
    Binary32.mk (sign32 ||| normalMagnitude b e)
  else
    Binary32.mk (sign32 ||| subnormalFraction b e.toNat) := by
  unfold narrow
  simp only [subnormalFractionWord_eq]

theorem narrow_finite_input_bound (value : Binary64)
    (h : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 2047) :
    (narrow value).magnitude ≤ 0x7f800000 := by
  simp only [narrow_def]
  split
  · rename_i hexception
    have heq : ((value.bits >>> 52) &&& 0x7ff : UInt64) = 0x7ff := by simpa using hexception
    rw [heq] at h
    contradiction
  · split
    · rename_i hnormal
      have hlo : 897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := hnormal
      have hb := normalMagnitude_bound value.bits _ hlo h
      rw [narrowSign_magnitude _ _ (by omega)]
      exact hb
    · rename_i hsubnormal
      have hlo : ¬ 897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := hsubnormal
      have hb := (subnormalFraction_exact value.bits (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat (by omega)).2
      rw [narrowSign_magnitude _ _ (by omega)]
      omega

theorem narrow_sign (value : Binary64) (finite : value.Finite) :
    (narrow value).bits.toNat / 2 ^ 31 = value.bits.toNat / 2 ^ 63 := by
  have hfields := fields64_decomposition value
  have hewidth : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 2047 := by
    change value.magnitude < 0x7ff0000000000000 at finite
    omega
  simp only [narrow_def]
  split
  · rename_i hexception
    have heq : ((value.bits >>> 52) &&& 0x7ff : UInt64) = 0x7ff := by simpa using hexception
    rw [heq] at hewidth
    contradiction
  · split
    · rename_i hnormal
      have hlo : 897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := hnormal
      have hb := normalMagnitude_bound value.bits _ hlo hewidth
      exact narrowSign_highBit _ _ (by omega)
    · rename_i hsubnormal
      have hlo : ¬ 897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := hsubnormal
      have hb := (subnormalFraction_exact value.bits
        (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat (by omega)).2
      exact narrowSign_highBit _ _ (by omega)

theorem narrow_finite_iff (value : Binary64) (finite : value.Finite) :
    (narrow value).Finite ↔
      (normalExponent value.bits ((value.bits >>> 52) &&& 0x7ff)).toNat ≤ 1150 := by
  let exponent : UInt64 := (value.bits >>> 52) &&& 0x7ff
  have hfields := fields64_decomposition value
  have hewidth : exponent.toNat < 2047 := by
    change value.magnitude < 0x7ff0000000000000 at finite
    change value.magnitude = exponent.toNat * 2 ^ 52 + _ at hfields
    omega
  have hexcept : (exponent == 0x7ff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  have hresult : narrow value =
      if exponent ≥ 897 then ⟨narrowSign value.bits ||| normalMagnitude value.bits exponent⟩
      else ⟨narrowSign value.bits ||| subnormalFraction value.bits exponent.toNat⟩ := by
    simp only [narrow_def, show (value.bits >>> 52 &&& 0x7ff) = exponent from rfl,
      hexcept, Bool.false_eq_true, ↓reduceIte]
  rw [hresult]
  by_cases hnormal : exponent ≥ 897
  · have hlo : 897 ≤ exponent.toNat := hnormal
    rw [ite_eq_left hnormal]
    change (Binary32.mk (narrowSign value.bits ||| normalMagnitude value.bits exponent)).magnitude < _ ↔ _
    have hb := normalMagnitude_bound value.bits exponent hlo hewidth
    rw [narrowSign_magnitude _ _ (by omega)]
    exact normalMagnitude_finite_iff value.bits exponent hlo hewidth
  · have hsubnormal : exponent.toNat < 897 := by
      change ¬ 897 ≤ exponent.toNat at hnormal
      omega
    rw [ite_eq_right hnormal]
    change (Binary32.mk (narrowSign value.bits ||| subnormalFraction value.bits exponent.toNat)).magnitude < _ ↔ _
    have hb := (subnormalFraction_exact value.bits exponent.toNat hsubnormal).2
    rw [narrowSign_magnitude _ _ (by omega)]
    have hcarry := normalExponent_exact value.bits exponent (by omega)
    change _ ↔ (normalExponent value.bits exponent).toNat ≤ 1150
    rw [hcarry]
    split <;> omega

def narrowUnit (value : Binary64) : Nat :=
  2 ^ max 925 ((((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat + 28)

set_option exponentiation.threshold 1024 in
theorem narrow_distance (value : Binary64) (finite : value.Finite)
    (noOverflow : (normalExponent value.bits ((value.bits >>> 52) &&& 0x7ff)).toNat ≤ 1150) :
    2 * magnitudeUnits64 value ≤ 2 * magnitudeUnits32 (narrow value) + narrowUnit value ∧
      2 * magnitudeUnits32 (narrow value) ≤ 2 * magnitudeUnits64 value + narrowUnit value := by
  let exponent : UInt64 := (value.bits >>> 52) &&& 0x7ff
  have hfields := fields64_decomposition value
  have hewidth : exponent.toNat < 2047 := by
    change value.magnitude < 0x7ff0000000000000 at finite
    change value.magnitude = exponent.toNat * 2 ^ 52 + _ at hfields
    omega
  have hexcept : (exponent == 0x7ff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  have hresult : narrow value =
      if exponent ≥ 897 then ⟨narrowSign value.bits ||| normalMagnitude value.bits exponent⟩
      else ⟨narrowSign value.bits ||| subnormalFraction value.bits exponent.toNat⟩ := by
    simp only [narrow_def, show (value.bits >>> 52 &&& 0x7ff) = exponent from rfl,
      hexcept, Bool.false_eq_true, ↓reduceIte]
  rw [hresult]
  change _ ≤ _ + 2 ^ max 925 (exponent.toNat + 28) ∧
    _ ≤ _ + 2 ^ max 925 (exponent.toNat + 28)
  by_cases hnormal : exponent ≥ 897
  · have hlo : 897 ≤ exponent.toNat := hnormal
    rw [ite_eq_left hnormal, Nat.max_eq_right (show 925 ≤ exponent.toNat + 28 by omega)]
    exact normalMagnitude_distance value hlo hewidth noOverflow
  · have hsubnormal : exponent.toNat < 897 := by
      change ¬ 897 ≤ exponent.toNat at hnormal
      omega
    rw [ite_eq_right hnormal, Nat.max_eq_left (show exponent.toNat + 28 ≤ 925 by omega)]
    exact subnormalMagnitude_distance value hsubnormal

theorem widen_sign (value : Binary32) (finite : value.Finite) : (widen value).bits.toNat / 2 ^ 63 = value.bits.toNat / 2 ^ 31 := by
  let e : UInt32 := (value.bits >>> 23) &&& 0xff
  let f : UInt64 := (value.bits &&& 0x7fffff).toUInt64
  have hfields : value.magnitude = e.toNat * 2 ^ 23 + f.toNat := fields32_decomposition value
  have hwidth : f.toNat < 2 ^ 23 := (fields32_bounds value).2
  have hewidth : e.toNat < 255 := by
    change value.magnitude < 0x7f800000 at finite
    omega
  have hexcept : (e == 0xff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  simp only [widen_def]
  change (if e == 0xff then _ else if e == 0 then _ else _ : Binary64).bits.toNat / 2 ^ 63 = _
  rw [hexcept]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if e == 0 then
    if f == 0 then Binary64.mk (widenSign value.bits) else
      ⟨widenSign value.bits ||| (((f.toNat.log2 + 874).toUInt64 <<< 52) ||| widenSubnormalFraction f)⟩
    else ⟨widenSign value.bits ||| (((e.toUInt64 + 896) <<< 52) ||| widenFraction f)⟩).bits.toNat / 2 ^ 63 = _
  split
  · split
    · change (widenSign value.bits).toNat / 2 ^ 63 = _
      rw [widenSign_exact, Nat.mul_div_cancel _ (Nat.two_pow_pos 63)]
    · rename_i hfzero
      have hfpositive : 0 < f.toNat := by
        have hfneq : f ≠ 0 := by simpa using hfzero
        have : f.toNat ≠ 0 := by intro h; exact hfneq (UInt64.toNat.inj h)
        omega
      have hl : f.toNat.log2 < 23 := (Nat.log2_lt (by omega)).mpr hwidth
      have hecast : (f.toNat.log2 + 874).toUInt64.toNat = f.toNat.log2 + 874 := by
        change (f.toNat.log2 + 874) % (2 ^ 64) = _
        exact Nat.mod_eq_of_lt (by omega)
      exact wideFields_sign value.bits _ _ (by rw [hecast]; omega)
        (widenSubnormalFraction_bound f hfpositive hwidth)
  · have hecast : (e.toUInt64 + 896).toNat = e.toNat + 896 := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
      change (e.toNat + 896) % (2 ^ 64) = _
      exact Nat.mod_eq_of_lt (by omega)
    exact wideFields_sign value.bits _ _ (by rw [hecast]; omega) (widenFraction_exact f hwidth).2

theorem narrow_finite_distance (value : Binary64) (sourceFinite : value.Finite)
    (resultFinite : (narrow value).Finite) :
    2 * magnitudeUnits64 value ≤ 2 * magnitudeUnits32 (narrow value) + narrowUnit value ∧
      2 * magnitudeUnits32 (narrow value) ≤ 2 * magnitudeUnits64 value + narrowUnit value :=
  narrow_distance value sourceFinite ((narrow_finite_iff value sourceFinite).mp resultFinite)

def trunc64 (value : Binary64) : Int :=
  let exponent := ((value.bits >>> 52) &&& 0x7ff).toNat
  if exponent < 1023 then 0
  else
    let significand := ((value.bits &&& 0xfffffffffffff) ||| 0x10000000000000).toNat
    let magnitude := if exponent ≥ 1075 then significand * 2 ^ (exponent - 1075)
      else significand / 2 ^ (1075 - exponent)
    if value.bits &&& 0x8000000000000000 != 0 then -(magnitude : Int) else magnitude

set_option exponentiation.threshold 2048 in
theorem trunc64_magnitude_exact (value : Binary64) :
    (trunc64 value).natAbs = magnitudeUnits64 value / 2 ^ 1074 := by
  rw [fields64_units]
  have hf := fraction64_bound value.bits
  let e := (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat
  let f := ((value.bits &&& 0xfffffffffffff) : UInt64).toNat
  have hsig : (((value.bits &&& 0xfffffffffffff) ||| 0x10000000000000) : UInt64).toNat = 2 ^ 52 + f := by
    simpa [normalSignificand, UInt64.toNat_or, Nat.or_comm, f] using normalSignificand_value value.bits
  change (trunc64 value).natAbs = (if e = 0 then f else (2 ^ 52 + f) * 2 ^ (e - 1)) / 2 ^ 1074
  unfold trunc64
  rw [hsig]
  change (if e < 1023 then (0 : Int) else
    if value.bits &&& 0x8000000000000000 != 0 then
      -((if e ≥ 1075 then (2 ^ 52 + f) * 2 ^ (e - 1075) else (2 ^ 52 + f) / 2 ^ (1075 - e) : Nat) : Int)
    else ((if e ≥ 1075 then (2 ^ 52 + f) * 2 ^ (e - 1075) else (2 ^ 52 + f) / 2 ^ (1075 - e) : Nat) : Int)).natAbs = _
  by_cases hsmall : e < 1023
  · rw [ite_eq_left hsmall]
    simp only [Int.natAbs_zero]
    apply Eq.symm
    apply Nat.div_eq_of_lt
    split
    · exact Nat.lt_trans hf (by decide)
    · have hs : 2 ^ 52 + f < 2 ^ 53 := by dsimp [f]; omega
      have he : e - 1 ≤ 1021 := by omega
      have hp : 2 ^ (e - 1) ≤ 2 ^ 1021 := Nat.pow_le_pow_right (by decide) he
      have := Nat.mul_lt_mul_of_pos_right hs (Nat.two_pow_pos (e - 1))
      have := Nat.mul_le_mul_left (2 ^ 53) hp
      omega
  · rw [ite_eq_right hsmall]
    have he : e ≠ 0 := by omega
    rw [ite_eq_right he]
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
    all_goals
      by_cases hlarge : e ≥ 1075
      · rw [ite_eq_left hlarge]
        have hp : e - 1 = (e - 1075) + 1074 := by omega
        rw [hp, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos 1074)]
      · rw [ite_eq_right hlarge]
        have hp : 1074 = (e - 1) + (1075 - e) := by omega
        conv => rhs; rw [hp, Nat.pow_add]
        rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos (e - 1))]

def clampInt (value lower upper : Int) : Int := max lower (min upper value)

theorem clampInt_bounds (value lower upper : Int) (h : lower ≤ upper) :
    lower ≤ clampInt value lower upper ∧ clampInt value lower upper ≤ upper := by
  unfold clampInt
  omega

def signedCast (bits : Nat) (value : Binary64) : Int :=
  let extent : Int := 2 ^ bits
  if value.isNaN then 0
  else if value.magnitude == 0x7ff0000000000000 then
    if value.bits &&& 0x8000000000000000 != 0 then -extent else extent - 1
  else clampInt (trunc64 value) (-extent) (extent - 1)

theorem signedCast_bounds (bits : Nat) (value : Binary64) :
    -(2 ^ bits : Int) ≤ signedCast bits value ∧
      signedCast bits value < (2 ^ bits : Int) := by
  have hp : (0 : Int) < 2 ^ bits := Int.pow_pos (by omega)
  dsimp only [signedCast]
  split
  · omega
  · split
    · split <;> omega
    · have := clampInt_bounds (trunc64 value) (-(2 ^ bits)) (2 ^ bits - 1) (by omega)
      omega

def truncI32Magnitude (bits : UInt64) : UInt32 :=
  (normalSignificand bits >>> ((1075 : UInt64) - ((bits >>> 52) &&& 0x7ff))).toUInt32

def toI32Word (value : Binary64) : Int32 :=
  let negative := value.bits &&& 0x8000000000000000 != 0
  if value.isNaN then (0 : UInt32).toInt32
  else if ((value.bits >>> 52) &&& 0x7ff) ≥ (1054 : UInt64) then
    if negative then (0x80000000 : UInt32).toInt32 else (0x7fffffff : UInt32).toInt32
  else
    let exponent := (value.bits >>> 52) &&& 0x7ff
    if exponent < (1023 : UInt64) then (0 : UInt32).toInt32
    else
      let truncated := (truncI32Magnitude value.bits).toInt32
      if negative then -truncated else truncated

def toI32 (value : Binary64) : Int := (toI32Word value).toInt

def ofInt (value : Int) : Binary64 :=
  let magnitude := value.natAbs.toUInt64.toFloat.toBits
  if value < 0 then ⟨magnitude ^^^ 0x8000000000000000⟩ else ⟨magnitude⟩

def ofI64Word (value : Int64) : Binary64 :=
  let negative := value.toUInt64 ≥ (0x8000000000000000 : UInt64)
  let magnitude := if negative then -value.toUInt64 else value.toUInt64
  let bits := magnitude.toFloat.toBits
  if negative then ⟨bits ^^^ 0x8000000000000000⟩ else ⟨bits⟩

theorem i64Sign_eq (value : Int64) :
    (value.toUInt64 ≥ (0x8000000000000000 : UInt64)) ↔ value < 0 := by
  change 2^63 ≤ value.toUInt64.toNat ↔ value < 0
  rw [Int64.lt_iff_toInt_lt]
  have repr := BitVec.toInt_eq_toNat_cond value.toBitVec
  change value.toInt = if 2 * value.toUInt64.toNat < 2^64 then
    (value.toUInt64.toNat : Int) else (value.toUInt64.toNat : Int) - (2^64 : Nat) at repr
  change 2^63 ≤ value.toUInt64.toNat ↔ value.toInt < 0
  have width := value.toUInt64.toNat_lt
  split at repr <;> omega

theorem i64Magnitude_exact (value : Int64) :
    (if value < 0 then -value.toUInt64 else value.toUInt64).toNat = value.toInt.natAbs := by
  have repr := BitVec.toInt_eq_toNat_cond value.toBitVec
  change value.toInt = if 2 * value.toUInt64.toNat < 2^64 then
    (value.toUInt64.toNat : Int) else (value.toUInt64.toNat : Int) - (2^64 : Nat) at repr
  have width := value.toUInt64.toNat_lt
  by_cases negative : value < 0
  · rw [ite_eq_left negative, UInt64.toNat_neg]
    have sign : value.toInt < 0 := by simpa using (Int64.lt_iff_toInt_lt.mp negative)
    have high : ¬ 2 * value.toUInt64.toNat < 2^64 := by intro h; rw [ite_eq_left h] at repr; omega
    rw [ite_eq_right high] at repr
    have magnitude : value.toInt.natAbs = 2^64 - value.toUInt64.toNat := by
      have abs := Int.ofNat_natAbs_of_nonpos (show value.toInt ≤ 0 by omega)
      omega
    rw [magnitude]
    exact Nat.mod_eq_of_lt (by change 2^64 - value.toUInt64.toNat < 2^64; omega)
  · rw [ite_eq_right negative]
    have sign : 0 ≤ value.toInt := by
      have h : ¬ value.toInt < 0 := by simpa [Int64.lt_iff_toInt_lt] using negative
      omega
    have low : 2 * value.toUInt64.toNat < 2^64 := by
      by_cases h : 2 * value.toUInt64.toNat < 2^64
      · exact h
      · rw [ite_eq_right h] at repr
        omega
    rw [ite_eq_left low] at repr
    rw [repr, Int.natAbs_natCast]

theorem ofI64Word_eq (value : Int64) : ofI64Word value = ofInt value.toInt := by
  have magnitude : (if value < 0 then -value.toUInt64 else value.toUInt64) =
      value.toInt.natAbs.toUInt64 := by
    apply UInt64.toNat.inj
    rw [i64Magnitude_exact]
    have bound : value.toInt.natAbs < 2^64 := by
      rw [← i64Magnitude_exact]
      exact UInt64.toNat_lt _
    symm
    exact UInt64.toNat_ofNat_of_lt' bound
  dsimp only [ofI64Word, ofInt]
  simp only [i64Sign_eq]
  rw [magnitude]
  simp only [Int64.lt_iff_toInt_lt]
  rfl

def ofI32Word (value : Int32) : Binary64 := ofI64Word value.toInt64

theorem ofI32Word_eq (value : Int32) : ofI32Word value = ofInt value.toInt := by
  rw [ofI32Word, ofI64Word_eq, Int32.toInt_toInt64]

theorem widen_magnitude_unit (value : Binary32) (bound : value.magnitude ≤ 0x3f800000) :
    (widen value).magnitude ≤ 0x3ff0000000000000 := by
  let e : UInt32 := (value.bits >>> 23) &&& 0xff
  let f : UInt64 := (value.bits &&& 0x7fffff).toUInt64
  have hfields : value.magnitude = e.toNat * 2 ^ 23 + f.toNat := fields32_decomposition value
  have hwidth : f.toNat < 2 ^ 23 := (fields32_bounds value).2
  have hewidth : e.toNat ≤ 127 := by omega
  have hexcept : (e == 0xff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  simp only [widen_def]
  change Binary64.magnitude (if e == 0xff then _ else if e == 0 then _ else _) ≤ _
  rw [hexcept]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if e == 0 then
    if f == 0 then Binary64.mk (widenSign value.bits) else
      ⟨widenSign value.bits ||| (((f.toNat.log2 + 874).toUInt64 <<< 52) ||| widenSubnormalFraction f)⟩
    else ⟨widenSign value.bits ||| (((e.toUInt64 + 896) <<< 52) ||| widenFraction f)⟩).magnitude ≤ _
  split
  · split
    · have hm := widenSign_magnitude value.bits 0 (by decide)
      simp only [UInt64.or_zero, UInt64.toNat_zero] at hm
      rw [hm]
      omega
    · rename_i hfzero
      have hfpositive : 0 < f.toNat := by
        have hfneq : f ≠ 0 := by simpa using hfzero
        have : f.toNat ≠ 0 := by intro h; exact hfneq (UInt64.toNat.inj h)
        omega
      have hl : f.toNat.log2 < 23 := (Nat.log2_lt (by omega)).mpr hwidth
      have hecast : (f.toNat.log2 + 874).toUInt64.toNat = f.toNat.log2 + 874 := by
        change (f.toNat.log2 + 874) % (2 ^ 64) = _
        exact Nat.mod_eq_of_lt (by omega)
      have hf := widenSubnormalFraction_bound f hfpositive hwidth
      have hw := wideFields_exact (f.toNat.log2 + 874).toUInt64
        (widenSubnormalFraction f) (by rw [hecast]; omega) hf
      rw [hecast] at hw
      rw [widenSign_magnitude _ _ (by rw [hw]; omega), hw]
      omega
  · have hecast : (e.toUInt64 + 896).toNat = e.toNat + 896 := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
      change (e.toNat + 896) % (2 ^ 64) = _
      exact Nat.mod_eq_of_lt (by omega)
    have hf := widenFraction_exact f hwidth
    have hw := wideFields_exact (e.toUInt64 + 896) (widenFraction f) (by rw [hecast]; omega) hf.2
    rw [hecast, hf.1] at hw
    rw [widenSign_magnitude _ _ (by rw [hw]; omega), hw]
    omega

theorem normalFraction_carry_zero (bits : UInt64)
    (carry : roundedNormal bits == ((1 : UInt64) <<< 24)) : normalFraction bits = 0 := by
  simp [normalFraction, normalizedNormal, beq_iff_eq.mp carry]

theorem roundedNormal_zero_fraction (bits : UInt64)
    (zero : (bits &&& 0xfffffffffffff : UInt64).toNat = 0) :
    roundedNormal bits = (1 : UInt64) <<< 23 := by
  have hm : normalSignificand bits = (1 : UInt64) <<< 52 := by
    apply UInt64.toNat.inj
    rw [normalSignificand_value, zero]
    rfl
  rw [roundedNormal, hm]
  rfl

theorem normalMagnitude_unit (bits exponent : UInt64) (lo : 897 ≤ exponent.toNat)
    (hi : exponent.toNat ≤ 1023)
    (top : exponent.toNat = 1023 → (bits &&& 0xfffffffffffff : UInt64).toNat = 0) :
    (normalMagnitude bits exponent).toNat ≤ 0x3f800000 := by
  have he := normalExponent_exact bits exponent (by omega)
  have hb := normalExponent_bounds bits exponent lo (by omega)
  have hfrac := normalFraction_exact bits
  have htop : (normalExponent bits exponent).toNat = 1023 → (normalFraction bits).toNat = 0 := by
    intro h
    by_cases carry : roundedNormal bits == ((1 : UInt64) <<< 24)
    · rw [normalFraction_carry_zero bits carry]
      rfl
    · have ec : exponent.toNat = 1023 := by rw [ite_eq_right carry] at he; omega
      have hr := roundedNormal_zero_fraction bits (top ec)
      simp [normalFraction, normalizedNormal, hr]
  have hupper : (normalExponent bits exponent).toNat ≤ 1023 := by
    by_cases et : exponent.toNat = 1023
    · have hr := roundedNormal_zero_fraction bits (top et)
      simp only [hr] at he
      change (normalExponent bits exponent).toNat = exponent.toNat + 0 at he
      omega
    · split at he <;> omega
  rw [normalMagnitude_components]
  rw [ite_eq_right (show ¬normalExponent bits exponent > 1150 by change ¬1150 < (normalExponent bits exponent).toNat; omega)]
  have hsub : (normalExponent bits exponent - 896).toNat = (normalExponent bits exponent).toNat - 896 := by
    rw [UInt64.toNat_sub_of_le]
    · rfl
    · change 896 ≤ (normalExponent bits exponent).toNat
      omega
  have hcast : (normalExponent bits exponent - 896).toUInt32.toNat = (normalExponent bits exponent).toNat - 896 := by
    rw [UInt64.toNat_toUInt32, hsub, Nat.mod_eq_of_lt (by omega)]
  rw [normalFields_exact _ _ (by rw [hcast]; omega) hfrac.2, hcast]
  by_cases ht : (normalExponent bits exponent).toNat = 1023
  · rw [ht, htop ht]
    decide
  · omega

theorem narrow_magnitude_unit (value : Binary64) (bound : value.magnitude ≤ 0x3ff0000000000000) :
    (narrow value).magnitude ≤ 0x3f800000 := by
  let e : UInt64 := (value.bits >>> 52) &&& 0x7ff
  have hfields := fields64_decomposition value
  have he : e.toNat ≤ 1023 := by change value.magnitude = e.toNat * 2^52 + _ at hfields; omega
  have htop : e.toNat = 1023 → (value.bits &&& 0xfffffffffffff : UInt64).toNat = 0 := by
    change value.magnitude = e.toNat * 2^52 + _ at hfields
    omega
  simp only [narrow_def]
  split
  · rename_i hexception
    have heq : e = 0x7ff := by simpa using hexception
    rw [heq] at he
    contradiction
  · split
    · rename_i hnormal
      have hlo : 897 ≤ e.toNat := hnormal
      have hb := normalMagnitude_unit value.bits e hlo he htop
      change (Binary32.mk (narrowSign value.bits ||| normalMagnitude value.bits e)).magnitude ≤ _
      rw [narrowSign_magnitude _ _ (by omega)]
      exact hb
    · rename_i hsubnormal
      have hlo : ¬897 ≤ e.toNat := hsubnormal
      have hb := (subnormalFraction_exact value.bits e.toNat (by omega)).2
      change (Binary32.mk (narrowSign value.bits ||| subnormalFraction value.bits e.toNat)).magnitude ≤ _
      rw [narrowSign_magnitude _ _ (by omega)]
      omega

theorem widen_word_unit (value : Binary32) (bound : value.bits.toNat ≤ 0x3f800000) :
    (widen value).bits.toNat ≤ 0x3ff0000000000000 := by
  have hm : value.magnitude = value.bits.toNat := by
    change value.bits.toNat &&& (2^31-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hb := widen_magnitude_unit value (by omega)
  have hs := widen_sign value (by change value.magnitude < 0x7f800000; omega)
  change (widen value).bits.toNat &&& (2^63-1) ≤ _ at hb
  rw [Nat.and_two_pow_sub_one_eq_mod] at hb
  omega

theorem narrow_word_unit (value : Binary64) (bound : value.bits.toNat ≤ 0x3ff0000000000000) :
    (narrow value).bits.toNat ≤ 0x3f800000 := by
  have hm : value.magnitude = value.bits.toNat := by
    change value.bits.toNat &&& (2^63-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hb := narrow_magnitude_unit value (by omega)
  have hs := narrow_sign value (by change value.magnitude < 0x7ff0000000000000; omega)
  change (narrow value).bits.toNat &&& (2^31-1) ≤ _ at hb
  rw [Nat.and_two_pow_sub_one_eq_mod] at hb
  omega
theorem narrow_signed_zero (sign : Bool) :
    narrow ⟨if sign then 0x8000000000000000 else 0⟩ = ⟨if sign then 0x80000000 else 0⟩ := by
  cases sign
  · change Binary32.mk (0 ||| (Rounding.wordShift 0 925).toUInt32) = ⟨0⟩
    rw [Rounding.wordShift_zero]
    rfl
  · change Binary32.mk (0x80000000 ||| (Rounding.wordShift 0 925).toUInt32) = ⟨0x80000000⟩
    rw [Rounding.wordShift_zero]
    rfl
theorem wideFields_extract (bits : UInt32) (exponent fraction : UInt64)
    (he : exponent.toNat < 2048) (hf : fraction.toNat < 2^52) :
    let word := widenSign bits ||| ((exponent <<< 52) ||| fraction)
    ((word >>> 52) &&& 0x7ff) = exponent ∧ (word &&& 0xfffffffffffff) = fraction := by
  dsimp only
  have hw := wideFields_exact exponent fraction he hf
  have hm := widenSign_magnitude bits ((exponent <<< 52) ||| fraction) (by rw [hw]; omega)
  have hd := fields64_decomposition ⟨widenSign bits ||| ((exponent <<< 52) ||| fraction)⟩
  have hfb := fraction64_bound (widenSign bits ||| ((exponent <<< 52) ||| fraction))
  rw [hm, hw] at hd
  dsimp only at hd
  constructor <;> apply UInt64.toNat.inj <;> omega

theorem narrow_magnitude_cases (value : Binary64)
    (he : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 2047) :
    (narrow value).magnitude =
      if 897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat
      then (normalMagnitude value.bits ((value.bits >>> 52) &&& 0x7ff)).toNat
      else (subnormalFraction value.bits (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat).toNat := by
  simp only [narrow_def]
  split
  · rename_i h
    have hx : ((value.bits >>> 52) &&& 0x7ff : UInt64) = 0x7ff := by simpa using h
    rw [hx] at he
    contradiction
  · split
    · rename_i h
      have hlo : 897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := h
      rw [ite_eq_left hlo]
      exact narrowSign_magnitude _ _ (by have := normalMagnitude_bound value.bits _ hlo he; omega)
    · rename_i h
      have hh : ¬897 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat := h
      rw [ite_eq_right hh]
      exact narrowSign_magnitude _ _ (by
        have := (subnormalFraction_exact value.bits (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat (by omega)).2
        omega)

theorem normalMagnitude_aligned (bits exponent : UInt64) (fraction : Nat)
    (he : 897 ≤ exponent.toNat) (he' : exponent.toNat ≤ 1150) (hf : fraction < 2^23)
    (aligned : (normalSignificand bits).toNat = (2^23+fraction)*2^29) :
    (normalMagnitude bits exponent).toNat = (exponent.toNat-896)*2^23+fraction := by
  have hr : (roundedNormal bits).toNat = 2^23+fraction := by
    rw [roundedNormal_eq, Rounding.wordShift_exact, aligned, Rounding.nearestEven_exact _ _ (Nat.two_pow_pos 29)]
  have hn : (roundedNormal bits == ((1 : UInt64) <<< 24)) = false := by
    simp only [beq_eq_false_iff_ne]
    intro h
    have hx := congrArg UInt64.toNat h
    change (roundedNormal bits).toNat = 2^24 at hx
    omega
  have heq : normalExponent bits exponent = exponent := by
    simp only [normalExponent, hn, Bool.false_eq_true, ↓reduceIte]
  have hnorm : normalizedNormal bits = roundedNormal bits := by
    simp only [normalizedNormal, hn, Bool.false_eq_true, ↓reduceIte]
  have hfrac := normalFraction_exact bits
  rw [hnorm, hr] at hfrac
  have hsub : (exponent-896).toNat = exponent.toNat-896 := by
    rw [UInt64.toNat_sub_of_le]
    · rfl
    · change 896 ≤ exponent.toNat
      omega
  have hcast : (exponent-896).toUInt32.toNat = exponent.toNat-896 := by
    rw [UInt64.toNat_toUInt32, hsub, Nat.mod_eq_of_lt (by omega)]
  rw [normalMagnitude_components, heq, ite_eq_right (show ¬ exponent > 1150 by change ¬1150 < exponent.toNat; omega)]
  rw [normalFields_exact _ _ (by rw [hcast]; omega) hfrac.2, hcast]
  omega

theorem subnormalFraction_aligned (bits : UInt64) (exponent fraction : Nat)
    (he : exponent < 897)
    (aligned : (subnormalSignificand bits).toNat = fraction*2^(subnormalShift exponent)) :
    (subnormalFraction bits exponent).toNat = fraction := by
  rw [(subnormalFraction_exact bits exponent he).1, aligned,
    Rounding.nearestEven_exact _ _ (Nat.two_pow_pos _)]

theorem wideFields_significand (bits : UInt32) (exponent fraction : UInt64)
    (he : 0 < exponent.toNat) (he' : exponent.toNat < 2047) (hf : fraction.toNat < 2^52) :
    let word := widenSign bits ||| ((exponent <<< 52) ||| fraction)
    (normalSignificand word).toNat = 2^52+fraction.toNat ∧
      (subnormalSignificand word).toNat = 2^52+fraction.toNat := by
  dsimp only
  have fields := wideFields_extract bits exponent fraction (by omega) hf
  have hn : (exponent == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    intro h
    rw [h] at he
    contradiction
  rw [normalSignificand_value, fields.2]
  refine ⟨rfl, ?_⟩
  rw [subnormalSignificand, fields.1, hn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [normalSignificand_value, fields.2]

theorem narrow_widen_magnitude (value : Binary32) (finite : value.Finite) :
    (narrow (widen value)).magnitude = value.magnitude := by
  let e : UInt32 := (value.bits >>> 23) &&& 0xff
  let f : UInt64 := (value.bits &&& 0x7fffff).toUInt64
  have hfields : value.magnitude = e.toNat * 2^23+f.toNat := fields32_decomposition value
  have hwidth : f.toNat < 2^23 := (fields32_bounds value).2
  have hewidth : e.toNat < 255 := by change value.magnitude < 0x7f800000 at finite; omega
  have hexcept : (e == 0xff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  simp only [widen_def]
  change (narrow (if e == 0xff then _ else if e == 0 then _ else _)).magnitude = _
  rw [hexcept]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (narrow (if e == 0 then
    if f == 0 then Binary64.mk (widenSign value.bits) else
      ⟨widenSign value.bits ||| (((f.toNat.log2+874).toUInt64 <<< 52) ||| widenSubnormalFraction f)⟩
    else ⟨widenSign value.bits ||| (((e.toUInt64+896) <<< 52) ||| widenFraction f)⟩)).magnitude = _
  by_cases ez : e = 0
  · rw [ez]
    simp only [BEq.rfl, ↓reduceIte]
    have hm : value.magnitude = f.toNat := by rw [ez] at hfields; simpa using hfields
    rw [hm]
    by_cases fz : f = 0
    · rw [fz]
      simp only [BEq.rfl, ↓reduceIte, UInt64.toNat_zero]
      have fields := wideFields_extract value.bits 0 0 (by decide) (by decide)
      simp only [UInt64.zero_shiftLeft, UInt64.or_zero] at fields
      rw [narrow_magnitude_cases _ (by rw [fields.1]; decide), fields.1]
      change (subnormalFraction (widenSign value.bits) 0).toNat = 0
      rw [(subnormalFraction_exact _ 0 (by decide)).1]
      have hs : subnormalSignificand (widenSign value.bits) = 0 := by
        rw [subnormalSignificand, fields.1]
        simp only [BEq.rfl, ↓reduceIte]
        exact fields.2
      rw [hs]
      have hx := Rounding.nearestEven_le_input 0 (2^subnormalShift 0) (Nat.two_pow_pos _)
      change Rounding.nearestEven 0 _ = 0
      omega
    · have hfpos : 0 < f.toNat := by
        have : f.toNat ≠ 0 := by intro h; exact fz (UInt64.toNat.inj h)
        omega
      have ffalse : (f == 0) = false := by simpa using fz
      rw [ffalse]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hl : f.toNat.log2 < 23 := (Nat.log2_lt (by omega)).mpr hwidth
      have hecast : (f.toNat.log2+874).toUInt64.toNat = f.toNat.log2+874 := by
        change (f.toNat.log2+874) % (2^64) = _
        exact Nat.mod_eq_of_lt (by omega)
      have hf := widenSubnormalFraction_bound f hfpos hwidth
      have fields := wideFields_extract value.bits (f.toNat.log2+874).toUInt64 (widenSubnormalFraction f)
        (by rw [hecast]; omega) hf
      have sigs := wideFields_significand value.bits (f.toNat.log2+874).toUInt64 (widenSubnormalFraction f)
        (by rw [hecast]; omega) (by rw [hecast]; omega) hf
      rw [narrow_magnitude_cases _ (by rw [fields.1, hecast]; omega), fields.1, hecast,
        ite_eq_right (show ¬897 ≤ f.toNat.log2+874 by omega)]
      apply subnormalFraction_aligned _ _ _ (by omega)
      rw [sigs.2, widenSubnormalFraction_value f hfpos hwidth]
      have hs : subnormalShift (f.toNat.log2+874) = 52-f.toNat.log2 := by
        unfold subnormalShift
        rw [ite_eq_right (by omega)]
        omega
      rw [hs]
  · have efalse : (e == 0) = false := by simpa using ez
    rw [efalse]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hepos : 0 < e.toNat := by
      have : e.toNat ≠ 0 := by intro h; exact ez (UInt32.toNat.inj h)
      omega
    have hecast : (e.toUInt64+896).toNat = e.toNat+896 := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
      change (e.toNat+896) % (2^64) = _
      exact Nat.mod_eq_of_lt (by omega)
    have hf := widenFraction_exact f hwidth
    have fields := wideFields_extract value.bits (e.toUInt64+896) (widenFraction f) (by rw [hecast]; omega) hf.2
    have sigs := wideFields_significand value.bits (e.toUInt64+896) (widenFraction f)
      (by rw [hecast]; omega) (by rw [hecast]; omega) hf.2
    rw [narrow_magnitude_cases _ (by rw [fields.1, hecast]; omega), fields.1,
      ite_eq_left (show 897 ≤ (e.toUInt64+896).toNat by rw [hecast]; omega)]
    rw [normalMagnitude_aligned _ _ f.toNat (by rw [hecast]; omega) (by rw [hecast]; omega) hwidth
      (by rw [sigs.1, hf.1]; rw [Nat.add_mul])]
    rw [hecast]
    omega

theorem narrow_widen_finite (value : Binary32) (finite : value.Finite) : narrow (widen value) = value := by
  have hm := narrow_widen_magnitude value finite
  have hs := narrow_sign (widen value) (widen_finite value finite)
  rw [widen_sign value finite] at hs
  change (narrow (widen value)).bits.toNat &&& (2^31-1) = value.bits.toNat &&& (2^31-1) at hm
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod] at hm
  have hw : (narrow (widen value)).bits.toNat = value.bits.toNat := by omega
  have heq := UInt32.toNat.inj hw
  exact congrArg Binary32.mk heq
theorem narrow_widen_nonNaN (value : Binary32) (notNan : value.isNaN = false) :
    narrow (widen value) = value := by
  by_cases finite : value.Finite
  · exact narrow_widen_finite value finite
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
theorem widen_normal_or_zero (value : Binary32) (finite : value.Finite) :
    (widen value).magnitude = 0 ∨ 2^52 ≤ (widen value).magnitude := by
  let e : UInt32 := (value.bits >>> 23) &&& 0xff
  let f : UInt64 := (value.bits &&& 0x7fffff).toUInt64
  have hfields : value.magnitude = e.toNat * 2^23+f.toNat := fields32_decomposition value
  have hwidth : f.toNat < 2^23 := (fields32_bounds value).2
  have hewidth : e.toNat < 255 := by change value.magnitude < 0x7f800000 at finite; omega
  have hexcept : (e == 0xff) = false := by
    simp only [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hewidth
    contradiction
  simp only [widen_def]
  change Binary64.magnitude (if e == 0xff then _ else if e == 0 then _ else _) = 0 ∨ _
  change Binary64.magnitude (if e == 0xff then _ else if e == 0 then _ else _) = 0 ∨
    2^52 ≤ Binary64.magnitude (if e == 0xff then _ else if e == 0 then _ else _)
  rw [hexcept]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if e == 0 then
    if f == 0 then Binary64.mk (widenSign value.bits) else
      ⟨widenSign value.bits ||| (((f.toNat.log2+874).toUInt64 <<< 52) ||| widenSubnormalFraction f)⟩
    else ⟨widenSign value.bits ||| (((e.toUInt64+896) <<< 52) ||| widenFraction f)⟩).magnitude = 0 ∨ 2^52 ≤ (if e == 0 then
    if f == 0 then Binary64.mk (widenSign value.bits) else
      ⟨widenSign value.bits ||| (((f.toNat.log2+874).toUInt64 <<< 52) ||| widenSubnormalFraction f)⟩
    else ⟨widenSign value.bits ||| (((e.toUInt64+896) <<< 52) ||| widenFraction f)⟩).magnitude
  by_cases ez : e = 0
  · rw [ez]
    simp only [BEq.rfl, ↓reduceIte]
    by_cases fz : f = 0
    · rw [fz]
      simp only [BEq.rfl, ↓reduceIte]
      left
      have hm := widenSign_magnitude value.bits 0 (by decide)
      simpa only [UInt64.or_zero, UInt64.toNat_zero] using hm
    · have hfpos : 0 < f.toNat := by
        have : f.toNat ≠ 0 := by intro h; exact fz (UInt64.toNat.inj h)
        omega
      have ffalse : (f == 0) = false := by simpa using fz
      rw [ffalse]
      simp only [Bool.false_eq_true, ↓reduceIte]
      right
      have hl : f.toNat.log2 < 23 := (Nat.log2_lt (by omega)).mpr hwidth
      have hecast : (f.toNat.log2+874).toUInt64.toNat = f.toNat.log2+874 := by
        change (f.toNat.log2+874) % (2^64) = _
        exact Nat.mod_eq_of_lt (by omega)
      have hf := widenSubnormalFraction_bound f hfpos hwidth
      have hw := wideFields_exact (f.toNat.log2+874).toUInt64 (widenSubnormalFraction f) (by rw [hecast]; omega) hf
      rw [hecast] at hw
      rw [widenSign_magnitude _ _ (by rw [hw]; omega), hw]
      omega
  · have efalse : (e == 0) = false := by simpa using ez
    rw [efalse]
    simp only [Bool.false_eq_true, ↓reduceIte]
    right
    have hecast : (e.toUInt64+896).toNat = e.toNat+896 := by
      simp only [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt64.toNat_ofNat]
      change (e.toNat+896) % (2^64) = _
      exact Nat.mod_eq_of_lt (by omega)
    have hf := widenFraction_exact f hwidth
    have hw := wideFields_exact (e.toUInt64+896) (widenFraction f) (by rw [hecast]; omega) hf.2
    rw [hecast] at hw
    rw [widenSign_magnitude _ _ (by rw [hw]; omega), hw]
    omega
theorem trunc64_signed_magnitude (value : Binary64) :
    trunc64 value =
      if value.bits &&& 0x8000000000000000 != 0 then -((trunc64 value).natAbs : Int)
      else (trunc64 value).natAbs := by
  unfold trunc64
  by_cases he : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 1023
  · simp only [he, ↓reduceIte, Int.natAbs_zero, Int.natCast_zero, Int.neg_zero, ite_self]
  · simp only [he, ↓reduceIte]
    split <;> simp

theorem trunc64_signed_exact (value : Binary64) :
    trunc64 value =
      if value.bits &&& 0x8000000000000000 != 0 then -((magnitudeUnits64 value / 2^1074 : Nat) : Int)
      else ((magnitudeUnits64 value / 2^1074 : Nat) : Int) := by
  conv => lhs; rw [trunc64_signed_magnitude]
  rw [trunc64_magnitude_exact]

theorem signedCast_finite (bits : Nat) (value : Binary64) (finite : value.Finite) :
    signedCast bits value = clampInt (trunc64 value) (-(2^bits)) (2^bits-1) := by
  have hn : value.isNaN = false := by
    simp only [Binary64.isNaN, decide_eq_false_iff_not]
    change ¬value.magnitude > 0x7ff0000000000000
    unfold Binary64.Finite at finite
    omega
  have hi : (value.magnitude == 0x7ff0000000000000) = false := by
    simp only [beq_eq_false_iff_ne]
    unfold Binary64.Finite at finite
    omega
  simp only [signedCast, hn, hi, Bool.false_eq_true, ↓reduceIte]

theorem signedCast_finite_value (bits : Nat) (value : Binary64) (finite : value.Finite) :
    signedCast bits value =
      clampInt (if value.bits &&& 0x8000000000000000 != 0 then -((magnitudeUnits64 value / 2^1074 : Nat) : Int)
        else ((magnitudeUnits64 value / 2^1074 : Nat) : Int)) (-(2^bits)) (2^bits-1) := by
  rw [signedCast_finite bits value finite, trunc64_signed_exact]
theorem truncI32Magnitude_exact (bits : UInt64)
    (lo : 1023 ≤ (((bits >>> 52) &&& 0x7ff) : UInt64).toNat)
    (hi : (((bits >>> 52) &&& 0x7ff) : UInt64).toNat < 1054) :
    (truncI32Magnitude bits).toNat =
      (normalSignificand bits).toNat / 2^(1075-(((bits >>> 52) &&& 0x7ff) : UInt64).toNat) ∧
      (truncI32Magnitude bits).toNat < 2^31 := by
  let e := ((bits >>> 52) &&& 0x7ff : UInt64)
  change 1023 ≤ e.toNat at lo
  change e.toNat < 1054 at hi
  have hs : ((1075 : UInt64)-e).toNat = 1075-e.toNat :=
    UInt64.toNat_sub_of_le _ _ (by change e.toNat ≤ 1075; omega)
  have hd : 22 ≤ 1075-e.toNat := by omega
  have hd' : 1075-e.toNat < 64 := by omega
  have hp : 2^22 ≤ 2^(1075-e.toNat) := Nat.pow_le_pow_right (by decide) hd
  have hq : (normalSignificand bits).toNat / 2^(1075-e.toNat) < 2^31 := by
    have upper := (normalSignificand_bounds bits).2
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    have : 2^31*2^22 ≤ 2^31*2^(1075-e.toNat) := Nat.mul_le_mul_left _ hp
    omega
  have heq : (truncI32Magnitude bits).toNat =
      (normalSignificand bits).toNat / 2^(1075-e.toNat) := by
    simp only [truncI32Magnitude, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow]
    change ((normalSignificand bits).toNat / 2^(((1075 : UInt64)-e).toNat % 64)) % (2^32) = _
    rw [hs, Nat.mod_eq_of_lt hd', Nat.mod_eq_of_lt (by omega)]
  exact ⟨heq, heq ▸ hq⟩

theorem trunc64_large_power (value : Binary64) (power : Nat) (width : power ≤ 52)
    (large : 1023 + power ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat) :
    2^power ≤ (trunc64 value).natAbs := by
  let e := (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat
  change 1023 + power ≤ e at large
  have factor : 2^power * 2^(52-power) = 2^52 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le width]
  have lower := Nat.pow_le_pow_right (n := 2) (by decide) width
  have sig := (normalSignificand_bounds value.bits).1
  have hs : ((value.bits &&& 0xfffffffffffff) ||| 0x10000000000000) =
      normalSignificand value.bits := UInt64.or_comm _ _
  unfold trunc64
  rw [hs, ite_eq_right (show ¬e < 1023 by omega)]
  by_cases negative : (value.bits &&& 0x8000000000000000 != 0) = true
  all_goals simp only [negative, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
  all_goals
    by_cases h : 1075 ≤ e
    · rw [ite_eq_left h]
      have hp := Nat.two_pow_pos (e-1075)
      have hm := Nat.mul_le_mul_left (normalSignificand value.bits).toNat hp
      dsimp only [e] at *
      omega
    · rw [ite_eq_right h]
      have hd : 1075-e ≤ 52-power := by omega
      have hp := Nat.pow_le_pow_right (n := 2) (by decide) hd
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      have hm := Nat.mul_le_mul_left (2^power) hp
      rw [factor] at hm
      dsimp only [e] at *
      omega

theorem trunc64_large (value : Binary64)
    (large : 1054 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat) :
    2^31 ≤ (trunc64 value).natAbs :=
  trunc64_large_power value 31 (by decide) large

theorem trunc64_i32 (value : Binary64)
    (lo : 1023 ≤ (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat)
    (hi : (((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 1054) :
    trunc64 value =
      if value.bits &&& 0x8000000000000000 != 0 then
        -((truncI32Magnitude value.bits).toNat : Int)
      else (truncI32Magnitude value.bits).toNat := by
  have eqn := (truncI32Magnitude_exact value.bits lo hi).1
  have hs : ((value.bits &&& 0xfffffffffffff) ||| 0x10000000000000) =
      normalSignificand value.bits := UInt64.or_comm _ _
  unfold trunc64
  rw [hs, ite_eq_right (show ¬(((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat < 1023 by omega)]
  dsimp only
  rw [ite_eq_right (show ¬(((value.bits >>> 52) &&& 0x7ff) : UInt64).toNat ≥ 1075 by omega), ← eqn]

theorem toI32_eq_signedCast (value : Binary64) : toI32 value = signedCast 31 value := by
  let e := ((value.bits >>> 52) &&& 0x7ff : UInt64)
  have fields := fields64_decomposition value
  have fraction := fraction64_bound value.bits
  change value.magnitude = e.toNat*2^52+_ at fields
  by_cases nan : value.isNaN = true
  · simp only [toI32, toI32Word, signedCast, nan, ↓reduceIte]
    rfl
  have notnan : value.isNaN = false := Bool.eq_false_iff.mpr nan
  have nm : ¬value.magnitude > 0x7ff0000000000000 := by
    exact of_decide_eq_false notnan
  by_cases inf : value.magnitude = 0x7ff0000000000000
  · have elarge : e ≥ (1054 : UInt64) := by change 1054 ≤ e.toNat; omega
    simp only [toI32, toI32Word, notnan, Bool.false_eq_true, ↓reduceIte,
      signedCast, inf, BEq.rfl]
    change Int32.toInt (if e ≥ 1054 then _ else _) = _
    rw [ite_eq_left elarge]
    by_cases neg : (value.bits &&& 0x8000000000000000 != 0) = true
    all_goals simp only [neg, Bool.false_eq_true, ↓reduceIte]; rfl
  have finite : value.Finite := by unfold Binary64.Finite; omega
  rw [signedCast_finite _ value finite]
  simp only [toI32, toI32Word, notnan, Bool.false_eq_true, ↓reduceIte]
  change Int32.toInt (if e ≥ 1054 then _ else if e < 1023 then _ else _) = _
  by_cases large : e ≥ (1054 : UInt64)
  · rw [ite_eq_left large]
    have bound := trunc64_large value large
    have signed := trunc64_signed_magnitude value
    by_cases neg : (value.bits &&& 0x8000000000000000 != 0) = true
    all_goals
      simp only [neg, Bool.false_eq_true, ↓reduceIte] at signed ⊢
      rw [signed]
      simp only [clampInt]
      have minValue : ((0x80000000 : UInt32).toInt32).toInt = -2147483648 := rfl
      have maxValue : ((0x7fffffff : UInt32).toInt32).toInt = 2147483647 := rfl
      omega
  · rw [ite_eq_right large]
    by_cases small : e < (1023 : UInt64)
    · rw [ite_eq_left small]
      have tz : trunc64 value = 0 := by
        unfold trunc64
        exact ite_eq_left (show e.toNat < 1023 from small)
      rw [tz]
      rfl
    · rw [ite_eq_right small]
      have lo : 1023 ≤ e.toNat := Nat.le_of_not_gt small
      have hi : e.toNat < 1054 := Nat.lt_of_not_ge large
      have exactWord := truncI32Magnitude_exact value.bits lo hi
      have cast : (truncI32Magnitude value.bits).toInt32.toInt =
          (truncI32Magnitude value.bits).toNat := by
        have word : (truncI32Magnitude value.bits).toInt32 =
            Int32.ofNat (truncI32Magnitude value.bits).toNat := by
          rw [← UInt32.toInt32_ofNat' , UInt32.ofNat_toNat]
        rw [word, Int32.toInt_ofNat_of_lt exactWord.2]
      rw [trunc64_i32 value lo hi]
      by_cases neg : (value.bits &&& 0x8000000000000000 != 0) = true
      · simp only [neg, ↓reduceIte, Int32.toInt_neg, cast, clampInt]
        rw [Int.bmod_eq_of_le (by omega) (by omega)]
        omega
      · simp only [neg, Bool.false_eq_true, ↓reduceIte, cast, clampInt]
        omega

def truncI64Magnitude (bits : UInt64) : UInt64 :=
  let exponent := bits >>> 52 &&& 0x7ff
  if exponent ≥ (1075 : UInt64) then normalSignificand bits <<< (exponent - 1075)
  else normalSignificand bits >>> ((1075 : UInt64) - exponent)

theorem truncI64Magnitude_exact (bits : UInt64)
    (lo : 1023 ≤ (bits >>> 52 &&& (0x7ff : UInt64)).toNat)
    (hi : (bits >>> 52 &&& (0x7ff : UInt64)).toNat < 1086) :
    (truncI64Magnitude bits).toNat =
      (if (bits >>> 52 &&& (0x7ff : UInt64)).toNat ≥ 1075 then
        (normalSignificand bits).toNat * 2^((bits >>> 52 &&& (0x7ff : UInt64)).toNat - 1075)
       else (normalSignificand bits).toNat / 2^(1075 - (bits >>> 52 &&& (0x7ff : UInt64)).toNat)) ∧
      (truncI64Magnitude bits).toNat < 2^63 := by
  let e := bits >>> 52 &&& (0x7ff : UInt64)
  change 1023 ≤ e.toNat at lo
  change e.toNat < 1086 at hi
  have sig := (normalSignificand_bounds bits).2
  unfold truncI64Magnitude
  by_cases large : e ≥ (1075 : UInt64)
  · rw [ite_eq_left large, ite_eq_left (show e.toNat ≥ 1075 from large)]
    have delta : (e - 1075).toNat = e.toNat - 1075 := UInt64.toNat_sub_of_le _ _ large
    have shiftBound : e.toNat - 1075 < 64 := by omega
    have power : 2^(e.toNat - 1075) ≤ 2^10 := Nat.pow_le_pow_right (by decide) (by omega)
    have bound : (normalSignificand bits).toNat * 2^(e.toNat - 1075) < 2^63 := by
      have strict := Nat.mul_lt_mul_of_pos_right sig (Nat.two_pow_pos (e.toNat - 1075))
      have upper := Nat.mul_le_mul_left (2^53) power
      omega
    have eqn : (normalSignificand bits <<< (e - 1075)).toNat =
        (normalSignificand bits).toNat * 2^(e.toNat - 1075) := by
      rw [UInt64.toNat_shiftLeft, delta, Nat.mod_eq_of_lt shiftBound, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega)]
    exact ⟨eqn, eqn ▸ bound⟩
  · rw [ite_eq_right large, ite_eq_right (show ¬ e.toNat ≥ 1075 from large)]
    have esmall : e.toNat < 1075 := Nat.lt_of_not_ge large
    have delta : ((1075 : UInt64) - e).toNat = 1075 - e.toNat :=
      UInt64.toNat_sub_of_le _ _ (by change e.toNat ≤ 1075; omega)
    have shiftBound : 1075 - e.toNat < 64 := by omega
    have eqn : (normalSignificand bits >>> ((1075 : UInt64) - e)).toNat =
        (normalSignificand bits).toNat / 2^(1075 - e.toNat) := by
      rw [UInt64.toNat_shiftRight, delta, Nat.mod_eq_of_lt shiftBound, Nat.shiftRight_eq_div_pow]
    have bound : (normalSignificand bits).toNat / 2^(1075 - e.toNat) < 2^63 := by
      have smaller := Nat.div_le_self (normalSignificand bits).toNat (2^(1075 - e.toNat))
      omega
    exact ⟨eqn, eqn ▸ bound⟩

theorem trunc64_large_i64 (value : Binary64)
    (large : 1086 ≤ (value.bits >>> 52 &&& (0x7ff : UInt64)).toNat) :
    2^63 ≤ (trunc64 value).natAbs := by
  let e := (value.bits >>> 52 &&& (0x7ff : UInt64)).toNat
  change 1086 ≤ e at large
  have sig := (normalSignificand_bounds value.bits).1
  have hs : ((value.bits &&& 0xfffffffffffff) ||| 0x10000000000000) =
      normalSignificand value.bits := UInt64.or_comm _ _
  unfold trunc64
  rw [hs, ite_eq_right (show ¬e < 1023 by omega)]
  dsimp only
  rw [ite_eq_left (show e ≥ 1075 by omega)]
  have power : 2^11 ≤ 2^(e-1075) := Nat.pow_le_pow_right (by decide) (by omega)
  have bound := Nat.mul_le_mul sig power
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> exact bound

theorem trunc64_i64 (value : Binary64)
    (lo : 1023 ≤ (value.bits >>> 52 &&& (0x7ff : UInt64)).toNat)
    (hi : (value.bits >>> 52 &&& (0x7ff : UInt64)).toNat < 1086) :
    trunc64 value = if value.bits &&& 0x8000000000000000 != 0 then
      -((truncI64Magnitude value.bits).toNat : Int) else (truncI64Magnitude value.bits).toNat := by
  have eqn := (truncI64Magnitude_exact value.bits lo hi).1
  have hs : ((value.bits &&& 0xfffffffffffff) ||| 0x10000000000000) =
      normalSignificand value.bits := UInt64.or_comm _ _
  unfold trunc64
  rw [hs, ite_eq_right (show ¬(value.bits >>> 52 &&& (0x7ff : UInt64)).toNat < 1023 by omega)]
  dsimp only
  rw [← eqn]

def toI64Word (value : Binary64) : Int64 :=
  let negative := value.bits &&& 0x8000000000000000 != 0
  if value.IsNaN then (0 : UInt64).toInt64
  else if (value.bits >>> 52 &&& 0x7ff) ≥ (1086 : UInt64) then
    if negative then (0x8000000000000000 : UInt64).toInt64 else (0x7fffffffffffffff : UInt64).toInt64
  else if (value.bits >>> 52 &&& 0x7ff) < (1023 : UInt64) then (0 : UInt64).toInt64
  else
    let magnitude := (truncI64Magnitude value.bits).toInt64
    if negative then -magnitude else magnitude

def toI64 (value : Binary64) : Int := (toI64Word value).toInt

theorem toI64_eq_signedCast (value : Binary64) : toI64 value = signedCast 63 value := by
  let e := ((value.bits >>> 52) &&& 0x7ff : UInt64)
  have fields := fields64_decomposition value
  have fraction := fraction64_bound value.bits
  change value.magnitude = e.toNat*2^52+_ at fields
  by_cases nan : value.isNaN = true
  · simp only [toI64, toI64Word, ← Binary64.isNaN_iff, signedCast, nan, ↓reduceIte]
    rfl
  have notnan : value.isNaN = false := Bool.eq_false_iff.mpr nan
  have nm : ¬value.magnitude > 0x7ff0000000000000 := by
    exact of_decide_eq_false notnan
  by_cases inf : value.magnitude = 0x7ff0000000000000
  · have elarge : e ≥ (1086 : UInt64) := by change 1086 ≤ e.toNat; omega
    simp only [toI64, toI64Word, ← Binary64.isNaN_iff, notnan, Bool.false_eq_true, ↓reduceIte,
      signedCast, inf, BEq.rfl]
    change Int64.toInt (if e ≥ 1086 then _ else _) = _
    rw [ite_eq_left elarge]
    by_cases neg : (value.bits &&& 0x8000000000000000 != 0) = true
    all_goals simp only [neg, Bool.false_eq_true, ↓reduceIte]; rfl
  have finite : value.Finite := by unfold Binary64.Finite; omega
  rw [signedCast_finite _ value finite]
  simp only [toI64, toI64Word, ← Binary64.isNaN_iff, notnan, Bool.false_eq_true, ↓reduceIte]
  change Int64.toInt (if e ≥ 1086 then _ else if e < 1023 then _ else _) = _
  by_cases large : e ≥ (1086 : UInt64)
  · rw [ite_eq_left large]
    have bound := trunc64_large_i64 value large
    have signed := trunc64_signed_magnitude value
    by_cases neg : (value.bits &&& 0x8000000000000000 != 0) = true
    all_goals
      simp only [neg, Bool.false_eq_true, ↓reduceIte] at signed ⊢
      rw [signed]
      simp only [clampInt]
      have minValue : ((0x8000000000000000 : UInt64).toInt64).toInt = -9223372036854775808 := rfl
      have maxValue : ((0x7fffffffffffffff : UInt64).toInt64).toInt = 9223372036854775807 := rfl
      omega
  · rw [ite_eq_right large]
    by_cases small : e < (1023 : UInt64)
    · rw [ite_eq_left small]
      have tz : trunc64 value = 0 := by
        unfold trunc64
        exact ite_eq_left (show e.toNat < 1023 from small)
      rw [tz]
      rfl
    · rw [ite_eq_right small]
      have lo : 1023 ≤ e.toNat := Nat.le_of_not_gt small
      have hi : e.toNat < 1086 := Nat.lt_of_not_ge large
      have exactWord := truncI64Magnitude_exact value.bits lo hi
      have cast : (truncI64Magnitude value.bits).toInt64.toInt =
          (truncI64Magnitude value.bits).toNat := by
        have word : (truncI64Magnitude value.bits).toInt64 =
            Int64.ofNat (truncI64Magnitude value.bits).toNat := by
          rw [← UInt64.toInt64_ofNat' , UInt64.ofNat_toNat]
        rw [word, Int64.toInt_ofNat_of_lt exactWord.2]
      rw [trunc64_i64 value lo hi]
      by_cases neg : (value.bits &&& 0x8000000000000000 != 0) = true
      · simp only [neg, ↓reduceIte, Int64.toInt_neg, cast, clampInt]
        rw [Int.bmod_eq_of_le (by omega) (by omega)]
        omega
      · simp only [neg, Bool.false_eq_true, ↓reduceIte, cast, clampInt]
        omega

def cappedTrunc128 (value : Binary64) : UInt32 :=
  if value.bits &&& 0x8000000000000000 != 0 then 0
  else
    let exponent := value.bits >>> 52 &&& 0x7ff
    if exponent ≥ 1030 then 128
    else if exponent < 1023 then 0
    else truncI32Magnitude value.bits

theorem cappedTrunc128_exact (value : Binary64) :
    (cappedTrunc128 value).toNat = min (trunc64 value).toNat 128 := by
  let e := ((value.bits >>> 52) &&& 0x7ff : UInt64)
  have signed := trunc64_signed_magnitude value
  unfold cappedTrunc128
  split
  · rename_i negative
    rw [ite_eq_left negative] at signed
    rw [signed]
    simp
  · rename_i nonnegative
    rw [ite_eq_right nonnegative] at signed
    simp only [ge_iff_le, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    split
    · rename_i high
      have large := trunc64_large_power value 7 (by decide) high
      rw [signed]
      simp only [Int.toNat_natCast, UInt32.toNat_ofNat]
      omega
    · rename_i high
      split
      · rename_i low
        have hz : trunc64 value = 0 := by
          unfold trunc64
          rw [ite_eq_left low]
        simp [hz]
      · rename_i low
        have hcast := trunc64_i32 value (by omega) (by omega)
        rw [ite_eq_right nonnegative] at hcast
        rw [hcast]
        simp only [Int.toNat_natCast]
        have exactMagnitude := (truncI32Magnitude_exact value.bits (by omega) (by omega)).1
        have bound := (normalSignificand_bounds value.bits).2
        have hp : 2^46 ≤ 2^(1075-e.toNat) :=
          Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
        have hm : (normalSignificand value.bits).toNat / 2^(1075-e.toNat) < 128 := by
          apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
          have := Nat.mul_le_mul_left 128 hp
          omega
        rw [exactMagnitude]
        exact (Nat.min_eq_left (by dsimp [e] at hm; omega)).symm

end Acorn.Conversion
