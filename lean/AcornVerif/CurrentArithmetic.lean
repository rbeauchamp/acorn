/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentPower
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
# Rounding semantics shared by the machine formats

These proofs unfold the pinned Lean 4.33.0 standard model in
`Init/Data/Float/Model/Unpacked/Round.lean`. Induction connects the actual
round/sticky-bit shifts to `Acorn.Rounding.nearestEven`; exact carry
normalization then gives the dyadic half-unit error bound for every format.
Normalization and packing lemmas connect those components to the actual
standard `Operations/Add.lean` and `Operations/Mul.lean` definitions and the
executing Acorn wrappers. The local binary64 operation contracts derive finite
results and error bounds from numerical magnitude hypotheses. Intermediate
rounding lemmas state their separate packing obligations explicitly. No theorem
assigns an IEEE numerical value to an exceptional encoding or proves native
compiler/runtime correspondence. Mathlib is confined to this proof layer.
-/
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower
namespace AcornVerif.CurrentArithmetic
/-- The model's residual bits record exactly whether any discarded source bit is nonzero. -/
theorem model_shift_residual (mantissa shift : Nat) :
    let shifted := ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>> shift
    (shifted.roundBit || shifted.stickyBit) = (mantissa % 2^shift != 0) := by
  dsimp only
  induction shift with
  | zero => simp only [Nat.pow_zero, Nat.mod_one]; rfl
  | succ shift ih =>
    change ((ExtendedMantissa.shiftRightOne (ExtendedMantissa.ofMantissaAndAccuracy mantissa
      .exact >>> shift)).roundBit ||
      (ExtendedMantissa.shiftRightOne (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>>
        shift)).stickyBit) = _
    simp only [ExtendedMantissa.shiftRightOne, model_shift_mantissa, ih]
    change ((mantissa / 2^shift % 2 != 0) || (mantissa % 2^shift != 0)) = _
    rw [Nat.pow_succ, Nat.mod_mul]
    apply Bool.eq_iff_iff.mpr
    simp [Bool.or_eq_true, or_comm]
    omega

/-- The exact standard-model shift and nearest-even rounding agree with the proved integer
  quotient recipe. -/
theorem model_round_shift_exact (mantissa shift : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>> shift).roundedMantissa =
      Rounding.nearestEven mantissa (2 ^ shift) := by
  cases shift with
  | zero =>
    change mantissa = Rounding.nearestEven mantissa 1
    simp [Rounding.nearestEven, Nat.mod_one]
  | succ shift =>
    let old := ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>> shift
    have hm : old.mantissa = mantissa / 2^shift := model_shift_mantissa _ _
    have hr : (old.roundBit || old.stickyBit) = (mantissa % 2^shift != 0) := model_shift_residual
      _ _
    change (ExtendedMantissa.shiftRightOne old).roundedMantissa = _
    have hb : (mantissa / 2^shift) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hp := Nat.two_pow_pos shift
    have hremainder := Nat.mod_lt mantissa hp
    have hquot : mantissa / 2^(shift+1) = mantissa / 2^shift / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hrem : mantissa % 2^(shift+1) = mantissa % 2^shift + 2^shift*(mantissa / 2^shift % 2) :=
      by
      rw [Nat.pow_succ, Nat.mod_mul]
    have hmodel : ExtendedMantissa.shiftRightOne old =
        ⟨mantissa/2^shift/2, (mantissa/2^shift%2 != 0), (mantissa%2^shift != 0)⟩ := by
      unfold ExtendedMantissa.shiftRightOne
      rw [hm, hr]
    rw [hmodel]
    unfold Rounding.nearestEven
    rw [hquot, hrem]
    by_cases bit : mantissa/2^shift%2 = 0
    · rw [bit]
      simp only [Nat.mul_zero, Nat.add_zero, bne_self_eq_false]
      have hcond : ¬ (2^(shift+1) < 2*(mantissa%2^shift) ∨
          (2^(shift+1) = 2*(mantissa%2^shift) ∧ (mantissa/2^shift/2)%2 = 1)) := by
        rw [Nat.pow_succ]
        omega
      rw [if_neg hcond]
      by_cases residual : mantissa%2^shift = 0
      · simp [residual, ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
        Accuracy.roundToNearestEven]
      · have rtrue : (mantissa%2^shift != 0) = true := by simpa using residual
        rw [rtrue]
        rfl
    · have bitone : mantissa/2^shift%2 = 1 := by omega
      rw [bitone]
      simp only [Nat.mul_one]
      by_cases residual : mantissa%2^shift = 0
      · rw [residual]
        simp only [Nat.zero_add]
        have heq : 2^(shift+1) = 2*2^shift := by rw [Nat.pow_succ]; omega
        simp only [heq, Nat.lt_irrefl, false_or, true_and]
        change mantissa/2^shift/2 + (mantissa/2^shift/2)%2 =
          if (mantissa/2^shift/2)%2 = 1 then mantissa/2^shift/2+1 else mantissa/2^shift/2
        split <;> have := Nat.mod_lt (mantissa/2^shift/2) (by decide : 0 < 2) <;> omega
      · have hcond : 2^(shift+1) < 2*(mantissa%2^shift+2^shift) ∨
          (2^(shift+1) = 2*(mantissa%2^shift+2^shift) ∧ (mantissa/2^shift/2)%2 = 1) := by
          left
          rw [Nat.pow_succ]
          omega
        rw [if_pos hcond]
        have rtrue : (mantissa%2^shift != 0) = true := by simpa using residual
        rw [rtrue]
        rfl
/-- The standard model's exact shift has the nearest-even half-unit distance bound on its actual
  rounded significand. -/
theorem model_round_shift_distance (mantissa shift : Nat) :
    let rounded := (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact >>>
      shift).roundedMantissa
    2*mantissa ≤ 2*(rounded*2^shift)+2^shift ∧ 2*(rounded*2^shift) ≤ 2*mantissa+2^shift := by
  dsimp only
  rw [model_round_shift_exact]
  exact Rounding.nearestEven_distance _ _ (Nat.two_pow_pos shift)

/-- Every format's first target-exponent shift retains fewer than its declared precision bits. -/
theorem model_first_mantissa_format (spec : Format) (mantissa : Nat) (exponent : Int) (accuracy :
  Accuracy) :
    (shiftToTargetExponent spec mantissa exponent accuracy).1.mantissa < 2 ^ spec.mantissaBits := by
  unfold shiftToTargetExponent shiftToExponent
  rw [model_shift_mantissa]
  have hinitial : (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy).mantissa = mantissa
    := by
    cases accuracy with
    | exact => rfl
    | inexact order => cases order <;> rfl
  rw [hinitial]
  by_cases hz : mantissa = 0
  · rw [hz]
    simp only [Nat.zero_div]
    exact Nat.two_pow_pos _
  · let shift := (spec.targetExponent (totalExponent mantissa exponent)-exponent).toNat
    have hlo : mantissa.log2+1 ≤ spec.mantissaBits+shift := by
      simp only [shift, Format.targetExponent, totalExponent]
      omega
    have hm := ((Nat.log2_eq_iff hz).mp rfl).2
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mpr
    rw [← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hlo)

/-- The second normalization shifts once exactly on a single carry, for every valid precision. -/
theorem model_second_shift_format (spec : Format) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≤ 2 ^ spec.mantissaBits) (he : spec.minExponent ≤ exponent) :
    shiftToTargetExponent spec mantissa exponent .exact =
      if mantissa = 2 ^ spec.mantissaBits then
        (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ spec.mantissaBitsWithoutImplicit) .exact,
          exponent + 1)
      else (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact, exponent) := by
  by_cases carry : mantissa = 2^spec.mantissaBits
  · rw [if_pos carry, carry]
    have hl : (2 ^ spec.mantissaBits :Nat).log2 = spec.mantissaBits := by simp
    have ht : spec.targetExponent (totalExponent (2 ^ spec.mantissaBits) exponent) = exponent+1 :=
      by
      simp only [Format.targetExponent, totalExponent, hl]
      omega
    simp only [shiftToTargetExponent, ht, shiftToExponent]
    have hd : (exponent+1-exponent).toNat = 1 := by omega
    rw [hd]
    change (ExtendedMantissa.shiftRightOne (ExtendedMantissa.ofMantissaAndAccuracy
      (2^spec.mantissaBits) .exact), exponent+1) = _
    have hp : 2^spec.mantissaBits = 2^spec.mantissaBitsWithoutImplicit*2 := by
      rw [Format.mantissaBits, Nat.add_comm, Nat.pow_succ]
    simp [ExtendedMantissa.shiftRightOne, ExtendedMantissa.ofMantissaAndAccuracy, hp]
  · rw [if_neg carry]
    have hl : mantissa.log2+1 ≤ spec.mantissaBits := by
      by_cases hz : mantissa = 0
      · rw [hz]
        simp [Format.mantissaBits]
      · have ht : mantissa < 2^spec.mantissaBits := by omega
        have hh := (Nat.log2_lt hz).mpr ht
        omega
    have ht : spec.targetExponent (totalExponent mantissa exponent) ≤ exponent := by
      simp only [Format.targetExponent, totalExponent]
      omega
    simp only [shiftToTargetExponent, shiftToExponent]
    have hd : (spec.targetExponent (totalExponent mantissa exponent)-exponent).toNat = 0 := by
      omega
    rw [hd]
    simp
    rfl

/-- Every accuracy case follows one rounded significand and exact carry normalization in the
actual standard model. -/
theorem model_round_accuracy_components (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy) :
    let first := shiftToTargetExponent spec mantissa exponent accuracy
    let rounded := first.1.roundedMantissa
    let outExponent := first.2
    roundWithAccuracy spec sign mantissa exponent accuracy =
      if rounded = 2 ^ spec.mantissaBits then
        .finite sign (2 ^ spec.mantissaBitsWithoutImplicit) (outExponent+1) (Nat.two_pow_pos _)
      else if h : rounded = 0 then .zero sign
      else .finite sign rounded outExponent (Nat.pos_of_ne_zero h) := by
  dsimp only
  let first := shiftToTargetExponent spec mantissa exponent accuracy
  have hr : first.1.roundedMantissa ≤ 2 ^ spec.mantissaBits := by
    have hlo := model_first_mantissa_format spec mantissa exponent accuracy
    have hhi := model_round_mantissa_ceiling first.1
    change first.1.mantissa < 2 ^ spec.mantissaBits at hlo
    omega
  have he : spec.minExponent ≤ first.2 := by
    simp only [first, shiftToTargetExponent, shiftToExponent, Format.targetExponent]
    omega
  rw [roundWithAccuracy]
  change (let final := shiftToTargetExponent spec first.1.roundedMantissa first.2 .exact
    if h : final.1.mantissa = 0 then UnpackedFloat.zero sign
    else UnpackedFloat.finite sign final.1.mantissa final.2 (Nat.pos_of_ne_zero h)) = _
  rw [model_second_shift_format spec _ _ hr he]
  by_cases hc : first.1.roundedMantissa = 2 ^ spec.mantissaBits
  · simp only [first] at hc
    simp [hc, first, ExtendedMantissa.ofMantissaAndAccuracy]
  · simp only [first] at hc
    simp [hc, first, ExtendedMantissa.ofMantissaAndAccuracy]

/-- The complete standard rounding path is one nearest-even quotient followed only by exact carry
  normalization. -/
theorem model_round_exact_components (spec : Format) (sign : Sign) (mantissa : Nat) (exponent :
  Int) :
    let shift := (spec.targetExponent (totalExponent mantissa exponent) - exponent).toNat
    let rounded := Rounding.nearestEven mantissa (2^shift)
    let outExponent := exponent+shift
    roundWithAccuracy spec sign mantissa exponent .exact =
      if rounded = 2^spec.mantissaBits then
        .finite sign (2^spec.mantissaBitsWithoutImplicit) (outExponent+1) (Nat.two_pow_pos _)
      else if h : rounded = 0 then .zero sign else .finite sign rounded outExponent
        (Nat.pos_of_ne_zero h) := by
  rw [model_round_accuracy_components]
  simp only [shiftToTargetExponent, shiftToExponent, model_round_shift_exact]

/-- The mathematical sign coefficient used only by the proof-side dyadic interpretation. -/
def signCoefficient : Sign → ℚ
  | .positive => 1
  | .negative => - 1

/-- Total proof-side reading of unpacked components. Only zero / finite constructors denote a
  numerical value; exceptional constructors require separate classification. -/
def unpackedValue : UnpackedFloat → ℚ
  | .zero _ => 0
  | .finite sign mantissa exponent _ => signCoefficient sign * mantissa * (2 : ℚ) ^ exponent
  | _ => 0

/-- Exact carry normalization preserves the mathematical dyadic value of the single rounded
  quotient. This is before the separate packing overflow decision. -/
theorem model_round_exact_value (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int) :
    let shift := (spec.targetExponent (totalExponent mantissa exponent) - exponent).toNat
    unpackedValue (roundWithAccuracy spec sign mantissa exponent .exact) =
      signCoefficient sign * (Rounding.nearestEven mantissa (2^shift) : ℚ) *
        (2:ℚ)^(exponent+shift) := by
  dsimp only
  rw [model_round_exact_components]
  by_cases hc : Rounding.nearestEven mantissa (2^(spec.targetExponent (totalExponent mantissa
    exponent)-exponent).toNat) = 2^spec.mantissaBits
  · rw [if_pos hc, hc]
    simp only [unpackedValue, Nat.cast_pow, Nat.cast_ofNat, Format.mantissaBits]
    rw [zpow_add₀ (by norm_num : (2:ℚ) ≠ 0) _ 1, zpow_one]
    rw [pow_add]
    ring
  · rw [if_neg hc]
    split
    · rename_i hz
      simp only [unpackedValue, hz, Nat.cast_zero, mul_zero, zero_mul]
    · rfl

/-- The actual two-stage standard rounding has at most half of its selected dyadic unit of error
  before packing. -/
theorem model_round_exact_error (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int) :
    let shift := (spec.targetExponent (totalExponent mantissa exponent) - exponent).toNat
    |unpackedValue (roundWithAccuracy spec sign mantissa exponent .exact) -
      signCoefficient sign * mantissa * (2:ℚ)^exponent| ≤ (2:ℚ)^(exponent+shift)/2 := by
  dsimp only
  rw [model_round_exact_value]
  let shift := (spec.targetExponent (totalExponent mantissa exponent)-exponent).toNat
  have distance := Rounding.nearestEven_distance mantissa (2^shift) (Nat.two_pow_pos shift)
  have hlo : 2*(mantissa:ℚ) ≤ 2*((Rounding.nearestEven mantissa
    (2^shift):ℚ)*(2:ℚ)^shift)+(2:ℚ)^shift := by
    exact_mod_cast distance.1
  have hhi : 2*((Rounding.nearestEven mantissa (2^shift):ℚ)*(2:ℚ)^shift) ≤
    2*(mantissa:ℚ)+(2:ℚ)^shift := by
    exact_mod_cast distance.2
  have hp : (0:ℚ) < (2:ℚ)^exponent := zpow_pos (by norm_num) _
  have hl := mul_le_mul_of_nonneg_right hlo (le_of_lt hp)
  have hh := mul_le_mul_of_nonneg_right hhi (le_of_lt hp)
  have he : (2:ℚ)^(exponent+shift) = (2:ℚ)^exponent*(2:ℚ)^shift := by
    rw [zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), zpow_natCast]
  change |signCoefficient sign * (Rounding.nearestEven mantissa (2^shift):ℚ) *
    (2:ℚ)^(exponent+shift) -
    signCoefficient sign * mantissa * (2:ℚ)^exponent| ≤ (2:ℚ)^(exponent+shift)/2
  rw [he, abs_le]
  cases sign <;> simp only [signCoefficient] <;> constructor <;> nlinarith
/-- Padding a significand with zero bits and compensating its exponent preserves its signed dyadic
  value. -/
theorem dyadic_padding_exact (sign : Sign) (mantissa shift : Nat) (exponent : Int) :
    signCoefficient sign * ((mantissa * 2 ^ shift : Nat) : ℚ) * (2 : ℚ) ^ (exponent - shift) =
      signCoefficient sign * mantissa * (2 : ℚ) ^ exponent := by
  have hp : (2:ℚ)^shift * (2:ℚ)^(exponent-shift) = (2:ℚ)^exponent := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
    congr 1
    omega
  push_cast
  calc
    signCoefficient sign * (mantissa * (2:ℚ)^shift) * (2:ℚ)^(exponent-shift) =
        signCoefficient sign * mantissa * ((2:ℚ)^shift * (2:ℚ)^(exponent-shift)) := by ring
    _ = _ := by rw [hp]

/-- Exact rounding keeps zero for every format, exponent and zero sign. -/
theorem model_roundWithAccuracy_zero (spec : Format) (sign : Sign) (exponent : Int) :
    roundWithAccuracy spec sign 0 exponent .exact = .zero sign := by
  rw [model_round_exact_components]
  have hp := Nat.two_pow_pos spec.mantissaBits
  simp [Rounding.nearestEven]
  omega

/-- The initial normalization also preserves zero and its sign. -/
theorem model_round_zero (spec : Format) (sign : Sign) (exponent : Int) :
    round spec sign 0 exponent = .zero sign := by
  simp only [round, decreaseExponent, Nat.zero_shiftLeft]
  exact model_roundWithAccuracy_zero spec sign _

/-- Full standard rounding, including initial left normalization, has half a target-unit error
  before packing. -/
theorem model_round_error (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int) :
    |unpackedValue (round spec sign mantissa exponent) - signCoefficient sign * mantissa *
      (2 : ℚ) ^ exponent| ≤
      (2 : ℚ) ^ (spec.targetExponent (totalExponent mantissa exponent)) / 2 := by
  by_cases hz : mantissa = 0
  · rw [hz, model_round_zero]
    simp only [unpackedValue, Nat.cast_zero, mul_zero, zero_mul, sub_self, abs_zero]
    exact div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  · let target := spec.targetExponent (totalExponent mantissa exponent)
    let shift := (exponent-target).toNat
    have hp : 0 < mantissa := by omega
    have htotal : totalExponent (mantissa*2^shift) (exponent-shift) = totalExponent mantissa
      exponent := by
      simp only [totalExponent, model_log2_scaled_positive mantissa shift hp]
      omega
    have he : exponent-shift ≤ target := by dsimp [shift]; omega
    have hout : exponent-shift+(target-(exponent-shift)).toNat = target := by omega
    have error := model_round_exact_error spec sign (mantissa*2^shift) (exponent-shift)
    dsimp only at error
    rw [htotal, hout, dyadic_padding_exact] at error
    change |unpackedValue (roundWithAccuracy spec sign (mantissa*2^shift) (exponent-shift) .exact)
      -
      signCoefficient sign * mantissa * (2:ℚ)^exponent| ≤ (2:ℚ)^target/2 at error
    simpa only [round, decreaseExponent, Nat.shiftLeft_eq] using error

/-- Finite canonical components: the significand fits the precision and has a leading bit unless
the exponent is at the subnormal floor. This predicate does not establish that packing avoids
overflow. -/
def ModelNormalized (spec : Format) : UnpackedFloat → Prop
  | .zero _ => True
  | .finite _ mantissa exponent _ =>
      mantissa < 2 ^ spec.mantissaBits ∧ spec.minExponent ≤ exponent ∧
      (exponent = spec.minExponent ∨ 2 ^ spec.mantissaBitsWithoutImplicit ≤ mantissa)
  | _ => False

/-- Nearest-even rounding never decreases the retained integer significand, for every residual-bit
combination. -/
theorem model_rounded_not_below (em : ExtendedMantissa) : em.mantissa ≤ em.roundedMantissa := by
  rcases em with ⟨mantissa, r, s⟩
  cases r <;> cases s <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven]


/-- A positive significand shifted to its target retains the implicit leading bit unless its
exponent reaches the subnormal floor. -/
theorem model_first_normalized_lower (spec : Format) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (hp : 0 < mantissa)
    (he : exponent ≤ spec.targetExponent (totalExponent mantissa exponent)) :
    let first := shiftToTargetExponent spec mantissa exponent accuracy
    first.2 = spec.minExponent ∨
      2 ^ spec.mantissaBitsWithoutImplicit ≤ first.1.mantissa := by
  dsimp only
  let target := spec.targetExponent (totalExponent mantissa exponent)
  let shift := (target - exponent).toNat
  have hexp : exponent + shift = target := by omega
  have heq : (shiftToTargetExponent spec mantissa exponent accuracy).2 = target := by
    change exponent + shift = target
    exact hexp
  rw [heq]
  by_cases hmin : target = spec.minExponent
  · exact Or.inl hmin
  · right
    have ht : target = mantissa.log2 + exponent - spec.mantissaBitsWithoutImplicit := by
      simp only [target, Format.targetExponent, totalExponent, Format.mantissaBits] at *
      omega
    have hshift : spec.mantissaBitsWithoutImplicit + shift = mantissa.log2 := by omega
    have hlo := ((Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mp rfl).1
    change 2 ^ spec.mantissaBitsWithoutImplicit ≤
      (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy >>> shift).mantissa
    rw [model_shift_mantissa]
    have hmantissa : (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy).mantissa =
        mantissa := by cases accuracy with
      | exact => rfl
      | inexact order => cases order <;> rfl
    rw [hmantissa]
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos shift)).mpr
    rw [← Nat.pow_add, hshift]
    exact hlo

/-- Rounding with residual-bit accuracy yields canonical components when its input exponent needs
no left normalization. -/
theorem model_round_accuracy_normalized (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy) (hp : 0 < mantissa)
    (he : exponent ≤ spec.targetExponent (totalExponent mantissa exponent)) :
    ModelNormalized spec (roundWithAccuracy spec sign mantissa exponent accuracy) := by
  rw [model_round_accuracy_components]
  let first := shiftToTargetExponent spec mantissa exponent accuracy
  have hb : first.1.roundedMantissa ≤ 2 ^ spec.mantissaBits := by
    have hlo := model_first_mantissa_format spec mantissa exponent accuracy
    have hhi := model_round_mantissa_ceiling first.1
    change first.1.mantissa < 2 ^ spec.mantissaBits at hlo
    omega
  have hlow := model_first_normalized_lower spec mantissa exponent accuracy hp he
  have hrounded := model_rounded_not_below first.1
  have hemin : spec.minExponent ≤ first.2 := by
    simp only [first, shiftToTargetExponent, shiftToExponent, Format.targetExponent]
    omega
  change ModelNormalized spec (if first.1.roundedMantissa = 2 ^ spec.mantissaBits then
    .finite sign (2 ^ spec.mantissaBitsWithoutImplicit) (first.2+1) (Nat.two_pow_pos _)
    else if h : first.1.roundedMantissa = 0 then .zero sign
    else .finite sign first.1.roundedMantissa first.2 (Nat.pos_of_ne_zero h))
  by_cases carry : first.1.roundedMantissa = 2 ^ spec.mantissaBits
  · rw [if_pos carry]
    dsimp only [ModelNormalized]
    have hpows : 2 ^ spec.mantissaBitsWithoutImplicit < 2 ^ spec.mantissaBits := by
      rw [Format.mantissaBits, Nat.add_comm, Nat.pow_succ]
      have := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit
      omega
    exact ⟨hpows, by omega, Or.inr (Nat.le_refl _)⟩
  · rw [if_neg carry]
    split
    · trivial
    · dsimp only [ModelNormalized]
      refine ⟨by omega, hemin, ?_⟩
      rcases hlow with h | h
      · exact Or.inl h
      · exact Or.inr (Nat.le_trans h hrounded)

/-- The complete standard rounding operation produces canonical components for every sign, natural
significand and integer exponent. -/
theorem model_round_normalized (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int) :
    ModelNormalized spec (round spec sign mantissa exponent) := by
  by_cases hz : mantissa = 0
  · rw [hz, model_round_zero]
    trivial
  · let target := spec.targetExponent (totalExponent mantissa exponent)
    let shift := (exponent-target).toNat
    have hp : 0 < mantissa := by omega
    have htotal : totalExponent (mantissa*2^shift) (exponent-shift) =
        totalExponent mantissa exponent := by
      simp only [totalExponent, model_log2_scaled_positive mantissa shift hp]
      omega
    change ModelNormalized spec (roundWithAccuracy spec sign
      (mantissa <<< shift) (exponent - shift) .exact)
    rw [Nat.shiftLeft_eq]
    apply model_round_accuracy_normalized
    · exact Nat.mul_pos hp (Nat.two_pow_pos _)
    · rw [htotal]
      change exponent-shift ≤ target
      dsimp [shift]
      omega


/-- The actual packing exponent guard stays below its infinity branch. Normalization is a separate
prerequisite for preserving the decoded value. -/
def ModelFits (spec : Format) : UnpackedFloat → Prop
  | .zero _ => True
  | .finite _ _ exponent _ =>
      (exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 <
        2 ^ spec.exponentBits
  | _ => False

/-- The subnormal floor and format bias derive the same exponent-field boundary. -/
theorem model_format_min_bias (spec : Format) :
    spec.minExponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit = 1 := by
  have hp := Nat.two_pow_pos (spec.exponentBits - 1)
  simp only [Format.minExponent, Format.exponentBias, Format.mantissaBits,
    Int.natCast_add, Int.natCast_one, Int.natCast_sub (by omega : 1 ≤ 2 ^ (spec.exponentBits-1)),
    Int.natCast_pow, Nat.cast_ofNat]
  omega

/-- Packing and extracting the sign field preserves either sign independently of all other fields.
-/
theorem model_unpack_sign_components (spec : Format) (sign : Sign)
    (exponent : BitVec spec.exponentBits) (mantissa : BitVec spec.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  have hz : i = 0 := by omega
  subst i
  simp [unpackSign, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append,
    BitVec.getElem_append]

/-- The actual decoder applied to packed components follows the declared exceptional, subnormal
and normal branches. -/
theorem model_unpack_components (spec : Format) (sign : Sign)
    (exponent : BitVec spec.exponentBits) (mantissa : BitVec spec.mantissaBitsWithoutImplicit) :
    unpack spec (packComponents spec sign exponent mantissa) =
      if exponent = - 1#_ then
        if mantissa = 0#_ then .infinity sign else .notANumber
      else if exponent = 0#_ then
        if h : mantissa = 0#_ then .zero sign else
          .finite sign mantissa.toNat
            (exponent.toNat - (spec.exponentBias + spec.mantissaBitsWithoutImplicit) + 1)
            (by simpa [BitVec.toNat_pos, BitVec.pos_iff_ne_zero])
      else .finite sign (1#1 ++ mantissa).toNat
        (exponent.toNat - (spec.exponentBias + spec.mantissaBitsWithoutImplicit)) (by simp) := by
  simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    model_unpack_sign_components]
  cases sign <;> rfl

/-- Packing and decoding preserve canonical finite components whenever the actual packing overflow
guard is false. -/
theorem model_unpack_pack_normalized (spec : Format) (value : UnpackedFloat)
    (normal : ModelNormalized spec value) (fits : ModelFits spec value) :
    unpack spec (pack spec value) = value := by
  cases value with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    rw [pack, packedZero, model_unpack_components]
    have hn : (0#spec.exponentBits) ≠ -1#spec.exponentBits := by
      have hp := Nat.one_lt_two_pow (Nat.ne_of_gt spec.he)
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.zero_mod, BitVec.neg_one_eq_allOnes,
        BitVec.toNat_allOnes] at this
      omega
    simp [hn]
  | finite sign mantissa exponent positive =>
    rcases normal with ⟨hbound, hemin, hleading⟩
    change (exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 <
      2 ^ spec.exponentBits at fits
    let biased := (exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat
    have hpositive : 0 < biased := by
      have hmin := model_format_min_bias spec
      dsimp [biased]
      omega
    have hfit : biased < 2 ^ spec.exponentBits := by omega
    have hinf : (BitVec.ofNat spec.exponentBits biased) ≠ -1#spec.exponentBits := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, BitVec.neg_one_eq_allOnes,
        BitVec.toNat_allOnes] at this
      omega
    have hzero : (BitVec.ofNat spec.exponentBits biased) ≠ 0#spec.exponentBits := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, Nat.zero_mod] at this
      omega
    have heval : (biased : Int) - (spec.exponentBias + spec.mantissaBitsWithoutImplicit) =
        exponent := by dsimp [biased]; omega
    unfold pack
    rw [if_neg (by omega)]
    by_cases leading : 2 ^ spec.mantissaBitsWithoutImplicit ≤ mantissa
    · have logeq : mantissa.log2 = spec.mantissaBitsWithoutImplicit := by
        apply (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr
        exact ⟨leading, by simpa [Format.mantissaBits, Nat.add_comm] using hbound⟩
      have hnormal : mantissa.log2 + 1 = spec.mantissaBits := by
        rw [logeq, Format.mantissaBits]
        omega
      rw [if_pos hnormal, model_unpack_components, if_neg hinf, if_neg hzero]
      have hmvec : (1#1 ++ BitVec.ofNat spec.mantissaBitsWithoutImplicit mantissa).toNat =
          2 ^ spec.mantissaBitsWithoutImplicit + mantissa % 2 ^ spec.mantissaBitsWithoutImplicit
            := by
        simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
          show 1 % 2 ^ 1 = 1 from rfl, Nat.one_mul]
        rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)),
          Nat.add_comm]
      have hquot : mantissa / 2 ^ spec.mantissaBitsWithoutImplicit = 1 := by
        apply Nat.div_eq_of_lt_le
        · simpa using leading
        · simpa [Format.mantissaBits, Nat.add_comm, Nat.pow_succ, Nat.mul_comm] using hbound
      have hreconstruct : 2 ^ spec.mantissaBitsWithoutImplicit +
          mantissa % 2 ^ spec.mantissaBitsWithoutImplicit = mantissa := by
        have h := Nat.div_add_mod mantissa (2 ^ spec.mantissaBitsWithoutImplicit)
        rw [hquot] at h
        omega
      dsimp only [biased] at hfit heval
      simp only [hmvec, hreconstruct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, heval]
    · have hsmall : mantissa < 2 ^ spec.mantissaBitsWithoutImplicit := by omega
      have heq : exponent = spec.minExponent := hleading.resolve_right leading
      have hnormal : ¬ mantissa.log2 + 1 = spec.mantissaBits := by
        have hl := (Nat.log2_lt (by omega : mantissa ≠ 0)).mpr hsmall
        simp only [Format.mantissaBits]
        omega
      rw [if_neg hnormal, model_unpack_components]
      have hn : (0#spec.exponentBits) ≠ -1#spec.exponentBits := by
        have hp := Nat.one_lt_two_pow (Nat.ne_of_gt spec.he)
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.zero_mod, BitVec.neg_one_eq_allOnes,
          BitVec.toNat_allOnes] at this
        omega
      rw [if_neg hn, if_pos rfl]
      have hmzero : BitVec.ofNat spec.mantissaBitsWithoutImplicit mantissa ≠ 0#_ := by
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.zero_mod] at this
        omega
      rw [dif_neg hmzero]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.zero_mod, Int.natCast_zero]
      have hbias := model_format_min_bias spec
      have hout : (0 : Int) - (spec.exponentBias + spec.mantissaBitsWithoutImplicit) + 1 =
          exponent := by omega
      rw [hout]


/-- Every finite raw encoding decodes to canonical components that fit the format. The exponent-
width hypothesis includes binary32 and binary64; one-bit exponent formats are excluded explicitly.
-/
theorem model_unpack_format (spec : Format) (exponentWidth : 1 < spec.exponentBits)
    (bits : BitVec spec.numBits) (finite : (unpack spec bits).isFinite = true) :
    ModelNormalized spec (unpack spec bits) ∧ ModelFits spec (unpack spec bits) := by
  let ev := unpackExponent bits
  let mv := unpackMantissa bits
  let sv := Sign.ofBitVec (unpackSign bits)
  have he := ev.isLt
  have hm := mv.isLt
  have hbias := model_format_min_bias spec
  have unpackEq : unpack spec bits =
      (if ev = -1#_ then if mv = 0#_ then .infinity sv else .notANumber
      else if ev = 0#_ then if h : mv = 0#_ then .zero sv else
        .finite sv mv.toNat (ev.toNat-(spec.exponentBias+spec.mantissaBitsWithoutImplicit)+1)
          (by simpa [BitVec.toNat_pos, BitVec.pos_iff_ne_zero])
      else .finite sv (1#1 ++ mv).toNat
        (ev.toNat-(spec.exponentBias+spec.mantissaBitsWithoutImplicit)) (by simp)) := rfl
  by_cases inf : ev = -1#_
  · rw [unpackEq, if_pos inf] at finite
    split at finite <;> contradiction
  · have hev : ev.toNat + 1 < 2 ^ spec.exponentBits := by
      have hn : ev.toNat ≠ 2 ^ spec.exponentBits-1 := by
        intro h
        apply inf
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] using h
      omega
    rw [if_neg inf] at unpackEq
    by_cases ez : ev = 0#_
    · rw [if_pos ez] at unpackEq
      have ezn : ev.toNat = 0 := congrArg BitVec.toNat ez
      have eout : (ev.toNat : Int) - (spec.exponentBias+spec.mantissaBitsWithoutImplicit)+1 =
          spec.minExponent := by rw [ezn]; omega
      by_cases mz : mv = 0#_
      · rw [dif_pos mz] at unpackEq
        rw [unpackEq]
        exact ⟨True.intro, True.intro⟩
      · rw [dif_neg mz] at unpackEq
        rw [unpackEq]
        dsimp only [ModelNormalized, ModelFits]
        rw [eout]
        have hprecision : 2 ^ spec.mantissaBitsWithoutImplicit ≤ 2 ^ spec.mantissaBits := by
          apply Nat.pow_le_pow_right (by decide)
          simp only [Format.mantissaBits]
          omega
        refine ⟨⟨Nat.lt_of_lt_of_le hm hprecision, Int.le_refl _, Or.inl rfl⟩, ?_⟩
        rw [hbias]
        change 2 < 2 ^ spec.exponentBits
        exact Nat.pow_lt_pow_right (by decide : 1 < 2) exponentWidth
    · rw [if_neg ez] at unpackEq
      rw [unpackEq]
      dsimp only [ModelNormalized, ModelFits]
      have ezn : 0 < ev.toNat := by
        apply Nat.pos_of_ne_zero
        intro h
        exact ez (BitVec.eq_of_toNat_eq h)
      have eout : spec.minExponent ≤
          (ev.toNat : Int) - (spec.exponentBias+spec.mantissaBitsWithoutImplicit) := by omega
      have hmantissa : (1#1 ++ mv).toNat = 2 ^ spec.mantissaBitsWithoutImplicit + mv.toNat := by
        simp only [BitVec.toNat_append, show (1#1).toNat = 1 from rfl, Nat.shiftLeft_eq,
          Nat.one_mul]
        rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt hm, Nat.add_comm]
      rw [hmantissa]
      have hpows : 2 ^ spec.mantissaBits = 2 * 2 ^ spec.mantissaBitsWithoutImplicit := by
        rw [Format.mantissaBits, Nat.pow_add]
      refine ⟨⟨by omega, eout, Or.inr (by omega)⟩, ?_⟩
      have heq : ((ev.toNat : Int)-(spec.exponentBias+spec.mantissaBitsWithoutImplicit)+
          spec.exponentBias+spec.mantissaBitsWithoutImplicit).toNat = ev.toNat := by omega
      rw [heq]
      exact hev


/-- The magnitude of a finite signed dyadic is exactly its nonnegative significand times its power
of two. -/
theorem model_finite_abs (sign : Sign) (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa) :
    |unpackedValue (.finite sign mantissa exponent positive)| = mantissa * (2 : ℚ) ^ exponent := by
  have hp : (0:ℚ) ≤ (mantissa:ℚ) * (2:ℚ)^exponent :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _))
  cases sign <;> simp only [unpackedValue, signCoefficient, one_mul, neg_mul, abs_neg] <;>
    exact abs_of_nonneg hp

/-- A numerical magnitude bound implies the actual packing exponent guard, given a finite
constructor and an admissible exponent limit. -/
theorem model_fits_of_value_bound (spec : Format) (value : UnpackedFloat)
    (finite : value.isFinite = true) (limit : Int)
    (range : (limit + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 <
      2 ^ spec.exponentBits)
    (bound : |unpackedValue value| ≤ (2 : ℚ) ^ limit) : ModelFits spec value := by
  cases value with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign => trivial
  | finite sign mantissa exponent positive =>
    rw [model_finite_abs] at bound
    have hm : (1:ℚ) ≤ mantissa := by exact_mod_cast positive
    have hp : (0:ℚ) < (2:ℚ)^exponent := zpow_pos (by norm_num) _
    have he : exponent ≤ limit := by
      apply (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℚ) < 2)).mp
      have := mul_le_mul_of_nonneg_right hm (le_of_lt hp)
      linarith
    dsimp only [ModelFits]
    have hcast : (exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat ≤
        (limit + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat := by omega
    omega

/-- Canonical components cannot be an infinity or a NaN constructor. -/
theorem model_normalized_finite (spec : Format) (value : UnpackedFloat)
    (normal : ModelNormalized spec value) : value.isFinite = true := by
  cases value <;> first | rfl | contradiction

/-- A positive dyadic lies in the half-open power-of-two interval selected by its actual total
exponent. -/
theorem model_positive_dyadic_window (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa) :
    (2 : ℚ) ^ (totalExponent mantissa exponent - 1) ≤ mantissa * (2 : ℚ) ^ exponent ∧
      mantissa * (2 : ℚ) ^ exponent < (2 : ℚ) ^ (totalExponent mantissa exponent) := by
  have hlog := (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mp rfl
  have hlo : (2:ℚ)^mantissa.log2 ≤ mantissa := by exact_mod_cast hlog.1
  have hhi : (mantissa:ℚ) < (2:ℚ)^(mantissa.log2+1) := by exact_mod_cast hlog.2
  have hp : (0:ℚ) < (2:ℚ)^exponent := zpow_pos (by norm_num) _
  have low := mul_le_mul_of_nonneg_right hlo (le_of_lt hp)
  have high := mul_lt_mul_of_pos_right hhi hp
  have ht : totalExponent mantissa exponent-1 = (mantissa.log2:Int)+exponent := by
    simp only [totalExponent]
    omega
  rw [ht, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), zpow_natCast]
  constructor
  · exact low
  · have ht' : totalExponent mantissa exponent = ((mantissa.log2+1:Nat):Int)+exponent := by
      simp [totalExponent]
    rw [ht', zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), zpow_natCast]
    exact high

/-- Numerical ordering of positive dyadics preserves ordering of the model total exponent. -/
theorem model_totalExponent_mono (left right : Nat) (leftExponent rightExponent : Int)
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (ordered : (left : ℚ) * (2 : ℚ) ^ leftExponent ≤ right * (2 : ℚ) ^ rightExponent) :
    totalExponent left leftExponent ≤ totalExponent right rightExponent := by
  have hlo := (model_positive_dyadic_window left leftExponent leftPositive).1
  have hhi := (model_positive_dyadic_window right rightExponent rightPositive).2
  have hp := lt_of_le_of_lt (le_trans hlo ordered) hhi
  have he := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ) < 2)).mp hp
  omega

/-- Every canonical finite component already has the exponent selected by the format target rule.
-/
theorem model_normalized_target (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent : Int) (positive : 0 < mantissa)
    (normal : ModelNormalized spec (.finite sign mantissa exponent positive)) :
    spec.targetExponent (totalExponent mantissa exponent) = exponent := by
  rcases normal with ⟨bound, floor, leading⟩
  have hlo := (Nat.log2_lt (by omega : mantissa ≠ 0)).mpr bound
  rcases leading with he | hm
  · simp only [Format.targetExponent, totalExponent]
    omega
  · have logeq : mantissa.log2 = spec.mantissaBitsWithoutImplicit := by
      apply (Nat.log2_eq_iff (by omega : mantissa ≠ 0)).mpr
      exact ⟨hm, by simpa [Format.mantissaBits, Nat.add_comm] using bound⟩
    simp only [Format.targetExponent, totalExponent, logeq, Format.mantissaBits]
    omega


/-- A power-of-two input magnitude bound supplies a uniform half-unit error bound for the complete
standard rounding path before packing. -/
theorem model_round_uniform_error (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent limit : Int)
    (bound : |signCoefficient sign * mantissa * (2 : ℚ) ^ exponent| ≤ (2 : ℚ) ^ limit) :
    |unpackedValue (round spec sign mantissa exponent) -
      signCoefficient sign * mantissa * (2 : ℚ) ^ exponent| ≤
      (2 : ℚ) ^ (max (limit + 1 - spec.mantissaBits) spec.minExponent) / 2 := by
  by_cases hz : mantissa = 0
  · rw [hz, model_round_zero]
    simp only [unpackedValue, Nat.cast_zero, mul_zero, zero_mul, sub_self, abs_zero]
    exact div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  · have hp : 0 < mantissa := by omega
    have habs : |signCoefficient sign * mantissa * (2:ℚ)^exponent| =
        mantissa*(2:ℚ)^exponent := model_finite_abs sign mantissa exponent hp
    rw [habs] at bound
    have hlo := (model_positive_dyadic_window mantissa exponent hp).1
    have htotal : totalExponent mantissa exponent ≤ limit+1 := by
      have he := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℚ) < 2)).mp (le_trans hlo bound)
      omega
    have htarget : spec.targetExponent (totalExponent mantissa exponent) ≤
        max (limit+1-spec.mantissaBits) spec.minExponent := by
      dsimp only [Format.targetExponent]
      omega
    apply le_trans (model_round_error spec sign mantissa exponent)
    exact div_le_div_of_nonneg_right
      (zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2) htarget) (by norm_num)

/-- The executing signed-integer application agrees with the proof-side rational sign coefficient.
-/
theorem model_sign_apply_value (sign : Sign) (mantissa : Nat) :
    (sign.apply mantissa : ℚ) = signCoefficient sign * mantissa := by
  cases sign <;> simp [Sign.apply, signCoefficient]

/-- Multiplication of the two machine signs agrees with multiplication of their rational
coefficients. -/
theorem model_sign_product_value (left right : Sign) :
    signCoefficient (left * right) = signCoefficient left * signCoefficient right := by
  cases left <;> cases right <;> norm_num [signCoefficient]

/-- Signed-integer normalization produces canonical components with the derived rounding bound,
including the zero branch. -/
theorem model_signed_round_value (spec : Format) (mantissa : Int) (exponent : Int) (zeroSign : Sign)
    (limit : Int) (bound : |(mantissa : ℚ) * (2 : ℚ) ^ exponent| ≤ (2 : ℚ) ^ limit) :
    ModelNormalized spec (normalize spec mantissa exponent zeroSign) ∧
      |unpackedValue (normalize spec mantissa exponent zeroSign) -
        (mantissa : ℚ) * (2 : ℚ) ^ exponent| ≤
        (2 : ℚ) ^ (max (limit + 1 - spec.mantissaBits) spec.minExponent) / 2 := by
  unfold normalize
  split
  · rename_i negative
    have hn : mantissa < 0 := (Int.compare_eq_lt).mp negative
    have hs : (signCoefficient Sign.negative * (-mantissa).toNat : ℚ) = mantissa := by
      simp only [signCoefficient]
      have he : ((-mantissa).toNat : Int) = -mantissa := Int.toNat_of_nonneg (by omega)
      have hc : ((-mantissa).toNat : ℚ) = -(mantissa:ℚ) := by exact_mod_cast he
      rw [hc]
      ring
    refine ⟨model_round_normalized _ _ _ _, ?_⟩
    have proof := model_round_uniform_error spec .negative (-mantissa).toNat exponent limit
      (by simpa only [hs] using bound)
    simpa only [hs] using proof
  · rename_i zero
    have hn : mantissa = 0 := (Int.compare_eq_eq).mp zero
    subst mantissa
    refine ⟨True.intro, ?_⟩
    simp only [unpackedValue, Int.cast_zero, zero_mul, sub_self, abs_zero]
    exact div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  · rename_i positive
    have hn : 0 < mantissa := (Int.compare_eq_gt).mp positive
    have hs : (signCoefficient Sign.positive * mantissa.toNat : ℚ) = mantissa := by
      simp only [signCoefficient, one_mul]
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ mantissa)
    refine ⟨model_round_normalized _ _ _ _, ?_⟩
    have proof := model_round_uniform_error spec .positive mantissa.toNat exponent limit
      (by simpa only [hs] using bound)
    simpa only [hs] using proof


/-- Every supported format has a nonpositive subnormal exponent floor, derived from its positive
field widths. -/
theorem model_format_min_nonpositive (spec : Format) : spec.minExponent ≤ 0 := by
  have hm := spec.hm
  have hp := Nat.two_pow_pos (spec.exponentBits-1)
  simp only [Format.minExponent, Format.mantissaBits]
  have hpower : (1:Int) ≤ 2 ^ (spec.exponentBits-1) := by exact_mod_cast hp
  omega

/-- Multiplying two canonical finite significands never needs left normalization before the
standard multiplication rounding path. -/
theorem model_product_exponent_ready (spec : Format) (left right : Nat)
    (leftExponent rightExponent : Int) (leftSign rightSign : Sign)
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (leftNormal : ModelNormalized spec (.finite leftSign left leftExponent leftPositive))
    (rightNormal : ModelNormalized spec (.finite rightSign right rightExponent rightPositive)) :
    leftExponent + rightExponent ≤
      spec.targetExponent (totalExponent (left * right) (leftExponent + rightExponent)) := by
  rcases leftNormal with ⟨_, _, leftLeading⟩
  rcases rightNormal with ⟨_, _, rightLeading⟩
  by_cases hl : 2 ^ spec.mantissaBitsWithoutImplicit ≤ left
  · have hp : 2 ^ spec.mantissaBitsWithoutImplicit ≤ left*right := by nlinarith
    have hlog : spec.mantissaBitsWithoutImplicit ≤ (left*right).log2 := by
      exact (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos leftPositive rightPositive))).mpr hp
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits]
    omega
  · by_cases hr : 2 ^ spec.mantissaBitsWithoutImplicit ≤ right
    · have hp : 2 ^ spec.mantissaBitsWithoutImplicit ≤ left*right := by nlinarith
      have hlog : spec.mantissaBitsWithoutImplicit ≤ (left*right).log2 := by
        exact (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos leftPositive rightPositive))).mpr hp
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits]
      omega
    · have he1 := leftLeading.resolve_right hl
      have he2 := rightLeading.resolve_right hr
      have hmin := model_format_min_nonpositive spec
      simp only [Format.targetExponent]
      omega

/-- When the source exponent is already small enough, complete rounding uses the same residual-bit
rounding path without padding. -/
theorem model_round_without_padding (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent : Int) (ready : exponent ≤ spec.targetExponent (totalExponent mantissa exponent)) :
    round spec sign mantissa exponent = roundWithAccuracy spec sign mantissa exponent .exact := by
  simp only [round, decreaseExponent]
  have hz : (exponent-spec.targetExponent (totalExponent mantissa exponent)).toNat = 0 := by omega
  rw [hz]
  simp only [Nat.shiftLeft_zero, Int.ofNat_zero, sub_zero]

/-- The actual unpacked multiplication preserves normalization and has the derived dyadic error
bound on finite canonical operands. Packing still requires its separate guard. -/
theorem model_mul_dyadic_local (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (limit : Int)
    (bound : |unpackedValue left * unpackedValue right| ≤ (2 : ℚ) ^ limit) :
    ModelNormalized spec (UnpackedFloat.mul spec left right) ∧
      |unpackedValue (UnpackedFloat.mul spec left right) -
        unpackedValue left * unpackedValue right| ≤
        (2 : ℚ) ^ (max (limit + 1 - spec.mantissaBits) spec.minExponent) / 2 := by
  have epsilon : (0:ℚ) ≤ (2:ℚ)^(max (limit+1-spec.mantissaBits) spec.minExponent)/2 :=
    div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right <;> first | contradiction |
      simpa only [UnpackedFloat.mul, ModelNormalized, unpackedValue, zero_mul,
        sub_self, abs_zero, true_and] using epsilon
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero rightSign =>
      simpa only [UnpackedFloat.mul, ModelNormalized, unpackedValue, mul_zero,
        sub_self, abs_zero, true_and] using epsilon
    | finite rightSign rm re rp =>
      have ready := model_product_exponent_ready spec lm rm le re leftSign rightSign lp rp
        leftNormal rightNormal
      simp only [UnpackedFloat.mul]
      rw [← model_round_without_padding spec _ _ _ ready]
      have heq : signCoefficient (leftSign*rightSign) * (lm*rm:Nat) * (2:ℚ)^(le+re) =
          unpackedValue (.finite leftSign lm le lp)*unpackedValue (.finite rightSign rm re rp) := by
        rw [model_sign_product_value, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
        simp only [unpackedValue, Nat.cast_mul]
        ring
      exact ⟨model_round_normalized _ _ _ _, by
        simpa only [heq] using model_round_uniform_error spec (leftSign*rightSign) (lm*rm)
          (le+re) limit (by simpa only [heq] using bound)⟩


/-- The exact exponent-alignment operation preserves the signed dyadic value whenever the target
exponent is no larger. -/
theorem model_decrease_dyadic_value (sign : Sign) (mantissa : Nat) (exponent target : Int)
    (ordered : target ≤ exponent) :
    (sign.apply (decreaseExponent mantissa exponent target).1 : ℚ) * (2 : ℚ) ^ target =
      signCoefficient sign * mantissa * (2 : ℚ) ^ exponent := by
  let shift := (exponent-target).toNat
  have ht : exponent-shift = target := by omega
  simp only [model_sign_apply_value, decreaseExponent, Nat.shiftLeft_eq]
  have hp := dyadic_padding_exact sign mantissa shift exponent
  rw [ht] at hp
  exact hp

/-- The actual unpacked addition, including signed alignment and cancellation, preserves
normalization and satisfies the derived dyadic error bound before packing. -/
theorem model_add_dyadic_local (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (limit : Int)
    (bound : |unpackedValue left + unpackedValue right| ≤ (2 : ℚ) ^ limit) :
    ModelNormalized spec (UnpackedFloat.add spec left right) ∧
      |unpackedValue (UnpackedFloat.add spec left right) -
        (unpackedValue left + unpackedValue right)| ≤
        (2 : ℚ) ^ (max (limit + 1 - spec.mantissaBits) spec.minExponent) / 2 := by
  have epsilon : (0:ℚ) ≤ (2:ℚ)^(max (limit+1-spec.mantissaBits) spec.minExponent)/2 :=
    div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right with
    | notANumber => contradiction
    | infinity s => contradiction
    | zero s =>
      cases sign <;> cases s <;>
        change True ∧ |(0:ℚ)-(0+0)| ≤ _
      all_goals exact ⟨True.intro, by simpa only [add_zero, sub_self, abs_zero] using epsilon⟩
    | finite s m e hp =>
      simpa only [UnpackedFloat.add, unpackedValue, zero_add, sub_self, abs_zero] using
        And.intro rightNormal epsilon
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero rightSign =>
      simpa only [UnpackedFloat.add, unpackedValue, add_zero, sub_self, abs_zero] using
        And.intro leftNormal epsilon
    | finite rightSign rm re rp =>
      simp only [UnpackedFloat.add]
      let target := min le re
      let lmantissa := (decreaseExponent lm le target).1
      let rmantissa := (decreaseExponent rm re target).1
      let sum := leftSign.apply lmantissa + rightSign.apply rmantissa
      have hl := model_decrease_dyadic_value leftSign lm le target (Int.min_le_left _ _)
      have hr := model_decrease_dyadic_value rightSign rm re target (Int.min_le_right _ _)
      have heq : (sum:ℚ)*(2:ℚ)^target =
          unpackedValue (.finite leftSign lm le lp)+unpackedValue (.finite rightSign rm re rp) := by
        change ((leftSign.apply lmantissa + rightSign.apply rmantissa : Int):ℚ)*(2:ℚ)^target = _
        rw [Int.cast_add, add_mul, hl, hr]
        rfl
      have proof := model_signed_round_value spec sum target .positive limit
        (by simpa only [heq] using bound)
      change ModelNormalized spec (normalize spec sum target .positive) ∧ _
      simpa only [heq] using proof


/-- The actual decoder is finite exactly when its exponent field is below the all-ones field, for
every raw encoding. -/
theorem model_unpack_finite_exponent (spec : Format) (bits : BitVec spec.numBits) :
    (unpack spec bits).isFinite =
      decide ((unpackExponent bits).toNat < 2 ^ spec.exponentBits - 1) := by
  let ev := unpackExponent bits
  have he := ev.isLt
  by_cases inf : ev = -1#_
  · have hn : ev.toNat = 2 ^ spec.exponentBits-1 := by
      rw [inf]
      simp only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
    have hfield : ¬ (unpackExponent bits).toNat < 2 ^ spec.exponentBits-1 := by
      change ¬ ev.toNat < _
      omega
    simp only [decide_eq_false hfield]
    unfold unpack
    rw [if_pos inf]
    split <;> rfl
  · have hn : ev.toNat < 2 ^ spec.exponentBits-1 := by
      have hne : ev.toNat ≠ 2 ^ spec.exponentBits-1 := by
        intro h
        apply inf
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] using h
      omega
    simp only [show (unpackExponent bits).toNat < 2 ^ spec.exponentBits-1 from hn,
      decide_true]
    unfold unpack
    rw [if_neg inf]
    split
    · split <;> rfl
    · rfl

/-- The pinned standard-model interpretation of a raw binary64 word. No arithmetic or payload-
changing conversion is performed here. -/
def decoded64 (value : Binary64) : UnpackedFloat := unpack Format.binary64 value.bits.toBitVec

/-- Proof-side dyadic reading of a binary64 word. Numerical claims require a finite-input
hypothesis; exceptional words use only the total extension of unpackedValue. -/
def numerical64 (value : Binary64) : ℚ := unpackedValue (decoded64 value)

/-- The pinned standard-model interpretation of a raw binary32 word, independent of native
arithmetic. -/
def decoded32 (value : Binary32) : UnpackedFloat := unpack Format.binary32 value.bits.toBitVec

/-- Proof-side dyadic reading of a binary32 word, meaningful as an IEEE number only under a
finite-input hypothesis. -/
def numerical32 (value : Binary32) : ℚ := unpackedValue (decoded32 value)

/-- The raw binary64 admission predicate agrees with the actual standard decoder on every machine
word. -/
theorem model_decoded64_finite (value : Binary64) :
    (decoded64 value).isFinite = true ↔ value.Finite := by
  rw [decoded64, model_unpack_finite_exponent, decide_eq_true_eq]
  rw [model_exponent_word]
  have fields := Conversion.fields64_decomposition value
  have fraction := Conversion.fraction64_bound value.bits
  change (((value.bits >>> 52) &&& 0x7ff).toNat < 2047) ↔
    value.magnitude < 0x7ff0000000000000
  omega

/-- The raw binary32 admission predicate agrees with the actual standard decoder on every machine
word. -/
theorem model_decoded32_finite (value : Binary32) :
    (decoded32 value).isFinite = true ↔ value.Finite := by
  rw [decoded32, model_unpack_finite_exponent, decide_eq_true_eq]
  have hexp : (unpackExponent (spec := Format.binary32) value.bits.toBitVec).toNat =
      ((value.bits >>> 23) &&& 0xff).toNat := by
    change (value.bits.toNat >>> 23) % 2^8 = (value.bits.toNat >>> 23) &&& (2^8-1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [hexp]
  have fields := Conversion.fields32_decomposition value
  have fraction := Conversion.fields32_bounds value
  change (((value.bits >>> 23) &&& 0xff).toNat < 255) ↔ value.magnitude < 0x7f800000
  omega

/-- The standard binary64 input conversion preserves every finite decoded value, including signed
zero and subnormals. -/
theorem model_ofBits64_decoded (value : Binary64) (finite : value.Finite) :
    (Float.Model.ofBits value.bits).unpack = decoded64 value := by
  have valid := model_unpack_format Format.binary64 (by decide) value.bits.toBitVec
    ((model_decoded64_finite value).mpr finite)
  change unpack Format.binary64 (pack Format.binary64 (decoded64 value)) = decoded64 value
  exact model_unpack_pack_normalized _ _ valid.1 valid.2

/-- The standard binary32 input conversion preserves every finite decoded value, including signed
zero and subnormals. -/
theorem model_ofBits32_decoded (value : Binary32) (finite : value.Finite) :
    (Float32.Model.ofBits value.bits).unpack = decoded32 value := by
  have valid := model_unpack_format Format.binary32 (by decide) value.bits.toBitVec
    ((model_decoded32_finite value).mpr finite)
  change unpack Format.binary32 (pack Format.binary32 (decoded32 value)) = decoded32 value
  exact model_unpack_pack_normalized _ _ valid.1 valid.2

/-- The executing binary64 addition uses the proved unpacked addition when its result is
normalized and fits the actual packing guard. -/
theorem model_add64_decoded (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (normal : ModelNormalized Format.binary64 (UnpackedFloat.add Format.binary64
      (decoded64 left) (decoded64 right)))
    (fits : ModelFits Format.binary64 (UnpackedFloat.add Format.binary64
      (decoded64 left) (decoded64 right))) :
    decoded64 (left.add right) =
      UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64 right) := by
  change unpack Format.binary64 (pack Format.binary64
    (UnpackedFloat.add Format.binary64 (Float.Model.ofBits left.bits).unpack
      (Float.Model.ofBits right.bits).unpack)) = _
  rw [model_ofBits64_decoded left leftFinite, model_ofBits64_decoded right rightFinite]
  exact model_unpack_pack_normalized _ _ normal fits

/-- The executing binary64 multiplication uses the proved unpacked multiplication when its result
is normalized and fits the actual packing guard. -/
theorem model_mul64_decoded (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (normal : ModelNormalized Format.binary64 (UnpackedFloat.mul Format.binary64
      (decoded64 left) (decoded64 right)))
    (fits : ModelFits Format.binary64 (UnpackedFloat.mul Format.binary64
      (decoded64 left) (decoded64 right))) :
    decoded64 (left.mul right) =
      UnpackedFloat.mul Format.binary64 (decoded64 left) (decoded64 right) := by
  change unpack Format.binary64 (pack Format.binary64
    (UnpackedFloat.mul Format.binary64 (Float.Model.ofBits left.bits).unpack
      (Float.Model.ofBits right.bits).unpack)) = _
  rw [model_ofBits64_decoded left leftFinite, model_ofBits64_decoded right rightFinite]
  exact model_unpack_pack_normalized _ _ normal fits

/-- The executing binary32 addition uses the proved unpacked addition when its result is
normalized and fits the actual packing guard. -/
theorem model_add32_decoded (left right : Binary32) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (normal : ModelNormalized Format.binary32 (UnpackedFloat.add Format.binary32
      (decoded32 left) (decoded32 right)))
    (fits : ModelFits Format.binary32 (UnpackedFloat.add Format.binary32
      (decoded32 left) (decoded32 right))) :
    decoded32 (left.add right) =
      UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right) := by
  change unpack Format.binary32 (pack Format.binary32
    (UnpackedFloat.add Format.binary32 (Float32.Model.ofBits left.bits).unpack
      (Float32.Model.ofBits right.bits).unpack)) = _
  rw [model_ofBits32_decoded left leftFinite, model_ofBits32_decoded right rightFinite]
  exact model_unpack_pack_normalized _ _ normal fits


/-- The local arithmetic magnitude and error bounds imply the actual binary64 packing guard
without an overflow assumption. -/
theorem model_local64_fits (value : UnpackedFloat) (exactValue : ℚ)
    (normal : ModelNormalized Format.binary64 value)
    (bound : |exactValue| ≤ 65536)
    (error : |unpackedValue value - exactValue| ≤ 1 / 137438953472) :
    ModelFits Format.binary64 value := by
  apply model_fits_of_value_bound Format.binary64 value
    (model_normalized_finite _ _ normal) 17 (by decide)
  calc
    |unpackedValue value| = |(unpackedValue value-exactValue)+exactValue| := by
      congr 1
      ring
    _ ≤ |unpackedValue value-exactValue|+|exactValue| := abs_add_le _ _
    _ ≤ 1/137438953472+65536 := add_le_add error bound
    _ ≤ (2:ℚ)^((17:Int)) := by norm_num

/-- Actual binary64 addition stays finite and has error at most 2^-37 whenever its finite operands
have an exact dyadic sum of magnitude at most 2^16. Native primitive correspondence remains the
declared trusted boundary. -/
theorem binary64_add_finite_error (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (bound : |numerical64 left + numerical64 right| ≤ 65536) :
    (left.add right).Finite ∧
      |numerical64 (left.add right) - (numerical64 left + numerical64 right)| ≤
        1 / 137438953472 := by
  have leftNormal := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rightNormal := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have power : (2 : ℚ) ^ (16 : Int) = 65536 := by norm_num
  have localProof := model_add_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    leftNormal rightNormal 16 (by simpa only [numerical64, power] using bound)
  have error : |unpackedValue (UnpackedFloat.add Format.binary64 (decoded64 left) (decoded64
    right))-
      (numerical64 left+numerical64 right)| ≤ 1/137438953472 := by
    have radius : (2:ℚ)^(max ((16:Int)+1-Format.binary64.mantissaBits)
        Format.binary64.minExponent)/2 = 1/137438953472 := by norm_num [Format.mantissaBits,
          Format.minExponent]
    simpa only [numerical64, radius] using localProof.2
  have fits := model_local64_fits _ _ localProof.1 bound error
  have exactDecoded := model_add64_decoded left right leftFinite rightFinite localProof.1 fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [exactDecoded]
    exact model_normalized_finite _ _ localProof.1
  · simpa only [numerical64, exactDecoded] using error

/-- Actual binary64 multiplication stays finite and has error at most 2^-37 whenever its finite
operands have an exact dyadic product of magnitude at most 2^16. Native primitive correspondence
remains the declared trusted boundary. -/
theorem binary64_mul_finite_error (left right : Binary64) (leftFinite : left.Finite)
    (rightFinite : right.Finite)
    (bound : |numerical64 left * numerical64 right| ≤ 65536) :
    (left.mul right).Finite ∧
      |numerical64 (left.mul right) - (numerical64 left * numerical64 right)| ≤
        1 / 137438953472 := by
  have leftNormal := (model_unpack_format Format.binary64 (by decide) left.bits.toBitVec
    ((model_decoded64_finite left).mpr leftFinite)).1
  have rightNormal := (model_unpack_format Format.binary64 (by decide) right.bits.toBitVec
    ((model_decoded64_finite right).mpr rightFinite)).1
  have power : (2 : ℚ) ^ (16 : Int) = 65536 := by norm_num
  have localProof := model_mul_dyadic_local Format.binary64 (decoded64 left) (decoded64 right)
    leftNormal rightNormal 16 (by simpa only [numerical64, power] using bound)
  have error : |unpackedValue (UnpackedFloat.mul Format.binary64 (decoded64 left) (decoded64
    right))-
      (numerical64 left*numerical64 right)| ≤ 1/137438953472 := by
    have radius : (2:ℚ)^(max ((16:Int)+1-Format.binary64.mantissaBits)
        Format.binary64.minExponent)/2 = 1/137438953472 := by norm_num [Format.mantissaBits,
          Format.minExponent]
    simpa only [numerical64, radius] using localProof.2
  have fits := model_local64_fits _ _ localProof.1 bound error
  have exactDecoded := model_mul64_decoded left right leftFinite rightFinite localProof.1 fits
  constructor
  · apply (model_decoded64_finite _).mp
    rw [exactDecoded]
    exact model_normalized_finite _ _ localProof.1
  · simpa only [numerical64, exactDecoded] using error
end AcornVerif.CurrentArithmetic
