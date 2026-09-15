/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentReduction
import AcornVerif.CurrentSeries
/-!
# Public portable-function contracts

The executable classifier, reduction, ordered polynomial, scale and narrowing
compose directly. Every arithmetic hypothesis is supplied by the preceding
operation. These are machine-domain range and exception contracts, not ideal
transcendental accuracy claims. Standard primitive and native compiler/runtime
correspondence remain the explicit trusted boundary.
-/
open Acorn
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder AcornVerif.CurrentOperations AcornVerif.CurrentDivision
open AcornVerif.CurrentIntervals AcornVerif.CurrentExponential
open AcornVerif.CurrentReduction AcornVerif.CurrentSeries
namespace AcornVerif.CurrentPortable

/-- Numerical polynomial bounds imply the raw positive normal word interval used by exact scaling.
-/
theorem exp_polynomial_words (polynomial : Binary64) (finite : polynomial.Finite)
    (lower : 7 / 10 ≤ numerical64 polynomial)
    (upper : numerical64 polynomial ≤ 14199 / 10000) :
    0x3fe0000000000000 ≤ polynomial.bits.toNat ∧
      polynomial.bits.toNat ≤ 0x3ff8000000000000 ∧
      (numerical64 polynomial ≤ 1 → polynomial.bits.toNat ≤ 0x3ff0000000000000) := by
  let half : Binary64 := ⟨0x3fe0000000000000⟩
  let top : Binary64 := ⟨0x3ff8000000000000⟩
  let unit : Binary64 := ⟨0x3ff0000000000000⟩
  have halfFinite : half.Finite := by decide
  have topFinite : top.Finite := by decide
  have unitFinite : unit.Finite := by decide
  have halfValue : numerical64 half = 1 / 2 := by
    dsimp only [half]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-53:Int) = _
    norm_num
  have topValue : numerical64 top = 3 / 2 := by
    dsimp only [top]
    change (1:ℚ)*6755399441055744*(2:ℚ)^(-52:Int) = _
    norm_num
  have unitValue : numerical64 unit = 1 := by
    dsimp only [unit]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-52:Int) = _
    norm_num
  have halfKey : half.key = (0x3fe0000000000000:Int) := by dsimp only [half]; rfl
  have topKey : top.key = (0x3ff8000000000000:Int) := by dsimp only [top]; rfl
  have unitKey : unit.key = (0x3ff0000000000000:Int) := by dsimp only [unit]; rfl
  have low := (numerical64_order half polynomial halfFinite finite).mp
    (by rw [halfValue]; linarith only [lower])
  have high := (numerical64_order polynomial top finite topFinite).mp
    (by rw [topValue]; linarith only [upper])
  rw [halfKey] at low
  rw [topKey] at high
  have word := binary64_positive_key_word polynomial (by omega)
  rw [word.2] at low high
  refine ⟨by omega,by omega,?_⟩
  intro bounded
  have h := (numerical64_order polynomial unit finite unitFinite).mp
    (by rw [unitValue]; exact bounded)
  rw [word.2,unitKey] at h
  omega

/-- Every admitted exponential input supplies the full component chain, with a positive-sign
non-NaN result and a finite unit-bounded result on the nonpositive half-line. -/
theorem exp_admitted_contract (value : Binary32)
    (admitted : Portable.expSaturation value = none) :
    (Portable.exp value).bits.toNat ≤ 0x7f800000 ∧
      (numerical32 value ≤ 0 → (Portable.exp value).bits.toNat ≤ 0x3f800000) := by
  let reduced := Portable.expReduce (Conversion.widen value)
  have reduction := exp_admitted_reduction value admitted
  change value.Finite ∧ -151 ≤ reduced.1 ∧ reduced.1 ≤ 129 ∧ reduced.2.Finite ∧
    |numerical64 reduced.2| ≤ 349/1000 ∧ (numerical32 value ≤ 0 → reduced.1 ≤ 0)
    at reduction
  have series := expSeries_contract reduced.2 reduction.2.2.2.1
    (le_trans reduction.2.2.2.2.1 (by norm_num))
  have words := exp_polynomial_words (Portable.expSeries reduced.2)
    series.1 series.2.1 series.2.2.1
  have expression : Portable.exp value = Portable.expScale (Portable.expSeries reduced.2)
      reduced.1 := by simp only [Portable.exp_eq_spec,admitted]; rfl
  rw [expression]
  refine ⟨expScale_nonnegative _ _ words.1 words.2.1 reduction.2.1 reduction.2.2.1,?_⟩
  intro nonpositive
  have exponent := reduction.2.2.2.2.2 nonpositive
  by_cases negative : reduced.1 < 0
  · exact expScale_negative_unit _ _ words.1 words.2.1 reduction.2.1 negative
  · have zero : reduced.1 = 0 := by omega
    have remainder := expReduce_zero_remainder (Conversion.widen value)
      (Conversion.widen_finite value reduction.1) zero
    have remNonpositive : numerical64 reduced.2 ≤ 0 := by
      change numerical64 (Portable.expReduce (Conversion.widen value)).2 ≤ 0
      rw [remainder.2,numerical_widen_exact value reduction.1]
      exact nonpositive
    rw [zero]
    exact expScale_zero_unit _ words.1 (words.2.2 (series.2.2.2 remNonpositive))

/-- Every non-NaN input, including both infinities, produces a positive-sign finite or infinite
word. No NaN can result from the executing exponential. -/
theorem exp_nonNaN_word (value : Binary32) (notNaN : value.isNaN = false) :
    (Portable.exp value).bits.toNat ≤ 0x7f800000 := by
  cases saturation : Portable.expSaturation value with
  | none => exact (exp_admitted_contract value saturation).1
  | some result =>
    have ends := expSaturation_ends value
    rw [saturation] at ends
    simp only [notNaN,Bool.false_eq_true,↓reduceIte] at ends
    have expression : Portable.exp value = result := by simp only [Portable.exp_eq_spec, saturation]
    rw [expression]
    split at ends
    · rw [ends]; decide
    · rw [ends.2]; decide

/-- On every finite nonpositive input, the executing exponential lies in the positive-sign unit
interval. This includes both input zero signs and underflow to zero. -/
theorem exp_nonpositive_unit (value : Binary32) (finite : value.Finite)
    (nonpositive : numerical32 value ≤ 0) :
    (Portable.exp value).bits.toNat ≤ 0x3f800000 := by
  cases saturation : Portable.expSaturation value with
  | none => exact (exp_admitted_contract value saturation).2 nonpositive
  | some result =>
    have notNaN := Binary32.finite_not_nan value finite
    have ends := expSaturation_ends value
    rw [saturation] at ends
    simp only [notNaN,Bool.false_eq_true,↓reduceIte] at ends
    have expression : Portable.exp value = result := by simp only [Portable.exp_eq_spec, saturation]
    rw [expression]
    have upperFinite : (Binary32.mk AcornSpec.Constants.expOverflowBits).Finite := by decide
    have upperValue : numerical32 (Binary32.mk AcornSpec.Constants.expOverflowBits) = 89 := by
      change (1:ℚ)*11665408*(2:ℚ)^(-17:Int) = _
      norm_num
    have less : value.less ⟨AcornSpec.Constants.expOverflowBits⟩ = true := by
      rw [numerical32_less _ _ finite upperFinite,decide_eq_true_eq,upperValue]
      linarith only [nonpositive]
    simp only [less,Bool.not_true,Bool.false_eq_true,↓reduceIte] at ends
    rw [ends.2]
    decide

end AcornVerif.CurrentPortable
