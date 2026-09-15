/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentIntervals
import Mathlib.Algebra.Order.Field.Basic
/-!
# Ordered polynomial envelopes

Each Horner step and coefficient quotient uses the executing Acorn primitives.
An arbitrary-list induction preserves an admitted envelope under an analytic
one-step inequality. The exponential proof groups its existing coefficient
prefix and derives the final quadratic bounds structurally, preserving every
operation and rounding boundary. Machine spacing supplies the closed upper
endpoint at one. The resulting interval is inside the retained component
bounds; ideal exponential approximation error is a separate claim. Native
primitive/compiler correspondence remains the declared trusted boundary.
-/
open Acorn
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder AcornVerif.CurrentOperations AcornVerif.CurrentDivision
open AcornVerif.CurrentIntervals
namespace AcornVerif.CurrentSeries

/-- Every executing Horner step in the stated local domain stays finite and differs from its exact
multiply-plus-add value by at most 2^-36. -/
theorem hornerStep_finite_error (argument accumulator coefficient : Binary64)
    (argumentFinite : argument.Finite) (accumulatorFinite : accumulator.Finite)
    (coefficientFinite : coefficient.Finite)
    (argumentBound : |numerical64 argument| ≤ 1)
    (accumulatorBound : |numerical64 accumulator| ≤ 256)
    (coefficientBound : |numerical64 coefficient| ≤ 256) :
    (Binary64.hornerStep argument accumulator coefficient).Finite ∧
      |numerical64 (Binary64.hornerStep argument accumulator coefficient)-
        (numerical64 accumulator * numerical64 argument + numerical64 coefficient)| ≤
        2 / 137438953472 := by
  have productBound : |numerical64 accumulator*numerical64 argument| ≤ 256 := by
    rw [abs_mul]
    exact le_trans (mul_le_mul accumulatorBound argumentBound (abs_nonneg _) (by norm_num))
      (by norm_num)
  have productProof := binary64_mul_finite_error accumulator argument
    accumulatorFinite argumentFinite
    (le_trans productBound (by norm_num))
  have roundedBound : |numerical64 (accumulator.mul argument)| ≤ 257 := by
    have triangle := abs_add_le
      (numerical64 (accumulator.mul argument)-numerical64 accumulator*numerical64 argument)
      (numerical64 accumulator*numerical64 argument)
    rw [sub_add_cancel] at triangle
    linarith only [triangle,productBound,productProof.2]
  have sumBound : |numerical64 (accumulator.mul argument)+numerical64 coefficient| ≤ 65536 := by
    have triangle := abs_add_le (numerical64 (accumulator.mul argument)) (numerical64 coefficient)
    linarith only [triangle,roundedBound,coefficientBound]
  have addition := binary64_add_finite_error (accumulator.mul argument) coefficient
    productProof.1 coefficientFinite sumBound
  refine ⟨addition.1,?_⟩
  change |numerical64 ((accumulator.mul argument).add coefficient)-
    (numerical64 accumulator*numerical64 argument+numerical64 coefficient)| ≤ _
  have pm := abs_le.mp productProof.2
  have pa := abs_le.mp addition.2
  rw [abs_le]
  constructor <;> linarith only [pm.1,pm.2,pa.1,pa.2]

/-- An analytic one-step inequality preserves the numerical envelope through every finite ordered
coefficient list, using the actual rounded accumulator. -/
theorem hornerFrom_envelope (argument initial : Binary64) (coefficients : List Binary64)
    (radius bound coefficientBound : ℚ)
    (argumentFinite : argument.Finite) (initialFinite : initial.Finite)
    (argumentBound : |numerical64 argument| ≤ radius)
    (initialBound : |numerical64 initial| ≤ bound)
    (coefficientBounds : ∀ coefficient ∈ coefficients,
      coefficient.Finite ∧ |numerical64 coefficient| ≤ coefficientBound)
    (radiusSmall : radius ≤ 1) (boundSmall : bound ≤ 256)
    (coefficientSmall : coefficientBound ≤ 256)
    (stable : radius * bound + coefficientBound + 2 / 137438953472 ≤ bound) :
    (Binary64.hornerFrom argument initial coefficients).Finite ∧
      |numerical64 (Binary64.hornerFrom argument initial coefficients)| ≤ bound := by
  have boundNonnegative : 0 ≤ bound := le_trans (abs_nonneg _) initialBound
  induction coefficients generalizing initial with
  | nil => exact ⟨initialFinite,initialBound⟩
  | cons coefficient rest ih =>
    have coefficientProof := coefficientBounds coefficient (by simp)
    have step := hornerStep_finite_error argument initial coefficient argumentFinite initialFinite
      coefficientProof.1 (le_trans argumentBound radiusSmall) (le_trans initialBound boundSmall)
      (le_trans coefficientProof.2 coefficientSmall)
    have productBound : |numerical64 initial*numerical64 argument| ≤ bound*radius := by
      rw [abs_mul]
      exact mul_le_mul initialBound argumentBound (abs_nonneg _) boundNonnegative
    have exactBound : |numerical64 initial*numerical64 argument+numerical64 coefficient| ≤
        bound*radius+coefficientBound :=
      le_trans (abs_add_le _ _) (add_le_add productBound coefficientProof.2)
    have nextBound : |numerical64 (Binary64.hornerStep argument initial coefficient)| ≤ bound := by
      have triangle := abs_add_le
        (numerical64 (Binary64.hornerStep argument initial coefficient)-
          (numerical64 initial*numerical64 argument+numerical64 coefficient))
        (numerical64 initial*numerical64 argument+numerical64 coefficient)
      rw [sub_add_cancel] at triangle
      nlinarith only [triangle,step.2,exactBound,stable]
    exact ih (Binary64.hornerStep argument initial coefficient) step.1 nextBound
      (fun c hc => coefficientBounds c (List.mem_cons_of_mem coefficient hc))

/-- Every positive admitted unsigned denominator yields a finite executing reciprocal bounded by
its exact reciprocal and the derived division error. -/
theorem reciprocal_coefficient_bound (denominator : UInt64) (minimum : Nat)
    (positive : 0 < minimum) (lower : minimum ≤ denominator.toNat)
    (small : denominator.toNat < 2 ^ 53) :
    let coefficient := (Binary64.ofUInt64 1).div (Binary64.ofUInt64 denominator)
    coefficient.Finite ∧ |numerical64 coefficient| ≤ 1/(minimum:ℚ)+1/34359738368 := by
  have denominatorPositive : (0:ℚ) < denominator.toNat := by
    exact_mod_cast Nat.lt_of_lt_of_le positive lower
  have minimumPositive : (0:ℚ) < minimum := by exact_mod_cast positive
  have minimumAtLeastOne : (1:ℚ) ≤ minimum := by exact_mod_cast positive
  have oneFinite : (Binary64.ofUInt64 1).Finite := by decide
  have wordBound := ofUInt64_word_bound denominator small
  have denominatorFinite : (Binary64.ofUInt64 denominator).Finite := by
    change (Binary64.ofUInt64 denominator).bits.toNat &&& (2^63-1) < 0x7ff0000000000000
    exact Nat.lt_of_le_of_lt Nat.and_le_left wordBound
  have oneValue : numerical64 (Binary64.ofUInt64 1)=1 := by
    have h := numerical64_ofUInt64 1 (by decide)
    exact h
  have denominatorValue := numerical64_ofUInt64 denominator small
  have quotientPositive : (0:ℚ) < 1/(denominator.toNat:ℚ) := one_div_pos.mpr denominatorPositive
  have minimumBound : (1:ℚ)/(minimum:ℚ) ≤ 1 := by
    apply (div_le_iff₀ minimumPositive).mpr
    simpa only [one_mul] using minimumAtLeastOne
  have quotientBound : (1:ℚ)/(denominator.toNat:ℚ) ≤ 1/(minimum:ℚ) :=
    one_div_le_one_div_of_le minimumPositive (by exact_mod_cast lower)
  have operation := binary64_div_finite_error (Binary64.ofUInt64 1) (Binary64.ofUInt64 denominator)
    oneFinite denominatorFinite (by rw [denominatorValue]; exact ne_of_gt denominatorPositive)
    (by rw [oneValue,denominatorValue,abs_of_pos quotientPositive]
        exact le_trans (le_trans quotientBound minimumBound) (by norm_num))
  rw [oneValue,denominatorValue] at operation
  refine ⟨operation.1,?_⟩
  have triangle := abs_add_le
    (numerical64 ((Binary64.ofUInt64 1).div (Binary64.ofUInt64 denominator))-
      1/(denominator.toNat:ℚ)) (1/(denominator.toNat:ℚ))
  rw [sub_add_cancel,abs_of_pos quotientPositive] at triangle
  linarith only [triangle,operation.2,quotientBound]

/-- The actual exponential polynomial is finite and lies in [0.7,1.4199] for every finite
remainder in [-0.35,0.35], and is at most one when that remainder is nonpositive. -/
theorem expSeries_contract (remainder : Binary64) (finite : remainder.Finite)
    (bounded : |numerical64 remainder| ≤ 7 / 20) :
    (Portable.expSeries remainder).Finite ∧
      7 / 10 ≤ numerical64 (Portable.expSeries remainder) ∧
      numerical64 (Portable.expSeries remainder) ≤ 14199 / 10000 ∧
      (numerical64 remainder ≤ 0 → numerical64 (Portable.expSeries remainder) ≤ 1) := by
  let r := numerical64 remainder
  let denominators : List UInt64 := [3628800,362880,40320,5040,720,120,24]
  let smallCoefficients := denominators.map
    (fun denominator => (Binary64.ofUInt64 1).div (Binary64.ofUInt64 denominator))
  let prefixValue := Binary64.hornerFrom remainder ⟨0⟩ smallCoefficients
  let sixth := (Binary64.ofUInt64 1).div (Binary64.ofUInt64 6)
  let half : Binary64 := ⟨0x3fe0000000000000⟩
  let one : Binary64 := ⟨0x3ff0000000000000⟩
  let first := Binary64.hornerStep remainder prefixValue sixth
  let middle := Binary64.hornerStep remainder first half
  let linear := Binary64.hornerStep remainder middle one
  let final := Binary64.hornerStep remainder linear one
  have rSmall : |numerical64 remainder| ≤ 1 := le_trans bounded (by norm_num)
  have rLow := (abs_le.mp bounded).1
  have rHigh := (abs_le.mp bounded).2
  have denominatorBounds : ∀ denominator ∈ denominators,
      24 ≤ denominator.toNat ∧ denominator.toNat < 2^53 := by
    intro denominator membership
    simp only [denominators,List.mem_cons,List.not_mem_nil,or_false] at membership
    rcases membership with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have coefficientBounds : ∀ coefficient ∈ smallCoefficients,
      coefficient.Finite ∧ |numerical64 coefficient| ≤ 1/24+1/34359738368 := by
    intro coefficient membership
    dsimp only [smallCoefficients] at membership
    rcases List.mem_map.mp membership with ⟨denominator,member,rfl⟩
    have bounds := denominatorBounds denominator member
    exact reciprocal_coefficient_bound denominator 24 (by decide) bounds.1 bounds.2
  have prefixProof := hornerFrom_envelope remainder ⟨0⟩ smallCoefficients (7/20) (13/200)
    (1/24+1/34359738368) finite (by decide) bounded
    (by change |(0:ℚ)|≤13/200; norm_num) coefficientBounds
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change prefixValue.Finite ∧ |numerical64 prefixValue|≤13/200 at prefixProof
  have sixthProof := reciprocal_coefficient_bound 6 6 (by decide) (by decide) (by decide)
  change sixth.Finite ∧ |numerical64 sixth|≤1/6+1/34359738368 at sixthProof
  have firstProof := hornerStep_finite_error remainder prefixValue sixth finite prefixProof.1
    sixthProof.1 rSmall (le_trans prefixProof.2 (by norm_num))
    (le_trans sixthProof.2 (by norm_num))
  change first.Finite ∧ |numerical64 first-(numerical64 prefixValue*r+numerical64 sixth)|≤
    2/137438953472 at firstProof
  have firstBound : |numerical64 first|≤19/100 := by
    have product : |numerical64 prefixValue*r|≤(13/200)*(7/20) := by
      rw [abs_mul]
      exact mul_le_mul prefixProof.2 bounded (abs_nonneg _) (by norm_num)
    have exactSum := abs_add_le (numerical64 prefixValue*r) (numerical64 sixth)
    have triangle := abs_add_le (numerical64 first-(numerical64 prefixValue*r+numerical64 sixth))
      (numerical64 prefixValue*r+numerical64 sixth)
    rw [sub_add_cancel] at triangle
    linarith only [triangle,firstProof.2,exactSum,product,sixthProof.2]
  have halfFinite : half.Finite := by decide
  have oneFinite : one.Finite := by decide
  have halfValue : numerical64 half=1/2 := by
    dsimp only [half]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-53:Int)=1/2
    norm_num
  have oneValue : numerical64 one=1 := by
    dsimp only [one]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-52:Int)=1
    norm_num
  have middleProof := hornerStep_finite_error remainder first half finite firstProof.1 halfFinite
    rSmall (le_trans firstBound (by norm_num)) (by rw [halfValue]; norm_num)
  rw [halfValue] at middleProof
  change middle.Finite ∧ |numerical64 middle-(numerical64 first*r+1/2)|≤
    2/137438953472 at middleProof
  have middleBounds : 433/1000≤numerical64 middle ∧ numerical64 middle≤567/1000 := by
    have product : |numerical64 first*r|≤(19/100)*(7/20) := by
      rw [abs_mul]
      exact mul_le_mul firstBound bounded (abs_nonneg _) (by norm_num)
    have productSides := abs_le.mp product
    have roundingSides := abs_le.mp middleProof.2
    constructor <;> linarith only [productSides.1,productSides.2,roundingSides.1,roundingSides.2]
  have middleBound : |numerical64 middle|≤567/1000 := by
    rw [abs_le]
    constructor <;> linarith only [middleBounds.1,middleBounds.2]
  have linearProof := hornerStep_finite_error remainder middle one finite middleProof.1 oneFinite
    rSmall (le_trans middleBound (by norm_num)) (by rw [oneValue]; norm_num)
  rw [oneValue] at linearProof
  change linear.Finite ∧ |numerical64 linear-(numerical64 middle*r+1)|≤2/137438953472 at linearProof
  have linearBounds : 4/5≤numerical64 linear ∧ numerical64 linear≤6/5 := by
    have product : |numerical64 middle*r|≤(567/1000)*(7/20) := by
      rw [abs_mul]
      exact mul_le_mul middleBound bounded (abs_nonneg _) (by norm_num)
    have productSides := abs_le.mp product
    have roundingSides := abs_le.mp linearProof.2
    constructor <;> linarith only [productSides.1,productSides.2,roundingSides.1,roundingSides.2]
  have linearBound : |numerical64 linear|≤6/5 := by
    rw [abs_le]
    constructor <;> linarith only [linearBounds.1,linearBounds.2]
  have finalProof := hornerStep_finite_error remainder linear one finite linearProof.1 oneFinite
    rSmall (le_trans linearBound (by norm_num)) (by rw [oneValue]; norm_num)
  rw [oneValue] at finalProof
  change final.Finite ∧ |numerical64 final-(numerical64 linear*r+1)|≤2/137438953472 at finalProof
  have expression : Portable.expSeries remainder=final := by
    have coefficients : Portable.expCoefficients=smallCoefficients++[sixth,half,one,one] := rfl
    rw [Portable.expSeries_eq,coefficients,Binary64.hornerFrom_append]
    rfl
  have polynomialError : |numerical64 final-(1+r+r^2*numerical64 middle)|≤3/137438953472 := by
    have multiplied : |(numerical64 linear-(numerical64 middle*r+1))*r|≤
        (2/137438953472)*(7/20) := by
      rw [abs_mul]
      exact mul_le_mul linearProof.2 bounded (abs_nonneg _) (by norm_num)
    have triangle := abs_add_le (numerical64 final-(numerical64 linear*r+1))
      ((numerical64 linear-(numerical64 middle*r+1))*r)
    have identity : (numerical64 final-(numerical64 linear*r+1))+
        (numerical64 linear-(numerical64 middle*r+1))*r =
        numerical64 final-(1+r+r^2*numerical64 middle) := by ring
    rw [identity] at triangle
    linarith only [triangle,finalProof.2,multiplied]
  have polynomialSides := abs_le.mp polynomialError
  have lowSquare := mul_le_mul_of_nonneg_left middleBounds.1 (sq_nonneg r)
  have highSquare := mul_le_mul_of_nonneg_left middleBounds.2 (sq_nonneg r)
  have lowComparison : 0≤(r+7/20)*(1+(433/1000)*(r-7/20)) :=
    mul_nonneg (by linarith only [rLow]) (by linarith only [rLow])
  have highComparison : 0≤(7/20-r)*(1+(567/1000)*(r+7/20)) :=
    mul_nonneg (by linarith only [rHigh]) (by linarith only [rLow])
  have finalLower : 7/10≤numerical64 final := by
    nlinarith only [polynomialSides.1,lowSquare,lowComparison]
  have finalUpper : numerical64 final≤14199/10000 := by
    nlinarith only [polynomialSides.2,highSquare,highComparison]
  have finalUnit : r≤0 → numerical64 final≤1 := by
    intro nonpositive
    have productBound : |numerical64 linear*r|≤(6/5)*(7/20) := by
      rw [abs_mul]
      exact mul_le_mul linearBound bounded (abs_nonneg _) (by norm_num)
    have direction : numerical64 linear*r≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith only [linearBounds.1]) nonpositive
    have signedProduct := binary64_mul_nonpositive linear remainder linearProof.1 finite
      (le_trans productBound (by norm_num)) direction
    have productProof := binary64_mul_finite_error linear remainder linearProof.1 finite
      (le_trans productBound (by norm_num))
    have productMagnitude : |numerical64 (linear.mul remainder)|≤1 := by
      have triangle := abs_add_le (numerical64 (linear.mul remainder)-numerical64 linear*r)
        (numerical64 linear*r)
      rw [sub_add_cancel] at triangle
      linarith only [triangle,productProof.2,productBound]
    have sumBound : |numerical64 (linear.mul remainder)+numerical64 one|≤1 := by
      rw [oneValue,abs_le]
      have bounds := abs_le.mp productMagnitude
      constructor <;> linarith only [bounds.1,bounds.2,signedProduct.2]
    exact (binary64_add_unit_upper (linear.mul remainder) one signedProduct.1 oneFinite sumBound).2
  rw [expression]
  exact ⟨finalProof.1,finalLower,finalUpper,finalUnit⟩

end AcornVerif.CurrentSeries
