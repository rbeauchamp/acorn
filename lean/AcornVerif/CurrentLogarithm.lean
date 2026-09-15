/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentReduction
import AcornVerif.CurrentSeries
/-!
# Executing logarithm totality

Raw mantissa construction fixes its exponent, independently of input history.
That interval supplies a positive denominator and a contracting polynomial
argument. A structural Horner envelope and local arithmetic bounds establish
finiteness before the final narrowing. Classification gives the exact exceptional
words. No ideal-logarithm error or native compiler/runtime correctness is inferred.
-/
open Acorn
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder AcornVerif.CurrentOperations AcornVerif.CurrentDivision
open AcornVerif.CurrentIntervals AcornVerif.CurrentReduction AcornVerif.CurrentSeries
namespace AcornVerif.CurrentLogarithm

/-- An absolute approximation error and an exact-value bound compose additively. -/
theorem approximation_magnitude (actual expected bound error : ℚ)
    (close : |actual - expected| ≤ error) (bounded : |expected| ≤ bound) :
    |actual| ≤ bound + error := by
  have triangle := abs_add_le (actual-expected) expected
  rw [sub_add_cancel] at triangle
  linarith only [triangle,close,bounded]

/-- The actual mantissa field construction is finite and belongs to [1,2] for every raw word. -/
theorem ln_mantissa_fields (bits : UInt64) :
    let mantissa : Binary64 :=
      ⟨(bits &&& (0xfffffffffffff : UInt64)) ||| ((1023 : UInt64) <<< 52)⟩
    mantissa.Finite ∧ 1 ≤ numerical64 mantissa ∧ numerical64 mantissa ≤ 2 := by
  let mantissa : Binary64 :=
    ⟨(bits &&& (0xfffffffffffff : UInt64)) ||| ((1023 : UInt64) <<< 52)⟩
  have fraction := Conversion.fraction64_bound bits
  have word := Conversion.wideFields_exact 1023 (bits &&& 0xfffffffffffff) (by decide) fraction
  rw [UInt64.or_comm] at word
  change mantissa.bits.toNat = 1023*2^52+(bits &&& (0xfffffffffffff:UInt64)).toNat at word
  have finite : mantissa.Finite := by
    change mantissa.bits.toNat &&& (2^63-1) < 0x7ff0000000000000
    exact Nat.lt_of_le_of_lt Nat.and_le_left (by omega)
  have key := binary64_key_nonnegative_word mantissa (by omega)
  let one : Binary64 := ⟨0x3ff0000000000000⟩
  let two : Binary64 := ⟨0x4000000000000000⟩
  have oneFinite : one.Finite := by decide
  have twoFinite : two.Finite := by decide
  have oneValue : numerical64 one = 1 := by
    dsimp only [one]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-52:Int) = _
    norm_num
  have twoValue : numerical64 two = 2 := by
    dsimp only [two]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-51:Int) = _
    norm_num
  have oneKey : one.key = (0x3ff0000000000000:Int) := by dsimp only [one]; rfl
  have twoKey : two.key = (0x4000000000000000:Int) := by dsimp only [two]; rfl
  have lower := (numerical64_order one mantissa oneFinite finite).mpr
    (by rw [oneKey,key]; omega)
  have upper := (numerical64_order mantissa two finite twoFinite).mpr
    (by rw [twoKey,key]; omega)
  exact ⟨finite,by simpa only [oneValue] using lower,by simpa only [twoValue] using upper⟩

/-- Every raw word supplies finite logarithm arithmetic after the classification stage. The
mantissa and exponent are constructed by the actual expression, with every rounding retained. -/
theorem ln_body_finite (bits : UInt64) :
    let exponent₀ := Conversion.ofInt ((((bits >>> 52) &&& 0x7ff).toNat : Int) - 1023)
    let mantissa₀ : Binary64 :=
      ⟨(bits &&& (0xfffffffffffff : UInt64)) ||| ((1023 : UInt64) <<< 52)⟩
    let centered := Portable.sqrt2.less mantissa₀
    let mantissa := if centered then mantissa₀.mul ⟨0x3fe0000000000000⟩ else mantissa₀
    let exponent := if centered then exponent₀.add (Binary64.ofUInt64 1) else exponent₀
    let ratio := (mantissa.sub (Binary64.ofUInt64 1)).div
      (mantissa.add (Binary64.ofUInt64 1))
    let ratioSq := ratio.mul ratio
    let polynomial := Binary64.hornerFrom ratioSq ⟨0⟩ Portable.lnCoefficients
    let lnMantissa := ((Binary64.ofUInt64 2).mul ratio).mul polynomial
    (Conversion.narrow ((exponent.mul Portable.ln2Hi).add
      ((exponent.mul Portable.ln2Lo).add lnMantissa))).Finite := by
  let one := Binary64.ofUInt64 1
  let two := Binary64.ofUInt64 2
  let half : Binary64 := ⟨0x3fe0000000000000⟩
  let integer := ((((bits >>> 52) &&& 0x7ff).toNat : Int)-1023)
  let exponent₀ := Conversion.ofInt integer
  let mantissa₀ : Binary64 :=
    ⟨(bits &&& (0xfffffffffffff : UInt64)) ||| ((1023 : UInt64) <<< 52)⟩
  let centered := Portable.sqrt2.less mantissa₀
  let mantissa := if centered then mantissa₀.mul half else mantissa₀
  let exponent := if centered then exponent₀.add one else exponent₀
  let numerator := mantissa.sub one
  let denominator := mantissa.add one
  let ratio := numerator.div denominator
  let ratioSq := ratio.mul ratio
  let polynomial := Binary64.hornerFrom ratioSq ⟨0⟩ Portable.lnCoefficients
  let twiceRatio := two.mul ratio
  let lnMantissa := twiceRatio.mul polynomial
  let high := exponent.mul Portable.ln2Hi
  let low := exponent.mul Portable.ln2Lo
  let tailValue := low.add lnMantissa
  let result := high.add tailValue
  have oneFinite : one.Finite := by decide
  have twoFinite : two.Finite := by decide
  have halfFinite : half.Finite := by decide
  have oneValue : numerical64 one = 1 := by
    exact numerical64_ofUInt64 1 (by decide)
  have twoValue : numerical64 two = 2 := by
    exact numerical64_ofUInt64 2 (by decide)
  have halfValue : numerical64 half = 1/2 := by
    dsimp only [half]
    change (1:ℚ)*4503599627370496*(2:ℚ)^(-53:Int) = _
    norm_num
  have fields : mantissa₀.Finite ∧ 1 ≤ numerical64 mantissa₀ ∧ numerical64 mantissa₀ ≤ 2 :=
    ln_mantissa_fields bits
  have mantissaProof : mantissa.Finite ∧ 49/100 ≤ numerical64 mantissa ∧
      numerical64 mantissa ≤ 201/100 := by
    dsimp only [mantissa]
    split
    · have product := binary64_mul_finite_error mantissa₀ half fields.1 halfFinite
        (by rw [halfValue,abs_le]; constructor <;> linarith only [fields.2.1,fields.2.2])
      rw [halfValue] at product
      have bounds := abs_le.mp product.2
      exact ⟨product.1,by linarith only [bounds.1,fields.2.1],
        by linarith only [bounds.2,fields.2.2]⟩
    · exact ⟨fields.1,by linarith only [fields.2.1],by linarith only [fields.2.2]⟩
  have fieldBound : (((bits >>> 52) &&& 0x7ff):UInt64).toNat ≤ 2047 := by
    change ((bits >>> 52).toNat &&& 2047) ≤ 2047
    exact Nat.and_le_right
  have integerLower : -1023 ≤ integer := by dsimp only [integer]; omega
  have integerUpper : integer ≤ 1024 := by dsimp only [integer]; omega
  have integerSmall : integer.natAbs < 2^53 := by omega
  have exponentFinite := ofInt_finite integer integerSmall
  have exponentValue := numerical64_ofInt integer integerSmall
  change numerical64 exponent₀ = (integer:ℚ) at exponentValue
  have initialBound : |numerical64 exponent₀| ≤ 1024 := by
    rw [exponentValue,abs_le]
    constructor
    · exact_mod_cast (show -1024 ≤ integer by omega)
    · exact_mod_cast integerUpper
  have exponentProof : exponent.Finite ∧ |numerical64 exponent| ≤ 1026 := by
    dsimp only [exponent]
    split
    · have exactBound : |numerical64 exponent₀+numerical64 one| ≤ 1025 := by
        rw [oneValue]
        have triangle := abs_add_le (numerical64 exponent₀) 1
        norm_num only [abs_one] at triangle
        linarith only [triangle,initialBound]
      have addition := binary64_add_finite_error exponent₀ one exponentFinite oneFinite
        (le_trans exactBound (by norm_num))
      exact ⟨addition.1,le_trans (approximation_magnitude _ _ _ _ addition.2 exactBound)
        (by norm_num)⟩
    · exact ⟨exponentFinite,le_trans initialBound (by norm_num)⟩
  have numeratorExact : |numerical64 mantissa-numerical64 one| ≤ 101/100 := by
    rw [oneValue,abs_le]
    constructor <;> linarith only [mantissaProof.2.1,mantissaProof.2.2]
  have numeratorProof := binary64_sub_finite_error mantissa one mantissaProof.1 oneFinite
    (le_trans numeratorExact (by norm_num))
  have numeratorBound : |numerical64 numerator| ≤ 102/100 :=
    le_trans (approximation_magnitude _ _ _ _ numeratorProof.2 numeratorExact) (by norm_num)
  have denominatorExact : |numerical64 mantissa+numerical64 one| ≤ 301/100 := by
    rw [oneValue,abs_le]
    constructor <;> linarith only [mantissaProof.2.1,mantissaProof.2.2]
  have denominatorProof := binary64_add_finite_error mantissa one mantissaProof.1 oneFinite
    (le_trans denominatorExact (by norm_num))
  have denominatorBounds : 148/100 ≤ numerical64 denominator ∧
      numerical64 denominator ≤ 302/100 := by
    have bounds := abs_le.mp denominatorProof.2
    rw [oneValue] at bounds
    constructor <;> linarith only [bounds.1,bounds.2,mantissaProof.2.1,mantissaProof.2.2]
  have denominatorPositive : 0 < numerical64 denominator := by
    linarith only [denominatorBounds.1]
  have ratioExact : |numerical64 numerator/numerical64 denominator| ≤ 51/74 := by
    rw [abs_div,abs_of_pos denominatorPositive]
    apply (div_le_iff₀ denominatorPositive).mpr
    linarith only [numeratorBound,denominatorBounds.1]
  have ratioProof := binary64_div_finite_error numerator denominator numeratorProof.1
    denominatorProof.1 (ne_of_gt denominatorPositive) (le_trans ratioExact (by norm_num))
  have ratioBound : |numerical64 ratio| ≤ 7/10 :=
    le_trans (approximation_magnitude _ _ _ _ ratioProof.2 ratioExact) (by norm_num)
  have squareExact : |numerical64 ratio*numerical64 ratio| ≤ 49/100 := by
    rw [abs_mul]
    exact le_trans (mul_le_mul ratioBound ratioBound (abs_nonneg _) (by norm_num)) (by norm_num)
  have squareProof := binary64_mul_finite_error ratio ratio ratioProof.1 ratioProof.1
    (le_trans squareExact (by norm_num))
  have squareBound : |numerical64 ratioSq| ≤ 1/2 :=
    le_trans (approximation_magnitude _ _ _ _ squareProof.2 squareExact) (by norm_num)
  have coefficientBounds : ∀ coefficient ∈ Portable.lnCoefficients,
      coefficient.Finite ∧ |numerical64 coefficient| ≤ 1+1/34359738368 := by
    intro coefficient member
    change coefficient ∈ ([15,13,11,9,7,5,3,1] : List UInt64).map
      (fun denominator => (Binary64.ofUInt64 1).div (Binary64.ofUInt64 denominator)) at member
    obtain ⟨denominator,denominatorMember,rfl⟩ := List.mem_map.mp member
    have small : 1 ≤ denominator.toNat ∧ denominator.toNat < 2^53 := by
      change denominator ∈ ([15,13,11,9,7,5,3,1] : List UInt64) at denominatorMember
      simp only [List.mem_cons,List.not_mem_nil,or_false] at denominatorMember
      rcases denominatorMember with h | h | h | h | h | h | h | h <;>
        subst denominator <;> decide
    simpa only [Nat.cast_one,div_one] using
      reciprocal_coefficient_bound denominator 1 (by decide) small.1 small.2
  have polynomialProof := hornerFrom_envelope ratioSq ⟨0⟩ Portable.lnCoefficients
    (1/2) 3 (1+1/34359738368) squareProof.1 (by decide) squareBound
    (by change |(0:ℚ)| ≤ 3; norm_num) coefficientBounds (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have twiceExact : |numerical64 two*numerical64 ratio| ≤ 14/10 := by
    rw [twoValue,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0:ℚ)<2)]
    linarith only [ratioBound]
  have twiceProof := binary64_mul_finite_error two ratio twoFinite ratioProof.1
    (le_trans twiceExact (by norm_num))
  have twiceBound : |numerical64 twiceRatio| ≤ 3/2 :=
    le_trans (approximation_magnitude _ _ _ _ twiceProof.2 twiceExact) (by norm_num)
  have lnExact : |numerical64 twiceRatio*numerical64 polynomial| ≤ 9/2 := by
    rw [abs_mul]
    exact le_trans (mul_le_mul twiceBound polynomialProof.2 (abs_nonneg _) (by norm_num))
      (by norm_num)
  have lnProof := binary64_mul_finite_error twiceRatio polynomial twiceProof.1 polynomialProof.1
    (le_trans lnExact (by norm_num))
  have lnBound : |numerical64 lnMantissa| ≤ 5 :=
    le_trans (approximation_magnitude _ _ _ _ lnProof.2 lnExact) (by norm_num)
  obtain ⟨_,hiFinite,loFinite,_,_,hiLo,hiHi,loLo,loHi,_⟩ := reduction_constants
  have highExact : |numerical64 exponent*numerical64 Portable.ln2Hi| ≤ 1026 := by
    rw [abs_mul,abs_of_nonneg hiLo]
    exact le_trans (mul_le_mul exponentProof.2 hiHi hiLo (by norm_num)) (by norm_num)
  have highProof := binary64_mul_finite_error exponent Portable.ln2Hi exponentProof.1 hiFinite
    (le_trans highExact (by norm_num))
  have highBound : |numerical64 high| ≤ 1027 :=
    le_trans (approximation_magnitude _ _ _ _ highProof.2 highExact) (by norm_num)
  have lowExact : |numerical64 exponent*numerical64 Portable.ln2Lo| ≤ 1026/1000000000 := by
    rw [abs_mul,abs_of_nonneg loLo]
    exact le_trans (mul_le_mul exponentProof.2 loHi loLo (by norm_num)) (by norm_num)
  have lowProof := binary64_mul_finite_error exponent Portable.ln2Lo exponentProof.1 loFinite
    (le_trans lowExact (by norm_num))
  have lowBound : |numerical64 low| ≤ 1 :=
    le_trans (approximation_magnitude _ _ _ _ lowProof.2 lowExact) (by norm_num)
  have tailExact : |numerical64 low+numerical64 lnMantissa| ≤ 6 :=
    le_trans (abs_add_le _ _) (by linarith only [lowBound,lnBound])
  have tailProof := binary64_add_finite_error low lnMantissa lowProof.1 lnProof.1
    (le_trans tailExact (by norm_num))
  have tailBound : |numerical64 tailValue| ≤ 7 :=
    le_trans (approximation_magnitude _ _ _ _ tailProof.2 tailExact) (by norm_num)
  have resultExact : |numerical64 high+numerical64 tailValue| ≤ 1034 :=
    le_trans (abs_add_le _ _) (by linarith only [highBound,tailBound])
  have resultProof := binary64_add_finite_error high tailValue highProof.1 tailProof.1
    (le_trans resultExact (by norm_num))
  have resultBound : |numerical64 result| ≤ 1035 :=
    le_trans (approximation_magnitude _ _ _ _ resultProof.2 resultExact) (by norm_num)
  exact narrow_finite_local result resultProof.1 (le_trans resultBound (by norm_num))

/-- The executing logarithm returns the prescribed exceptional words and a finite result on
every remaining input, including all positive finite subnormals. -/
theorem ln_total_contract (value : Binary32) :
    if value.isNaN || value.less .zero then Portable.ln value = ⟨0x7fc00000⟩
    else if value.magnitude == 0 then Portable.ln value = ⟨0xff800000⟩
    else if value.magnitude == 0x7f800000 then Portable.ln value = ⟨0x7f800000⟩
    else (Portable.ln value).Finite := by
  unfold Portable.ln
  simp only [Binary32.magnitudeEq_exact, UInt32.toNat_ofNat, Portable.lnSeries_eq,
    Conversion.ofI32Word_eq, Portable.logarithmExponent_exact]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · exact ln_body_finite (Conversion.widen value).bits

end AcornVerif.CurrentLogarithm
