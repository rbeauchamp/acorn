/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentIntervals
import AcornVerif.CurrentExponential
/-!
# Executing exponential argument reduction

The actual primitive operations, exact widening, finite truncation and
source-generated constants bound the chosen exponent and the ordered two-part
remainder. The polynomial input interval and nonpositive exponent conclusion
hold for every admitted machine input. At exponent zero the remainder retains
the input numerical value, including either zero sign. These are contracts for
the approximation recipe, with the declared native primitive/compiler trust;
they make no claim about ideal exponential accuracy.
-/
open Acorn
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder AcornVerif.CurrentOperations AcornVerif.CurrentDivision
open AcornVerif.CurrentIntervals
namespace AcornVerif.CurrentReduction

/-- The exact generated dyadic constant values satisfy the bounds used by reduction and its two-
part residual identity. -/
theorem reduction_constants :
    Portable.log2e.Finite ∧ Portable.ln2Hi.Finite ∧ Portable.ln2Lo.Finite ∧
    1 < numerical64 Portable.log2e ∧ numerical64 Portable.log2e < 29 / 20 ∧
    0 ≤ numerical64 Portable.ln2Hi ∧ numerical64 Portable.ln2Hi ≤ 1 ∧
    0 ≤ numerical64 Portable.ln2Lo ∧ numerical64 Portable.ln2Lo ≤ 1 / 1000000000 ∧
    0 ≤ numerical64 Portable.ln2Hi + numerical64 Portable.ln2Lo ∧
    numerical64 Portable.ln2Hi + numerical64 Portable.ln2Lo ≤ 347 / 500 ∧
    |1 - numerical64 Portable.log2e * (numerical64 Portable.ln2Hi + numerical64 Portable.ln2Lo)| ≤
      1 / 1000000000000 := by
  have logValue : numerical64 Portable.log2e=3248660424278399/2251799813685248 := by
    change (1:ℚ)*6497320848556798*(2:ℚ)^(-52:Int)=_
    norm_num
  have highValue : numerical64 Portable.ln2Hi=2977044471/4294967296 := by
    change (1:ℚ)*6243314766446592*(2:ℚ)^(-53:Int)=_
    norm_num
  have lowValue : numerical64 Portable.ln2Lo=7382048951581815/38685626227668133590597632 := by
    change (1:ℚ)*7382048951581815*(2:ℚ)^(-85:Int)=_
    norm_num
  refine ⟨by decide,by decide,by decide,?_⟩
  rw [logValue,highValue,lowValue]
  norm_num

/-- A half-away offset followed by toward-zero truncation stays within one half plus the stated
selection error of its input. -/
theorem trunc_selection_band (product selected : ℚ) (integer : Int) (error : ℚ)
    (errorSmall : error < 1 / 2)
    (near : |selected - (product + (if product < 0 then -(1 / 2 : ℚ) else 1 / 2))| ≤ error)
    (trunc : if selected < 0 then (integer : ℚ) - 1 < selected ∧ selected ≤ integer
      else (integer : ℚ) ≤ selected ∧ selected < (integer : ℚ) + 1) :
    |product - (integer : ℚ)| ≤ 1 / 2 + error := by
  by_cases negative : product<0
  · simp only [negative, ↓reduceIte] at near
    have hn := abs_le.mp near
    have sign : selected<0 := by linarith [hn.2]
    simp only [sign, ↓reduceIte] at trunc
    rw [abs_le]
    constructor <;> linarith [trunc.1,trunc.2,hn.1,hn.2]
  · simp only [negative, ↓reduceIte] at near
    have hn := abs_le.mp near
    have sign : ¬ selected<0 := by linarith [hn.1]
    simp only [sign, ↓reduceIte] at trunc
    rw [abs_le]
    constructor <;> linarith [trunc.1,trunc.2,hn.1,hn.2]

/-- Every finite wide input in the containing interval [-104,89] produces an exponent in
[-151,129] and a finite remainder in [-0.349,0.349]; nonpositive inputs give nonpositive exponents.
-/
theorem expReduce_contract (wide : Binary64) (finite : wide.Finite)
    (lower : -104 ≤ numerical64 wide) (upper : numerical64 wide ≤ 89) :
    let reduced := Portable.expReduce wide;
    -151 ≤ reduced.1 ∧ reduced.1 ≤ 129 ∧ reduced.2.Finite ∧
      |numerical64 reduced.2| ≤ 349/1000 ∧
      (numerical64 wide ≤ 0 → reduced.1 ≤ 0) := by
  simp only [Portable.expReduce, Portable.expReduceWord, Portable.expExponent,
    Portable.expRemainder, Conversion.ofI32Word_eq]
  let x := numerical64 wide
  let log := numerical64 Portable.log2e
  let hi := numerical64 Portable.ln2Hi
  let lo := numerical64 Portable.ln2Lo
  let half : Binary64 := if wide.less ⟨0⟩ then ⟨0xbfe0000000000000⟩ else ⟨0x3fe0000000000000⟩
  let product := wide.mul Portable.log2e
  let selected := product.add half
  let exponent := Conversion.toI32 selected
  let scaled := Conversion.ofInt exponent
  let highProduct := scaled.mul Portable.ln2Hi
  let intermediate := wide.sub highProduct
  let lowProduct := scaled.mul Portable.ln2Lo
  let remainder := intermediate.sub lowProduct
  have constants := reduction_constants
  obtain ⟨logFinite,hiFinite,loFinite,logLo,logHi,hiLo,hiHi,loLo,loHi,
    sumLo,sumHi,drift⟩ := constants
  change 1<log at logLo
  change log<29/20 at logHi
  change 0≤hi at hiLo
  change hi≤1 at hiHi
  change 0≤lo at loLo
  change lo≤1/1000000000 at loHi
  change 0≤hi+lo at sumLo
  change hi+lo≤347/500 at sumHi
  change |1-log*(hi+lo)|≤1/1000000000000 at drift
  have xBound : |x|≤104 := by rw [abs_le]; exact ⟨lower,by linarith only [upper]⟩
  have productRange : -151≤x*log ∧ x*log≤130 := by
    have low := mul_nonneg (by linarith only [lower] : 0≤x+104) (by linarith only [logLo] : 0≤log)
    have high := mul_nonneg (by linarith only [upper] : 0≤89-x) (by linarith only [logLo] : 0≤log)
    constructor <;> nlinarith only [low,high,logHi]
  have productProof := binary64_mul_finite_error wide Portable.log2e finite logFinite
    (by
      change |x*log|≤65536
      rw [abs_le]
      constructor <;> linarith only [productRange.1,productRange.2])
  change product.Finite ∧ |numerical64 product-x*log|≤1/137438953472 at productProof
  have halfValue : numerical64 half = if x<0 then -(1/2:ℚ) else 1/2 := by
    have compare := numerical64_less wide (Binary64.mk 0) finite (by decide)
    have zeroValue : numerical64 (Binary64.mk 0)=0 := by decide
    rw [zeroValue] at compare
    dsimp only [half]
    rw [compare]
    by_cases sign : x<0
    · simp only [show numerical64 wide<0 from sign, decide_true, ↓reduceIte, sign]
      change (-1:ℚ)*4503599627370496*(2:ℚ)^(-53:Int)=-(1/2:ℚ)
      norm_num
    · simp only [show ¬numerical64 wide<0 from sign, decide_false,
        Bool.false_eq_true, ↓reduceIte, sign]
      change (1:ℚ)*4503599627370496*(2:ℚ)^(-53:Int)=1/2
      norm_num
  have halfFinite : half.Finite := by dsimp only [half]; split <;> decide
  have halfBound : -(1/2:ℚ)≤numerical64 half ∧ numerical64 half≤1/2 := by
    rw [halfValue]
    split <;> norm_num
  have prodLow := (abs_le.mp productProof.2).1
  have prodHigh := (abs_le.mp productProof.2).2
  have selectedProof := binary64_add_finite_error product half productProof.1 halfFinite (by
    rw [abs_le]
    constructor <;> linarith only
      [productRange.1,productRange.2,halfBound.1,halfBound.2,prodLow,prodHigh])
  change selected.Finite ∧ |numerical64 selected-(numerical64 product+numerical64 half)|≤
    1/137438953472 at selectedProof
  have selectedLow := (abs_le.mp selectedProof.2).1
  have selectedHigh := (abs_le.mp selectedProof.2).2
  have selectedBound : |numerical64 selected|≤65536 := by
    rw [abs_le]
    constructor <;> linarith only [productRange.1,productRange.2,halfBound.1,halfBound.2,
      prodLow,prodHigh,selectedLow,selectedHigh]
  have cast := numerical64_toI32_trunc selected selectedProof.1 selectedBound
  have trunc := numerical64_trunc_toward_zero selected selectedProof.1
  rw [← cast] at trunc
  change (if numerical64 selected<0 then (exponent:ℚ)-1<numerical64 selected ∧
    numerical64 selected≤exponent else (exponent:ℚ)≤numerical64 selected ∧
    numerical64 selected<(exponent:ℚ)+1) at trunc
  have signLink : x*log<0 ↔ x<0 := by
    simpa only [zero_mul] using
      (mul_lt_mul_iff_left₀ (b:=x) (c:=0) (by linarith only [logLo] : 0<log))
  have combined : |numerical64 selected-(x*log+(if x*log<0 then -(1/2:ℚ) else 1/2))|≤
      2/137438953472 := by
    simp only [signLink]
    rw [← halfValue, abs_le]
    constructor <;> linarith only [prodLow,prodHigh,selectedLow,selectedHigh]
  have nearest := trunc_selection_band (x*log) (numerical64 selected) exponent
    (2/137438953472) (by norm_num) combined trunc
  have bandLo := (abs_le.mp nearest).1
  have bandHi := (abs_le.mp nearest).2
  have exponentLo : -151≤exponent := by
    have h : (-152:ℚ)<(exponent:ℚ) := by linarith only [productRange.1,bandHi]
    have hn : (-152:Int)<exponent := by exact_mod_cast h
    omega
  have exponentHi : exponent≤129 := by
    have sharper : x*log≤2581/20 := by
      have high := mul_nonneg (by linarith only [upper] : 0≤89-x) (by linarith only [logLo] : 0≤log)
      nlinarith only [high,logHi]
    have h : (exponent:ℚ)<130 := by linarith only [sharper,bandLo]
    have hn : exponent<(130:Int) := by exact_mod_cast h
    omega
  have exponentSize : exponent.natAbs<2^53 := by omega
  have scaledFinite := ofInt_finite exponent exponentSize
  have scaledValue := numerical64_ofInt exponent exponentSize
  change scaled.Finite at scaledFinite
  change numerical64 scaled=exponent at scaledValue
  have kBound : |(exponent:ℚ)|≤151 := by
    rw [abs_le]
    constructor
    · exact_mod_cast exponentLo
    · have : (exponent:ℚ)≤129 := by exact_mod_cast exponentHi
      linarith only [this]
  have highMagnitude : |numerical64 scaled*hi|≤151 := by
    rw [scaledValue,abs_mul,abs_of_nonneg hiLo]
    calc
      _ ≤ 151*1 := mul_le_mul kBound hiHi hiLo (by norm_num)
      _ = _ := by norm_num
  have highProof := binary64_mul_finite_error scaled Portable.ln2Hi scaledFinite hiFinite
    (by exact le_trans highMagnitude (by norm_num))
  rw [scaledValue] at highProof
  change highProduct.Finite ∧ |numerical64 highProduct-(exponent:ℚ)*hi|≤1/137438953472 at highProof
  have highLow := (abs_le.mp highProof.2).1
  have highHigh := (abs_le.mp highProof.2).2
  have highBound : |numerical64 highProduct|≤152 := by
    have ht := abs_add_le (numerical64 highProduct-(exponent:ℚ)*hi) ((exponent:ℚ)*hi)
    rw [sub_add_cancel] at ht
    rw [scaledValue] at highMagnitude
    linarith only [ht,highProof.2,highMagnitude]
  have partialProof := binary64_sub_finite_error wide highProduct finite highProof.1 (by
    have ht : |x-numerical64 highProduct|≤|x|+|numerical64 highProduct| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le x (-numerical64 highProduct)
    change |x-numerical64 highProduct|≤65536
    linarith only [ht,xBound,highBound])
  change intermediate.Finite ∧ |numerical64 intermediate-(x-numerical64 highProduct)|≤
    1/137438953472 at partialProof
  have partialLow := (abs_le.mp partialProof.2).1
  have partialHigh := (abs_le.mp partialProof.2).2
  have partialBound : |numerical64 intermediate|≤257 := by
    have p := (abs_le.mp xBound)
    have q := (abs_le.mp highBound)
    rw [abs_le]
    constructor <;> linarith only [p.1,p.2,q.1,q.2,partialLow,partialHigh]
  have lowMagnitude : |numerical64 scaled*lo|≤1 := by
    rw [scaledValue,abs_mul,abs_of_nonneg loLo]
    calc
      _ ≤ 151*(1/1000000000) := mul_le_mul kBound loHi loLo (by norm_num)
      _ ≤ _ := by norm_num
  have lowProof := binary64_mul_finite_error scaled Portable.ln2Lo scaledFinite loFinite
    (by exact le_trans lowMagnitude (by norm_num))
  rw [scaledValue] at lowProof
  change lowProduct.Finite ∧ |numerical64 lowProduct-(exponent:ℚ)*lo|≤1/137438953472 at lowProof
  have lowLow := (abs_le.mp lowProof.2).1
  have lowHigh := (abs_le.mp lowProof.2).2
  have lowBound : |numerical64 lowProduct|≤2 := by
    have ht := abs_add_le (numerical64 lowProduct-(exponent:ℚ)*lo) ((exponent:ℚ)*lo)
    rw [sub_add_cancel] at ht
    rw [scaledValue] at lowMagnitude
    linarith only [ht,lowProof.2,lowMagnitude]
  have remainderProof := binary64_sub_finite_error intermediate lowProduct
    partialProof.1 lowProof.1 (by
    have ht : |numerical64 intermediate-numerical64 lowProduct|≤
        |numerical64 intermediate|+|numerical64 lowProduct| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (numerical64 intermediate) (-numerical64 lowProduct)
    linarith only [ht,partialBound,lowBound])
  change remainder.Finite ∧
    |numerical64 remainder-(numerical64 intermediate-numerical64 lowProduct)|≤
    1/137438953472 at remainderProof
  have remainderLow := (abs_le.mp remainderProof.2).1
  have remainderHigh := (abs_le.mp remainderProof.2).2
  have arithmetic : |numerical64 remainder-(x-(exponent:ℚ)*(hi+lo))|≤4/137438953472 := by
    rw [abs_le]
    constructor <;> linarith only [highLow,highHigh,partialLow,partialHigh,
      lowLow,lowHigh,remainderLow,remainderHigh]
  have identity : x-(exponent:ℚ)*(hi+lo) = (x*log-(exponent:ℚ))*(hi+lo)+x*(1-log*(hi+lo)) := by ring
  have remainderBound : |numerical64 remainder|≤349/1000 := by
    have ht := abs_add_le (numerical64 remainder-(x-(exponent:ℚ)*(hi+lo)))
      (x-(exponent:ℚ)*(hi+lo))
    rw [sub_add_cancel] at ht
    have hsum := abs_add_le ((x*log-(exponent:ℚ))*(hi+lo)) (x*(1-log*(hi+lo)))
    rw [← identity] at hsum
    have small : |x*(1-log*(hi+lo))|≤104/1000000000000 := by
      rw [abs_mul]
      exact le_trans (mul_le_mul xBound drift (abs_nonneg _) (by norm_num)) (by norm_num)
    have main : |(x*log-(exponent:ℚ))*(hi+lo)|≤(1/2+2/137438953472)*(347/500) := by
      rw [abs_mul,abs_of_nonneg sumLo]
      exact mul_le_mul nearest sumHi sumLo (by norm_num)
    linarith only [ht,hsum,small,main,arithmetic]
  have nonpositive : x≤0 → exponent≤0 := by
    intro hx
    have prod : x*log≤0 := mul_nonpos_of_nonpos_of_nonneg hx (by linarith only [logLo])
    have h : (exponent:ℚ)<1 := by linarith only [prod,bandLo]
    have hn : exponent<(1:Int) := by exact_mod_cast h
    omega
  change -151≤exponent ∧ exponent≤129 ∧ remainder.Finite ∧ |numerical64 remainder|≤349/1000 ∧
    (numerical64 wide≤0 → exponent≤0)
  exact ⟨exponentLo,exponentHi,remainderProof.1,remainderBound,nonpositive⟩

/-- If actual reduction selects exponent zero, its two subtractions preserve the finite input
numerical value. -/
theorem expReduce_zero_remainder (wide : Binary64) (finite : wide.Finite)
    (zero : (Portable.expReduce wide).1 = 0) :
    (Portable.expReduce wide).2.Finite ∧
      numerical64 (Portable.expReduce wide).2 = numerical64 wide := by
  simp only [Portable.expReduce, Portable.expReduceWord, Portable.expExponent,
    Portable.expRemainder, Conversion.ofI32Word_eq] at zero ⊢
  let half : Binary64 := if wide.less ⟨0⟩ then ⟨0xbfe0000000000000⟩ else ⟨0x3fe0000000000000⟩
  let exponent := Conversion.toI32 ((wide.mul Portable.log2e).add half)
  change exponent=0 at zero
  change ((wide.sub ((Conversion.ofInt exponent).mul Portable.ln2Hi)).sub
      ((Conversion.ofInt exponent).mul Portable.ln2Lo)).Finite ∧
    numerical64 ((wide.sub ((Conversion.ofInt exponent).mul Portable.ln2Hi)).sub
      ((Conversion.ofInt exponent).mul Portable.ln2Lo))=numerical64 wide
  rw [zero]
  have high : (Conversion.ofInt 0).mul Portable.ln2Hi=⟨0⟩ := rfl
  have low : (Conversion.ofInt 0).mul Portable.ln2Lo=⟨0⟩ := rfl
  rw [high,low]
  have first := binary64_sub_zero_value wide finite
  have second := binary64_sub_zero_value (wide.sub ⟨0⟩) first.1
  exact ⟨second.1,second.2.trans first.2⟩

/-- The actual saturation classifier and exact widening supply every hypothesis of the executing
reduction contract. -/
theorem exp_admitted_reduction (value : Binary32) (admitted : Portable.expSaturation value = none) :
    let reduced := Portable.expReduce (Conversion.widen value);
    value.Finite ∧ -151≤reduced.1 ∧ reduced.1≤129 ∧ reduced.2.Finite ∧
      |numerical64 reduced.2|≤349/1000 ∧ (numerical32 value≤0 → reduced.1≤0) := by
  have classifier := AcornVerif.CurrentExponential.expSaturation_ends value
  rw [admitted] at classifier
  have lowerFinite : (Binary32.mk AcornSpec.Constants.expUnderflowBits).Finite := by decide
  have upperFinite : (Binary32.mk AcornSpec.Constants.expOverflowBits).Finite := by decide
  have lowerValue : numerical32 (Binary32.mk AcornSpec.Constants.expUnderflowBits)= -104 := by
    change (-1:ℚ)*13631488*(2:ℚ)^(-17:Int)= -104
    norm_num
  have upperValue : numerical32 (Binary32.mk AcornSpec.Constants.expOverflowBits)=89 := by
    change (1:ℚ)*11665408*(2:ℚ)^(-17:Int)=89
    norm_num
  have lower := classifier.2.1
  have upper := classifier.2.2
  rw [numerical32_less _ _ lowerFinite classifier.1,decide_eq_true_eq,lowerValue] at lower
  rw [numerical32_less _ _ classifier.1 upperFinite,decide_eq_true_eq,upperValue] at upper
  have wideFinite := Conversion.widen_finite value classifier.1
  have wideValue := numerical_widen_exact value classifier.1
  have reduced := expReduce_contract (Conversion.widen value) wideFinite
    (by rw [wideValue]; exact le_of_lt lower) (by rw [wideValue]; exact le_of_lt upper)
  dsimp only at reduced ⊢
  rw [wideValue] at reduced
  exact ⟨classifier.1,reduced⟩

end AcornVerif.CurrentReduction
