/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Arithmetic
import Acorn.Constants
import Acorn.Conversion

/-!
# Executable local exponential, logarithm and integer power

Arithmetic and conversions use the executable definitions in `Acorn`. Each
polynomial is an ordered Horner fold with separate primitive rounding boundaries;
coefficients come from the shared `Acorn.Constants` interface.

These are approximation recipes, not opaque transcendental functions. Their
ideal-function errors and the native primitive correspondence remain separate
proof obligations. NaN handling is explicit: exponential preserves the input
word; logarithm selects positive quiet NaN; narrowing follows Conversion's
native cast policy. No cross-platform payload equivalence is asserted.
-/

namespace Acorn.Portable

/-- High part of the generated binary64 ln(2) split. -/
def ln2Hi : Binary64 := ⟨Acorn.Constants.ln2HiBits⟩
/-- Low part of the same split. -/
def ln2Lo : Binary64 := ⟨Acorn.Constants.ln2LoBits⟩
/-- Binary64 approximation of log2(e). -/
def log2e : Binary64 := ⟨Acorn.Constants.log2eBits⟩
/-- Binary64 approximation of sqrt(2), used only as a comparison threshold. -/
def sqrt2 : Binary64 := ⟨Acorn.Constants.sqrt2Bits⟩

/-- A coefficient uses the same separate binary64 conversion and division
boundaries in both the scalar executable and the retained list interface. -/
def coefficient (denominator : UInt64) : Binary64 :=
  (Binary64.ofUInt64 1).div (Binary64.ofUInt64 denominator)

/-- Exponential coefficients as ordered binary64 quotients, ending in two ones. -/
def expCoefficients : List Binary64 :=
  [coefficient 3628800, coefficient 362880, coefficient 40320, coefficient 5040,
    coefficient 720, coefficient 120, coefficient 24, coefficient 6, coefficient 2,
    coefficient 1, coefficient 1]

/-- Logarithm coefficients, highest power first. -/
def lnCoefficients : List Binary64 :=
  [coefficient 15, coefficient 13, coefficient 11, coefficient 9, coefficient 7,
    coefficient 5, coefficient 3, coefficient 1]

/-- Exponential's exceptional and saturation branches, before any conversion. -/
def expSaturation (value : Binary32) : Option Binary32 :=
  if value.isNaN then some value
  else if !value.less ⟨Acorn.Constants.expOverflowBits⟩ then some ⟨0x7f800000⟩
  else if !(Binary32.mk Acorn.Constants.expUnderflowBits).less value then some .zero
  else none

/-- Half-away integer selection keeps the exponent in a native signed word. -/
def expExponent (wide : Binary64) : Int32 :=
  let half : Binary64 := if wide.less ⟨0⟩ then ⟨0xbfe0000000000000⟩
    else ⟨0x3fe0000000000000⟩
  Conversion.toI32Word ((wide.mul log2e).add half)

/-- Ordered two-part subtraction uses the admitted signed-word conversion. -/
def expRemainder (wide : Binary64) (exponent : Int32) : Binary64 :=
  let scaled := Conversion.ofI32Word exponent
  (wide.sub (scaled.mul ln2Hi)).sub (scaled.mul ln2Lo)

/-- The pair-facing interface shares both executing scalar reduction owners. -/
def expReduceWord (wide : Binary64) : Int32 × Binary64 :=
  let exponent := expExponent wide
  (exponent, expRemainder wide exponent)

/-- Integer-facing view of the word reduction. The live exponential retains
its i32 exponent through scaling. -/
def expReduce (wide : Binary64) : Int × Binary64 :=
  let reduced := expReduceWord wide
  (reduced.1.toInt, reduced.2)

/-- Ordered degree-ten scalar polynomial, including the initial zero multiplication. -/
def expSeries (argument : Binary64) : Binary64 :=
  let a0 := Binary64.hornerStep argument ⟨0⟩ (coefficient 3628800)
  let a1 := Binary64.hornerStep argument a0 (coefficient 362880)
  let a2 := Binary64.hornerStep argument a1 (coefficient 40320)
  let a3 := Binary64.hornerStep argument a2 (coefficient 5040)
  let a4 := Binary64.hornerStep argument a3 (coefficient 720)
  let a5 := Binary64.hornerStep argument a4 (coefficient 120)
  let a6 := Binary64.hornerStep argument a5 (coefficient 24)
  let a7 := Binary64.hornerStep argument a6 (coefficient 6)
  let a8 := Binary64.hornerStep argument a7 (coefficient 2)
  let a9 := Binary64.hornerStep argument a8 (coefficient 1)
  let a10 := Binary64.hornerStep argument a9 (coefficient 1)
  a10

/-- Scalar evaluation equals the retained ordered fold for every raw argument. -/
theorem expSeries_eq (argument : Binary64) :
    expSeries argument = Binary64.hornerFrom argument ⟨0⟩ expCoefficients := by
  rfl

/-- Ordered logarithm polynomial without a runtime list traversal. -/
def lnSeries (argument : Binary64) : Binary64 :=
  let a0 := Binary64.hornerStep argument ⟨0⟩ (coefficient 15)
  let a1 := Binary64.hornerStep argument a0 (coefficient 13)
  let a2 := Binary64.hornerStep argument a1 (coefficient 11)
  let a3 := Binary64.hornerStep argument a2 (coefficient 9)
  let a4 := Binary64.hornerStep argument a3 (coefficient 7)
  let a5 := Binary64.hornerStep argument a4 (coefficient 5)
  let a6 := Binary64.hornerStep argument a5 (coefficient 3)
  let a7 := Binary64.hornerStep argument a6 (coefficient 1)
  a7

/-- Scalar evaluation equals the retained ordered fold for every raw argument. -/
theorem lnSeries_eq (argument : Binary64) :
    lnSeries argument = Binary64.hornerFrom argument ⟨0⟩ lnCoefficients := by
  rfl

/-- Exponent-field construction; exact normal scaling requires the separately
stated exponent range. The raw function itself is total for every integer. -/
def powerOfTwo (exponent : Int) : Binary64 :=
  let word : UInt64 := ((exponent + 1023) % (2 ^ 64)).toNat.toUInt64
  ⟨word <<< (52 : UInt64)⟩

/-- Sign extension and exponent-field assembly use only fixed-width words.
The total word recipe agrees with the integer-facing recipe for every i32. -/
def powerOfTwoWord (exponent : Int32) : Binary64 :=
  ⟨(exponent.toInt64.toUInt64 + 1023) <<< (52 : UInt64)⟩

/-- Sign-extending an i32 produces the same 64-bit residue as its integer
reading. This is a universal word-conversion identity. -/
theorem powerOfTwoWord_eq (exponent : Int32) :
    powerOfTwoWord exponent = powerOfTwo exponent.toInt := by
  have cast : exponent.toInt64.toUInt64 = UInt64.ofInt exponent.toInt := by
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toInt_eq
    have view : (UInt64.ofInt exponent.toInt).toBitVec = BitVec.ofInt 64 exponent.toInt := by
      apply BitVec.eq_of_toNat_eq
      simp only [UInt64.toNat_toBitVec, UInt64.ofInt, UInt64.toNat_ofNat', BitVec.toNat_ofInt]
      have h := Int.emod_lt_of_pos exponent.toInt (show (0 : Int) < 2^64 by decide)
      omega
    rw [view]
    change (exponent.toBitVec.signExtend 64).toInt = (BitVec.ofInt 64 exponent.toInt).toInt
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt]
    change exponent.toInt = exponent.toInt.bmod (2^64)
    rw [Int.bmod_eq_of_le (by have := exponent.toInt_lt; have := exponent.le_toInt; omega)
      (by have := exponent.toInt_lt; omega)]
  unfold powerOfTwoWord
  rw [cast]
  change Binary64.mk ((UInt64.ofInt exponent.toInt + 1023) <<< 52) =
    Binary64.mk ((UInt64.ofInt (exponent.toInt + 1023)) <<< 52)
  rw [UInt64.ofInt_add]
  rfl

/-- Scale by the exponent field and narrow once. -/
def expScale (polynomial : Binary64) (exponent : Int) : Binary32 :=
  Conversion.narrow (polynomial.mul (powerOfTwo exponent))

/-- Scaling with the actual i32 reduction result avoids general integer
conversion and modulo in the exponential's executable path. -/
def expScaleWord (polynomial : Binary64) (exponent : Int32) : Binary32 :=
  Conversion.narrow (polynomial.mul (powerOfTwoWord exponent))

/-- Local exponential classifies directly and retains scalar reduction values;
no option or pair allocation is needed on the executing numerical path. -/
def exp (value : Binary32) : Binary32 :=
  if value.isNaN then value
  else if !value.less ⟨Acorn.Constants.expOverflowBits⟩ then ⟨0x7f800000⟩
  else if !(Binary32.mk Acorn.Constants.expUnderflowBits).less value then .zero
  else
    let wide := Conversion.widen value
    let exponent := expExponent wide
    expScaleWord (expSeries (expRemainder wide exponent)) exponent

/-- Word execution agrees with the integer-facing reduction and scaling
specification; the result equality covers every raw binary32 input. -/
theorem exp_eq_spec (value : Binary32) : exp value =
    match expSaturation value with
    | some result => result
    | none => let reduced := expReduce (Conversion.widen value)
              expScale (expSeries reduced.2) reduced.1 := by
  unfold exp expSaturation
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · simp only [expScaleWord, expScale, expReduce, expReduceWord, powerOfTwoWord_eq]

/-- Exponential preserves every input NaN word, including its sign and payload. -/
theorem exp_nan_word (value : Binary32) (h : value.isNaN = true) : exp value = value := by
  simp [exp, h]

/-- The stored binary64 exponent occupies eleven bits, so subtracting its
bias fits in i32 for every raw storage word. -/
def logarithmExponent (bits : UInt64) : Int32 :=
  ((bits >>> 52 &&& 0x7ff).toUInt32.toInt32) - (1023 : UInt32).toInt32

/-- Exponent extraction and bias subtraction have their exact integer meaning
on the complete storage-word domain; no caller range assumption is needed. -/
theorem logarithmExponent_exact (bits : UInt64) :
    (logarithmExponent bits).toInt = (((bits >>> 52 &&& 0x7ff).toNat : Int) - 1023) := by
  let e := bits >>> 52 &&& (0x7ff : UInt64)
  have bound : e.toNat ≤ 2047 := by
    dsimp only [e]
    rw [UInt64.toNat_and]
    exact Nat.and_le_right
  have castNat : e.toUInt32.toNat = e.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have castInt : e.toUInt32.toInt32.toInt = (e.toNat : Int) := by
    have word : e.toUInt32.toInt32 = Int32.ofNat e.toUInt32.toNat := by
      rw [← UInt32.toInt32_ofNat', UInt32.ofNat_toNat]
    rw [word, Int32.toInt_ofNat_of_lt (by rw [castNat]; omega), castNat]
  unfold logarithmExponent
  rw [Int32.toInt_sub]
  change (e.toUInt32.toInt32.toInt - 1023).bmod (2^32) = _
  rw [castInt, Int.bmod_eq_of_le (by omega) (by omega)]

/-- Local logarithm with classification before mantissa decomposition. -/
def ln (value : Binary32) : Binary32 :=
  if value.isNaN || value.less .zero then ⟨0x7fc00000⟩
  else if value.magnitudeEq 0 then ⟨0xff800000⟩
  else if value.magnitudeEq 0x7f800000 then ⟨0x7f800000⟩
  else
    let bits := (Conversion.widen value).bits
    let exponent₀ := Conversion.ofI32Word (logarithmExponent bits)
    let mantissa₀ : Binary64 := ⟨(bits &&& (0xfffffffffffff : UInt64)) ||| ((1023 : UInt64) <<< 52)⟩
    let centered := sqrt2.less mantissa₀
    let mantissa := if centered then mantissa₀.mul ⟨0x3fe0000000000000⟩ else mantissa₀
    let exponent := if centered then exponent₀.add (Binary64.ofUInt64 1) else exponent₀
    let ratio := (mantissa.sub (Binary64.ofUInt64 1)).div (mantissa.add (Binary64.ofUInt64 1))
    let ratioSq := ratio.mul ratio
    let polynomial := lnSeries ratioSq
    let lnMantissa := ((Binary64.ofUInt64 2).mul ratio).mul polynomial
    Conversion.narrow ((exponent.mul ln2Hi).add ((exponent.mul ln2Lo).add lnMantissa))

/-- Integer-power loop terminates by halving the remaining exponent. Its
accumulator update precedes the square, including the final iteration. -/
def powLoop (accumulator squared : Binary64) (remaining : Nat) : Binary64 :=
  if h : remaining = 0 then accumulator
  else
    let next := if remaining % 2 = 1 then accumulator.mul squared else accumulator
    powLoop next (squared.mul squared) (remaining / 2)
termination_by remaining
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The live integer-power loop retains the admitted u32 exponent throughout.
Its termination measure is proof-only; each executing update is word division. -/
def powLoopWord (accumulator squared : Binary64) (remaining : UInt32) : Binary64 :=
  if remaining = 0 then accumulator
  else
    let next := if remaining % 2 = 1 then accumulator.mul squared else accumulator
    powLoopWord next (squared.mul squared) (remaining / 2)
termination_by remaining.toNat
decreasing_by
  rw [UInt32.toNat_div]
  apply Nat.div_lt_self
  · have : remaining.toNat ≠ 0 := by intro h; exact ‹remaining ≠ 0› (UInt32.toNat.inj h)
    omega
  · decide

/-- Every u32 loop has exactly the general loop's rounded operation order,
including its terminal square and its zero-exponent behavior. -/
theorem powLoopWord_eq (accumulator squared : Binary64) (remaining : UInt32) :
    powLoopWord accumulator squared remaining = powLoop accumulator squared remaining.toNat := by
  rw [powLoopWord, powLoop]
  have zero : remaining = 0 ↔ remaining.toNat = 0 := by
    rw [← UInt32.toNat_inj]
    rfl
  have odd : remaining % 2 = 1 ↔ remaining.toNat % 2 = 1 := by
    rw [← UInt32.toNat_inj, UInt32.toNat_mod]
    rfl
  simp only [zero, odd]
  split
  · rfl
  · rw [powLoopWord_eq]
    rw [UInt32.toNat_div]
    rfl
termination_by remaining.toNat
decreasing_by
  rw [UInt32.toNat_div]
  apply Nat.div_lt_self (by omega) (by decide)

/-- Machine u32 integer power, with one initial widening and one final narrowing. -/
def pow (value : Binary32) (exponent : UInt32) : Binary32 :=
  Conversion.narrow (powLoopWord (Binary64.ofUInt64 1) (Conversion.widen value) exponent)

/-- Public power retains the complete general loop's specified machine result. -/
theorem pow_eq (value : Binary32) (exponent : UInt32) :
    pow value exponent = Conversion.narrow
      (powLoop (Binary64.ofUInt64 1) (Conversion.widen value) exponent.toNat) := by
  rw [pow, powLoopWord_eq]

/-- The zero exponent exits without inspecting or multiplying the base. -/
theorem powLoop_zero (accumulator squared : Binary64) :
    powLoop accumulator squared 0 = accumulator := by
  rw [powLoop]
  simp

/-- Every positive iteration follows the stated machine order. This is a
universal transition identity, not a sampled comparison with ideal powers. -/
theorem powLoop_step (accumulator squared : Binary64) (remaining : Nat)
    (h : remaining ≠ 0) :
    powLoop accumulator squared remaining =
      powLoop (if remaining % 2 = 1 then accumulator.mul squared else accumulator)
        (squared.mul squared) (remaining / 2) := by
  rw [powLoop]
  simp [h]

end Acorn.Portable
