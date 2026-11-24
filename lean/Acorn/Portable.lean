import Acorn.Arithmetic
import Acorn.Constants
import Acorn.Conversion

namespace Acorn.Portable

def ln2Hi : Binary64 := ⟨Acorn.Constants.ln2HiBits⟩
def ln2Lo : Binary64 := ⟨Acorn.Constants.ln2LoBits⟩
def log2e : Binary64 := ⟨Acorn.Constants.log2eBits⟩
def sqrt2 : Binary64 := ⟨Acorn.Constants.sqrt2Bits⟩

def coefficient (denominator : UInt64) : Binary64 :=
  (Binary64.ofUInt64 1).div (Binary64.ofUInt64 denominator)

def expCoefficients : List Binary64 :=
  [coefficient 3628800, coefficient 362880, coefficient 40320, coefficient 5040,
    coefficient 720, coefficient 120, coefficient 24, coefficient 6, coefficient 2,
    coefficient 1, coefficient 1]

def lnCoefficients : List Binary64 :=
  [coefficient 15, coefficient 13, coefficient 11, coefficient 9, coefficient 7,
    coefficient 5, coefficient 3, coefficient 1]

def expSaturation (value : Binary32) : Option Binary32 :=
  if value.isNaN then some value
  else if !value.less ⟨Acorn.Constants.expOverflowBits⟩ then some ⟨0x7f800000⟩
  else if !(Binary32.mk Acorn.Constants.expUnderflowBits).less value then some .zero
  else none

def expExponent (wide : Binary64) : Int32 :=
  let half : Binary64 := if wide.less ⟨0⟩ then ⟨0xbfe0000000000000⟩
    else ⟨0x3fe0000000000000⟩
  Conversion.toI32Word ((wide.mul log2e).add half)

def expRemainder (wide : Binary64) (exponent : Int32) : Binary64 :=
  let scaled := Conversion.ofI32Word exponent
  (wide.sub (scaled.mul ln2Hi)).sub (scaled.mul ln2Lo)

def expReduceWord (wide : Binary64) : Int32 × Binary64 :=
  let exponent := expExponent wide
  (exponent, expRemainder wide exponent)

def expReduce (wide : Binary64) : Int × Binary64 :=
  let reduced := expReduceWord wide
  (reduced.1.toInt, reduced.2)

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

theorem expSeries_eq (argument : Binary64) :
    expSeries argument = Binary64.hornerFrom argument ⟨0⟩ expCoefficients := by
  rfl

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

theorem lnSeries_eq (argument : Binary64) :
    lnSeries argument = Binary64.hornerFrom argument ⟨0⟩ lnCoefficients := by
  rfl

def powerOfTwo (exponent : Int) : Binary64 :=
  let word : UInt64 := ((exponent + 1023) % (2 ^ 64)).toNat.toUInt64
  ⟨word <<< (52 : UInt64)⟩

def powerOfTwoWord (exponent : Int32) : Binary64 :=
  ⟨(exponent.toInt64.toUInt64 + 1023) <<< (52 : UInt64)⟩

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

def expScale (polynomial : Binary64) (exponent : Int) : Binary32 :=
  Conversion.narrow (polynomial.mul (powerOfTwo exponent))

def expScaleWord (polynomial : Binary64) (exponent : Int32) : Binary32 :=
  Conversion.narrow (polynomial.mul (powerOfTwoWord exponent))

def exp (value : Binary32) : Binary32 :=
  if value.isNaN then value
  else if !value.less ⟨Acorn.Constants.expOverflowBits⟩ then ⟨0x7f800000⟩
  else if !(Binary32.mk Acorn.Constants.expUnderflowBits).less value then .zero
  else
    let wide := Conversion.widen value
    let exponent := expExponent wide
    expScaleWord (expSeries (expRemainder wide exponent)) exponent

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

theorem exp_nan_word (value : Binary32) (h : value.isNaN = true) : exp value = value := by
  simp [exp, h]

def logarithmExponent (bits : UInt64) : Int32 :=
  ((bits >>> 52 &&& 0x7ff).toUInt32.toInt32) - (1023 : UInt32).toInt32

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

def powLoop (accumulator squared : Binary64) (remaining : Nat) : Binary64 :=
  if h : remaining = 0 then accumulator
  else
    let next := if remaining % 2 = 1 then accumulator.mul squared else accumulator
    powLoop next (squared.mul squared) (remaining / 2)
termination_by remaining
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

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

def pow (value : Binary32) (exponent : UInt32) : Binary32 :=
  Conversion.narrow (powLoopWord (Binary64.ofUInt64 1) (Conversion.widen value) exponent)

theorem pow_eq (value : Binary32) (exponent : UInt32) :
    pow value exponent = Conversion.narrow
      (powLoop (Binary64.ofUInt64 1) (Conversion.widen value) exponent.toNat) := by
  rw [pow, powLoopWord_eq]

theorem powLoop_zero (accumulator squared : Binary64) :
    powLoop accumulator squared 0 = accumulator := by
  rw [powLoop]
  simp

theorem powLoop_step (accumulator squared : Binary64) (remaining : Nat)
    (h : remaining ≠ 0) :
    powLoop accumulator squared remaining =
      powLoop (if remaining % 2 = 1 then accumulator.mul squared else accumulator)
        (squared.mul squared) (remaining / 2) := by
  rw [powLoop]
  simp [h]

end Acorn.Portable
