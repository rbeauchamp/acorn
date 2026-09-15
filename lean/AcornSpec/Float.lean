/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Constants
import AcornSpec.MachineWords

/-!
# Executable specification: platform-identical float vocabulary

Mirrors the float operations the Rust study path is allowed to use. Acorn's
own discipline (`clippy.toml` bans every libm-backed method; `src/float.rs`
builds `exp`/`ln`/`pow` from IEEE-required primitives) restricts the system to
exactly the subset Lean v4.33's bit-level kernel float model specifies —
`add/sub/mul/div/neg`, comparisons, `ofBits/toBits`, and the integer→float
conversions. The remaining Rust vocabulary (width conversions, `floor`, the
saturating `as` casts) is **defined here from those modeled primitives by bit
manipulation**, so no opaque float operation appears anywhere in `AcornSpec`:
every arithmetic step of the specified system has machine-independent kernel
meaning.

Rust semantics mirrored exactly:

- `f64::from(f32)` — exact widening (`widen`);
- `x as f32` on `f64` — round-to-nearest-even narrowing (`narrow`);
- `f32::floor` / `f64::floor` — round toward −∞ (`floor32`, `floor64`);
- float→integer `as` casts — NaN ↦ 0, truncate toward zero, saturate at the
  target range (`rustF64toI32` and friends);
- integer→float `as` casts — round to nearest, even ties (delegated to the
  modeled `UInt64.toFloat32`/`UInt64.toFloat` with a sign symmetry for the
  signed cases);
- `f32::max` — IEEE maxNum as this platform's `fmaxnm` computes it: a NaN
  operand yields the other, and a `(+0, −0)` pair yields `+0`;
- `Portable::{exp, ln, pow}` — transcribed from `src/float.rs` line by line.
-/

namespace AcornSpec

open AcornSpec.Constants

/-! ## Constants and small helpers -/

/-- `f32` positive infinity bits. -/
def f32InfBits : UInt32 := 0x7F800000
/-- `f32::INFINITY`. -/
def f32Inf : Float32 := Float32.ofBits f32InfBits
/-- `f32::NEG_INFINITY`. -/
def f32NegInf : Float32 := Float32.ofBits 0xFF800000
/-- `f32::NAN` (Rust's quiet-NaN constant bits). -/
def f32NaN : Float32 := Float32.ofBits 0x7FC00000
/-- `0.0f32`. -/
def f32zero : Float32 := Float32.ofBits 0
/-- `0.0f64`. -/
def f64zero : Float := Float.ofBits 0

/-- Exact `f32` of a small natural number (every call site is < 2²⁴, where
the conversion is exact). -/
@[inline]
def natF32 (n : Nat) : Float32 := UInt64.toFloat32 n.toUInt64

/-- Exact `f64` of a natural number below 2⁵³. -/
@[inline]
def natF64 (n : Nat) : Float := UInt64.toFloat n.toUInt64

/-- Rust `x as f32` on an `i64`: round to nearest, ties to even. Negative
values go through the sign symmetry of round-to-nearest. -/
@[inline]
def i64ToF32 (n : Int) : Float32 :=
  if 0 ≤ n then UInt64.toFloat32 n.toNat.toUInt64
  else Float32.neg (UInt64.toFloat32 (-n).toNat.toUInt64)

/-- Rust `f64::from(k)` on an `i32`-ranged integer: exact. -/
@[inline]
def intToF64 (n : Int) : Float :=
  if 0 ≤ n then UInt64.toFloat n.toNat.toUInt64
  else Float.neg (UInt64.toFloat (-n).toNat.toUInt64)

/-! ## Width conversions from the bit model -/

/-- Exact `f32 → f64` widening — Rust's `f64::from(x)`. Defined from
`toBits`/`ofBits` alone: normals rebias, subnormals normalize (every `f32`
subnormal is an `f64` normal), infinities and NaNs keep their class and
payload. -/
def widen (x : Float32) : Float :=
  let b := x.toBits
  let sign : UInt64 := (b.toUInt64 >>> 31) <<< 63
  let e : UInt32 := (b >>> 23) &&& 0xFF
  let f : UInt64 := (b &&& 0x7FFFFF).toUInt64
  if e == 0xFF then
    Float.ofBits (sign ||| ((0x7FF : UInt64) <<< 52) ||| (f <<< 29))
  else if e == 0 then
    if f == 0 then Float.ofBits sign
    else
      -- Subnormal: value = f · 2⁻¹⁴⁹ with f < 2²³. Normalize to an f64.
      let L := f.toNat.log2
      let e64 : UInt64 := (L + 874).toUInt64
      let frac64 : UInt64 := (f - ((1 : UInt64) <<< L.toUInt64)) <<< (52 - L).toUInt64
      Float.ofBits (sign ||| (e64 <<< 52) ||| frac64)
  else
    Float.ofBits (sign ||| ((e.toUInt64 + 896) <<< 52) ||| (f <<< 29))

/-- Round-to-nearest-even `f64 → f32` narrowing — Rust's `x as f32`. Defined
from the bit model, in fixed-width arithmetic. NaN input yields the
canonical quiet NaN (the payload a NaN narrowing carries is unobservable on
the study path: no NaN is ever narrowed there, and payloads never reach a
decision). -/
def narrow (y : Float) : Float32 :=
  let b := y.toBits
  let sign32 : UInt32 := ((b >>> 63).toUInt32) <<< 31
  let e : UInt64 := (b >>> 52) &&& 0x7FF
  let f : UInt64 := b &&& 0xFFFFFFFFFFFFF
  if e == 0x7FF then
    if f == 0 then Float32.ofBits (sign32 ||| f32InfBits)
    else Float32.ofBits (sign32 ||| 0x7FC00000)
  else if e ≥ 897 then
    -- Normal-target candidate (the leading-bit exponent T = e − 1023 ≥ −126):
    -- keep 24 of the 53 significand bits, round the low 29 to nearest-even.
    let S : UInt64 := ((1 : UInt64) <<< 52) ||| f
    let kept : UInt64 := S >>> 29
    let rem : UInt64 := S &&& 0x1FFFFFFF
    let half : UInt64 := 0x10000000
    let up : Bool := rem > half || (rem == half && kept &&& 1 == 1)
    let kept := if up then kept + 1 else kept
    let (kept, e) := if kept == ((1 : UInt64) <<< 24) then ((1 : UInt64) <<< 23, e + 1) else (kept, e)
    if e > 1150 then Float32.ofBits (sign32 ||| f32InfBits)  -- T > 127
    else
      -- Biased f32 exponent: T + 127 = e − 896.
      Float32.ofBits (sign32 ||| (((e - 896).toUInt32) <<< 23) ||| (kept.toUInt32 - ((1 : UInt32) <<< 23)))
  else
    -- Subnormal target (or zero): result = round(S · 2^(E+149)); the shift
    -- is d = 925 for a subnormal input, 926 − e otherwise (≥ 30 here).
    let S : UInt64 := if e == 0 then f else ((1 : UInt64) <<< 52) ||| f
    if S == 0 then Float32.ofBits sign32
    else
      let d : UInt64 := if e == 0 then 925 else 926 - e
      if d ≥ 54 then Float32.ofBits sign32
      else
        let kept : UInt64 := S >>> d
        let rem : UInt64 := S &&& (((1 : UInt64) <<< d) - 1)
        let half : UInt64 := (1 : UInt64) <<< (d - 1)
        let up : Bool := rem > half || (rem == half && kept &&& 1 == 1)
        let kept := if up then kept + 1 else kept
        Float32.ofBits (sign32 ||| kept.toUInt32)

/-! ## Floor and the saturating casts -/

/-- Rust `f64::floor`: round toward −∞. Defined from the bit model. -/
def floor64 (y : Float) : Float :=
  let b := y.toBits
  let e : UInt64 := (b >>> 52) &&& 0x7FF
  if e == 0x7FF then y  -- NaN and ±∞ are their own floor
  else
    let E : Int := (e.toNat : Int) - 1023
    if E ≥ 52 then y
    else if E < 0 then
      -- |y| < 1: floor is ±0 or −1.
      if b >>> 63 == 1 ∧ (b <<< 1) != 0 then Float.ofBits 0xBFF0000000000000
      else Float.ofBits (b &&& 0x8000000000000000)
    else
      let mask : UInt64 := (1 <<< (52 - E).toNat.toUInt64) - 1
      if b &&& mask == 0 then y
      else if b >>> 63 == 1 then Float.ofBits ((b &&& (~~~mask)) + (mask + 1))
      else Float.ofBits (b &&& (~~~mask))

/-- Rust `f32::floor`: round toward −∞. -/
def floor32 (x : Float32) : Float32 :=
  let b := x.toBits
  let e : UInt32 := (b >>> 23) &&& 0xFF
  if e == 0xFF then x
  else
    let E : Int := (e.toNat : Int) - 127
    if E ≥ 23 then x
    else if E < 0 then
      if b >>> 31 == 1 ∧ (b <<< 1) != 0 then Float32.ofBits 0xBF800000
      else Float32.ofBits (b &&& 0x80000000)
    else
      let mask : UInt32 := (1 <<< (23 - E).toNat.toUInt32) - 1
      if b &&& mask == 0 then x
      else if b >>> 31 == 1 then Float32.ofBits ((b &&& (~~~mask)) + (mask + 1))
      else Float32.ofBits (b &&& (~~~mask))

/-- Truncation of a finite `f64` toward zero as an exact integer (helper for
the saturating casts; the callers handle NaN and saturation). -/
def truncF64 (y : Float) : Int :=
  let b := y.toBits
  let e : UInt64 := (b >>> 52) &&& 0x7FF
  let E : Int := (e.toNat : Int) - 1023
  if e == 0 || E < 0 then 0
  else
    let S : UInt64 := ((1 : UInt64) <<< 52) ||| (b &&& 0xFFFFFFFFFFFFF)
    let mag : Int :=
      if E ≥ 52 then (S.toNat : Int) * (2 ^ (E - 52).toNat)
      else ((S >>> (52 - E).toNat.toUInt64).toNat : Int)
    if b >>> 63 == 1 then -mag else mag

/-- Truncation of a finite `f32` toward zero as an exact integer. -/
def truncF32 (x : Float32) : Int :=
  let b := x.toBits
  let e : UInt32 := (b >>> 23) &&& 0xFF
  let E : Int := (e.toNat : Int) - 127
  if e == 0 || E < 0 then 0
  else
    let S : UInt32 := ((1 : UInt32) <<< 23) ||| (b &&& 0x7FFFFF)
    let mag : Int :=
      if E ≥ 23 then (S.toNat : Int) * (2 ^ (E - 23).toNat)
      else ((S >>> (23 - E).toNat.toUInt32).toNat : Int)
    if b >>> 31 == 1 then -mag else mag

/-- Rust `x as i32` on `f64`: NaN ↦ 0, truncate toward zero, saturate. -/
def rustF64toI32 (y : Float) : Int :=
  if y.isNaN then 0
  else if y.isInf then (if y < f64zero then -2147483648 else 2147483647)
  else
    let t := truncF64 y
    if t > 2147483647 then 2147483647
    else if t < -2147483648 then -2147483648
    else t

/-- Rust `x as i64` on `f32`: NaN ↦ 0, truncate toward zero, saturate. -/
def rustF32toI64 (x : Float32) : Int :=
  if x.isNaN then 0
  else if x.isInf then
    (if x < f32zero then -9223372036854775808 else 9223372036854775807)
  else
    let t := truncF32 x
    if t > 9223372036854775807 then 9223372036854775807
    else if t < -9223372036854775808 then -9223372036854775808
    else t

/-- Rust `x as u8` on `f32`: NaN ↦ 0, truncate toward zero, saturate to
`[0, 255]`. -/
def rustF32toU8 (x : Float32) : UInt8 :=
  if x.isNaN then 0
  else if x.isInf then (if x < f32zero then 0 else 255)
  else
    let t := truncF32 x
    if t ≤ 0 then 0 else if t ≥ 255 then 255 else t.toNat.toUInt8

/-- Rust `x as u32` on `f64`: NaN ↦ 0, truncate toward zero, saturate to
`[0, 2³² − 1]`. -/
def rustF64toU32 (y : Float) : UInt32 :=
  if y.isNaN then 0
  else if y.isInf then (if y < f64zero then 0 else 0xFFFFFFFF)
  else
    let t := truncF64 y
    if t ≤ 0 then 0 else if t ≥ 4294967295 then 0xFFFFFFFF else t.toNat.toUInt32

/-- Rust `f32::is_finite`: neither NaN nor infinite. -/
@[inline]
def isFinite32 (x : Float32) : Bool := !x.isNaN && !x.isInf

/-- Rust `f32::max` as this platform computes it (`fmaxnm`): a NaN operand
yields the other operand, and a `(+0, −0)` pair yields `+0`. Values on the
study path never present the signed-zero pair (predictions are `+0`-seeded
sums), so only the IEEE maxNum half is ever exercised. -/
@[inline]
def rustMax32 (a b : Float32) : Float32 :=
  if a.isNaN then b
  else if b.isNaN then a
  else if a < b then b
  else if b < a then a
  else if a.toBits >>> 31 == 1 then b else a

/-- Rust `y as i32` as its two's-complement `u64` image, in fixed-width
arithmetic. The common path (|y| < 2³¹) never allocates; NaN, infinities and
saturation delegate to `rustF64toI32`, whose semantics this agrees with
everywhere. -/
def f64toI32Wrapped (y : Float) : UInt64 :=
  let b := y.toBits
  let e : UInt64 := (b >>> 52) &&& 0x7FF
  if e < 1023 then 0
  else if e ≥ 1054 then i64bits (rustF64toI32 y)
  else
    let E := e - 1023
    let S : UInt64 := ((1 : UInt64) <<< 52) ||| (b &&& 0xFFFFFFFFFFFFF)
    let mag := S >>> (52 - E)
    if b >>> 63 == 1 then 0 - mag else mag

/-- Exact `f64` of an i32-ranged two's-complement image — `f64::from(k)`. -/
@[inline]
def i32WrappedToF64 (kb : UInt64) : Float :=
  if kb >>> 63 == 1 then Float.neg (UInt64.toFloat (0 - kb)) else UInt64.toFloat kb

/-! ## `Portable` — `src/float.rs` transcribed -/

/-- `float.rs LN2_HI`. -/
def ln2Hi : Float := Float.ofBits ln2HiBits
/-- `float.rs LN2_LO`. -/
def ln2Lo : Float := Float.ofBits ln2LoBits
/-- `core::f64::consts::LOG2_E`. -/
def log2e : Float := Float.ofBits log2eBits
/-- `core::f64::consts::SQRT_2`. -/
def sqrt2 : Float := Float.ofBits sqrt2Bits
/-- `float.rs EXP_OVERFLOW` (89.0f32). -/
def expOverflow : Float32 := Float32.ofBits expOverflowBits
/-- `float.rs EXP_UNDERFLOW` (−104.0f32). -/
def expUnderflow : Float32 := Float32.ofBits expUnderflowBits
/-- `0.5f64` (the rounding half of `exp32`'s reduction). -/
def half64 : Float := Float.ofBits 0x3FE0000000000000
/-- `−0.5f64`. -/
def negHalf64 : Float := Float.ofBits 0xBFE0000000000000
/-- `0.5f64` again under the mantissa-centring name `ln32` uses. -/
def pointFive64 : Float := Float.ofBits 0x3FE0000000000000

/-- `float.rs EXP_TAYLOR[0] = 1/10!` — the exact correctly-rounded `f64`
quotient the Rust constant expression folds to (the divisions here are the
same IEEE divisions rustc performs at compile time). -/
def expC0 : Float := natF64 1 / natF64 3628800
/-- `1/9!`. -/
def expC1 : Float := natF64 1 / natF64 362880
/-- `1/8!`. -/
def expC2 : Float := natF64 1 / natF64 40320
/-- `1/7!`. -/
def expC3 : Float := natF64 1 / natF64 5040
/-- `1/6!`. -/
def expC4 : Float := natF64 1 / natF64 720
/-- `1/5!`. -/
def expC5 : Float := natF64 1 / natF64 120
/-- `1/4!`. -/
def expC6 : Float := natF64 1 / natF64 24
/-- `1/3!`. -/
def expC7 : Float := natF64 1 / natF64 6
/-- `1/2!`. -/
def expC8 : Float := natF64 1 / natF64 2
/-- The linear and constant Taylor terms. -/
def expC9 : Float := natF64 1

/-- `float.rs LN_SERIES` entries, highest power first — exact quotients. -/
def lnC0 : Float := natF64 1 / natF64 15
/-- `1/13`. -/
def lnC1 : Float := natF64 1 / natF64 13
/-- `1/11`. -/
def lnC2 : Float := natF64 1 / natF64 11
/-- `1/9`. -/
def lnC3 : Float := natF64 1 / natF64 9
/-- `1/7`. -/
def lnC4 : Float := natF64 1 / natF64 7
/-- `1/5`. -/
def lnC5 : Float := natF64 1 / natF64 5
/-- `1/3`. -/
def lnC6 : Float := natF64 1 / natF64 3
/-- The final series term. -/
def lnC7 : Float := natF64 1

/-- `float.rs exp2i`: `2^k` as an exact `f64` via the exponent field, over
the two's-complement image of `k`. Total; on the reduction range
`k ∈ [−151, 129]` it is the Rust expression bit for bit (the wrapping add
mirrors `(k + 1023) as u64`). -/
@[inline]
def exp2i (kb : UInt64) : Float :=
  Float.ofBits ((kb + 1023) <<< 52)

/-- `float.rs exp32` — `e^x` for `f32`, evaluated in `f64`. -/
def exp32 (x : Float32) : Float32 :=
  if x.isNaN then x
  else if expOverflow ≤ x then f32Inf
  else if x ≤ expUnderflow then f32zero
  else
    let wide := widen x
    let half : Float := if wide < f64zero then negHalf64 else half64
    let kb := f64toI32Wrapped (wide * log2e + half)
    let scaled := i32WrappedToF64 kb
    let rem := (wide - scaled * ln2Hi) - scaled * ln2Lo
    -- Horner over EXP_TAYLOR, unrolled in the exact fold order.
    let poly := f64zero
    let poly := poly * rem + expC0
    let poly := poly * rem + expC1
    let poly := poly * rem + expC2
    let poly := poly * rem + expC3
    let poly := poly * rem + expC4
    let poly := poly * rem + expC5
    let poly := poly * rem + expC6
    let poly := poly * rem + expC7
    let poly := poly * rem + expC8
    let poly := poly * rem + expC9
    let poly := poly * rem + expC9
    narrow (poly * exp2i kb)

/-- `float.rs ln32` — `ln x` for `f32`, evaluated in `f64`. -/
def ln32 (x : Float32) : Float32 :=
  if x.isNaN || x < f32zero then f32NaN
  else if x == f32zero then f32NegInf
  else if x.isInf then f32Inf
  else
    let bits := (widen x).toBits
    let eb := (bits >>> 52) &&& 0x7FF
    let exponent₀ := if eb ≥ 1023 then UInt64.toFloat (eb - 1023)
                     else Float.neg (UInt64.toFloat (1023 - eb))
    let mantissa₀ := Float.ofBits ((bits &&& (0x000FFFFFFFFFFFFF : UInt64)) ||| ((1023 : UInt64) <<< 52))
    let centre := mantissa₀ > sqrt2
    let mantissa := if centre then mantissa₀ * pointFive64 else mantissa₀
    let exponent := if centre then exponent₀ + natF64 1 else exponent₀
    let ratio := (mantissa - natF64 1) / (mantissa + natF64 1)
    let ratioSq := ratio * ratio
    -- Horner over LN_SERIES, unrolled in the exact fold order.
    let poly := f64zero
    let poly := poly * ratioSq + lnC0
    let poly := poly * ratioSq + lnC1
    let poly := poly * ratioSq + lnC2
    let poly := poly * ratioSq + lnC3
    let poly := poly * ratioSq + lnC4
    let poly := poly * ratioSq + lnC5
    let poly := poly * ratioSq + lnC6
    let poly := poly * ratioSq + lnC7
    let lnMantissa := natF64 2 * ratio * poly
    narrow (exponent * ln2Hi + (exponent * ln2Lo + lnMantissa))

/-- Binary-exponentiation loop of `pow32`, structurally on a 32-step fuel —
one step per bit of a `u32` exponent, exiting exactly where the Rust
`while remaining > 0` loop exits. -/
def pow32Go (acc squared : Float) (remaining : UInt32) : Nat → Float
  | 0 => acc
  | fuel + 1 =>
    if remaining == 0 then acc
    else
      let acc := if remaining &&& 1 == 1 then acc * squared else acc
      pow32Go acc (squared * squared) (remaining >>> 1) fuel

/-- `float.rs pow32` — `base^exp` for a non-negative integer exponent, by
squaring, accumulated in `f64`. -/
def pow32 (base : Float32) (exp : UInt32) : Float32 :=
  narrow (pow32Go (natF64 1) (widen base) exp 32)

end AcornSpec
