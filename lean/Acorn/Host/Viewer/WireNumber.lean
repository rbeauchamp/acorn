/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Encoding

/-!
# Exact numeric telemetry spelling

Finite binary values are dyadic rationals. Multiplying a denominator `2^n`
by `5^n` yields an exact decimal, with no floating formatting operation or
precision setting. Exceptional encodings become JSON null; negative zero
retains its sign. JSON consumers own their decimal-to-machine rounding.
-/
namespace Acorn.Host.Viewer

/-- Exact unsigned dyadic magnitude, with sign retained independently for negative zero. -/
structure WireDyadic where
  /-- Raw sign, including for a zero significand. -/
  negative : Bool
  /-- Integer significand including the implicit normal bit. -/
  significand : Nat
  /-- Unbiased power of two multiplying the significand. -/
  exponent : Int

/-- Exact decimal represented as signed coefficient divided by a power of ten. -/
structure WireDecimal where
  /-- Sign is never inferred from the possibly zero coefficient. -/
  negative : Bool
  /-- All significant decimal digits are emitted. -/
  coefficient : Nat
  /-- Number of decimal fractional places. -/
  scale : Nat

/-- Positive-exponent contribution to the dyadic numerator. -/
def WireDyadic.numerator (value : WireDyadic) : Nat :=
  value.significand * 2 ^ value.exponent.toNat

/-- Negative-exponent contribution to the dyadic denominator. -/
def WireDyadic.denominator (value : WireDyadic) : Nat := 2 ^ (-value.exponent).toNat

/-- Decimal conversion uses integer operations only, including for subnormal inputs. -/
def WireDyadic.decimal (value : WireDyadic) : WireDecimal :=
  ⟨value.negative, value.numerator * 5 ^ (-value.exponent).toNat, (-value.exponent).toNat⟩

/-- Every exact decimal denotes the same rational magnitude as its input dyadic.
Cross multiplication avoids introducing a separate runtime rational implementation. -/
theorem WireDyadic.decimal_exact (value : WireDyadic) :
    value.decimal.coefficient * value.denominator =
      value.numerator * 10 ^ value.decimal.scale := by
  simp only [decimal, denominator]
  rw [Nat.mul_assoc, ← Nat.mul_pow]

/-- Decimal conversion preserves the raw sign even when the magnitude is zero. -/
theorem WireDyadic.decimal_sign (value : WireDyadic) :
    value.decimal.negative = value.negative := rfl

/-- Integer decimal digits and an explicit base-ten exponent form a JSON number. -/
def WireDecimal.text (value : WireDecimal) : String :=
  (if value.negative then "-" else "") ++ toString value.coefficient ++
    (if value.scale = 0 then "" else "e-" ++ toString value.scale)

/-- Extract the exact finite IEEE binary32 fields, refusing all exceptional encodings. -/
def binary32Dyadic (value : Binary32) : Option WireDyadic :=
  if value.Finite then
    let exponent : Nat := value.magnitude / 2 ^ 23
    let fraction := value.magnitude % 2 ^ 23
    some ⟨value.negative, fraction + (if exponent = 0 then 0 else 2 ^ 23),
      (if exponent = 0 then -149 else (exponent : Int) - 150)⟩
  else none

/-- Extract the exact finite IEEE binary64 fields, preserving the raw sign separately. -/
def binary64Dyadic (value : Binary64) : Option WireDyadic :=
  if value.Finite then
    let exponent : Nat := value.magnitude / 2 ^ 52
    let fraction := value.magnitude % 2 ^ 52
    some ⟨value.bits &&& 0x8000000000000000 != 0,
      fraction + (if exponent = 0 then 0 else 2 ^ 52),
      (if exponent = 0 then -1074 else (exponent : Int) - 1075)⟩
  else none

/-- Binary32 emission preserves the exact finite decimal and marks exceptional values as null. -/
def binary32Text (value : Binary32) : String :=
  match binary32Dyadic value with
  | none => "null"
  | some dyadic => dyadic.decimal.text

/-- Binary64 lifetime accumulators retain all their finite precision on the wire. -/
def binary64Text (value : Binary64) : String :=
  match binary64Dyadic value with
  | none => "null"
  | some dyadic => dyadic.decimal.text

/-- Every non-finite binary32 pattern is visibly exceptional, never a numeric zero. -/
theorem binary32Text_exceptional (value : Binary32) (exceptional : ¬ value.Finite) :
    binary32Text value = "null" := by simp [binary32Text, binary32Dyadic, exceptional]

/-- Every non-finite binary64 pattern is visibly exceptional, including NaN payload variants. -/
theorem binary64Text_exceptional (value : Binary64) (exceptional : ¬ value.Finite) :
    binary64Text value = "null" := by simp [binary64Text, binary64Dyadic, exceptional]

end Acorn.Host.Viewer
