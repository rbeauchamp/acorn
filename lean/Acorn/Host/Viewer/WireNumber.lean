import Acorn.Encoding

namespace Acorn.Host.Viewer

structure WireDyadic where
  negative : Bool
  significand : Nat
  exponent : Int

structure WireDecimal where
  negative : Bool
  coefficient : Nat
  scale : Nat

def WireDyadic.numerator (value : WireDyadic) : Nat :=
  value.significand * 2 ^ value.exponent.toNat

def WireDyadic.denominator (value : WireDyadic) : Nat := 2 ^ (-value.exponent).toNat

def WireDyadic.decimal (value : WireDyadic) : WireDecimal :=
  ⟨value.negative, value.numerator * 5 ^ (-value.exponent).toNat, (-value.exponent).toNat⟩

theorem WireDyadic.decimal_exact (value : WireDyadic) :
    value.decimal.coefficient * value.denominator =
      value.numerator * 10 ^ value.decimal.scale := by
  simp only [decimal, denominator]
  rw [Nat.mul_assoc, ← Nat.mul_pow]

theorem WireDyadic.decimal_sign (value : WireDyadic) :
    value.decimal.negative = value.negative := rfl

def WireDecimal.text (value : WireDecimal) : String :=
  (if value.negative then "-" else "") ++ toString value.coefficient ++
    (if value.scale = 0 then "" else "e-" ++ toString value.scale)

def binary32Dyadic (value : Binary32) : Option WireDyadic :=
  if value.Finite then
    let exponent : Nat := value.magnitude / 2 ^ 23
    let fraction := value.magnitude % 2 ^ 23
    some ⟨value.negative, fraction + (if exponent = 0 then 0 else 2 ^ 23),
      (if exponent = 0 then -149 else (exponent : Int) - 150)⟩
  else none

def binary64Dyadic (value : Binary64) : Option WireDyadic :=
  if value.Finite then
    let exponent : Nat := value.magnitude / 2 ^ 52
    let fraction := value.magnitude % 2 ^ 52
    some ⟨value.bits &&& 0x8000000000000000 != 0,
      fraction + (if exponent = 0 then 0 else 2 ^ 52),
      (if exponent = 0 then -1074 else (exponent : Int) - 1075)⟩
  else none

def binary32Text (value : Binary32) : String :=
  match binary32Dyadic value with
  | none => "null"
  | some dyadic => dyadic.decimal.text

def binary64Text (value : Binary64) : String :=
  match binary64Dyadic value with
  | none => "null"
  | some dyadic => dyadic.decimal.text

theorem binary32Text_exceptional (value : Binary32) (exceptional : ¬ value.Finite) :
    binary32Text value = "null" := by simp [binary32Text, binary32Dyadic, exceptional]

theorem binary64Text_exceptional (value : Binary64) (exceptional : ¬ value.Finite) :
    binary64Text value = "null" := by simp [binary64Text, binary64Dyadic, exceptional]

end Acorn.Host.Viewer
