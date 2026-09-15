/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Admission

/-!
# Standard native arithmetic boundary

Storage remains raw. Arithmetic alone crosses Lean's standard `Float32` and
`Float` boundary. Their definitions have kernel models and standard native
replacements; native replacement correctness, IEEE arithmetic mode, and the
compiler/runtime remain trusted. In particular the logical float model
canonicalizes NaNs whereas native arithmetic may choose a sign and payload.
No theorem here equates those exceptional result words across targets.

All subsequent state writes must re-enter the receiving refinement. Its
admission guarantee holds for every result word, independently of floating
accuracy or native NaN choices. Ordered folds below use the same primitive
definitions as individual updates. No fused operation, transcendental call,
or custom native replacement is introduced.
-/

namespace Acorn

namespace Binary32

/-- Standard binary32 addition; raw result bits retain the native NaN policy. -/
def add (left right : Binary32) : Binary32 :=
  ⟨(Float32.add (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

/-- Standard binary32 subtraction. -/
def sub (left right : Binary32) : Binary32 :=
  ⟨(Float32.sub (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

/-- Standard binary32 multiplication, rounded independently of later additions. -/
def mul (left right : Binary32) : Binary32 :=
  ⟨(Float32.mul (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

/-- Standard binary32 division, including exceptional operands and results. -/
def div (left right : Binary32) : Binary32 :=
  ⟨(Float32.div (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

/-- Unsigned word conversion uses the standard modeled conversion primitive. -/
def ofUInt64 (word : UInt64) : Binary32 := ⟨word.toFloat32.toBits⟩

/-- A left-to-right machine sum; reassociation is not part of this definition. -/
def sumFrom (initial : Binary32) (values : List Binary32) : Binary32 :=
  values.foldl add initial

/-- Read and add each term in input order without constructing a mapped list. -/
@[inline] def sumMap {α : Type} (initial : Binary32) (values : List α)
    (read : α → Binary32) : Binary32 :=
  values.foldl (fun total value => total.add (read value)) initial

/-- Fusion preserves every rounded addition, for every initial word and input. -/
theorem sumMap_eq {α : Type} (initial : Binary32) (values : List α)
    (read : α → Binary32) :
    sumMap initial values read = sumFrom initial (values.map read) := by
  simp [sumMap, sumFrom, List.foldl_map]

/-- Splitting an ordered sum preserves the intermediate machine accumulator. -/
theorem sumFrom_append (initial : Binary32) (first second : List Binary32) :
    sumFrom initial (first ++ second) = sumFrom (sumFrom initial first) second := by
  simp [sumFrom, List.foldl_append]

end Binary32

namespace Binary64

/-- Standard binary64 addition. -/
def add (left right : Binary64) : Binary64 :=
  ⟨(Float.add (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

/-- Standard binary64 subtraction. -/
def sub (left right : Binary64) : Binary64 :=
  ⟨(Float.sub (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

/-- Standard binary64 multiplication, with its own rounding boundary. -/
def mul (left right : Binary64) : Binary64 :=
  ⟨(Float.mul (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

/-- Standard binary64 division. -/
def div (left right : Binary64) : Binary64 :=
  ⟨(Float.div (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

/-- Unsigned word conversion through the standard modeled primitive. -/
def ofUInt64 (word : UInt64) : Binary64 := ⟨word.toFloat.toBits⟩

/-- Sign change is performed on storage, without losing any NaN payload bits. -/
def negate (value : Binary64) : Binary64 := ⟨value.bits ^^^ 0x8000000000000000⟩

/-- Raw signed machine-order key, identifying the two zero encodings. -/
def key (value : Binary64) : Int :=
  if value.bits &&& 0x8000000000000000 != 0 then -(value.magnitude : Int)
  else value.magnitude

/-- Strict comparison keeps NaNs unordered without translating their words. -/
def less (left right : Binary64) : Bool :=
  let lm := left.bits &&& 0x7fffffffffffffff
  let rm := right.bits &&& 0x7fffffffffffffff
  let ln := left.bits &&& 0x8000000000000000 != 0
  let rn := right.bits &&& 0x8000000000000000 != 0
  !left.isNaN && !right.isNaN &&
    (if ln then if rn then rm < lm else lm != 0 || rm != 0
     else if rn then false else lm < rm)

/-- Word comparison agrees with the signed-magnitude specification for every
encoding, including unordered NaNs and the two equal zero encodings. -/
theorem less_eq_key (left right : Binary64) :
    left.less right = (!left.isNaN && !right.isNaN && decide (left.key < right.key)) := by
  unfold less key
  split <;> split <;> simp_all [magnitude, UInt64.lt_iff_toNat_lt]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq]
  have lz : left.bits &&& 0x7fffffffffffffff = 0 ↔
      left.bits.toNat &&& 0x7fffffffffffffff = 0 := by
    rw [← UInt64.toNat_inj]; rfl
  have rz : right.bits &&& 0x7fffffffffffffff = 0 ↔
      right.bits.toNat &&& 0x7fffffffffffffff = 0 := by
    rw [← UInt64.toNat_inj]; rfl
  simp only [ne_eq, lz, rz]
  omega


/-- One Horner step has a separate multiply followed by a separate addition. -/
def hornerStep (argument accumulator coefficient : Binary64) : Binary64 :=
  (accumulator.mul argument).add coefficient

/-- Horner evaluation in coefficient order, from the specified accumulator. -/
def hornerFrom (argument initial : Binary64) (coefficients : List Binary64) : Binary64 :=
  coefficients.foldl (hornerStep argument) initial

/-- Every finite coefficient sequence composes through the actual accumulator,
including nonfinite inputs; no real-polynomial equivalence is assumed. -/
theorem hornerFrom_append (argument initial : Binary64) (first second : List Binary64) :
    hornerFrom argument initial (first ++ second) =
      hornerFrom argument (hornerFrom argument initial first) second := by
  simp [hornerFrom, List.foldl_append]

end Binary64

namespace Bounded32

/-- A native arithmetic update must pass through the receiving state's interval. -/
def addProjected {range : Interval32} (stored : Bounded32 range) (delta : Binary32) :
    Bounded32 range := project range (stored.value.add delta)

/-- The actual arithmetic write preserves the indexed storage invariant for
all operands; it requires no assumption that an intermediate result is finite. -/
theorem addProjected_legal {range : Interval32} (stored : Bounded32 range)
    (delta : Binary32) : range.Contains (stored.addProjected delta).value :=
  (stored.addProjected delta).legal

end Bounded32
end Acorn
