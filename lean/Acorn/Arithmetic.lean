import Acorn.Admission
import Acorn.Cost

namespace Acorn

namespace Binary32

def add (left right : Binary32) : Binary32 :=
  ⟨(Float32.add (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

def sub (left right : Binary32) : Binary32 :=
  ⟨(Float32.sub (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

def mul (left right : Binary32) : Binary32 :=
  ⟨(Float32.mul (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

def div (left right : Binary32) : Binary32 :=
  ⟨(Float32.div (Float32.ofBits left.bits) (Float32.ofBits right.bits)).toBits⟩

def ofUInt64 (word : UInt64) : Binary32 := ⟨word.toFloat32.toBits⟩

def sumFromCosted (initial : Binary32) (values : List Binary32) : Costed Binary32 :=
  Costed.foldl (fun total value => Costed.op .sumTerm (total.add value)) initial values

def sumFrom (initial : Binary32) (values : List Binary32) : Binary32 :=
  (sumFromCosted initial values).val

theorem sumFrom_def (initial : Binary32) (values : List Binary32) :
    sumFrom initial values = values.foldl add initial := rfl

@[inline] def sumMapCosted {α : Type} (site : Site) (initial : Binary32) (values : List α)
    (read : α → Costed Binary32) : Costed Binary32 :=
  Costed.foldl (fun total value => Costed.bind (read value) fun term =>
    Costed.op site (total.add term)) initial values

@[inline] def sumMap {α : Type} (initial : Binary32) (values : List α)
    (read : α → Binary32) : Binary32 :=
  (sumMapCosted .sumTerm initial values fun value => Costed.pure (read value)).val

theorem sumMap_def {α : Type} (initial : Binary32) (values : List α) (read : α → Binary32) :
    sumMap initial values read = values.foldl (fun total value => total.add (read value)) initial :=
  rfl

theorem sumMap_eq {α : Type} (initial : Binary32) (values : List α)
    (read : α → Binary32) :
    sumMap initial values read = sumFrom initial (values.map read) := by
  simp [sumMap_def, sumFrom_def, List.foldl_map]

theorem sumFrom_append (initial : Binary32) (first second : List Binary32) :
    sumFrom initial (first ++ second) = sumFrom (sumFrom initial first) second := by
  simp [sumFrom_def, List.foldl_append]

end Binary32

namespace Binary64

def add (left right : Binary64) : Binary64 :=
  ⟨(Float.add (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

def sub (left right : Binary64) : Binary64 :=
  ⟨(Float.sub (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

def mul (left right : Binary64) : Binary64 :=
  ⟨(Float.mul (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

def div (left right : Binary64) : Binary64 :=
  ⟨(Float.div (Float.ofBits left.bits) (Float.ofBits right.bits)).toBits⟩

def ofUInt64 (word : UInt64) : Binary64 := ⟨word.toFloat.toBits⟩

def negate (value : Binary64) : Binary64 := ⟨value.bits ^^^ 0x8000000000000000⟩

def key (value : Binary64) : Int :=
  if value.bits &&& 0x8000000000000000 != 0 then -(value.magnitude : Int)
  else value.magnitude

def less (left right : Binary64) : Bool :=
  let lm := left.bits &&& 0x7fffffffffffffff
  let rm := right.bits &&& 0x7fffffffffffffff
  let ln := left.bits &&& 0x8000000000000000 != 0
  let rn := right.bits &&& 0x8000000000000000 != 0
  !left.isNaN && !right.isNaN &&
    (if ln then if rn then rm < lm else lm != 0 || rm != 0
     else if rn then false else lm < rm)

theorem less_eq_key (left right : Binary64) :
    left.less right = (!left.isNaN && !right.isNaN && decide (left.key < right.key)) := by
  have order (a b : Binary64) :
      a.bits &&& 0x7fffffffffffffff < b.bits &&& 0x7fffffffffffffff ↔
        a.magnitude < b.magnitude :=
    UInt64.lt_iff_toNat_lt
  have zero (a : Binary64) : a.bits &&& 0x7fffffffffffffff = 0 ↔ a.magnitude = 0 := by
    rw [← UInt64.toNat_inj]
    exact Iff.rfl
  unfold less key
  change (!left.isNaN && !right.isNaN &&
    (if left.bits &&& 0x8000000000000000 != 0 then
      if right.bits &&& 0x8000000000000000 != 0 then
        decide (right.bits &&& 0x7fffffffffffffff < left.bits &&& 0x7fffffffffffffff)
      else (left.bits &&& 0x7fffffffffffffff != 0 || right.bits &&& 0x7fffffffffffffff != 0)
    else if right.bits &&& 0x8000000000000000 != 0 then false
    else decide (left.bits &&& 0x7fffffffffffffff < right.bits &&& 0x7fffffffffffffff))) = _
  congr 1
  cases left.bits &&& 0x8000000000000000 != 0 <;>
    cases right.bits &&& 0x8000000000000000 != 0 <;>
    simp only [↓reduceIte, Bool.false_eq_true] <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, order, zero,
      Bool.false_eq_true, false_iff]
  · constructor <;> intro _ <;> omega
  · intro _
    omega
  · constructor
    · intro _
      omega
    · intro below
      by_cases none : left.magnitude = 0
      · exact .inr (by omega)
      · exact .inl none
  · constructor <;> intro _ <;> omega

def Less (left right : Binary64) : Prop := ¬left.IsNaN ∧ ¬right.IsNaN ∧ left.key < right.key

theorem less_iff (left right : Binary64) : left.less right = true ↔ left.Less right := by
  rw [less_eq_key]
  simp only [Less, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, ← isNaN_iff,
    Bool.not_eq_true, and_assoc]

instance (left right : Binary64) : Decidable (left.Less right) :=
  decidable_of_iff _ (less_iff left right)

def hornerStep (argument accumulator coefficient : Binary64) : Binary64 :=
  (accumulator.mul argument).add coefficient

def hornerFrom (argument initial : Binary64) (coefficients : List Binary64) : Binary64 :=
  coefficients.foldl (hornerStep argument) initial

theorem hornerFrom_append (argument initial : Binary64) (first second : List Binary64) :
    hornerFrom argument initial (first ++ second) =
      hornerFrom argument (hornerFrom argument initial first) second := by
  simp [hornerFrom, List.foldl_append]

end Binary64

namespace Bounded32

def addProjected {range : Interval32} (stored : Bounded32 range) (delta : Binary32) :
    Bounded32 range := project range (stored.value.add delta)

theorem addProjected_legal {range : Interval32} (stored : Bounded32 range)
    (delta : Binary32) : range.Contains (stored.addProjected delta).value :=
  (stored.addProjected delta).legal

end Bounded32
end Acorn
