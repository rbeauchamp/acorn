import Acorn.Host.Microduck.Decimal

namespace Acorn.Host.Microduck

def Declared.milli : Scale := ⟨3, -32767, 32767, by decide⟩

def Declared.range : Scale := ⟨0, 0, 32767, by decide⟩

theorem Declared.milli_sixteen :
    -(2 ^ 15) ≤ Declared.milli.low ∧ Declared.milli.high < 2 ^ 15 := by decide

theorem Declared.range_sixteen :
    0 ≤ Declared.range.low ∧ Declared.range.high < 2 ^ 15 := by decide

structure Stamp where
  nanoseconds : Nat

inductive Policy where
  | stand
  | walk
  | held
  | homing
  | sit
  | rise
  | kickLeft
  | kickRight
  | groundPick
  | roulade
  | other
  deriving DecidableEq

structure Limits where
  deadman : Bool
  range : Bool
  finite : Bool
  other : Bool
  deriving DecidableEq

structure State where
  taken : Stamp
  joints : Vector Declared.milli.Word 15
  speeds : Option (Vector Declared.milli.Word 15)
  gravity : Vector Declared.milli.Word 3
  gyro : Vector Declared.milli.Word 3
  height : Declared.milli.Word
  policy : Policy
  fallen : Bool
  limp : Bool
  gain : Option UInt16
  limits : Limits

structure Cell where
  distance : Declared.range.Word
  status : UInt8

structure Depth where
  taken : Stamp
  cells : Vector Cell 64

def Depth.zone (depth : Depth) (row column : Fin 8) : Cell :=
  depth.cells[row.val * 8 + column.val]'(by omega)

structure Reading where
  state : State
  depth : Option Depth

def Reading.age (reading : Reading) : Option Nat :=
  reading.depth.map fun depth =>
    reading.state.taken.nanoseconds - depth.taken.nanoseconds

theorem Reading.age_present (reading : Reading) :
    reading.age.isSome = reading.depth.isSome := by
  unfold Reading.age
  cases reading.depth <;> rfl

theorem Reading.age_exact (reading : Reading) (depth : Depth)
    (paired : reading.depth = some depth)
    (older : depth.taken.nanoseconds ≤ reading.state.taken.nanoseconds) :
    ∃ age, reading.age = some age ∧
      depth.taken.nanoseconds + age = reading.state.taken.nanoseconds := by
  refine ⟨reading.state.taken.nanoseconds - depth.taken.nanoseconds, ?_, by omega⟩
  unfold Reading.age
  rw [paired]
  rfl

theorem Reading.age_ahead (reading : Reading) (depth : Depth)
    (paired : reading.depth = some depth)
    (ahead : reading.state.taken.nanoseconds ≤ depth.taken.nanoseconds) :
    reading.age = some 0 := by
  unfold Reading.age
  rw [paired]
  exact congrArg some (Nat.sub_eq_zero_of_le ahead)

end Acorn.Host.Microduck
