/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Microduck.Decimal

/-!
# What the Microduck senses, as bounded integers

The Microduck's daemons publish two streams on one monotonic clock of their own: the
state of the body at 50 Hz, and an 8 by 8 grid of depths at about 14 Hz. The record of
both, from one observed run of the vendor's simulator, is at
https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6051119525. It labels a fact
as observed in that run, or as read in the vendor's source and not exercised. This
module is the form a host keeps the two streams in: a `State`, a `Depth` and their
pair, a `Reading`. No value here is a float.

A quantity that the daemon writes as a decimal fraction is a `Scale.Word`, an integer
with the proof of its bounds. Two scales are declared, and each fits sixteen bits
(`Declared.milli_sixteen`, `Declared.range_sixteen`):

- `Declared.milli` keeps three decimal places and saturates at plus and minus 32,767
  thousandths. It holds angles in radians, rates in radians per second, the components
  of the gravity direction, and a height in metres.
- `Declared.range` keeps whole millimetres from 0 to 32,767. It holds a depth, which
  the daemon writes as a signed sixteen-bit integer.

A quantity that the daemon writes as an unsigned integer has no scale. The servo gain
and the status of a depth zone keep the daemon's width, sixteen bits and eight. A stamp
of the daemons' clock, which the daemon writes in sixty-four bits, is a natural number
with no width, as an `Instant` of `Acorn.Timing` is, and so is the age of a depth frame.

A field whose absence means that nothing was measured is an `Option`, and absence is
not a zero. The joint rates are absent when the daemon does not report them and the
servo gain is absent when the daemon sends null; both cases are read in the vendor's
source, and every frame of the observed run had both. A reading has no depth frame
before the first one arrives, or on a body with no depth sensor; the vendor's
documentation says most bodies have none
(https://github.com/rbeauchamp/acorn/issues/70#issuecomment-5976760764).

A `Reading` pairs a state frame with a depth frame. The two streams are not
synchronised, so the reading states the age of its depth frame, `Reading.age`: the time
from the depth frame to the state frame, and zero for a depth frame that is not the
older (`Reading.age_exact`, `Reading.age_ahead`). It is absent exactly when the depth
frame is (`Reading.age_present`). A `Stamp` is an instant of the daemons' clock. It is
not the `Instant` of a host's clock that `Acorn.Timing` counts cycles on: a host on the
daemons' machine reads the same clock, and a host that reaches the daemons from another
machine does not, so this module relates the two in no way.

The two scales and the choice of the fields are authored. Nothing here reaches the
agent, so nothing here is on its action path. A frame of the interface is built on a
reading by a later module, which declares its channels and signals under departures D1
and D5 of `docs/learned-only-binding.md`; what a reading leaves out, that frame cannot
carry.

This module defines no text form. The function that reads a frame of the daemon into
these types is not built. It owes the name of each field, the order of each array, the
table of labels behind `Policy` and of names behind `Limits`, and the refusal of a gain
or a status that its type does not hold. Not kept, by decision: the time in
seconds beside the stamp, the pose of each body link and of each sensor, the commanded
joint positions, the head command, the orientation as a quaternion (the gravity
direction holds the tilt, and the heading is arbitrary at each start), the motor
currents (in the simulator they are a stand-in computed from the actuator force), the
horizontal position and the heading of the odometry (their frame is chosen at each
start), the echo of the velocity command, the rate and the overruns of the control
loop, two objects that the daemon sends only while optional features run, the battery,
which is a separate request, and of a depth frame its sequence number, its second
stamp and its stated numbers of rows and columns.
-/
namespace Acorn.Host.Microduck

/-- Thousandths, in sixteen bits: three decimal places, saturating at plus and minus
32,767. -/
def Declared.milli : Scale := ⟨3, -32767, 32767, by decide⟩

/-- Whole millimetres of depth, in sixteen bits: no decimal place, from 0 to 32,767. -/
def Declared.range : Scale := ⟨0, 0, 32767, by decide⟩

/-- Every thousandth of `Declared.milli` is a signed sixteen-bit integer. -/
theorem Declared.milli_sixteen :
    -(2 ^ 15) ≤ Declared.milli.low ∧ Declared.milli.high < 2 ^ 15 := by decide

/-- Every depth of `Declared.range` is a signed sixteen-bit integer that is not
negative. -/
theorem Declared.range_sixteen :
    0 ≤ Declared.range.low ∧ Declared.range.high < 2 ^ 15 := by decide

/-- An instant of the daemons' monotonic clock, which a state frame and a depth frame
are both stamped on. It is a type of its own, so it cannot stand where an instant of a
host's clock is expected. -/
structure Stamp where
  /-- Nanoseconds from the clock's own zero. -/
  nanoseconds : Nat

/-- What drove a control tick, as a state frame labels it: the ten labels of the observed
run, and one value for every other label. -/
inductive Policy where
  /-- The label `stand`: the standing network. -/
  | stand
  /-- The label `walk`: the walking network. -/
  | walk
  /-- The label `held`, observed while the policy was disabled. -/
  | held
  /-- The label `homing`, observed for two seconds after the daemon's `robot.init`. -/
  | homing
  /-- The label `sit`, observed from the toggle that sat the body down and for as long
  as it sat. -/
  | sit
  /-- The label `rise`, observed for one second after the toggle that stood the body
  up. -/
  | rise
  /-- The label `kick_left`: the kick with the left foot. -/
  | kickLeft
  /-- The label `kick_right`: the kick with the right foot. -/
  | kickRight
  /-- The label `ground_pick`: the pick from the ground. -/
  | groundPick
  /-- The label `roulade`: the forward roll. -/
  | roulade
  /-- A label outside this table. -/
  | other
  deriving DecidableEq

/-- The names in a state frame's list of what limited the daemon's commands at a control
tick. The daemon leaves the list out when it is empty, which is every field false. -/
structure Limits where
  /-- The name `deadman`, observed when the daemon replaced a velocity that was too old
  by zero. -/
  deadman : Bool
  /-- The name `joint_range`, observed in four frames while the body stood up after its
  policy was enabled again, for example with a target of the neck at -3.25 rad. The
  vendor's source clamps a target to the range of its actuator. -/
  range : Bool
  /-- The name `not_finite`, read in the vendor's source, where a target that is not
  finite is refused. Not observed. -/
  finite : Bool
  /-- A name outside these three. -/
  other : Bool
  deriving DecidableEq

/-- One frame of the state stream. Arrays of fifteen follow the daemon's order of the
joints: the left leg (hip yaw, hip roll, hip pitch, knee, ankle), the neck pitch, the
head (pitch, yaw, roll), the mouth, and the right leg in the order of the left. -/
structure State where
  /-- The stamp of the control tick. -/
  taken : Stamp
  /-- The measured angle of each joint, in thousandths of a radian. -/
  joints : Vector Declared.milli.Word 15
  /-- The measured rate of each joint, in thousandths of a radian per second. Absent
  when the daemon does not report rates. -/
  speeds : Option (Vector Declared.milli.Word 15)
  /-- The direction of gravity in the frame of the trunk (forward, left, up), in
  thousandths. A trunk that is upright reads about 0, 0, -1000. -/
  gravity : Vector Declared.milli.Word 3
  /-- The turning rate of the trunk about its three axes, in thousandths of a radian
  per second. -/
  gyro : Vector Declared.milli.Word 3
  /-- The height of the trunk by the daemon's contact odometry, in thousandths of a
  metre. It is relative and the daemon does not correct it. -/
  height : Declared.milli.Word
  /-- What drove the tick. -/
  policy : Policy
  /-- The daemon's report that the body has fallen. -/
  fallen : Bool
  /-- The daemon's report that the body is in its limp fall. -/
  limp : Bool
  /-- The position gain of the servos, as the register holds it. Absent when the daemon
  sends null. -/
  gain : Option UInt16
  /-- What limited the daemon's commands. -/
  limits : Limits

/-- One zone of a depth frame. -/
structure Cell where
  /-- The distance of the return, in millimetres. It has a meaning only with a status
  that says the return is valid. -/
  distance : Declared.range.Word
  /-- The sensor's status of the zone. The simulator sent 5 for a valid return and 255
  for nothing in range, and no other value; the record says a sensor sends more
  codes. -/
  status : UInt8

/-- One frame of the depth stream: eight rows of eight zones, row by row. Row 0 is the
top row, and column 0 is at the left of the sensor. -/
structure Depth where
  /-- The stamp of the frame, on the clock of a state frame's stamp. -/
  taken : Stamp
  /-- The zones, row by row. -/
  cells : Vector Cell 64

/-- The zone of a row and a column. -/
def Depth.zone (depth : Depth) (row column : Fin 8) : Cell :=
  depth.cells[row.val * 8 + column.val]'(by omega)

/-- What a host holds for one percept: a state frame, and the depth frame it is paired
with, if there is one. -/
structure Reading where
  /-- The state frame. -/
  state : State
  /-- The depth frame. Absent before the first one arrives, and on a body with no depth
  sensor. -/
  depth : Option Depth

/-- The age of the depth frame of a reading, in nanoseconds: the time from the depth
frame to the state frame, and zero for a depth frame that is not the older. -/
def Reading.age (reading : Reading) : Option Nat :=
  reading.depth.map fun depth =>
    reading.state.taken.nanoseconds - depth.taken.nanoseconds

/-- A reading has an age exactly when it has a depth frame. -/
theorem Reading.age_present (reading : Reading) :
    reading.age.isSome = reading.depth.isSome := by
  unfold Reading.age
  cases reading.depth <;> rfl

/-- **The age is the time from the depth frame to the state frame.** For every reading
whose depth frame is not after its state frame, the stamp of the depth frame plus the
age is the stamp of the state frame. -/
theorem Reading.age_exact (reading : Reading) (depth : Depth)
    (paired : reading.depth = some depth)
    (older : depth.taken.nanoseconds ≤ reading.state.taken.nanoseconds) :
    ∃ age, reading.age = some age ∧
      depth.taken.nanoseconds + age = reading.state.taken.nanoseconds := by
  refine ⟨reading.state.taken.nanoseconds - depth.taken.nanoseconds, ?_, by omega⟩
  unfold Reading.age
  rw [paired]
  rfl

/-- A depth frame that is not older than the state frame has the age zero. -/
theorem Reading.age_ahead (reading : Reading) (depth : Depth)
    (paired : reading.depth = some depth)
    (ahead : reading.state.taken.nanoseconds ≤ depth.taken.nanoseconds) :
    reading.age = some 0 := by
  unfold Reading.age
  rw [paired]
  exact congrArg some (Nat.sub_eq_zero_of_le ahead)

end Acorn.Host.Microduck
