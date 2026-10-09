/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Signals
import Acorn.Host.Microduck.Bridge
import Acorn.Host.Microduck.Sensing

/-!
# The Microduck as one instance of the interface

This module binds the Microduck world to the interface between the agent and a world:
the interface value, and the adapter that turns a reading of the body into a percept. It
is authored, and it declares what it authors under `docs/learned-only-binding.md`: the
channels and the symbols of a frame (D1), the prediction signals (D5) and the event of
the goal (D8). It authors no subtask potential: every potential of a frame is false, so
a profile whose subtasks are declared has none that can hold in this world. What a
frame can carry is bounded by the reading of `Acorn.Host.Microduck.Sensing`, whose kept
fields and scales are authored in that host module. Each signal carries its declared
origin in its value. The layout has no type of its own to carry one: its declaration is
the entry of the register and the inventory of the departure audit.

The executing code that builds a percept is the host's sensing, `Acorn.Host.Microduck.Idle.sense`,
which the loop of `Acorn.Host.Microduck.Loop` calls and the executable of
`Acorn.Host.Microduck.Driver` runs.
A host owes the adapter four things: the reading, what became of the preceding action,
whether its release was late, and the state of the goal's latch, which starts disarmed
and which `arm` advances at each reading. `Acorn.Host.Microduck.Idle.sense` gives the
four as pure definitions, with the latch held in the state of the host, so that the
latch of every reachable host is the fold of `arm` over the readings it sensed
(`Acorn.Host.Microduck.Reached.latch`).

## The interface value

`interface` has the 64 zones of a depth frame as its symbol array, four signals after the
agent's own reward question, ten actions, at most 48 words, prediction feedback channels
from `0x50`, and the timing of a wall clock with the declared pace (`interface_timing`).
Its count of actions is ten (`interface_actions`), the positions of the action table of
`Acorn.Host.Microduck.Action`, whose `Action.index` and `Action.named` are inverse to
each other.

## The words

A frame has one word for each kept quantity of a reading and two for host events. A word
is a position of the layout and a value; `channel` gives the
channel of a position, from `0x100`. No such channel is a prediction feedback channel
(`channel_clear`), two positions have two channels (`channel_injective`), and each
position carries at most one word of a frame (`entries_distinct`).

| Positions | Word | Value |
|---|---|---|
| 0 to 14 | the angle of each joint | level, in steps of 0.1 rad |
| 15 to 29 | the rate of each joint, when the reading has rates | level, in steps of 0.5 rad/s |
| 30 | whether the reading has rates | 0 or 1 |
| 31 to 33 | the gravity direction | level, in steps of 0.1 |
| 34 to 36 | the turning rate of the trunk | level, in steps of 0.25 rad/s |
| 37 | the height of the trunk | level, in steps of 1 cm |
| 38 | the label of what drove the tick | its code, 0 to 10 |
| 39, 40 | the daemon's reports of a fall and of a limp fall | 0 or 1 |
| 41 | whether the reading has a servo gain | 0 or 1 |
| 42 | the servo gain, when the reading has one | in steps of 8 |
| 43 | the four limit names | one bit for each |
| 44 | whether the reading has a depth frame | 0 or 1 |
| 45 | the age of the depth frame, when there is one | in steps of 20 ms, at most 25 |
| 46 | what became of the preceding action | 0 before any action, then 1 to 5 |
| 47 | whether the release of the preceding action was late | 0 or 1 |

A level is the count of whole steps from the least value of the scale of thousandths, so
it is never negative. The coder hashes a channel and a value into a feature and does not
generalise between two values, so a step is the resolution the agent has of a quantity.
The steps are authored numbers of this module. None has been qualified by an
experiment. The five outcomes of an action and the case before any action have six
values of their word (`became_injective`), so a refused action, an accepted action that
was not executed and an action whose answer was not complete are three words.

Absence is a word and not a zero. The presence word of the rates, of the gain and of the
depth frame is one when the reading has the quantity and zero when it does not
(`entries_presence`), and a reading without rates has no word on a rate position, one
without a gain none on the gain position, and one without a depth frame none on the age
position (`entries_rates`, `entries_gain`, `entries_depth`).

## The symbols

The symbol array has one symbol for each zone of the depth frame, row by row
(`symbols_zone`). The symbol of a zone with a valid return is one more than its distance
in whole decimetres; the symbol of a zone with another status is `0x1000` plus the
status, whatever its distance. So a symbol is below `0x1000` exactly for a valid return
(`symbol_valid`). With no depth frame every symbol is `missing` (`symbols_missing`),
which is the symbol of no zone (`symbol_present`). On a body with no depth sensor every
symbol is therefore that one constant, and every generated unit over the symbols is
constant; another use of the symbol positions for such a body is not built.

## The goal

The body is **near** an obstacle when its trunk is upright, its depth frame is under
half a second old, and a zone of the two top rows has a valid return under 300 mm. It is
**clear** of obstacles when the trunk is upright, the depth frame is as fresh, and every
zone of the two top rows has the status 255, which the simulator sends for nothing in
range, or a valid return of at least 400 mm. The trunk is upright when the gravity word
of the frame for the upward component, on position 33, is below the level of -0.95, which
is 318 (`entries_gravity`). In thousandths that is an upward component below -967
(`upright_iff`): a level is a step of 0.1 counted from the least value of the scale, so
the levels do not separate -0.95 from -0.967, and a reading whose upward component is
from -967 to -951 thousandths is not upright. The depth frame is fresh exactly when the
age word of the frame is below its cap (`fresh_level`). So both tests are functions of
what the frame gives the agent: the gravity word, the age word and the symbols of the two
top rows (`near_symbols`, `clear_symbols`). No reading is both (`near_clear`).

The goal has a latch. A near reading disarms it, a clear reading arms it, and any other
reading leaves it as it was (`arm_near`, `arm_clear`, `arm_keeps`). The event of the
goal is a near reading while the goal is armed (`achieved_iff`), and the reward of a
percept is one at that event and zero otherwise. So after a near reading no reading is
the event until a clear one, whatever lies between (`arm_held`): two events need a clear
reading between them. That is the whole guarantee. A reading is not clear while a zone of
the two top rows has a valid return under 400 mm or a status other than 5 and 255, while
the trunk is not upright, or while the depth frame is not fresh. So a return that wavers
between 300 mm and 400 mm gives no second event, and neither does a trunk that wavers
across the upright threshold in front of an obstacle. The record gives the noise of a
depth as 3 mm plus 20 mm for each 4 m of range, read in the vendor's source and not
observed.

A reading whose top zones all have the status 255 is clear, so the guarantee says
nothing against a sensor whose status drops out. Every top zone at 255, then one valid
return at 100 mm, then that zone at 255, then the return again, is two events with no
retreat.

The four signals are whether the body is near an obstacle and whether the daemon reports
a fall, each at the horizons 0.9 and 0.99.

## Why these tests, and what they do not show

A minimum over the whole grid reads the floor: the record of the observed run, at
https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6051119525, observed the lower
rows returning a bare floor at 0.41 to 3.35 m and the two top rows returning nothing.

That a flat floor is not read as near is argued from that record's geometry. It is not
machine-checked, and these are its inputs: the sensor is 0.082 m forward, 0.021 m to the
left and 0.113 m up from the origin of the trunk, pitched 14.2 degrees down and rolled 2.8
degrees at rest; its field of view is 45 degrees over eight rows; and the origin of the
trunk is 0.116 m above the floor for a standing body and 0.061 m for a sitting one
(https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895). On the axis the
lower edge of row 1 points 2.95 degrees below the horizontal, and the roll adds at most
1.1 degrees at the side of the row, so no beam of the two top rows points more than 4.1
degrees below the horizontal at rest. An upright trunk is tilted by less than 14.8
degrees, and a tilt lowers a beam by at most its own angle, so no such beam points more
than 18.9 degrees below the horizontal, and a flat floor is returned at more than 3.08
times the height of the sensor. At a tilt of 14.8 degrees in the least favourable
direction the sensor is at least 203 mm above the floor for a standing body and 148 mm
for a sitting one, so a flat floor is returned at more than 450 mm. The argument assumes
a flat floor, a gravity word that is a unit direction, the head at its rest pose, and a
trunk whose origin stays at its standing or sitting height while it tilts.

Nearness has no converse. For a standing body with an upright trunk and the head at
rest, the lowest beam of the two top rows passes about 0.2 m above the floor at 300 mm,
so a lower obstacle is not near for such a body. A sitting body's sensor is lower, at
0.174 m, and so are its beams.

The study microduck-depth-and-tilt (docs/studies/microduck-depth-and-tilt) measured two
quantities in the simulator: every state frame of a scripted walk forward and of turns on a
bare floor was upright, the trunk tilting by at most 4.9 degrees, and at rest in front of a
wall no clear frame came between two near ones. The bound of an upright trunk does not move
to the next level of the gravity word, at which a sitting body could read a flat floor as
near (the study's protocol makes the argument). In the simulator a zone's status is 255 only
when its ray meets nothing within 4 m, so it does not drop out at close range.

UNKNOWN, because no run has measured them: how far a learning agent's actions, skills and
falls tilt the trunk; where the standing and walking networks and each skill hold the head,
which they drive; the height of the trunk during a skill; which status a robot's sensor sends
for a usable return and for nothing in range, and whether it drops out at close range; what
the two top rows return on a slope, a step or a soft floor; and how often the event occurs
for a body that does not approach anything. A body with no depth sensor is never near and
never clear, so this goal gives it no reward.
-/
namespace Acorn.Handcrafted.Microduck
open Features
open Acorn.Host.Microduck (Reading State Depth Cell Policy Limits Outcome)

/-- The channel of the word at a position of the layout. Every word of a frame is on one
of these 256 channels, which start at `0x100`. -/
def channel (index : Fin 256) : UInt64 := 0x100 + index.val.toUInt64

/-- The level of a thousandth: the count of whole steps from the least value of the
scale. -/
def level (step : Nat) (word : Host.Microduck.Declared.milli.Word) : UInt64 :=
  ((word.val - Host.Microduck.Declared.milli.low).toNat / step).toUInt64

/-- The step of the level of a joint angle: a tenth of a radian. -/
def Declared.angle : Nat := 100

/-- The step of the level of a joint rate: half a radian per second. -/
def Declared.rate : Nat := 500

/-- The step of the level of a component of the gravity direction: a tenth. -/
def Declared.share : Nat := 100

/-- The step of the level of a turning rate of the trunk: a quarter of a radian per
second. -/
def Declared.turn : Nat := 250

/-- The step of the level of the height of the trunk: a centimetre. -/
def Declared.rise : Nat := 10

/-- The step of the level of the age of a depth frame: twenty milliseconds. -/
def Declared.stale : Nat := 20000000

/-- The greatest level of the age of a depth frame: half a second and more. -/
def Declared.oldest : Nat := 25

/-- The code of a label of what drove a control tick. -/
def code : Policy → UInt64
  | .stand => 0
  | .walk => 1
  | .held => 2
  | .homing => 3
  | .sit => 4
  | .rise => 5
  | .kickLeft => 6
  | .kickRight => 7
  | .groundPick => 8
  | .roulade => 9
  | .other => 10

/-- One for a true flag and zero for a false one. -/
def flag (value : Bool) : UInt64 := if value then 1 else 0

/-- The four limit names as one word: one bit for each. -/
def limited (limits : Limits) : UInt64 :=
  flag limits.deadman + 2 * flag limits.range + 4 * flag limits.finite + 8 * flag limits.other

/-- The code of what became of the preceding action: zero before any action, and one to five
for the five outcomes, five for an action whose answer was not complete. -/
def became : Option Outcome → UInt64
  | none => 0
  | some .executed => 1
  | some .unchanged => 2
  | some .refused => 3
  | some .unexecuted => 4
  | some .unanswered => 5

/-- The level of the gravity word for the upward component below which the trunk counts as
upright: the level of -950 thousandths, which is 318. -/
def Declared.upright : UInt64 := level Declared.share ⟨-950, by decide⟩

/-- Whether the trunk is upright: the gravity word of the frame for the upward component
is below `Declared.upright`. -/
def upright (state : State) : Bool :=
  decide (level Declared.share (state.gravity.get 2) < Declared.upright)

/-- The words of the joint angles, on positions 0 to 14. -/
def jointEntries (state : State) : List (Fin 256 × UInt64) :=
  (List.finRange 15).map fun joint =>
    (⟨joint.val, by omega⟩, level Declared.angle (state.joints.get joint))

/-- The words of the joint rates: the presence word on position 30, and with rates one
word for each joint on positions 15 to 29. -/
def rateEntries : Option (Vector Host.Microduck.Declared.milli.Word 15) →
    List (Fin 256 × UInt64)
  | none => [(30, 0)]
  | some speeds => (30, 1) :: (List.finRange 15).map fun joint =>
      (⟨15 + joint.val, by omega⟩, level Declared.rate (speeds.get joint))

/-- The words of the trunk: the gravity direction on positions 31 to 33, the turning
rate on 34 to 36 and the height on 37. -/
def trunkEntries (state : State) : List (Fin 256 × UInt64) :=
  ((List.finRange 3).map fun axis =>
      ((⟨31 + axis.val, by omega⟩ : Fin 256), level Declared.share (state.gravity.get axis))) ++
    ((List.finRange 3).map fun axis =>
      ((⟨34 + axis.val, by omega⟩ : Fin 256), level Declared.turn (state.gyro.get axis))) ++
    [(37, level Declared.rise state.height)]

/-- The words of the servo gain: the presence word on position 41, and with a gain its
level in steps of eight on position 42. -/
def gainEntries : Option UInt16 → List (Fin 256 × UInt64)
  | none => [(41, 0)]
  | some gain => [(41, 1), (42, (gain.toNat / 8).toUInt64)]

/-- The words of the depth frame's age: the presence word on position 44, and with a depth
frame the level of its age on position 45, which stops at `Declared.oldest`. -/
def ageEntries : Option Nat → List (Fin 256 × UInt64)
  | none => [(44, 0)]
  | some age => [(44, 1), (45, (min (age / Declared.stale) Declared.oldest).toUInt64)]

/-- Every word of a frame as a position of the layout and a value: the body, then the
two host events, which are what became of the preceding action and whether its release
was late. -/
def entries (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    List (Fin 256 × UInt64) :=
  jointEntries reading.state ++ rateEntries reading.state.speeds ++
    trunkEntries reading.state ++
    [(38, code reading.state.policy), (39, flag reading.state.fallen),
      (40, flag reading.state.limp)] ++
    gainEntries reading.state.gain ++ [(43, limited reading.state.limits)] ++
    ageEntries reading.age ++
    [(46, became outcome), (47, flag late)]

/-- The words of a frame. -/
def words (reading : Reading) (outcome : Option Outcome) (late : Bool) : List SensorWord :=
  (entries reading outcome late).map fun entry => ⟨channel entry.1, entry.2⟩

/-- Most words of one frame. -/
def wordBound : Nat := 48

/-- The symbol array: the 64 zones of a depth frame. -/
def shape : PatchShape := ⟨64, by decide, by decide⟩

/-- The symbol of a zone with no depth frame. -/
def missing : UInt64 := 0xFFFF

/-- The symbol of a zone: for a valid return, one more than its distance in whole
decimetres; for another status, `0x1000` plus the status. -/
def symbol (cell : Cell) : UInt64 :=
  if cell.status = 5 then 1 + (cell.distance.val.toNat / 100).toUInt64
  else 0x1000 + cell.status.toUInt64

/-- The symbols of a frame: the symbol of each zone, row by row, and `missing` at every
position with no depth frame. -/
def symbols : Option Depth → Patch shape
  | none => Vector.replicate 64 missing
  | some depth => depth.cells.map symbol

/-- The distance in millimetres under which a return in the two top rows counts as
near. -/
def Declared.near : Int := 300

/-- The distance in millimetres from which a return in the two top rows counts as clear. -/
def Declared.clear : Int := 400

/-- The age in nanoseconds under which a depth frame counts as fresh: the age at which the
age word of a frame reaches its cap, half a second. -/
def Declared.fresh : Nat := Declared.stale * Declared.oldest

/-- Whether a reading has a fresh depth frame: it has one, and its age is under
`Declared.fresh`. -/
def fresh (reading : Reading) : Bool :=
  reading.age.elim false fun age => decide (age < Declared.fresh)

/-- Whether a depth frame has a valid return under `Declared.near` in its two top rows. -/
def close (depth : Depth) : Bool :=
  (List.finRange 8).any fun row => (List.finRange 8).any fun column =>
    decide (row.val < 2) && (depth.zone row column).status == 5 &&
      decide ((depth.zone row column).distance.val < Declared.near)

/-- Whether every zone of the two top rows of a depth frame has nothing in range, or a
valid return of at least `Declared.clear`. -/
def distant (depth : Depth) : Bool :=
  (List.finRange 8).all fun row => (List.finRange 8).all fun column =>
    !decide (row.val < 2) || (depth.zone row column).status == 255 ||
      ((depth.zone row column).status == 5 &&
        decide (Declared.clear ≤ (depth.zone row column).distance.val))

/-- Whether the body is near an obstacle: it is upright, its depth frame is fresh, and
that frame has a valid return under the declared distance in the two top rows. -/
def near (reading : Reading) : Bool :=
  upright reading.state && fresh reading && reading.depth.elim false close

/-- Whether the body is clear of obstacles: it is upright, its depth frame is fresh, and
every zone of the two top rows of that frame has nothing in range or a valid return of at
least the declared distance. -/
def clear (reading : Reading) : Bool :=
  upright reading.state && fresh reading && reading.depth.elim false distant

/-- The event of the goal: the goal is armed and the body is near an obstacle. -/
def achieved (armed : Bool) (reading : Reading) : Bool :=
  armed && near reading

/-- Whether the goal is armed after a reading: a near reading disarms it, a clear reading
arms it, and any other reading leaves it as it was. -/
def arm (armed : Bool) (reading : Reading) : Bool :=
  if near reading then false else armed || clear reading

/-- The four signals the Microduck world supplies after the agent's reward question:
whether the body is near an obstacle, at the short and the long horizon, and whether the
daemon reports a fall, at the same two. -/
abbrev signals : List Discount := [.g90, .g99, .g90, .g99]

/-- The values of the four signals of a reading. -/
def cumulants (reading : Reading) : Cumulants signals :=
  .cons (some .cumulants) (indicator (near reading)) <|
    .cons (some .cumulants) (indicator (near reading)) <|
      .cons (some .cumulants) (indicator reading.state.fallen) <|
        .cons (some .cumulants) (indicator reading.state.fallen) .nil

/-- The Microduck world accepts ten primitive actions. -/
abbrev actions : Word.Count := ⟨10, by decide⟩

/-- The Microduck world's interface: the 64 zones of a depth frame as the symbol array,
four signals after the agent's reward question, ten actions, at most 48 words, prediction
feedback channels from `0x50`, and the timing of a wall clock with the declared pace. -/
abbrev interface : Interface :=
  ⟨shape, signals, actions, wordBound, 0x50, .wallClock Host.Microduck.Declared.pace⟩

/-- No channel of the layout is a prediction feedback channel. -/
theorem channel_clear (index : Fin 256) : interface.reserved (channel index) = false := by
  have bound := index.isLt
  have apart : ¬(0x100 + index.val.toUInt64 - 0x50 : UInt64).toNat < 5 := by
    rw [UInt64.toNat_sub, UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    omega
  exact decide_eq_false apart

/-- A frame has at most the declared number of words, for every reading and host event. -/
theorem words_length (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    (words reading outcome late).length ≤ wordBound := by
  have rates : (rateEntries reading.state.speeds).length ≤ 16 := by
    unfold rateEntries
    split <;> simp [List.length_finRange]
  have gain : (gainEntries reading.state.gain).length ≤ 2 := by
    unfold gainEntries
    split <;> simp
  have age : (ageEntries reading.age).length ≤ 2 := by
    unfold ageEntries
    split <;> simp
  simp only [words, entries, jointEntries, trunkEntries, wordBound, List.length_map,
    List.length_append, List.length_finRange, List.length_cons, List.length_nil]
  omega

/-- No word of a frame is on a prediction feedback channel. -/
theorem words_clear (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ∀ word ∈ words reading outcome late, interface.reserved word.channel = false := by
  intro word member
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  exact channel_clear entry.1

/-- One frame: the words of the reading and of the two host events, the symbols of the
depth frame, the four signals, no declared potential, and the event of the goal, for the
state of the goal's latch before the reading. -/
def frame (armed : Bool) (reading : Reading) (outcome : Option Outcome)
    (late : Bool) : Frame interface where
  words := words reading outcome late
  bounded := words_length reading outcome late
  clear := words_clear reading outcome late
  symbols := symbols reading.depth
  signals := cumulants reading
  potentials := Vector.replicate Acorn.FeatureConstants.skillCount false
  achieved := achieved armed reading

/-- The percept of one step: the frame, and a reward of one for the event of the goal and
of zero without it. -/
def percept (armed : Bool) (reading : Reading) (outcome : Option Outcome)
    (late : Bool) : Percept interface :=
  ⟨frame armed reading outcome late, indicator (achieved armed reading)⟩

/-- **Each position of the layout carries at most one word of a frame.** For every
reading and host event, the positions of the words are pairwise different. -/
theorem entries_distinct (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ((entries reading outcome late).map Prod.fst).Nodup := by
  unfold entries
  cases reading.state.speeds <;> cases reading.state.gain <;> cases reading.age <;>
    simp only [jointEntries, rateEntries, trunkEntries, gainEntries, ageEntries,
      List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def] <;>
    decide

/-- **The symbol of a zone is below `0x1000` exactly for a valid return.** -/
theorem symbol_valid (cell : Cell) : (symbol cell).toNat < 0x1000 ↔ cell.status = 5 := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  unfold symbol
  split
  · rename_i valid
    refine ⟨fun _ => valid, fun _ => ?_⟩
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    omega
  · rename_i other
    refine ⟨fun small => ?_, fun valid => absurd valid other⟩
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64] at small
    simp only [UInt64.toNat_ofNat] at small
    omega

/-- **No zone has the symbol of a missing depth frame.** -/
theorem symbol_present (cell : Cell) : symbol cell ≠ missing := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  intro same
  have value := congrArg UInt64.toNat same
  unfold symbol missing at value
  split at value
  · rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat'] at value
    simp only [UInt64.toNat_ofNat] at value
    omega
  · rw [UInt64.toNat_add, UInt8.toNat_toUInt64] at value
    simp only [UInt64.toNat_ofNat] at value
    omega

/-- With no depth frame every symbol is `missing`. -/
theorem symbols_missing (position : Fin shape.inputs) :
    (symbols none).get position = missing := by
  show (Vector.replicate 64 missing)[position.val]'position.isLt = missing
  exact Vector.getElem_replicate _

/-- With a depth frame the symbol at the position of a row and a column is the symbol of
that zone. -/
theorem symbols_zone (depth : Depth) (row column : Fin 8) :
    (symbols (some depth)).get ⟨row.val * 8 + column.val, by show _ < 64; omega⟩ =
      symbol (depth.zone row column) := by
  have inside : row.val * 8 + column.val < 64 := by omega
  show (depth.cells.map symbol)[row.val * 8 + column.val]'inside =
    symbol (depth.cells[row.val * 8 + column.val]'inside)
  exact Vector.getElem_map _ _

/-- **The symbol of a zone is at most 3 exactly for a valid return under 300 mm.** -/
theorem symbol_close (cell : Cell) :
    (symbol cell).toNat ≤ 3 ↔ cell.status = 5 ∧ cell.distance.val < 300 := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  unfold symbol
  split
  · rename_i valid
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro small
      exact ⟨valid, by omega⟩
    · rintro ⟨_, short⟩
      omega
  · rename_i other
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64]
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro small
      omega
    · rintro ⟨valid, _⟩
      exact absurd valid other

/-- **The symbol of a zone is from 5 and below `0x1000`, or `0x10FF`, exactly for a valid
return of at least 400 mm or the status 255.** -/
theorem symbol_distant (cell : Cell) :
    ((5 ≤ (symbol cell).toNat ∧ (symbol cell).toNat < 0x1000) ∨
        (symbol cell).toNat = 0x10FF) ↔
      (cell.status = 255 ∨ (cell.status = 5 ∧ 400 ≤ cell.distance.val)) := by
  have bounds : 0 ≤ cell.distance.val ∧ cell.distance.val ≤ 32767 := cell.distance.property
  have byte : cell.status.toNat < 256 := cell.status.toNat_lt
  unfold symbol
  split
  · rename_i valid
    have other : cell.status ≠ 255 := by rw [valid]; decide
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro wide
      exact Or.inr ⟨valid, by omega⟩
    · rintro (none | ⟨_, far⟩)
      · exact absurd none other
      · exact Or.inl (by omega)
  · rename_i other
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64]
    simp only [UInt64.toNat_ofNat]
    constructor
    · intro wide
      exact Or.inl (UInt8.toNat_inj.mp (by show cell.status.toNat = 255; omega))
    · rintro (none | ⟨valid, _⟩)
      · exact Or.inr (by rw [none]; decide)
      · exact absurd valid other

/-- **The trunk is upright exactly when the upward component of gravity is below -967
thousandths.** A level is a step of a tenth counted from the least value of the scale, and
the level of -950 thousandths is 318, so a level is below it exactly for a value below
-967. -/
theorem upright_iff (state : State) :
    upright state = true ↔ (state.gravity.get 2).val < -967 := by
  have bounds : -32767 ≤ (state.gravity.get 2).val ∧ (state.gravity.get 2).val ≤ 32767 :=
    (state.gravity.get 2).property
  unfold upright Declared.upright level
  rw [decide_eq_true_iff, UInt64.lt_iff_toNat_lt, Nat.toUInt64_eq, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  show ((state.gravity.get 2).val - -32767).toNat / 100 % 2 ^ 64 <
    ((-950 : Int) - -32767).toNat / 100 % 2 ^ 64 ↔ _
  omega

/-- **The depth frame is fresh exactly when the age word of the frame is below its cap.**
For every reading: it has a fresh depth frame exactly when it has a depth frame whose age
word, the value on position 45, is below `Declared.oldest`. -/
theorem fresh_level (reading : Reading) :
    fresh reading = true ↔
      ∃ age, reading.age = some age ∧
        min (age / Declared.stale) Declared.oldest < Declared.oldest := by
  unfold fresh
  cases reading.age with
  | none =>
    exact ⟨fun young => absurd young (by decide), fun ⟨_, absent, _⟩ => nomatch absent⟩
  | some age =>
    have cap : age < Declared.fresh ↔
        min (age / Declared.stale) Declared.oldest < Declared.oldest := by
      unfold Declared.fresh Declared.stale Declared.oldest
      omega
    show decide (age < Declared.fresh) = true ↔ _
    rw [decide_eq_true_iff, cap]
    constructor
    · intro capped
      exact ⟨age, rfl, capped⟩
    · rintro ⟨other, same, capped⟩
      rw [Option.some.inj same]
      exact capped

/-- The body is near an obstacle exactly when the trunk is upright, the depth frame is
fresh, and a zone of its two top rows has a valid return under the declared distance. -/
theorem near_iff (reading : Reading) :
    near reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∃ depth, reading.depth = some depth ∧ ∃ row column : Fin 8, row.val < 2 ∧
            (depth.zone row column).status = 5 ∧
              (depth.zone row column).distance.val < Declared.near := by
  rw [← upright_iff]
  unfold near fresh close
  cases reading.age <;> cases reading.depth <;>
    simp [and_assoc]

/-- The body is clear of obstacles exactly when the trunk is upright, the depth frame is
fresh, and every zone of its two top rows has the status 255 or a valid return of at least
the declared distance. -/
theorem clear_iff (reading : Reading) :
    clear reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∃ depth, reading.depth = some depth ∧ ∀ row column : Fin 8, row.val < 2 →
            (depth.zone row column).status = 255 ∨
              ((depth.zone row column).status = 5 ∧
                Declared.clear ≤ (depth.zone row column).distance.val) := by
  rw [← upright_iff]
  unfold clear fresh distant
  cases reading.age with
  | none => cases reading.depth <;> simp
  | some age =>
    cases reading.depth with
    | none => simp
    | some depth =>
      simp [or_assoc]
      constructor
      · rintro ⟨⟨tilt, young⟩, wide⟩
        exact ⟨tilt, young, fun row column top =>
          (wide row column).resolve_left (by omega)⟩
      · rintro ⟨tilt, young, wide⟩
        refine ⟨⟨tilt, young⟩, fun row column => ?_⟩
        rcases Nat.lt_or_ge row.val 2 with top | low
        · exact Or.inr (wide row column top)
        · exact Or.inl low

/-- **The goal test, read from the frame's symbols.** For every reading: the body is near an
obstacle exactly when the upward component of gravity is below -967 thousandths, the
depth frame is under half a second old, and one of the first sixteen symbols of the frame,
which are its two top rows, is at most 3. -/
theorem near_symbols (reading : Reading) :
    near reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∃ position : Fin shape.inputs, position.val < 16 ∧
            ((symbols reading.depth).get position).toNat ≤ 3 := by
  rw [near_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨depth, paired, row, column, top, valid, short⟩
    refine ⟨⟨row.val * 8 + column.val, by show _ < 64; omega⟩,
      by show row.val * 8 + column.val < 16; omega, ?_⟩
    rw [paired, symbols_zone]
    exact (symbol_close _).mpr ⟨valid, short⟩
  · rintro ⟨position, top, small⟩
    have inside : position.val < 64 := position.isLt
    cases paired : reading.depth with
    | none =>
      rw [paired, symbols_missing] at small
      exact absurd small (by decide)
    | some depth =>
      have same : position = ⟨(position.val / 8) * 8 + position.val % 8,
          by show _ < 64; omega⟩ :=
        Fin.ext (by show position.val = position.val / 8 * 8 + position.val % 8; omega)
      rw [paired, same,
        symbols_zone depth ⟨position.val / 8, by omega⟩ ⟨position.val % 8, by omega⟩] at small
      exact ⟨depth, rfl, ⟨position.val / 8, by omega⟩, ⟨position.val % 8, by omega⟩,
        by show position.val / 8 < 2; omega, (symbol_close _).mp small⟩

/-- **The clear test, read from the frame's symbols.** For every reading: the body is
clear of obstacles exactly when the upward component of gravity is below -967
thousandths, the depth frame is under half a second old, and each of the first sixteen
symbols of the frame is from 5 and below `0x1000`, or is `0x10FF`. -/
theorem clear_symbols (reading : Reading) :
    clear reading = true ↔
      (reading.state.gravity.get 2).val < -967 ∧
        (∃ age, reading.age = some age ∧ age < Declared.fresh) ∧
          ∀ position : Fin shape.inputs, position.val < 16 →
            (5 ≤ ((symbols reading.depth).get position).toNat ∧
                ((symbols reading.depth).get position).toNat < 0x1000) ∨
              ((symbols reading.depth).get position).toNat = 0x10FF := by
  rw [clear_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨depth, paired, wide⟩ position top
    have inside : position.val < 64 := position.isLt
    have same : position = ⟨(position.val / 8) * 8 + position.val % 8,
        by show _ < 64; omega⟩ :=
      Fin.ext (by show position.val = position.val / 8 * 8 + position.val % 8; omega)
    rw [paired, same,
      symbols_zone depth ⟨position.val / 8, by omega⟩ ⟨position.val % 8, by omega⟩]
    exact (symbol_distant _).mpr
      (wide ⟨position.val / 8, by omega⟩ ⟨position.val % 8, by omega⟩
        (by show position.val / 8 < 2; omega))
  · intro wide
    cases paired : reading.depth with
    | none =>
      have first := wide ⟨0, by decide⟩ (by decide)
      rw [paired, symbols_missing] at first
      exact absurd first (by decide)
    | some depth =>
      refine ⟨depth, rfl, fun row column top => ?_⟩
      have zone := wide ⟨row.val * 8 + column.val, by show _ < 64; omega⟩
        (by show row.val * 8 + column.val < 16; omega)
      rw [paired, symbols_zone] at zone
      exact (symbol_distant _).mp zone

/-- **A reading is not both near and clear.** -/
theorem near_clear (reading : Reading) (close : near reading = true) :
    clear reading = false := by
  obtain ⟨_, _, depth, paired, row, column, top, valid, short⟩ := (near_iff reading).mp close
  cases wide : clear reading with
  | false => rfl
  | true =>
    obtain ⟨_, _, other, same, far⟩ := (clear_iff reading).mp wide
    have equal : other = depth := Option.some.inj (same.symm.trans paired)
    rw [equal] at far
    rcases far row column top with none | ⟨_, long⟩
    · rw [valid] at none
      exact absurd none (by decide)
    · have short : (depth.zone row column).distance.val < 300 := short
      have long : (400 : Int) ≤ (depth.zone row column).distance.val := long
      omega

/-- The event of the goal holds exactly when the goal is armed and the body is near an
obstacle. -/
theorem achieved_iff (armed : Bool) (reading : Reading) :
    achieved armed reading = true ↔ armed = true ∧ near reading = true := by
  simp only [achieved, Bool.and_eq_true]

/-- A near reading disarms the goal. -/
theorem arm_near (armed : Bool) (reading : Reading) (close : near reading = true) :
    arm armed reading = false := by
  unfold arm
  simp only [close, ↓reduceIte]

/-- A clear reading arms the goal. -/
theorem arm_clear (armed : Bool) (reading : Reading) (wide : clear reading = true) :
    arm armed reading = true := by
  have apart : near reading = false := by
    cases close : near reading with
    | false => rfl
    | true => rw [near_clear reading close] at wide; exact absurd wide (by decide)
  unfold arm
  simp only [apart, wide, Bool.false_eq_true, ↓reduceIte, Bool.or_true]

/-- A reading that is neither near nor clear leaves the goal as it was. -/
theorem arm_keeps (armed : Bool) (reading : Reading) (apart : near reading = false)
    (narrow : clear reading = false) : arm armed reading = armed := by
  unfold arm
  simp only [apart, narrow, Bool.false_eq_true, ↓reduceIte, Bool.or_false]

/-- **After a near reading, no reading is the event of the goal until a clear reading.**
For every state of the latch, near reading and list of later readings none of which is
clear: after them the goal is not armed, so the next reading is not the event. -/
theorem arm_held (armed : Bool) (first : Reading) (later : List Reading) (next : Reading)
    (close : near first = true) (narrow : ∀ reading ∈ later, clear reading = false) :
    achieved (later.foldl arm (arm armed first)) next = false := by
  have disarmed : later.foldl arm (arm armed first) = false := by
    rw [arm_near armed first close]
    clear close
    induction later with
    | nil => rfl
    | cons reading rest hold =>
      have stays : arm false reading = false := by
        unfold arm
        split
        · rfl
        · simp only [narrow reading List.mem_cons_self, Bool.or_false]
      rw [List.foldl_cons, stays]
      exact hold fun other member => narrow other (List.mem_cons_of_mem _ member)
  unfold achieved
  rw [disarmed]
  rfl

/-- **The word the upright test reads is the gravity word of the frame on position 33.**
For every reading and host event, the frame has on that position the level of the upward
component of gravity. -/
theorem entries_gravity (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ((33 : Fin 256), level Declared.share (reading.state.gravity.get 2)) ∈
      entries reading outcome late := by
  have trunk : ((33 : Fin 256), level Declared.share (reading.state.gravity.get 2)) ∈
      trunkEntries reading.state := by
    unfold trunkEntries
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨2, List.mem_finRange 2, rfl⟩))
  unfold entries
  simp only [List.mem_append, trunk, or_true, true_or]

/-- The presence words of a frame: the word on position 30 is one with rates and zero
without, and likewise the word on position 41 for the gain and the word on position 44 for
the depth frame. Each position carries one word only (`entries_distinct`). -/
theorem entries_presence (reading : Reading) (outcome : Option Outcome) (late : Bool) :
    ((30 : Fin 256), flag reading.state.speeds.isSome) ∈ entries reading outcome late ∧
      ((41 : Fin 256), flag reading.state.gain.isSome) ∈ entries reading outcome late ∧
        ((44 : Fin 256), flag reading.depth.isSome) ∈ entries reading outcome late := by
  rw [← Reading.age_present]
  unfold entries
  cases reading.state.speeds <;> cases reading.state.gain <;> cases reading.age <;>
    simp [rateEntries, gainEntries, ageEntries, flag]

set_option maxRecDepth 4096 in
/-- **A reading without rates has no rate word.** No word of its frame is on positions 15
to 29. -/
theorem entries_rates (reading : Reading) (outcome : Option Outcome) (late : Bool)
    (absent : reading.state.speeds = none) :
    ∀ position ∈ (entries reading outcome late).map Prod.fst,
      ¬(15 ≤ position.val ∧ position.val ≤ 29) := by
  unfold entries
  rw [absent]
  cases reading.state.gain <;> cases reading.age <;>
    simp only [jointEntries, rateEntries, trunkEntries, gainEntries, ageEntries,
      List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def] <;>
    decide

set_option maxRecDepth 4096 in
/-- **A reading without a gain has no gain word.** No word of its frame is on position
42. -/
theorem entries_gain (reading : Reading) (outcome : Option Outcome) (late : Bool)
    (absent : reading.state.gain = none) :
    ∀ position ∈ (entries reading outcome late).map Prod.fst, position.val ≠ 42 := by
  unfold entries
  rw [absent]
  cases reading.state.speeds <;> cases reading.age <;>
    simp only [jointEntries, rateEntries, trunkEntries, gainEntries, ageEntries,
      List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def] <;>
    decide

set_option maxRecDepth 4096 in
/-- **A reading without a depth frame has no age word.** No word of its frame is on
position 45. -/
theorem entries_depth (reading : Reading) (outcome : Option Outcome) (late : Bool)
    (absent : reading.depth = none) :
    ∀ position ∈ (entries reading outcome late).map Prod.fst, position.val ≠ 45 := by
  have ageless : reading.age = none := by
    unfold Reading.age
    rw [absent]
    rfl
  unfold entries
  rw [ageless]
  cases reading.state.speeds <;> cases reading.state.gain <;>
    simp only [jointEntries, rateEntries, trunkEntries, gainEntries, ageEntries,
      List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def] <;>
    decide

/-- Two positions of the layout have two channels. -/
theorem channel_injective (first second : Fin 256) (same : channel first = channel second) :
    first = second := by
  have left := first.isLt
  have right := second.isLt
  have value := congrArg UInt64.toNat same
  unfold channel at value
  rw [UInt64.toNat_add, UInt64.toNat_add, Nat.toUInt64_eq, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat'] at value
  simp only [UInt64.toNat_ofNat] at value
  exact Fin.ext (by omega)

/-- Two outcomes of an action, or an outcome and none, have two codes: a refused action
and an accepted action that was not executed are two values of the word. -/
theorem became_injective (first second : Option Outcome) (same : became first = became second) :
    first = second := by
  cases first with
  | none => cases second with
    | none => rfl
    | some other => cases other <;> exact absurd same (by decide)
  | some outcome => cases second with
    | none => cases outcome <;> exact absurd same (by decide)
    | some other => cases outcome <;> cases other <;> first | rfl | exact absurd same (by decide)

/-- The interface's count of actions is the ten positions of the action table. -/
theorem interface_actions : interface.actions.word.toNat = 10 := rfl

/-- The Microduck world declares a wall clock with the declared pace. -/
theorem interface_timing : interface.timing = .wallClock Host.Microduck.Declared.pace := rfl

end Acorn.Handcrafted.Microduck
