/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Time between an agent and a world

A step of the agent has two parts. The first selects the action. The second completes
the step from the value the first returned. `StepOrder` declares which of three orders
an agent and its host run. `Timing` is what a world declares about its own time; the
last section of this comment describes it.

Under `learnThenAct` both parts run before the world receives the action, and the
first part plans at a free boundary before it draws. Under `planAfterAct` the host
releases the action between the two parts, and planning is the first work of the
second part: at a free boundary the meta action is drawn from the meta-controller
before that frame's planning. The name says what the order does and no more. An option
that starts still draws its first action after the terminal credit and the settlement
that this percept causes, so this order is not a complete "act, then learn".

Under `actThenLearn` the first part makes every draw of the step and takes no reward
word, and every write that reads the reward of the percept is in the second part, with
the planning of a free boundary after it. An option that starts draws its first action
from its policy as the preceding step left it. The first part still reads the frame's
achievement event (D8), on which an executing option ends.

Releasing the action before the learning update is the reordering of Travnik,
Mathewson, Sutton & Pilarski, *Reactive Reinforcement Learning in Asynchronous
Environments*, Frontiers in Robotics and AI 5:79 (2018), sections 2 and 3. Its
Algorithm 1 (SARSA, section 2) takes the action it chose at the start of the next
iteration, after the update; its Algorithm 2 (Reactive SARSA, section 3) takes the
action directly after choosing it, before the update. Both listings choose the action
before the update; the source has no planning. Moving planning after the action is Acorn's own change of PAR-14's
schedule, declared in PAR-19. Drawing the first action of an option before the credit
that the same percept causes is the source's order of choice and update applied to that
option's learner, and is declared with its other consequences in PAR-20.

## The time a world declares

A world declares its `Timing`. A `synchronized` world takes one transition for each
action and waits for it. A `wallClock` world moves while the agent computes, and declares
a `Pace`: the length of one action cycle, and the latency, a positive number of cycles.

The functions of a `Pace` give the two numbers their meaning. They take an origin, an
`Instant` of a host's monotonic clock. Cycle `index` starts at
`Pace.boundary origin index`. The deadline of the action of the percept of that cycle is
`Pace.deadline origin index`, the start of the cycle `latency` cycles later. `Pace.meets`
is the verdict on the instant an action is released at: true exactly when the release is
before the deadline (`Pace.meets_iff`). `Pace.overdue` counts the cycles, from the one the
deadline starts, that have started at or before the release (`Pace.overdue_cycles`), and it
is zero exactly when the deadline is met (`Pace.overdue_met`). When the earlier of two
actions is released at or after the start of its percept's cycle and the later one meets
its deadline, for percepts `span` cycles apart, the later release is less than
`span + latency` cycles after the earlier one (`Pace.met_gap`): `latency + 1` cycles for
two consecutive percepts.

An instant is a natural number of nanoseconds, as the runtime's monotonic clock returns
it (`IO.monoNanosNow`), so this arithmetic is exact and has no word bound. An instant and
a count of cycles are different types, so neither takes the other's place in a function
of this section.

The statements are about these functions. No executing loop reads a `Pace`, and the one
executing world, the grid world, declares `synchronized`. So nothing here states what a
host does: that it senses a percept at the start of a cycle, that it releases a late
action late and drops none, or which action is in force during the cycles that
`Pace.overdue` counts. Those belong to the host loop of a wall-clock world, which is not
built (https://github.com/rbeauchamp/acorn/issues/95).
-/
namespace Acorn

/-- The order of the agent's two step parts, planning and the world's transition. -/
inductive StepOrder where
  /-- Both parts run before the world receives the action, and a free boundary plans
  before its meta draw. -/
  | learnThenAct
  /-- The world receives the action after the first part. Planning is the first work
  of the second part, which runs after the world's transition. -/
  | planAfterAct
  /-- The world receives the action after the first part, which makes every draw and
  takes no reward. Every write that reads the reward, and then planning, is in the
  second part, which runs after the world's transition. -/
  | actThenLearn
  deriving DecidableEq

/-- Canonical spelling of each order; the single text vocabulary shared by command
admission and run provenance. -/
def StepOrder.name : StepOrder → String
  | .learnThenAct => "learn-then-act"
  | .planAfterAct => "plan-after-act"
  | .actThenLearn => "act-then-learn"

/-- The single closed textual admission rule: exactly the three canonical spellings
parse; every other string is refused and never substituted. -/
def StepOrder.parse (text : String) : Option StepOrder :=
  if text = "learn-then-act" then some .learnThenAct
  else if text = "plan-after-act" then some .planAfterAct
  else if text = "act-then-learn" then some .actThenLearn
  else none

/-- Stored word of each order in a checkpoint header. -/
def StepOrder.tag : StepOrder → UInt32
  | .learnThenAct => 0
  | .planAfterAct => 1
  | .actThenLearn => 2

/-- Two orders with one stored word are one order. -/
theorem StepOrder.tag_injective (first second : StepOrder) (same : first.tag = second.tag) :
    first = second := by
  cases first <;> cases second <;> first | rfl | cases same

/-- The stored word of every order is below 256: it occupies one byte of its four. -/
theorem StepOrder.tag_small (order : StepOrder) : order.tag.toNat < 256 := by
  cases order <;> decide

/-- The specification of the stored word of a step order, written with no executed
function: word 0 is learn-then-act, word 1 is plan-after-act and word 2 is
act-then-learn. -/
def StepOrder.Stored (word : UInt32) (order : StepOrder) : Prop :=
  (word = 0 ∧ order = .learnThenAct) ∨ (word = 1 ∧ order = .planAfterAct) ∨
    (word = 2 ∧ order = .actThenLearn)

/-- **The stored word of an order is exactly its specified word.** For every order and
word, `tag` gives the word exactly when the word is stored for the order. -/
theorem StepOrder.tag_stored (order : StepOrder) (word : UInt32) :
    order.tag = word ↔ StepOrder.Stored word order := by
  cases order <;> simp [StepOrder.tag, StepOrder.Stored, eq_comm]

/-- One stored word is the word of one order. -/
theorem StepOrder.stored_injective (word : UInt32) (first second : StepOrder)
    (one : StepOrder.Stored word first) (other : StepOrder.Stored word second) :
    first = second :=
  StepOrder.tag_injective first second
    (((StepOrder.tag_stored first word).mpr one).trans
      ((StepOrder.tag_stored second word).mpr other).symm)

/-- The specification of the spelling of a step order, written with no executed function:
a text spells an order when it is that order's one word. -/
def StepOrder.Spelled (text : String) (order : StepOrder) : Prop :=
  (text = "learn-then-act" ∧ order = .learnThenAct) ∨
    (text = "plan-after-act" ∧ order = .planAfterAct) ∨
    (text = "act-then-learn" ∧ order = .actThenLearn)

/-- **The parser accepts exactly the spelled orders.** For every string and order, the
parser returns the order exactly when the text spells it. -/
theorem StepOrder.parse_spelled (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ StepOrder.Spelled text order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "plan-after-act" <;>
    by_cases third : text = "act-then-learn" <;>
    simp_all [StepOrder.parse, StepOrder.Spelled]

/-- **The parser refuses exactly the texts that spell no order.** -/
theorem StepOrder.parse_refused (text : String) :
    StepOrder.parse text = none ↔ ∀ order, ¬ StepOrder.Spelled text order := by
  constructor
  · intro refused order spelled
    rw [(StepOrder.parse_spelled text order).mpr spelled] at refused
    cases refused
  · intro unspelled
    cases parsed : StepOrder.parse text with
    | none => rfl
    | some order => exact (unspelled order ((StepOrder.parse_spelled text order).mp parsed)).elim

/-- The word that run provenance prints for an order spells that order, and no other. -/
theorem StepOrder.name_spelled (order other : StepOrder) :
    StepOrder.Spelled order.name other ↔ other = order := by
  cases order <;> cases other <;> simp [StepOrder.Spelled, StepOrder.name]

/-- Accepted spelling identifies exactly the selected constructor over the entire
string domain. -/
theorem StepOrder.parse_accepted (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ text = StepOrder.name order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "plan-after-act" <;>
    by_cases third : text = "act-then-learn" <;>
    simp_all [StepOrder.parse, StepOrder.name]

/-- An order whose host loop releases the action between the two parts of a step: every
order but the default. A host loop that releases takes the callbacks of such an order. -/
def StepOrder.Releases (order : StepOrder) : Prop := order ≠ .learnThenAct

/-! ## The time a world declares -/

/-- The wall-clock declaration of a world: the length of one action cycle and the number
of cycles an action may take. Both are positive, so a value of this type declares a
cycle that has a length and a deadline that follows its percept. -/
structure Pace where
  /-- Nanoseconds of one action cycle. -/
  cycle : Nat
  /-- Whole cycles from the start of a percept's cycle to the deadline of its action. -/
  latency : Nat
  /-- A cycle has a length. -/
  running : 0 < cycle
  /-- A deadline is later than the start of its percept's cycle. -/
  causal : 0 < latency

/-- The timing discipline of a world. -/
inductive Timing where
  /-- The world takes one transition for each action and waits for it. -/
  | synchronized
  /-- The world moves on a wall clock, with the declared cycle and latency. -/
  | wallClock (pace : Pace)

/-- A reading of a host's monotonic clock. It is a type of its own, so a count of cycles
cannot stand where an instant is expected. -/
structure Instant where
  /-- Nanoseconds from the clock's own zero. -/
  nanoseconds : Nat

/-- Start of a cycle, for a host whose cycle zero starts at `origin`. -/
def Pace.boundary (pace : Pace) (origin : Instant) (index : Nat) : Instant :=
  ⟨origin.nanoseconds + index * pace.cycle⟩

/-- The cycle an instant falls in. An instant before the origin falls in cycle zero. -/
def Pace.index (pace : Pace) (origin now : Instant) : Nat :=
  (now.nanoseconds - origin.nanoseconds) / pace.cycle

/-- Deadline of the action of the percept of a cycle: the start of the cycle `latency`
cycles later. -/
def Pace.deadline (pace : Pace) (origin : Instant) (index : Nat) : Instant :=
  pace.boundary origin (index + pace.latency)

/-- Whether an action released at an instant meets the deadline of the percept of a
cycle: it is released before the deadline. -/
def Pace.meets (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) : Bool :=
  decide (released.nanoseconds < (pace.deadline origin index).nanoseconds)

/-- How many cycles, from the one a deadline starts, have started at or before the
instant the action is released at. It is zero for a release that meets the deadline. -/
def Pace.overdue (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) : Nat :=
  pace.index origin released + 1 - (index + pace.latency)

/-- The start of a cycle in nanoseconds: the origin plus that many cycles. -/
theorem Pace.boundary_nanoseconds (pace : Pace) (origin : Instant) (index : Nat) :
    (pace.boundary origin index).nanoseconds = origin.nanoseconds + index * pace.cycle := rfl

/-- A later cycle starts later. -/
theorem Pace.boundary_lt (pace : Pace) (origin : Instant) {index other : Nat}
    (earlier : index < other) :
    (pace.boundary origin index).nanoseconds < (pace.boundary origin other).nanoseconds :=
  Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right earlier pace.running) origin.nanoseconds

/-- **A cycle has started at an instant exactly when the instant is not before the origin
and the cycle is not after the instant's cycle.** For every pace, origin, cycle and
instant. -/
theorem Pace.boundary_le (pace : Pace) (origin : Instant) (index : Nat) (now : Instant) :
    (pace.boundary origin index).nanoseconds ≤ now.nanoseconds ↔
      origin.nanoseconds ≤ now.nanoseconds ∧ index ≤ pace.index origin now := by
  rw [pace.boundary_nanoseconds origin index]
  unfold Pace.index
  rw [Nat.le_div_iff_mul_le pace.running]
  omega

/-- The instant a cycle starts at falls in that cycle. -/
theorem Pace.index_boundary (pace : Pace) (origin : Instant) (index : Nat) :
    pace.index origin (pace.boundary origin index) = index := by
  unfold Pace.index
  rw [pace.boundary_nanoseconds origin index, Nat.add_sub_cancel_left]
  exact Nat.mul_div_cancel index pace.running

/-- **An instant at or after the origin falls in exactly the cycle that has started and
whose successor has not.** -/
theorem Pace.index_iff (pace : Pace) (origin now : Instant) (index : Nat)
    (started : origin.nanoseconds ≤ now.nanoseconds) :
    pace.index origin now = index ↔
      (pace.boundary origin index).nanoseconds ≤ now.nanoseconds ∧
        now.nanoseconds < (pace.boundary origin (index + 1)).nanoseconds := by
  have here := pace.boundary_le origin index now
  have next := pace.boundary_le origin (index + 1) now
  omega

/-- The deadline of a percept is later than the start of its cycle. -/
theorem Pace.deadline_lt (pace : Pace) (origin : Instant) (index : Nat) :
    (pace.boundary origin index).nanoseconds < (pace.deadline origin index).nanoseconds :=
  pace.boundary_lt origin (Nat.lt_add_of_pos_right pace.causal)

/-- **The verdict on the declared numbers.** For every pace, origin, cycle and release:
the deadline is met exactly when the release is earlier than the origin plus
`index + latency` cycles. -/
theorem Pace.meets_iff (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) :
    pace.meets origin index released = true ↔
      released.nanoseconds < origin.nanoseconds + (index + pace.latency) * pace.cycle :=
  decide_eq_true_iff

/-- **The cycles behind a deadline.** For every pace, origin, cycle and release: a cycle
that is not before the one the deadline starts has started at or before the release
exactly when it is one of the first `overdue` of them. -/
theorem Pace.overdue_cycles (pace : Pace) (origin : Instant) (index : Nat) (released : Instant)
    (later : Nat) (due : index + pace.latency ≤ later) :
    (pace.boundary origin later).nanoseconds ≤ released.nanoseconds ↔
      later < index + pace.latency + pace.overdue origin index released := by
  have started := pace.boundary_le origin later released
  have early : released.nanoseconds < origin.nanoseconds → pace.index origin released = 0 := by
    intro before
    unfold Pace.index
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt before)]
    exact Nat.zero_div pace.cycle
  have positive := pace.causal
  unfold Pace.overdue
  omega

/-- **The later of two releases, when it meets its deadline.** For every pace, origin,
cycle and number of cycles between two percepts: when the earlier action is released at
or after the start of its percept's cycle, and the later one meets its deadline, the
later release is less than `span + latency` cycles after the earlier one. For two
consecutive cycles the bound is `latency + 1` cycles. The statement has no hypothesis
that the earlier release meets its own deadline, and it bounds one direction only. -/
theorem Pace.met_gap (pace : Pace) (origin : Instant) (index span : Nat)
    (first second : Instant)
    (sensed : (pace.boundary origin index).nanoseconds ≤ first.nanoseconds)
    (met : pace.meets origin (index + span) second = true) :
    second.nanoseconds < first.nanoseconds + (span + pace.latency) * pace.cycle := by
  have verdict := (pace.meets_iff origin (index + span) second).mp met
  have split : (index + span + pace.latency) * pace.cycle =
      index * pace.cycle + (span + pace.latency) * pace.cycle := by
    rw [Nat.add_assoc, Nat.add_mul]
  rw [pace.boundary_nanoseconds origin index] at sensed
  omega

/-- **No cycle behind a deadline exactly when it is met.** -/
theorem Pace.overdue_met (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) :
    pace.overdue origin index released = 0 ↔ pace.meets origin index released = true := by
  have first := pace.overdue_cycles origin index released (index + pace.latency) (Nat.le_refl _)
  rw [pace.meets_iff origin index released]
  rw [pace.boundary_nanoseconds origin (index + pace.latency)] at first
  omega

end Acorn
