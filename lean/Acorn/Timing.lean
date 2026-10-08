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
section "The time a world declares" describes it.

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
is the verdict on the instant an action is released at: true exactly when the release
falls in a cycle before the one the deadline starts (`Pace.meets_index`), which is when
no cycle from that one on has begun at the release (`Pace.meets_begun`). `Pace.first` is
the first cycle that starts at or after an instant (`Pace.first_starts`,
`Pace.first_least`), and less than one cycle after an instant that is not before the
origin (`Pace.first_within`).

## The fault of a missed deadline

A `Force` is an action in force, with the instant from which the world's default
replaces it, if the world has one: its lapse. A world whose actions stay in force until
the next release has no lapse. A `Standing` is what a host of a wall-clock world holds
between two events: the force of the last release and the percept, if any, whose action
is not released yet. `Pace.outcome` gives what holds at an instant for a standing, in a
world whose default is `rest`: the action that the force names at the instant
(`Pace.outcome_action`, `Force.named_lapse`, `Force.named_lasting`), and whether a fault
holds. A fault holds exactly while a percept awaits its action at or after its deadline
(`Pace.outcome_fault`).

`Standing.during` is the standing through one step: a percept is sensed with a preceding
force, and its action is released at an instant. An action is in force after the instant
it is released at. For that step, a fault holds exactly from the deadline to the release
(`Pace.step_fault`), and no instant has a fault exactly when the release meets the
deadline (`Pace.step_faultless`). At every instant of the fault at which the preceding
force has not lapsed, the preceding action is in force (`Pace.step_holds`); a force with
no lapse has lapsed at no instant, so in a world whose actions do not lapse the preceding
action holds through the whole fault. From the lapse of the preceding force, the fault
has the world's default (`Pace.step_lapsed`). After the release, however late it is, the
outcome follows the chosen force: its action until its lapse, and the default from it
(`Pace.step_action`).

When the earlier of two actions is released at or after the start of its percept's
cycle and the later one meets its deadline, for percepts `span` cycles apart, the later
release is less than `span + latency` cycles after the earlier one (`Pace.met_gap`):
`latency + 1` cycles for two consecutive percepts.

An instant is a natural number of nanoseconds, as the runtime's monotonic clock returns
it (`IO.monoNanosNow`), so this arithmetic is exact and has no word bound. An instant and
a count of cycles are different types, so neither takes the other's place in a function
of this section.

The statements are about these functions. No executing loop keeps a `Standing` or reads
a `Pace`, and the one executing world, the grid world, declares `synchronized`. A host
loop of a wall-clock world is to compute its verdicts with `Pace.outcome`; that loop is
not built (https://github.com/rbeauchamp/acorn/issues/95), and nothing here states that
a world keeps in force the action that a standing names.
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

/-- The cycle an instant falls in: the instant a cycle starts at falls in that cycle
(`Pace.index_boundary`). An instant before the origin falls in cycle zero. -/
def Pace.index (pace : Pace) (origin now : Instant) : Nat :=
  (now.nanoseconds - origin.nanoseconds) / pace.cycle

/-- Deadline of the action of the percept of a cycle: the start of the cycle `latency`
cycles later, which is later than the start of the percept's cycle (`Pace.deadline_lt`). -/
def Pace.deadline (pace : Pace) (origin : Instant) (index : Nat) : Instant :=
  pace.boundary origin (index + pace.latency)

/-- Whether an action released at an instant meets the deadline of the percept of a
cycle: it is released before the deadline. -/
def Pace.meets (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) : Bool :=
  decide (released.nanoseconds < (pace.deadline origin index).nanoseconds)

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

/-- An instant before the origin falls in cycle zero. -/
theorem Pace.index_early (pace : Pace) (origin now : Instant)
    (before : now.nanoseconds < origin.nanoseconds) : pace.index origin now = 0 := by
  unfold Pace.index
  rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt before)]
  exact Nat.zero_div pace.cycle

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

/-- The deadline in nanoseconds: the origin plus `index + latency` cycles. -/
theorem Pace.deadline_nanoseconds (pace : Pace) (origin : Instant) (index : Nat) :
    (pace.deadline origin index).nanoseconds =
      origin.nanoseconds + (index + pace.latency) * pace.cycle := rfl

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

/-- **The verdict through the cycle of the release.** For every pace, origin, cycle and
release: the deadline is met exactly when the release falls in a cycle before the one the
deadline starts. The verdict computes the start of that cycle and compares; this
statement is through `Pace.index`, which divides. -/
theorem Pace.meets_index (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) :
    pace.meets origin index released = true ↔
      pace.index origin released < index + pace.latency := by
  have started := pace.boundary_le origin (index + pace.latency) released
  have early := pace.index_early origin released
  have positive := pace.causal
  rw [pace.boundary_nanoseconds origin (index + pace.latency)] at started
  rw [pace.meets_iff origin index released]
  omega

/-- **The verdict through the cycles that have begun.** For every pace, origin, cycle and
release: the deadline is met exactly when no cycle from the one the deadline starts has
begun at the instant of the release. -/
theorem Pace.meets_begun (pace : Pace) (origin : Instant) (index : Nat) (released : Instant) :
    pace.meets origin index released = true ↔
      ∀ later, index + pace.latency ≤ later →
        released.nanoseconds < (pace.boundary origin later).nanoseconds := by
  rw [pace.meets_iff origin index released]
  constructor
  · intro met later due
    have grows : (index + pace.latency) * pace.cycle ≤ later * pace.cycle :=
      Nat.mul_le_mul_right pace.cycle due
    rw [pace.boundary_nanoseconds origin later]
    omega
  · intro none
    have first := none (index + pace.latency) (Nat.le_refl _)
    rw [pace.boundary_nanoseconds origin (index + pace.latency)] at first
    exact first

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

/-- The first cycle that starts at or after an instant (`Pace.first_starts`,
`Pace.first_least`). For an instant that is not before the origin, it starts less than
one cycle after the instant (`Pace.first_within`). -/
def Pace.first (pace : Pace) (origin now : Instant) : Nat :=
  (now.nanoseconds - origin.nanoseconds + pace.cycle - 1) / pace.cycle

/-- **The cycle `first` names starts at or after the instant.** For every pace, origin
and instant. -/
theorem Pace.first_starts (pace : Pace) (origin now : Instant) :
    now.nanoseconds ≤ (pace.boundary origin (pace.first origin now)).nanoseconds := by
  have running := pace.running
  have lower := Nat.lt_div_mul_add
    (a := now.nanoseconds - origin.nanoseconds + pace.cycle - 1) running
  rw [pace.boundary_nanoseconds origin (pace.first origin now)]
  unfold Pace.first
  omega

/-- **No earlier cycle starts at or after the instant.** For every pace, origin, instant
and cycle that starts at or after the instant, `first` names a cycle that is not later. -/
theorem Pace.first_least (pace : Pace) (origin now : Instant) (index : Nat)
    (starts : now.nanoseconds ≤ (pace.boundary origin index).nanoseconds) :
    pace.first origin now ≤ index := by
  have running := pace.running
  rw [pace.boundary_nanoseconds origin index] at starts
  unfold Pace.first
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul running, Nat.succ_mul]
  omega

/-- **The cycle `first` names starts less than one cycle after the instant.** For every
pace, origin and instant that is not before the origin. -/
theorem Pace.first_within (pace : Pace) (origin now : Instant)
    (started : origin.nanoseconds ≤ now.nanoseconds) :
    (pace.boundary origin (pace.first origin now)).nanoseconds <
      now.nanoseconds + pace.cycle := by
  have running := pace.running
  have upper := Nat.div_mul_le_self
    (now.nanoseconds - origin.nanoseconds + pace.cycle - 1) pace.cycle
  rw [pace.boundary_nanoseconds origin (pace.first origin now)]
  unfold Pace.first
  omega

/-! ## The fault of a missed deadline -/

/-- An action in force, with the instant from which the world's default replaces it. A
world whose actions stay in force until the next release has no such instant. -/
structure Force (α : Type) where
  /-- The action, if one was released. -/
  action : Option α
  /-- The instant from which the action is in force no more, if the world has one. -/
  lapse : Option Instant

variable {α : Type}

/-- The action a force names at an instant, for a world whose default is `rest`: the
action before its lapse, and the default from the lapse on. -/
def Force.named (force : Force α) (rest : Option α) (now : Instant) : Option α :=
  match force.lapse with
  | none => force.action
  | some lapse => if now.nanoseconds < lapse.nanoseconds then force.action else rest

/-- What a host of a wall-clock world holds between two events, over the world's actions:
the force of the last release and the percept, if any, whose action is not released yet. -/
inductive Standing (α : Type) where
  /-- No percept awaits its action. The force is the one of the last release. -/
  | idle (force : Force α)
  /-- The percept of a cycle awaits its action. The force of the action that was in force
  when the percept was sensed stays. -/
  | awaiting (prior : Force α) (index : Nat)

/-- The force of a standing. -/
def Standing.force : Standing α → Force α
  | .idle force => force
  | .awaiting prior _ => prior

/-- What holds at an instant: the action in force, and whether a deadline has passed with
its action not released. -/
structure Standing.Outcome (α : Type) where
  /-- The action in force. -/
  action : Option α
  /-- Whether a percept awaits its action at or after its deadline. -/
  fault : Bool

/-- What holds at an instant for a standing, in a world whose default is `rest`. The
action is the one the standing's force names at the instant. While a percept awaits its
action a fault holds from the deadline on: at every instant at which a release would not
meet the deadline. -/
def Pace.outcome (pace : Pace) (origin : Instant) (rest : Option α) (standing : Standing α)
    (now : Instant) : Standing.Outcome α :=
  match standing with
  | .idle force => ⟨force.named rest now, false⟩
  | .awaiting prior index => ⟨prior.named rest now, !pace.meets origin index now⟩

/-- The standing at an instant of one step: the percept of cycle `index` is sensed with
the force `prior`, and its action is released at `released` with the force `chosen`. An
action is in force after the instant it is released at, so the percept still awaits at
that instant. -/
def Standing.during (prior : Force α) (index : Nat) (released : Instant) (chosen : Force α)
    (now : Instant) : Standing α :=
  if now.nanoseconds ≤ released.nanoseconds then .awaiting prior index else .idle chosen

/-- A force with no lapse names its action at every instant, whatever the default. -/
theorem Force.named_lasting (force : Force α) (rest : Option α) (now : Instant)
    (lasting : force.lapse = none) : force.named rest now = force.action := by
  unfold Force.named
  rw [lasting]

/-- **A force names its action before its lapse and the default from it.** For every
force that lapses, default and instant. -/
theorem Force.named_lapse (force : Force α) (rest : Option α) (now lapse : Instant)
    (lapses : force.lapse = some lapse) :
    force.named rest now =
      if now.nanoseconds < lapse.nanoseconds then force.action else rest := by
  unfold Force.named
  rw [lapses]

/-- At every instant the action of the outcome is the action that the standing's force
names. -/
theorem Pace.outcome_action (pace : Pace) (origin : Instant) (rest : Option α)
    (standing : Standing α) (now : Instant) :
    (pace.outcome origin rest standing now).action = standing.force.named rest now := by
  cases standing <;> rfl

/-- **A fault holds exactly while a percept awaits its action at or after its deadline.**
For every pace, origin, default, standing and instant. -/
theorem Pace.outcome_fault (pace : Pace) (origin : Instant) (rest : Option α)
    (standing : Standing α) (now : Instant) :
    (pace.outcome origin rest standing now).fault = true ↔
      ∃ prior index, standing = .awaiting prior index ∧
        (pace.deadline origin index).nanoseconds ≤ now.nanoseconds := by
  cases standing with
  | idle force =>
    constructor
    · intro fault
      cases fault
    · intro ⟨_, _, same, _⟩
      cases same
  | awaiting prior index =>
    simp only [Pace.outcome, Pace.meets, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
    constructor
    · intro late
      exact ⟨prior, index, rfl, late⟩
    · intro ⟨_, _, same, late⟩
      cases same
      exact late

/-- **A missed deadline is a fault from the deadline to the release.** For every pace,
origin, default, preceding force, cycle, release, chosen force and instant: in one step a
fault holds exactly at the instants that are not before the deadline and not after the
release. -/
theorem Pace.step_fault (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now : Instant) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).fault =
        true ↔
      (pace.deadline origin index).nanoseconds ≤ now.nanoseconds ∧
        now.nanoseconds ≤ released.nanoseconds := by
  rw [pace.outcome_fault origin]
  unfold Standing.during
  split
  · rename_i awaited
    constructor
    · intro ⟨_, _, same, late⟩
      cases same
      exact ⟨late, awaited⟩
    · intro ⟨late, _⟩
      exact ⟨prior, index, rfl, late⟩
  · rename_i passed
    constructor
    · intro ⟨_, _, same, _⟩
      cases same
    · intro ⟨_, awaited⟩
      exact absurd awaited passed

/-- **The action in force through one step.** Up to the instant of the release the
action is the one the preceding force names, and after it the one the chosen force
names. -/
theorem Pace.step_action (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now : Instant) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).action =
      if now.nanoseconds ≤ released.nanoseconds then prior.named rest now
      else chosen.named rest now := by
  rw [pace.outcome_action origin]
  unfold Standing.during
  split <;> rfl

/-- **During a fault the preceding action holds until its lapse.** For every instant of
one step at which a fault holds and at which the preceding force has not lapsed, the
action in force is the preceding one. A force with no lapse has lapsed at no instant, so
in a world whose actions do not lapse the preceding action holds through the whole
fault. -/
theorem Pace.step_holds (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now : Instant)
    (fault : (pace.outcome origin rest (Standing.during prior index released chosen now)
      now).fault = true)
    (holding : ∀ lapse, prior.lapse = some lapse → now.nanoseconds < lapse.nanoseconds) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).action =
      prior.action := by
  rw [pace.step_action origin rest prior index released chosen now]
  split
  · cases lapses : prior.lapse with
    | none => exact prior.named_lasting rest now lapses
    | some lapse =>
      rw [prior.named_lapse rest now lapse lapses]
      split
      · rfl
      · rename_i lapsed
        exact absurd (holding lapse lapses) lapsed
  · rename_i passed
    exact absurd
      ((pace.step_fault origin rest prior index released chosen now).mp fault).2 passed

/-- **From the lapse of the preceding action, a fault has the world's default.** For
every instant of one step at which a fault holds and that is not before the lapse of the
preceding force, the action in force is the default. -/
theorem Pace.step_lapsed (pace : Pace) (origin : Instant) (rest : Option α) (prior : Force α)
    (index : Nat) (released : Instant) (chosen : Force α) (now lapse : Instant)
    (fault : (pace.outcome origin rest (Standing.during prior index released chosen now)
      now).fault = true)
    (lapses : prior.lapse = some lapse) (lapsed : lapse.nanoseconds ≤ now.nanoseconds) :
    (pace.outcome origin rest (Standing.during prior index released chosen now) now).action =
      rest := by
  rw [pace.step_action origin rest prior index released chosen now]
  split
  · rw [prior.named_lapse rest now lapse lapses]
    split
    · rename_i before
      exact absurd before (Nat.not_lt.mpr lapsed)
    · rfl
  · rename_i passed
    exact absurd
      ((pace.step_fault origin rest prior index released chosen now).mp fault).2 passed

/-- **A step has no instant of fault exactly when its release meets the deadline.** -/
theorem Pace.step_faultless (pace : Pace) (origin : Instant) (rest : Option α)
    (prior : Force α) (index : Nat) (released : Instant) (chosen : Force α) :
    pace.meets origin index released = true ↔
      ∀ now, (pace.outcome origin rest (Standing.during prior index released chosen now)
        now).fault = false := by
  have verdict := pace.meets_iff origin index released
  have due := pace.deadline_nanoseconds origin index
  constructor
  · intro met now
    have early := verdict.mp met
    have none := not_congr (pace.step_fault origin rest prior index released chosen now)
    rw [Bool.not_eq_true] at none
    refine none.mpr ?_
    omega
  · intro none
    have last := not_congr
      (pace.step_fault origin rest prior index released chosen released)
    rw [Bool.not_eq_true] at last
    have clear := last.mp (none released)
    refine verdict.mpr ?_
    omega

end Acorn
