/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Microduck
import Acorn.Host.Microduck.Wire

/-!
# What a host of the Microduck's world holds, and its transitions

The Microduck's world moves on a wall clock. A host of that world hears lines of the two
daemons, senses a percept at the start of a cycle, releases the action that the agent
chose, and reads its clock between releases. This module is the state a host holds
between those events and one pure transition for each event. It reads no clock, no socket
and no agent: an executing loop that calls these transitions in the order of time is not
built, and nothing here states that one does.

**Two phases, two types.** An `Idle` is a host with no percept awaiting its action: before
the first percept, and between a release and the next percept. An `Awaiting` is a host
with a percept that awaits its action. `Idle.sense` gives an `Awaiting`, and
`Awaiting.release` gives an `Idle`, so a second percept over an awaited one and a release
with nothing awaited are not functions of this module. Each of the two types carries a
proof that its state is reached from the start by the transitions (`Reached`, an inductive
proposition with one constructor for each transition), so every value of either type,
however it was written, has a derivation from `Idle.start`: an awaited percept was sensed,
and what holds of every derivation holds of every value. `Reached` also names the readings
sensed on the way and the identifiers given to requests on the way, each in order. `Calm`
and `Poised` are what the two phases hold, as plain data; the transitions on them are
private, and the statements below are about the sealed types.

**Hearing a line** (`Idle.hear`, `Awaiting.hear`). While no percept awaits, a state frame
replaces the latest one and a depth frame becomes the latest of two that the host keeps
(`Idle.hear_frame`). Hearing changes neither the settings nor the record of a release nor
the standing of the deadline rule (`Idle.hear_keeps`). Two facts about the action released
last are gathered from the lines heard since its release.

- The answer. A release holds the identifiers of its requests that are not answered: those
  of its own commands, and those of its velocities sent again. A result or a fault counts
  only for the release that holds its identifier, and removes it; an answer with another
  identifier, with none, or heard while a percept awaits changes nothing
  (`Sent.answer_iff`). The answer of a release has three states (`Sent.reply_iff`): refused
  when a request of the release was refused, by a fault or by a result that does not
  accept; pending while a command of the release is not answered; accepted when every
  command of the release was accepted. A result with no boolean leaves its request
  unanswered. A fault with a null identifier names no request and is not counted.
- The evidence. The action is shown exactly when a state frame named a policy that the
  table `Action.Shown` gives for the action (`Idle.hear_shown`, `Action.shows_iff`). The
  table is declared from the labels of the record
  (https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895): the walking
  network for the three velocities that move, the label of each skill, the sitting label
  for `sit`, the rising label or the standing network for `stand`, and the standing
  network or the sitting label for `still`. The record has each skill's label and the
  walking label for a forward velocity; the walking label for a turn and the sitting
  label for standing still while seated are read from its text and were not timed. It is
  weak evidence in three ways. The forward velocity and the two turns share one label, so
  it does not tell which one the daemon executes. A frame heard just after a release can
  be from before the command took effect, so an action that the body already showed for
  the action before it is shown at once. And the evidence can be missing for an action
  that is executed: the next percept can be sensed before the label changes, since the
  record has the walking label 3 to 62 ms after a send and the standing network 44 to 271
  ms after a stop. How often the evidence is wrong in either direction is UNKNOWN: it
  needs runs of the simulator.

**Pairing a state frame with a depth frame.** A depth frame may not lead the state frame it
is paired with: a `Pair` is a state frame with a depth frame that is stamped at or before
it, or with none. The host holds the latest state frame heard since the last release and
the two latest depth frames heard, and pairs them when it senses: the state frame with the
later of the two depth frames that is stamped at or before it (`Pair.of`). When neither
is, and before any depth frame is heard, the reading has no depth, which the frame of the
interface marks as absent. So the depth frame of every reading is stamped at or before its
state frame, and its age is the exact difference of the two stamps, with no subtraction
that truncates (`Idle.sense_age`). Each of the three frames held is a function of the
frames of one stream, in their order, so the reading does not depend on how the two
streams interleave (`Idle.heard_frames`). The bound of this is the cache of two depth
frames: a state frame heard after two depth frames stamped after it has no depth, even when
an older depth frame at or before it was heard.

**Sensing a percept** (`Idle.sense`, `Idle.sense_iff`). A percept is sensed at an instant,
for the cycle the instant falls in, only when the cycle is not before the first cycle that
the last release allows, `Bridge.next` of its record (`Calm.cycle`), and a state frame was
heard since that release: a release drops the frame held, and a percept uses it up. The
frame was heard after the release. It can have been made before it: nothing here reads
when a frame was made against the instant of the release, which are instants of two
clocks. How old the frame is on the host's clock is not measured either.

The percept is `Sensed.percept`, which the adapter of `Acorn.Handcrafted.Microduck` builds
from the reading, what became of the action released last, whether its release was late,
and the latch of the goal. What became of the action is `Bridge.outcome` for the answer and
the evidence, so an outcome that says the daemon accepted the action is given only for a
release whose commands were all accepted, and a release whose answer is still pending
reads `unanswered` (`Action.outcome_accepted`). The latch is in the state: it starts
disarmed and each sensing advances it with the adapter's `arm`, so the latch of every
reachable state is the fold of `arm` over the readings sensed (`Reached.latch`), and
after a near reading no percept is the event of the goal until a clear one
(`Idle.sense_held`).

**Releasing an action** (`Awaiting.release`, `Awaiting.release_iff`). A release names the
cycle it answers and is admitted exactly when that is the awaited cycle and the cycle has
started. The commands are the action's for the posture of the percept's state frame, by
the sitting label (`State.Sitting`), each with one of the host's next unused identifiers.
The identifiers given are the consecutive numbers from those of the opening requests, in the
order given, and the counter is the next one (`Reached.counter`); each transition raises
the counter by the count of the identifiers it gives (`counter_rises`). So the identifiers
of a release are at or above the counter before it, given on no earlier step and held by no
earlier release (`Awaiting.release_fresh`). The hold of every released action ends a
bounded time after it (`Idle.hold_bounded`).

**The deadline rule.** No standing is stored. The standing of an `Awaiting` is the force
of the release before it with the awaited cycle (`Poised.standing`). The standing of an
`Idle` at an instant is the one that `Standing.during` gives for its last step
(`Calm.standing`), which is the convention of `Acorn.Timing`: at the instant of a release
and before it the percept still awaits, and after it the released action is in force. So
the verdict that the host returned by a release gives is the one of the step at every
instant, by definition (`Awaiting.release_standing`). A fault holds from the deadline to
the release, the instant of the release included, and the release is recorded as late
exactly when the deadline has passed (`Awaiting.release_fault`). During a fault the action
in force is the one of the release before, up to the end of its hold, and the world's
default from then (`Calm.fault_named`).

**Reading the clock** (`Idle.tick`, `Awaiting.tick`). In either phase the velocity of the
last release is sent again when `Bridge.tick` says so, as a request with a new identifier
that the release then holds, and nothing that the deadline rule or the next percept reads
changes (`Idle.tick_keeps`, `Awaiting.tick_keeps`). So the host keeps the preceding
velocity alive while the agent computes: while a percept awaits, what a reading of the
clock sends is the velocity of the action that the deadline rule names in force, and from
the end of that action's hold it sends nothing and the rule names the world's default
(`Awaiting.tick_named`).

What is not here: every effect. The three opening requests, two that subscribe and one
that enables the policy, have the identifiers below `opening`, and a host sends them when
it starts; their answers are held by no release and change nothing. A frame that a reader
refuses changes nothing here, so this state does not tell a stream that sends such frames
from one that sends nothing. That the daemon keeps in force the action that the standing
names is a fact about the daemon.
-/
namespace Acorn.Host.Microduck

/-! ## What shows an action -/

/-- The table of what shows an action: the policy that a state frame names while the
daemon executes the action. -/
inductive Action.Shown : Action → Policy → Prop where
  /-- Standing still is shown by the standing network. -/
  | still : Action.Shown .still .stand
  /-- Sitting still is shown by the sitting label. -/
  | seated : Action.Shown .still .sit
  /-- Walking forward is shown by the walking network. -/
  | forward : Action.Shown .forward .walk
  /-- Turning to the left is shown by the walking network. -/
  | turnLeft : Action.Shown .turnLeft .walk
  /-- Turning to the right is shown by the walking network. -/
  | turnRight : Action.Shown .turnRight .walk
  /-- Sitting is shown by the sitting label. -/
  | sit : Action.Shown .sit .sit
  /-- Standing up is shown by the rising label. -/
  | rise : Action.Shown .stand .rise
  /-- Standing is shown by the standing network. -/
  | stand : Action.Shown .stand .stand
  /-- The kick with the left foot is shown by its own label. -/
  | kickLeft : Action.Shown .kickLeft .kickLeft
  /-- The kick with the right foot is shown by its own label. -/
  | kickRight : Action.Shown .kickRight .kickRight
  /-- The pick is shown by its own label. -/
  | pick : Action.Shown .pick .groundPick
  /-- The forward roll is shown by its own label. -/
  | roll : Action.Shown .roll .roulade

/-- Whether a policy shows an action. -/
def Action.shows : Action → Policy → Bool
  | .still, .stand | .still, .sit => true
  | .forward, .walk | .turnLeft, .walk | .turnRight, .walk => true
  | .sit, .sit => true
  | .stand, .rise | .stand, .stand => true
  | .kickLeft, .kickLeft | .kickRight, .kickRight => true
  | .pick, .groundPick | .roll, .roulade => true
  | _, _ => false

/-- **The test of what shows an action is the table.** For every action and policy. -/
theorem Action.shows_iff (action : Action) (policy : Policy) :
    action.shows policy = true ↔ action.Shown policy := by
  constructor
  · intro shown
    cases action <;> cases policy <;> first
      | constructor
      | (exact absurd shown (by decide))
  · intro shown
    cases shown <;> rfl

/-- The body sits, by the label of a state frame. -/
def State.Sitting (state : State) : Prop :=
  state.policy = .sit

instance (state : State) : Decidable state.Sitting :=
  inferInstanceAs (Decidable (state.policy = .sit))

/-! ## A state frame with its depth frame -/

/-- A state frame with the depth frame that is paired with it. The depth frame is not
stamped after the state frame: a depth frame may not lead the state frame it is paired
with, so the age of a paired depth frame is an exact difference. -/
structure Pair where
  /-- The state frame. -/
  state : State
  /-- The depth frame paired with it, if one is. -/
  depth : Option Depth
  /-- The depth frame is stamped at or before the state frame. -/
  ordered : ∀ frame, depth = some frame →
    frame.taken.nanoseconds ≤ state.taken.nanoseconds

/-- A candidate depth frame, when it is stamped at or before a state frame. -/
def fitting (state : State) (candidate : Option Depth) : Option Depth :=
  candidate.filter fun frame => frame.taken.nanoseconds ≤ state.taken.nanoseconds

/-- A candidate that fits is stamped at or before the state frame. -/
theorem fitting_ordered (state : State) (candidate : Option Depth) (frame : Depth)
    (fits : fitting state candidate = some frame) :
    frame.taken.nanoseconds ≤ state.taken.nanoseconds := by
  have kept := (Option.filter_eq_some_iff.mp fits).2
  exact of_decide_eq_true kept

/-- The pair of a state frame with the later of two candidate depth frames that is stamped
at or before it: the latest one heard when it is, the one heard before it when that one
is, and no depth frame when neither is. -/
def Pair.of (state : State) (latest earlier : Option Depth) : Pair :=
  match first : fitting state latest with
  | some frame =>
    ⟨state, some frame, fun other same => by
      cases same
      exact fitting_ordered state latest _ first⟩
  | none =>
    match second : fitting state earlier with
    | some frame =>
      ⟨state, some frame, fun other same => by
        cases same
        exact fitting_ordered state earlier _ second⟩
    | none => ⟨state, none, fun _ wrong => nomatch wrong⟩

/-- The reading of a pair. -/
def Pair.reading (pair : Pair) : Reading :=
  ⟨pair.state, pair.depth⟩

/-! ## The requests of a release -/

/-- What a host holds of one release: the record of the release, the identifiers of its
requests that are not answered yet, and whether one was refused. -/
structure Sent where
  /-- The record of the release. -/
  record : Bridge
  /-- The identifiers of the commands of the release whose answers were not heard. -/
  awaited : List Nat
  /-- The identifiers of the velocities sent again whose answers were not heard. -/
  resent : List Nat
  /-- Whether an answer to one of these requests was a refusal. -/
  refused : Bool

/-- The daemon's answer to a release, as far as it was heard: refused when a request of the
release was refused, pending while a command of the release is not answered, and accepted
when every command of the release was accepted. -/
def Sent.reply (sent : Sent) : Reply :=
  if sent.refused then .refused
  else if sent.awaited.isEmpty then .accepted
  else .pending

/-- An answer to the request with an identifier is heard: when the release holds the
identifier, it holds it no more, and an answer that does not accept is a refusal. An
answer to a request that the release does not hold changes nothing. -/
def Sent.answer (id : Nat) (accepted : Bool) (sent : Sent) : Sent :=
  if sent.awaited.contains id || sent.resent.contains id then
    { sent with
      awaited := sent.awaited.erase id
      resent := sent.resent.erase id
      refused := sent.refused || !accepted }
  else sent

/-! ## The two phases of a host -/

/-- The force of a release record, and no action in force with no record. -/
def force (pace : Pace) (keep : Keep) (origin : Instant) : Option Bridge → Force Action
  | some bridge => bridge.force pace keep origin
  | none => ⟨none, none⟩

/-- What a host holds while no percept awaits its action: before the first percept, and
between a release and the next percept. -/
structure Calm where
  /-- The declared cycle and latency of the world. -/
  pace : Pace
  /-- What the bridge declares about keeping a velocity alive. -/
  keep : Keep
  /-- The instant of the host's clock that cycle zero starts at. -/
  origin : Instant
  /-- The next unused request identifier. -/
  next : Nat
  /-- The record of the release before the last one, if there was one. -/
  before : Option Bridge
  /-- The last release, if an action was released. -/
  last : Option Sent
  /-- The latest state frame heard since the last release. -/
  state : Option State
  /-- The latest depth frame heard. -/
  depth : Option Depth
  /-- The depth frame heard before the latest one. -/
  earlier : Option Depth
  /-- Whether a state frame heard since the last release showed its action. -/
  shown : Bool
  /-- Whether the last release missed its deadline. -/
  late : Bool
  /-- The latch of the goal, after the readings sensed so far. -/
  armed : Bool

/-- What a host holds while a percept awaits its action. -/
structure Poised where
  /-- The declared cycle and latency of the world. -/
  pace : Pace
  /-- What the bridge declares about keeping a velocity alive. -/
  keep : Keep
  /-- The instant of the host's clock that cycle zero starts at. -/
  origin : Instant
  /-- The next unused request identifier. -/
  next : Nat
  /-- The release before the percept, if an action was released. -/
  last : Option Sent
  /-- The latest depth frame heard. -/
  depth : Option Depth
  /-- The depth frame heard before the latest one. -/
  earlier : Option Depth
  /-- The latch of the goal, after the readings sensed so far, the awaited one included. -/
  armed : Bool
  /-- The cycle of the percept that awaits its action. -/
  index : Nat
  /-- Whether the body sat in the state frame of that percept. -/
  sitting : Bool

/-- The identifiers of the three requests that a host sends when it starts: the two that
subscribe and the one that enables the policy. A session gives none of them to a
command. -/
def opening : Nat := 3

/-- A host before its first event. -/
private def Calm.start (pace : Pace) (keep : Keep) (origin : Instant) : Calm :=
  ⟨pace, keep, origin, opening, none, none, none, none, none, false, false, false⟩

/-- Whether a state frame shows the action of a release. -/
private def showing (last : Option Sent) (frame : State) : Bool :=
  match last with
  | some sent => sent.record.action.shows frame.policy
  | none => false

/-- A line is heard while no percept awaits. -/
private def Calm.heard (calm : Calm) : Line → Calm
  | .state frame =>
    { calm with state := some frame, shown := calm.shown || showing calm.last frame }
  | .depth frame => { calm with depth := some frame, earlier := calm.depth }
  | .result id (some accepted) => { calm with last := calm.last.map (Sent.answer id accepted) }
  | .fault (some id) => { calm with last := calm.last.map (Sent.answer id false) }
  | .result _ none => calm
  | .fault none => calm
  | .unread _ => calm
  | .notice => calm
  | .invalid => calm

/-- The first cycle in which the next percept may be sensed: the cycle that the record of
the last release gives, and cycle zero before the first release. -/
def Calm.cycle (calm : Calm) : Nat :=
  match calm.last with
  | some sent => sent.record.next calm.pace calm.keep calm.origin
  | none => 0

/-- What a percept is built from. -/
structure Sensed where
  /-- The state frame and the depth frame paired with it. -/
  reading : Reading
  /-- What became of the action released last, if one was. -/
  outcome : Option Outcome
  /-- Whether that release missed its deadline. -/
  late : Bool
  /-- The latch of the goal before this reading. -/
  armed : Bool

/-- The percept that the adapter builds from what was sensed. -/
def Sensed.percept (sensed : Sensed) : Features.Percept Handcrafted.Microduck.interface :=
  Handcrafted.Microduck.percept sensed.armed sensed.reading sensed.outcome sensed.late

/-- A percept is sensed at an instant. -/
private def Calm.sensed (now : Instant) (calm : Calm) : Option (Poised × Sensed) :=
  match calm.state with
  | some frame =>
    if calm.cycle ≤ calm.pace.index calm.origin now then
      some (⟨calm.pace, calm.keep, calm.origin, calm.next, calm.last, calm.depth, calm.earlier,
          Handcrafted.Microduck.arm calm.armed (Pair.of frame calm.depth calm.earlier).reading,
          calm.pace.index calm.origin now, decide frame.Sitting⟩,
        ⟨(Pair.of frame calm.depth calm.earlier).reading,
          calm.last.map fun sent => sent.record.outcome sent.reply calm.shown,
          calm.late, calm.armed⟩)
    else none
  | none => none

/-- A line is heard while a percept awaits: a depth frame is kept, and nothing else. -/
private def Poised.heard (poised : Poised) : Line → Poised
  | .depth frame => { poised with depth := some frame, earlier := poised.depth }
  | .state _ => poised
  | .unread _ => poised
  | .notice => poised
  | .result _ _ => poised
  | .fault _ => poised
  | .invalid => poised

/-- What a tick of the bridge makes of what a host holds while a percept awaits: a velocity
sent again is a request with the next unused identifier, which the release before the
percept then holds. -/
private def Poised.resend (poised : Poised) (sent : Sent) :
    Bridge × Option Command → Poised × Option (Nat × Command)
  | (record, some command) =>
    ({ poised with
        next := poised.next + 1
        last := some { sent with record := record, resent := poised.next :: sent.resent } },
      some (poised.next, command))
  | (_, none) => (poised, none)

/-- The clock is read while a percept awaits. -/
private def Poised.ticked (now : Instant) (poised : Poised) : Poised × Option (Nat × Command) :=
  match poised.last with
  | some sent => poised.resend sent (sent.record.tick poised.pace poised.keep poised.origin now)
  | none => (poised, none)

/-- The standing of the deadline rule while a percept awaits: the force of the release
before it, and its cycle. -/
def Poised.standing (poised : Poised) : Standing Action :=
  .awaiting (force poised.pace poised.keep poised.origin (poised.last.map (·.record)))
    poised.index

/-- The action of the awaited percept is released at an instant, for the cycle it names. -/
private def Poised.released (index : Nat) (now : Instant) (action : Action) (poised : Poised) :
    Option (Calm × List (Nat × Command)) :=
  if index = poised.index then
    if (poised.pace.boundary poised.origin index).nanoseconds ≤ now.nanoseconds then
      some (⟨poised.pace, poised.keep, poised.origin,
          poised.next + (action.commands poised.sitting).length,
          poised.last.map (·.record),
          some ⟨(Bridge.release index now poised.sitting action).1,
            List.range' poised.next (action.commands poised.sitting).length, [], false⟩,
          none, poised.depth, poised.earlier, false,
          (poised.pace.outcome poised.origin (some Declared.rest) poised.standing now).fault,
          poised.armed⟩,
        (List.range' poised.next (action.commands poised.sitting).length).zip
          (action.commands poised.sitting))
    else none
  else none

/-- What a tick of the bridge makes of what a host holds: a velocity sent again is a
request with the next unused identifier, which the last release then holds. -/
private def Calm.resend (calm : Calm) (sent : Sent) :
    Bridge × Option Command → Calm × Option (Nat × Command)
  | (record, some command) =>
    ({ calm with
        next := calm.next + 1
        last := some { sent with record := record, resent := calm.next :: sent.resent } },
      some (calm.next, command))
  | (_, none) => (calm, none)

/-- The clock is read while no percept awaits. -/
private def Calm.ticked (now : Instant) (calm : Calm) : Calm × Option (Nat × Command) :=
  match calm.last with
  | some sent => calm.resend sent (sent.record.tick calm.pace calm.keep calm.origin now)
  | none => (calm, none)

/-- The standing of the deadline rule at an instant while no percept awaits: the one that
`Standing.during` gives for the last step, with the force of the release before it as the
prior force. So at the instant of the last release, and before it, the percept of that step
still awaits; after it the released action is in force. Before the first release no action
is in force. -/
def Calm.standing (calm : Calm) (now : Instant) : Standing Action :=
  match calm.last with
  | some sent =>
    Standing.during (force calm.pace calm.keep calm.origin calm.before) sent.record.index
      sent.record.released (sent.record.force calm.pace calm.keep calm.origin) now
  | none => .idle ⟨none, none⟩

/-! ## Reachability -/

/-- A state of a host, in one of its two phases. -/
inductive Phase where
  /-- No percept awaits its action. -/
  | idle (calm : Calm)
  /-- A percept awaits its action. -/
  | awaiting (poised : Poised)

/-- The identifier of a request that a reading of the clock sent, if it sent one. -/
def issue (sent : Option (Nat × Command)) : List Nat :=
  match sent with
  | some pair => [pair.1]
  | none => []

/-- The state is reached from the start by the transitions, with the readings that were
sensed on the way and the identifiers that were given to requests on the way, each in
order. There is one constructor for each transition, and no other way to a state. -/
inductive Reached : List Reading → List Nat → Phase → Prop where
  /-- A host starts. -/
  | start (pace : Pace) (keep : Keep) (origin : Instant) :
      Reached [] [] (.idle (Calm.start pace keep origin))
  /-- A line is heard while no percept awaits. -/
  | hear {readings : List Reading} {issued : List Nat} {calm : Calm}
      (reached : Reached readings issued (.idle calm)) (line : Line) :
      Reached readings issued (.idle (calm.heard line))
  /-- The clock is read while no percept awaits. -/
  | tick {readings : List Reading} {issued : List Nat} {calm : Calm}
      (reached : Reached readings issued (.idle calm)) (now : Instant) :
      Reached readings (issued ++ issue (calm.ticked now).2) (.idle (calm.ticked now).1)
  /-- A percept is sensed. -/
  | sense {readings : List Reading} {issued : List Nat} {calm : Calm}
      (reached : Reached readings issued (.idle calm)) (now : Instant) {poised : Poised}
      {sensed : Sensed} (admitted : calm.sensed now = some (poised, sensed)) :
      Reached (readings ++ [sensed.reading]) issued (.awaiting poised)
  /-- A line is heard while a percept awaits. -/
  | listen {readings : List Reading} {issued : List Nat} {poised : Poised}
      (reached : Reached readings issued (.awaiting poised)) (line : Line) :
      Reached readings issued (.awaiting (poised.heard line))
  /-- The clock is read while a percept awaits. -/
  | watch {readings : List Reading} {issued : List Nat} {poised : Poised}
      (reached : Reached readings issued (.awaiting poised)) (now : Instant) :
      Reached readings (issued ++ issue (poised.ticked now).2) (.awaiting (poised.ticked now).1)
  /-- The action of the awaited percept is released. -/
  | release {readings : List Reading} {issued : List Nat} {poised : Poised}
      (reached : Reached readings issued (.awaiting poised)) (index : Nat) (now : Instant)
      (action : Action) {calm : Calm} {commands : List (Nat × Command)}
      (admitted : poised.released index now action = some (calm, commands)) :
      Reached readings (issued ++ commands.map fun pair => pair.1) (.idle calm)

/-- A host while no percept awaits its action. Every value has a derivation from the start
by the transitions. -/
structure Idle where
  /-- What the host holds. -/
  calm : Calm
  /-- The state is reached from the start. -/
  reached : ∃ readings issued, Reached readings issued (.idle calm)

/-- A host while a percept awaits its action. Every value has a derivation from the start
by the transitions, so the awaited percept was sensed. -/
structure Awaiting where
  /-- What the host holds. -/
  poised : Poised
  /-- The state is reached from the start. -/
  reached : ∃ readings issued, Reached readings issued (.awaiting poised)

/-- A host before its first event: no action was released, no frame was heard and no
percept awaits. Its first unused identifier is after those of the opening requests. -/
def Idle.start (pace : Pace) (keep : Keep) (origin : Instant) : Idle :=
  ⟨Calm.start pace keep origin, [], [], .start pace keep origin⟩

/-- One line of a daemon is heard while no percept awaits. A state frame replaces the
latest one and is tested for showing the action of the last release; it is paired with a
depth frame only when a percept is sensed (`Idle.sense`). A depth frame becomes the latest
one, and the one before it the earlier one. A result or a fault with the identifier of a
request of the last release answers it. Every other line changes nothing. -/
def Idle.hear (idle : Idle) (line : Line) : Idle :=
  ⟨idle.calm.heard line,
    idle.reached.elim fun _ found => found.elim fun _ reached => ⟨_, _, reached.hear line⟩⟩

/-- The clock is read while no percept awaits: the velocity of the last release is sent
again when the bridge says so, as a request with a new identifier. -/
def Idle.tick (now : Instant) (idle : Idle) : Idle × Option (Nat × Command) :=
  (⟨(idle.calm.ticked now).1,
      idle.reached.elim fun _ found => found.elim fun _ reached => ⟨_, _, reached.tick now⟩⟩,
    (idle.calm.ticked now).2)

/-- A percept is sensed at an instant, for the cycle the instant falls in. There is one
only when the cycle is not before the first cycle that the last release allows and a state
frame was heard since that release. The state frame is used up, and the latch of the goal
advances by the reading. -/
def Idle.sense (now : Instant) (idle : Idle) : Option (Awaiting × Sensed) :=
  match admitted : idle.calm.sensed now with
  | some (poised, sensed) =>
    some (⟨poised, idle.reached.elim fun _ found => found.elim fun _ reached =>
      ⟨_, _, reached.sense now admitted⟩⟩, sensed)
  | none => none

/-- One line of a daemon is heard while a percept awaits: a depth frame becomes the latest
one, and every other line changes nothing. -/
def Awaiting.hear (awaiting : Awaiting) (line : Line) : Awaiting :=
  ⟨awaiting.poised.heard line,
    awaiting.reached.elim fun _ found => found.elim fun _ reached =>
      ⟨_, _, reached.listen line⟩⟩

/-- The clock is read while a percept awaits: the velocity of the release before the
percept is sent again when the bridge says so, as a request with a new identifier. So a
host can keep the preceding action in force while the agent computes, up to the end of
its hold. -/
def Awaiting.tick (now : Instant) (awaiting : Awaiting) : Awaiting × Option (Nat × Command) :=
  (⟨(awaiting.poised.ticked now).1,
      awaiting.reached.elim fun _ found => found.elim fun _ reached =>
        ⟨_, _, reached.watch now⟩⟩,
    (awaiting.poised.ticked now).2)

/-- The action of the awaited percept is released at an instant, for the cycle it names:
the state after the release, and the commands to send, each with a new identifier. Nothing
is released for another cycle than the awaited one, and nothing at an instant before the
start of that cycle. -/
def Awaiting.release (index : Nat) (now : Instant) (action : Action) (awaiting : Awaiting) :
    Option (Idle × List (Nat × Command)) :=
  match admitted : awaiting.poised.released index now action with
  | some (calm, commands) =>
    some (⟨calm, awaiting.reached.elim fun _ found => found.elim fun _ reached =>
      ⟨_, _, reached.release index now action admitted⟩⟩, commands)
  | none => none

/-! ## The answer to a release -/

/-- **The three states of the answer to a release.** For every release as a host holds it:
the answer is a refusal exactly when a request of the release was refused; it is accepted
exactly when none was refused and every command of the release was answered; and it is
pending exactly when none was refused and a command of the release is not answered. -/
theorem Sent.reply_iff (sent : Sent) :
    (sent.reply = .refused ↔ sent.refused = true) ∧
      (sent.reply = .accepted ↔ sent.refused = false ∧ sent.awaited = []) ∧
      (sent.reply = .pending ↔ sent.refused = false ∧ sent.awaited ≠ []) := by
  unfold Sent.reply
  cases sent.refused with
  | true => simp
  | false =>
    cases sent.awaited with
    | nil => simp
    | cons head tail => simp

/-- **An answer counts only for the release that holds its identifier.** For every release
as a host holds it, identifier and answer: when the release holds the identifier, among its
commands or among its resent velocities, the answer removes it and a refusing answer makes
the release refused; when it does not, nothing changes. The record of the release is never
changed. -/
theorem Sent.answer_iff (id : Nat) (accepted : Bool) (sent : Sent) :
    (sent.answer id accepted).record = sent.record ∧
      ((id ∈ sent.awaited ∨ id ∈ sent.resent) →
        (sent.answer id accepted).awaited = sent.awaited.erase id ∧
          (sent.answer id accepted).resent = sent.resent.erase id ∧
          (sent.answer id accepted).refused = (sent.refused || !accepted)) ∧
      (id ∉ sent.awaited → id ∉ sent.resent → sent.answer id accepted = sent) := by
  unfold Sent.answer
  split
  · rename_i held
    refine ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun first second => ?_⟩
    simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at held
    exact absurd held (fun either => either.elim first second)
  · rename_i held
    refine ⟨rfl, fun either => ?_, fun _ _ => rfl⟩
    simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at held
    exact absurd either held

/-- The identifiers that a release holds after an answer are among those it held. -/
private theorem Sent.answer_subset (id : Nat) (accepted : Bool) (sent : Sent) (other : Nat)
    (held : other ∈ (sent.answer id accepted).awaited ++ (sent.answer id accepted).resent) :
    other ∈ sent.awaited ++ sent.resent := by
  unfold Sent.answer at held
  split at held
  · rcases List.mem_append.mp held with first | second
    · exact List.mem_append_left _ (List.mem_of_mem_erase first)
    · exact List.mem_append_right _ (List.mem_of_mem_erase second)
  · exact held

/-! ## Sensing and releasing -/

/-- The sensing of the sealed type is the sensing of what it holds. -/
private theorem Idle.sense_sensed (now : Instant) (idle : Idle) (awaiting : Awaiting)
    (sensed : Sensed) :
    idle.sense now = some (awaiting, sensed) ↔
      idle.calm.sensed now = some (awaiting.poised, sensed) := by
  unfold Idle.sense
  constructor
  · intro found
    split at found
    · rename_i poised other admitted
      cases Option.some.inj found
      exact admitted
    · exact nomatch found
  · intro admitted
    split
    · rename_i poised other again
      cases Option.some.inj (admitted.symm.trans again)
      rfl
    · rename_i missing
      rw [admitted] at missing
      exact nomatch missing

/-- **When a percept is sensed, and what it is built from.** For every instant and host
with no percept awaiting: a percept is sensed exactly when a state frame is held and the
cycle of the instant is not before the first cycle that the last release allows. The
reading is that state frame paired, by `Pair.of`, with the later of the two depth frames
held that is stamped at or before it; what became of the preceding action is the outcome of
the last release for its answer and the evidence; and the state after it awaits the action
of the instant's cycle, holds whether the body sat in the state frame, and holds the latch
advanced by the reading. -/
theorem Idle.sense_iff (now : Instant) (idle : Idle) (awaiting : Awaiting) (sensed : Sensed) :
    idle.sense now = some (awaiting, sensed) ↔
      ∃ frame, idle.calm.state = some frame ∧
        idle.calm.cycle ≤ idle.calm.pace.index idle.calm.origin now ∧
        awaiting.poised = ⟨idle.calm.pace, idle.calm.keep, idle.calm.origin, idle.calm.next,
          idle.calm.last, idle.calm.depth, idle.calm.earlier,
          Handcrafted.Microduck.arm idle.calm.armed
            (Pair.of frame idle.calm.depth idle.calm.earlier).reading,
          idle.calm.pace.index idle.calm.origin now, decide frame.Sitting⟩ ∧
        sensed = ⟨(Pair.of frame idle.calm.depth idle.calm.earlier).reading,
          idle.calm.last.map fun sent => sent.record.outcome sent.reply idle.calm.shown,
          idle.calm.late, idle.calm.armed⟩ := by
  rw [Idle.sense_sensed]
  unfold Calm.sensed
  constructor
  · intro found
    split at found
    · rename_i frame held
      split at found
      · rename_i due
        have same := Prod.mk.inj (Option.some.inj found)
        exact ⟨frame, held, due, same.1.symm, same.2.symm⟩
      · exact nomatch found
    · exact nomatch found
  · rintro ⟨frame, held, due, poised, rfl⟩
    rw [poised]
    simp only [held, due, ↓reduceIte]

/-- **A percept is sensed exactly when a state frame is held and the cycle is due.** For
every instant and host with no percept awaiting. -/
theorem Idle.sense_admitted (now : Instant) (idle : Idle) :
    (idle.sense now).isSome = true ↔
      (∃ frame, idle.calm.state = some frame) ∧
        idle.calm.cycle ≤ idle.calm.pace.index idle.calm.origin now := by
  constructor
  · intro found
    obtain ⟨⟨awaiting, sensed⟩, same⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨frame, held, due, _⟩ := (Idle.sense_iff now idle awaiting sensed).mp same
    exact ⟨⟨frame, held⟩, due⟩
  · rintro ⟨⟨frame, held⟩, due⟩
    unfold Idle.sense
    split
    · rfl
    · rename_i missing
      unfold Calm.sensed at missing
      simp only [held, due, ↓reduceIte] at missing
      exact nomatch missing

/-- The release of the sealed type is the release of what it holds. -/
private theorem Awaiting.release_released (index : Nat) (now : Instant) (action : Action)
    (awaiting : Awaiting) (idle : Idle) (commands : List (Nat × Command)) :
    awaiting.release index now action = some (idle, commands) ↔
      awaiting.poised.released index now action = some (idle.calm, commands) := by
  unfold Awaiting.release
  constructor
  · intro found
    split at found
    · rename_i calm other admitted
      cases Option.some.inj found
      exact admitted
    · exact nomatch found
  · intro admitted
    split
    · rename_i calm other again
      cases Option.some.inj (admitted.symm.trans again)
      rfl
    · rename_i missing
      rw [admitted] at missing
      exact nomatch missing

/-- **When an action is released, what is sent and what is recorded.** For every cycle,
instant, action and host with a percept awaiting: the action is released exactly when the
cycle is the awaited one and has started at the instant. The commands are the action's for
the posture of the percept's state frame, each with one of the next unused identifiers in
order. The state after it holds the record of the release with those identifiers awaited,
the record of the release before it, no state frame, no evidence, and whether the release
is late, which is whether `Pace.outcome` has a fault at the instant for the standing of the
awaiting host. -/
theorem Awaiting.release_iff (index : Nat) (now : Instant) (action : Action)
    (awaiting : Awaiting) (idle : Idle) (commands : List (Nat × Command)) :
    awaiting.release index now action = some (idle, commands) ↔
      index = awaiting.poised.index ∧
        (awaiting.poised.pace.boundary awaiting.poised.origin index).nanoseconds ≤
          now.nanoseconds ∧
        idle.calm = ⟨awaiting.poised.pace, awaiting.poised.keep, awaiting.poised.origin,
          awaiting.poised.next + (action.commands awaiting.poised.sitting).length,
          awaiting.poised.last.map (·.record),
          some ⟨(Bridge.release index now awaiting.poised.sitting action).1,
            List.range' awaiting.poised.next (action.commands awaiting.poised.sitting).length,
            [], false⟩,
          none, awaiting.poised.depth, awaiting.poised.earlier, false,
          (awaiting.poised.pace.outcome awaiting.poised.origin (some Declared.rest)
            awaiting.poised.standing now).fault,
          awaiting.poised.armed⟩ ∧
        commands =
          (List.range' awaiting.poised.next (action.commands awaiting.poised.sitting).length).zip
            (action.commands awaiting.poised.sitting) := by
  rw [Awaiting.release_released]
  unfold Poised.released
  constructor
  · intro found
    split at found
    · rename_i named
      split at found
      · rename_i begun
        have same := Prod.mk.inj (Option.some.inj found)
        exact ⟨named, begun, same.1.symm, same.2.symm⟩
      · exact nomatch found
    · exact nomatch found
  · rintro ⟨rfl, begun, calm, rfl⟩
    rw [calm]
    simp only [begun, ↓reduceIte]

/-! ## The standing of the deadline rule -/

/-- **The verdict of the host after a release is the one of the step, at every instant.**
For every admitted release at an instant, and every instant: the standing of the host
after the release is the one that `Standing.during` gives for the step, with the force that
stood while the percept awaited as the prior force and the force of the release's record as
the chosen one. This is the definition of the standing of the returned host, so the
statements of `Acorn.Timing` about one step are about it as they stand: at the instant of
the release and before it the percept awaits, and after it the released action is in
force. -/
theorem Awaiting.release_standing (index : Nat) (released : Instant) (action : Action)
    (awaiting : Awaiting) (idle : Idle) (commands : List (Nat × Command))
    (admitted : awaiting.release index released action = some (idle, commands))
    (now : Instant) :
    idle.calm.standing now =
      Standing.during awaiting.poised.standing.force index released
        ((Bridge.release index released awaiting.poised.sitting action).1.force
          awaiting.poised.pace awaiting.poised.keep awaiting.poised.origin) now := by
  obtain ⟨_, _, calm, _⟩ :=
    (Awaiting.release_iff index released action awaiting idle commands).mp admitted
  rw [calm]
  rfl

/-- **A fault holds from the deadline to the release, the instant of the release
included, and the release is recorded as late exactly when the deadline has passed.** For
every admitted release at an instant for a cycle: for every instant, `Pace.outcome` has a
fault for the host after the release exactly when the instant is at or after the deadline
of the cycle and at or before the release; and the host records a late release exactly when
the release is at or after the deadline. -/
theorem Awaiting.release_fault (index : Nat) (released : Instant) (action : Action)
    (awaiting : Awaiting) (idle : Idle) (commands : List (Nat × Command))
    (admitted : awaiting.release index released action = some (idle, commands)) :
    (∀ now : Instant,
      (idle.calm.pace.outcome idle.calm.origin (some Declared.rest) (idle.calm.standing now)
          now).fault = true ↔
        (idle.calm.pace.deadline idle.calm.origin index).nanoseconds ≤ now.nanoseconds ∧
          now.nanoseconds ≤ released.nanoseconds) ∧
      (idle.calm.late = true ↔
        (idle.calm.pace.deadline idle.calm.origin index).nanoseconds ≤
          released.nanoseconds) := by
  have standing := Awaiting.release_standing index released action awaiting idle commands
    admitted
  obtain ⟨named, _, calm, _⟩ :=
    (Awaiting.release_iff index released action awaiting idle commands).mp admitted
  have paced : idle.calm.pace = awaiting.poised.pace := by rw [calm]
  have started : idle.calm.origin = awaiting.poised.origin := by rw [calm]
  refine ⟨fun now => ?_, ?_⟩
  · rw [standing now]
    exact idle.calm.pace.step_fault idle.calm.origin _ _ index released _ now
  · have late : idle.calm.late = (awaiting.poised.pace.outcome awaiting.poised.origin
        (some Declared.rest) awaiting.poised.standing released).fault := by rw [calm]
    rw [late, paced, started, awaiting.poised.pace.outcome_fault awaiting.poised.origin]
    constructor
    · rintro ⟨_, _, same, passed⟩
      cases same
      rw [named]
      exact passed
    · intro passed
      exact ⟨_, _, rfl, named ▸ passed⟩

/-- **During a fault the action in force is the one of the release before, up to the end of
its hold.** For every state of a host with no percept awaiting, and every instant at which
`Pace.outcome` has a fault for it: the action in force is the action of the release before
the last one before the end of its hold and the world's default from then; and no action
when there was no release before the last one. -/
theorem Calm.fault_named (calm : Calm) (now : Instant)
    (fault : (calm.pace.outcome calm.origin (some Declared.rest) (calm.standing now) now).fault =
      true) :
    (calm.pace.outcome calm.origin (some Declared.rest) (calm.standing now) now).action =
      match calm.before with
      | some bridge =>
        if now.nanoseconds < (bridge.ends calm.pace calm.keep calm.origin).nanoseconds then
          some bridge.action
        else some Declared.rest
      | none => none := by
  unfold Calm.standing at fault ⊢
  cases held : calm.last with
  | none =>
    rw [held] at fault
    exact nomatch fault
  | some sent =>
    rw [held] at fault
    cases prior : calm.before with
    | some bridge =>
      rw [prior] at fault
      exact Bridge.fault_named calm.pace calm.keep calm.origin (some Declared.rest) bridge
        sent.record.index sent.record.released _ now fault
    | none =>
      rw [prior] at fault
      have awaited := (calm.pace.step_fault calm.origin (some Declared.rest) ⟨none, none⟩
        sent.record.index sent.record.released _ now).mp fault
      show (calm.pace.outcome calm.origin (some Declared.rest)
        (Standing.during ⟨none, none⟩ sent.record.index sent.record.released
          (sent.record.force calm.pace calm.keep calm.origin) now) now).action = none
      rw [calm.pace.step_action calm.origin]
      simp only [awaited.2, ↓reduceIte]
      rfl

/-! ## Hearing a line and reading the clock -/

/-- **What hearing a line changes while no percept awaits.** For every host and line. The
settings, the next identifier, the record before the last, the late release and the latch
are as before, and so are the record of the last release and the standing of the deadline
rule at every instant. A result with a boolean, and a fault with an identifier, answer the
request with that identifier in the last release; no other line changes what the host
holds of the last release. -/
theorem Idle.hear_keeps (idle : Idle) (line : Line) :
    (idle.hear line).calm.pace = idle.calm.pace ∧ (idle.hear line).calm.keep = idle.calm.keep ∧
      (idle.hear line).calm.origin = idle.calm.origin ∧
      (idle.hear line).calm.next = idle.calm.next ∧
      (idle.hear line).calm.before = idle.calm.before ∧
      (idle.hear line).calm.late = idle.calm.late ∧
      (idle.hear line).calm.armed = idle.calm.armed ∧
      (idle.hear line).calm.last.map (·.record) = idle.calm.last.map (·.record) ∧
      (∀ now, (idle.hear line).calm.standing now = idle.calm.standing now) ∧
      (idle.hear line).calm.last =
        match line with
        | .result id (some accepted) => idle.calm.last.map (Sent.answer id accepted)
        | .fault (some id) => idle.calm.last.map (Sent.answer id false)
        | _ => idle.calm.last := by
  have answered : ∀ (id : Nat) (accepted : Bool),
      (idle.calm.last.map (Sent.answer id accepted)).map (·.record) =
        idle.calm.last.map (·.record) := fun id accepted => by
    cases idle.calm.last with
    | none => rfl
    | some sent => exact congrArg some (sent.answer_iff id accepted).1
  have stood : ∀ (id : Nat) (accepted : Bool) (now : Instant),
      Calm.standing { idle.calm with last := idle.calm.last.map (Sent.answer id accepted) } now =
        idle.calm.standing now := fun id accepted now => by
    unfold Calm.standing
    cases idle.calm.last with
    | none => rfl
    | some sent =>
      show Standing.during _ (sent.answer id accepted).record.index
        (sent.answer id accepted).record.released _ now = _
      rw [(sent.answer_iff id accepted).1]
  show (idle.calm.heard line).pace = _ ∧ _
  cases line with
  | state frame => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  | depth frame => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  | unread stream => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  | notice => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  | invalid => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  | result id accepted =>
    cases accepted with
    | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
    | some value =>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, answered id value, stood id value, rfl⟩
  | fault id =>
    cases id with
    | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
    | some number =>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, answered number false, stood number false, rfl⟩

/-- The state frame of a line, when the line is one. -/
def Line.stateFrame : Line → Option State
  | .state frame => some frame
  | _ => none

/-- The depth frame of a line, when the line is one. -/
def Line.depthFrame : Line → Option Depth
  | .depth frame => some frame
  | _ => none

/-- **The frames a host holds after hearing a line.** For every host with no percept
awaiting and every line: a state frame becomes the state frame held, and a depth frame
becomes the latest depth frame held, with the one that was the latest as the earlier one;
every other line leaves the three as they are. -/
theorem Idle.hear_frame (idle : Idle) (line : Line) :
    (idle.hear line).calm.state = (line.stateFrame.map some).getD idle.calm.state ∧
      ((idle.hear line).calm.depth, (idle.hear line).calm.earlier) =
        match line.depthFrame with
        | some frame => (some frame, idle.calm.depth)
        | none => (idle.calm.depth, idle.calm.earlier) := by
  show (idle.calm.heard line).state = _ ∧
    ((idle.calm.heard line).depth, (idle.calm.heard line).earlier) = _
  cases line with
  | result id accepted => cases accepted <;> exact ⟨rfl, rfl⟩
  | fault id => cases id <;> exact ⟨rfl, rfl⟩
  | state _ | depth _ | unread _ | notice | invalid => exact ⟨rfl, rfl⟩

/-- **The frames held are a function of the frames heard on each stream, and not of how
the two streams are interleaved.** For every host with no percept awaiting and every list
of lines heard in order: the state frame held is the last state frame of the list, or the
one held before when the list has none; and the two depth frames held are the last two
depth frames heard, counting those held before. Each is computed from the frames of one
stream alone, in their order, so two lists of lines with the same state frames in order
and the same depth frames in order leave the same three frames. The reading of the next
percept is `Pair.of` of those three, so it does not depend on the interleaving either. A
host keeps two depth frames: a state frame is paired with a depth frame when one of the
two latest depth frames heard is stamped at or before it. -/
theorem Idle.heard_frames (lines : List Line) (idle : Idle) :
    (lines.foldl Idle.hear idle).calm.state =
        (lines.filterMap Line.stateFrame).foldl (fun _ frame => some frame) idle.calm.state ∧
      ((lines.foldl Idle.hear idle).calm.depth, (lines.foldl Idle.hear idle).calm.earlier) =
        (lines.filterMap Line.depthFrame).foldl
          (fun (cache : Option Depth × Option Depth) frame => (some frame, cache.1))
          (idle.calm.depth, idle.calm.earlier) := by
  induction lines generalizing idle with
  | nil => exact ⟨rfl, rfl⟩
  | cons line rest hold =>
    obtain ⟨held, cached⟩ := idle.hear_frame line
    obtain ⟨later, cache⟩ := hold (idle.hear line)
    rw [List.foldl_cons, later, cache, held, cached]
    cases line with
    | state frame => exact ⟨rfl, rfl⟩
    | depth frame => exact ⟨rfl, rfl⟩
    | result id accepted => exact ⟨rfl, rfl⟩
    | fault id => exact ⟨rfl, rfl⟩
    | unread stream => exact ⟨rfl, rfl⟩
    | notice => exact ⟨rfl, rfl⟩
    | invalid => exact ⟨rfl, rfl⟩

/-- **The action is shown exactly when a state frame showed it.** For every host with no
percept awaiting and every line: after the line the evidence holds exactly when it held
before, or the line is a state frame whose policy the table gives for the action of the
last release. -/
theorem Idle.hear_shown (idle : Idle) (line : Line) :
    (idle.hear line).calm.shown = true ↔
      idle.calm.shown = true ∨
        ∃ frame sent, line = .state frame ∧ idle.calm.last = some sent ∧
          sent.record.action.Shown frame.policy := by
  show (idle.calm.heard line).shown = true ↔ _
  cases line with
  | state frame =>
    show (idle.calm.shown || showing idle.calm.last frame) = true ↔ _
    rw [Bool.or_eq_true]
    unfold showing
    constructor
    · rintro (kept | shows)
      · exact .inl kept
      · cases held : idle.calm.last with
        | none =>
          rw [held] at shows
          exact nomatch shows
        | some sent =>
          rw [held] at shows
          exact .inr ⟨frame, sent, rfl, rfl, (sent.record.action.shows_iff _).mp shows⟩
    · rintro (kept | ⟨_, sent, same, held, shown⟩)
      · exact .inl kept
      · cases same
        rw [held]
        exact .inr ((sent.record.action.shows_iff _).mpr shown)
  | result id accepted =>
    have kept : (idle.calm.heard (.result id accepted)).shown = idle.calm.shown := by
      cases accepted <;> rfl
    rw [kept]
    exact ⟨fun held => .inl held, fun
      | .inl held => held
      | .inr ⟨_, _, wrong, _⟩ => nomatch wrong⟩
  | fault id =>
    have kept : (idle.calm.heard (.fault id)).shown = idle.calm.shown := by
      cases id <;> rfl
    rw [kept]
    exact ⟨fun held => .inl held, fun
      | .inl held => held
      | .inr ⟨_, _, wrong, _⟩ => nomatch wrong⟩
  | depth _ | unread _ | notice | invalid =>
    exact ⟨fun held => .inl held, fun
      | .inl held => held
      | .inr ⟨_, _, wrong, _⟩ => nomatch wrong⟩

/-- A tick of the bridge changes neither the cycle nor the instant of the release. -/
private theorem tick_record (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) :
    (bridge.tick pace keep origin now).1.index = bridge.index ∧
      (bridge.tick pace keep origin now).1.released = bridge.released ∧
      (bridge.tick pace keep origin now).1.force pace keep origin =
        bridge.force pace keep origin := by
  obtain ⟨action, _, _, ends⟩ := bridge.tick_keeps pace keep origin now
  refine ⟨?_, ?_, ?_⟩
  · unfold Bridge.tick
    split <;> rfl
  · unfold Bridge.tick
    split <;> rfl
  · unfold Bridge.force
    rw [action, ends]

/-- What a reading of the clock sends and keeps, for what the host holds. -/
private theorem Calm.ticked_keeps (now : Instant) (calm : Calm) :
    (calm.ticked now).2 =
        (calm.last.bind fun sent =>
          (sent.record.tick calm.pace calm.keep calm.origin now).2.map
            fun command => (calm.next, command)) ∧
      (calm.ticked now).1.pace = calm.pace ∧
      (calm.ticked now).1.keep = calm.keep ∧
      (calm.ticked now).1.origin = calm.origin ∧
      (calm.ticked now).1.before = calm.before ∧
      (calm.ticked now).1.state = calm.state ∧
      (calm.ticked now).1.shown = calm.shown ∧
      (calm.ticked now).1.late = calm.late ∧
      (calm.ticked now).1.armed = calm.armed ∧
      (∀ instant, (calm.ticked now).1.standing instant = calm.standing instant) ∧
      (calm.ticked now).1.cycle = calm.cycle := by
  have resent : ∀ (sent : Sent) (result : Bridge × Option Command),
      calm.last = some sent → result.1.index = sent.record.index →
      result.1.released = sent.record.released →
      result.1.force calm.pace calm.keep calm.origin =
        sent.record.force calm.pace calm.keep calm.origin →
      result.1.next calm.pace calm.keep calm.origin =
        sent.record.next calm.pace calm.keep calm.origin →
      (calm.resend sent result).2 = result.2.map (fun command => (calm.next, command)) ∧
        (calm.resend sent result).1.pace = calm.pace ∧
        (calm.resend sent result).1.keep = calm.keep ∧
        (calm.resend sent result).1.origin = calm.origin ∧
        (calm.resend sent result).1.before = calm.before ∧
        (calm.resend sent result).1.state = calm.state ∧
        (calm.resend sent result).1.shown = calm.shown ∧
        (calm.resend sent result).1.late = calm.late ∧
        (calm.resend sent result).1.armed = calm.armed ∧
        (∀ instant, (calm.resend sent result).1.standing instant = calm.standing instant) ∧
        (calm.resend sent result).1.cycle = calm.cycle := by
    intro sent result held index released forced next
    obtain ⟨record, command⟩ := result
    cases command with
    | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
    | some command =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun instant => ?_, ?_⟩
      · show Standing.during _ record.index record.released
          (record.force calm.pace calm.keep calm.origin) instant = calm.standing instant
        unfold Calm.standing
        rw [held, show record.index = sent.record.index from index,
          show record.released = sent.record.released from released,
          show record.force calm.pace calm.keep calm.origin =
            sent.record.force calm.pace calm.keep calm.origin from forced]
        rfl
      · show record.next calm.pace calm.keep calm.origin = calm.cycle
        unfold Calm.cycle
        rw [held]
        exact next
  unfold Calm.ticked
  cases held : calm.last with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  | some sent =>
    obtain ⟨index, released, forced⟩ :=
      tick_record calm.pace calm.keep calm.origin sent.record now
    exact resent sent _ held index released forced
      (sent.record.tick_keeps calm.pace calm.keep calm.origin now).2.2.1

/-- **A reading of the clock sends what the bridge's tick sends, with a new identifier, and
changes nothing that the deadline rule or the next percept reads.** For every instant and
host with no percept awaiting: the command is the one of `Bridge.tick` for the record of
the last release, with the host's next unused identifier, and none for a host that has
released nothing; the settings, the state frame held, the evidence, the late release, the
latch and the record before the last are as before; and the standing of the deadline rule
at every instant and the first cycle of the next percept are as before. -/
theorem Idle.tick_keeps (now : Instant) (idle : Idle) :
    (idle.tick now).2 =
        (idle.calm.last.bind fun sent =>
          (sent.record.tick idle.calm.pace idle.calm.keep idle.calm.origin now).2.map
            fun command => (idle.calm.next, command)) ∧
      (idle.tick now).1.calm.pace = idle.calm.pace ∧
      (idle.tick now).1.calm.keep = idle.calm.keep ∧
      (idle.tick now).1.calm.origin = idle.calm.origin ∧
      (idle.tick now).1.calm.before = idle.calm.before ∧
      (idle.tick now).1.calm.state = idle.calm.state ∧
      (idle.tick now).1.calm.shown = idle.calm.shown ∧
      (idle.tick now).1.calm.late = idle.calm.late ∧
      (idle.tick now).1.calm.armed = idle.calm.armed ∧
      (∀ instant, (idle.tick now).1.calm.standing instant = idle.calm.standing instant) ∧
      (idle.tick now).1.calm.cycle = idle.calm.cycle :=
  Calm.ticked_keeps now idle.calm

/-- What a reading of the clock sends and keeps while a percept awaits, for what the host
holds. -/
private theorem Poised.ticked_keeps (now : Instant) (poised : Poised) :
    (poised.ticked now).2 =
        (poised.last.bind fun sent =>
          (sent.record.tick poised.pace poised.keep poised.origin now).2.map
            fun command => (poised.next, command)) ∧
      (poised.ticked now).1.pace = poised.pace ∧
      (poised.ticked now).1.keep = poised.keep ∧
      (poised.ticked now).1.origin = poised.origin ∧
      (poised.ticked now).1.depth = poised.depth ∧
      (poised.ticked now).1.earlier = poised.earlier ∧
      (poised.ticked now).1.armed = poised.armed ∧
      (poised.ticked now).1.index = poised.index ∧
      (poised.ticked now).1.sitting = poised.sitting ∧
      (poised.ticked now).1.standing = poised.standing := by
  have resent : ∀ (sent : Sent) (result : Bridge × Option Command),
      poised.last = some sent →
      result.1.force poised.pace poised.keep poised.origin =
        sent.record.force poised.pace poised.keep poised.origin →
      (poised.resend sent result).2 = result.2.map (fun command => (poised.next, command)) ∧
        (poised.resend sent result).1.pace = poised.pace ∧
        (poised.resend sent result).1.keep = poised.keep ∧
        (poised.resend sent result).1.origin = poised.origin ∧
        (poised.resend sent result).1.depth = poised.depth ∧
        (poised.resend sent result).1.earlier = poised.earlier ∧
        (poised.resend sent result).1.armed = poised.armed ∧
        (poised.resend sent result).1.index = poised.index ∧
        (poised.resend sent result).1.sitting = poised.sitting ∧
        (poised.resend sent result).1.standing = poised.standing := by
    intro sent result held forced
    obtain ⟨record, command⟩ := result
    cases command with
    | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some command =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      show Standing.awaiting (record.force poised.pace poised.keep poised.origin) poised.index =
        poised.standing
      unfold Poised.standing
      rw [held, show record.force poised.pace poised.keep poised.origin =
        sent.record.force poised.pace poised.keep poised.origin from forced]
      rfl
  unfold Poised.ticked
  cases held : poised.last with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some sent =>
    exact resent sent _ held
      (tick_record poised.pace poised.keep poised.origin sent.record now).2.2

/-- **A reading of the clock while a percept awaits sends what the bridge's tick sends, with
a new identifier, and changes nothing else.** For every instant and host with a percept
awaiting: the command is the one of `Bridge.tick` for the record of the release before the
percept, with the host's next unused identifier, and none for a host that has released
nothing; the settings, the depth frames held, the latch, the awaited cycle, the held
posture and the standing of the deadline rule are as before. -/
theorem Awaiting.tick_keeps (now : Instant) (awaiting : Awaiting) :
    (awaiting.tick now).2 =
        (awaiting.poised.last.bind fun sent =>
          (sent.record.tick awaiting.poised.pace awaiting.poised.keep awaiting.poised.origin
            now).2.map fun command => (awaiting.poised.next, command)) ∧
      (awaiting.tick now).1.poised.pace = awaiting.poised.pace ∧
      (awaiting.tick now).1.poised.keep = awaiting.poised.keep ∧
      (awaiting.tick now).1.poised.origin = awaiting.poised.origin ∧
      (awaiting.tick now).1.poised.depth = awaiting.poised.depth ∧
      (awaiting.tick now).1.poised.earlier = awaiting.poised.earlier ∧
      (awaiting.tick now).1.poised.armed = awaiting.poised.armed ∧
      (awaiting.tick now).1.poised.index = awaiting.poised.index ∧
      (awaiting.tick now).1.poised.sitting = awaiting.poised.sitting ∧
      (awaiting.tick now).1.poised.standing = awaiting.poised.standing :=
  Poised.ticked_keeps now awaiting.poised

/-- **Hearing a line while a percept awaits keeps everything but the depth frames held.**
For every host with a percept awaiting and every line: the settings, the next identifier,
the release before the percept, the latch, the awaited cycle and the held posture are as
before. -/
theorem Awaiting.hear_keeps (awaiting : Awaiting) (line : Line) :
    (awaiting.hear line).poised.pace = awaiting.poised.pace ∧
      (awaiting.hear line).poised.keep = awaiting.poised.keep ∧
      (awaiting.hear line).poised.origin = awaiting.poised.origin ∧
      (awaiting.hear line).poised.next = awaiting.poised.next ∧
      (awaiting.hear line).poised.last = awaiting.poised.last ∧
      (awaiting.hear line).poised.armed = awaiting.poised.armed ∧
      (awaiting.hear line).poised.index = awaiting.poised.index ∧
      (awaiting.hear line).poised.sitting = awaiting.poised.sitting := by
  show (awaiting.poised.heard line).pace = _ ∧ _
  cases line <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A refused frame and an invalid line change nothing in a host with no percept
awaiting.** For every such host and every stream: hearing a notification of the stream whose
frame was refused, or an invalid line, gives the host back. -/
theorem Idle.hear_refused (idle : Idle) (stream : Stream) :
    idle.hear (.unread stream) = idle ∧ idle.hear .invalid = idle := by
  obtain ⟨calm, _⟩ := idle
  exact ⟨rfl, rfl⟩

/-- **A refused frame and an invalid line change nothing in a host with a percept
awaiting.** For every such host and every stream. -/
theorem Awaiting.hear_refused (awaiting : Awaiting) (stream : Stream) :
    awaiting.hear (.unread stream) = awaiting ∧ awaiting.hear .invalid = awaiting := by
  obtain ⟨poised, _⟩ := awaiting
  exact ⟨rfl, rfl⟩

/-- **While a percept awaits, what is sent is the velocity of the action that the deadline
rule names, up to the end of its hold.** For every instant and host with a percept awaiting.
When a reading of the clock sends a command, it is the velocity of the action of the release
before the percept, the instant is before the end of that action's hold, and `Pace.outcome`
names that action as the one in force at the instant. From the end of the hold a reading of
the clock sends nothing, and `Pace.outcome` names the world's default. So while the agent
computes, late or not, the host sends the action that the rule holds in force and no other,
and it stops sending when the rule stops naming it. -/
theorem Awaiting.tick_named (now : Instant) (awaiting : Awaiting) (sent : Sent)
    (held : awaiting.poised.last = some sent) :
    (∀ id command, (awaiting.tick now).2 = some (id, command) →
      command = .move sent.record.action.velocity ∧
        now.nanoseconds <
          (sent.record.ends awaiting.poised.pace awaiting.poised.keep
            awaiting.poised.origin).nanoseconds ∧
        (awaiting.poised.pace.outcome awaiting.poised.origin (some Declared.rest)
          awaiting.poised.standing now).action = some sent.record.action) ∧
      ((sent.record.ends awaiting.poised.pace awaiting.poised.keep
          awaiting.poised.origin).nanoseconds ≤ now.nanoseconds →
        (awaiting.tick now).2 = none ∧
          (awaiting.poised.pace.outcome awaiting.poised.origin (some Declared.rest)
            awaiting.poised.standing now).action = some Declared.rest) := by
  have sends := (Awaiting.tick_keeps now awaiting).1
  have named : (awaiting.poised.pace.outcome awaiting.poised.origin (some Declared.rest)
      awaiting.poised.standing now).action =
        if now.nanoseconds < (sent.record.ends awaiting.poised.pace awaiting.poised.keep
          awaiting.poised.origin).nanoseconds then some sent.record.action
        else some Declared.rest := by
    rw [awaiting.poised.pace.outcome_action awaiting.poised.origin]
    unfold Poised.standing
    rw [held]
    exact sent.record.force_named awaiting.poised.pace awaiting.poised.keep
      awaiting.poised.origin (some Declared.rest) now
  rw [held] at sends
  constructor
  · intro id command sent_
    rw [sent_] at sends
    obtain ⟨other, ticked, same⟩ := Option.map_eq_some_iff.mp sends.symm
    obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨moved, _, inside⟩ := sent.record.tick_command awaiting.poised.pace
      awaiting.poised.keep awaiting.poised.origin now other ticked
    refine ⟨moved, inside, ?_⟩
    rw [named]
    simp only [inside, ↓reduceIte]
  · intro ended
    obtain ⟨_, quiet⟩ := sent.record.tick_lapsed awaiting.poised.pace awaiting.poised.keep
      awaiting.poised.origin (some Declared.rest) now ended
    refine ⟨?_, ?_⟩
    · rw [sends]
      show Option.map _ (sent.record.tick awaiting.poised.pace awaiting.poised.keep
        awaiting.poised.origin now).2 = none
      rw [quiet]
      rfl
    · rw [named]
      simp only [Nat.not_lt.mpr ended, ↓reduceIte]

/-! ## What holds of every reachable state -/

/-- The latch of the goal that a state holds. -/
def Phase.armed : Phase → Bool
  | .idle calm => calm.armed
  | .awaiting poised => poised.armed

/-- The next unused identifier of a state. -/
def Phase.next : Phase → Nat
  | .idle calm => calm.next
  | .awaiting poised => poised.next

/-- The last release that a state holds. -/
def Phase.last : Phase → Option Sent
  | .idle calm => calm.last
  | .awaiting poised => poised.last

/-- **The latch of the goal is the latch after the readings sensed, in order.** For every
state reached with a list of sensed readings: the latch that the state holds is the fold of
the adapter's `arm` over those readings, from a disarmed latch. So the event of the goal in
a percept is decided by the readings the host sensed and by nothing a caller supplies. -/
theorem Reached.latch {readings : List Reading} {issued : List Nat} {phase : Phase}
    (reached : Reached readings issued phase) :
    phase.armed = readings.foldl Handcrafted.Microduck.arm false := by
  induction reached with
  | start => rfl
  | @hear readings issued calm _ line hold =>
    have kept : (calm.heard line).armed = calm.armed := by
      cases line with
      | result id accepted => cases accepted <;> rfl
      | fault id => cases id <;> rfl
      | state _ | depth _ | unread _ | notice | invalid => rfl
    exact kept.trans hold
  | @tick readings issued calm _ now hold =>
    exact ((Calm.ticked_keeps now calm).2.2.2.2.2.2.2.2.1).trans hold
  | @sense readings issued calm _ now poised sensed admitted hold =>
    unfold Calm.sensed at admitted
    split at admitted
    · rename_i frame held
      split at admitted
      · have same := Prod.mk.inj (Option.some.inj admitted)
        rw [← same.1, ← same.2, List.foldl_append]
        show Handcrafted.Microduck.arm calm.armed _ = _
        rw [show calm.armed = _ from hold]
        rfl
      · exact nomatch admitted
    · exact nomatch admitted
  | @listen readings issued poised _ line hold =>
    have kept : (poised.heard line).armed = poised.armed := by cases line <;> rfl
    exact kept.trans hold
  | @watch readings issued poised _ now hold =>
    exact ((Poised.ticked_keeps now poised).2.2.2.2.2.2.1).trans hold
  | @release readings issued poised _ index now action calm commands admitted hold =>
    unfold Poised.released at admitted
    split at admitted
    · split at admitted
      · rw [← (Prod.mk.inj (Option.some.inj admitted)).1]
        exact hold
      · exact nomatch admitted
    · exact nomatch admitted

/-- What a reading of the clock issues is the next unused identifier, and the counter then
moves past it. -/
private theorem issue_next (next after : Nat) (sent : Option (Nat × Command))
    (given : ∀ pair, sent = some pair → pair.1 = next ∧ after = next + 1)
    (kept : sent = none → after = next) (issued : List Nat)
    (below : ∀ id ∈ issued, opening ≤ id ∧ id < next) (distinct : issued.Nodup)
    (least : opening ≤ next) :
    next ≤ after ∧ (∀ id ∈ issued ++ issue sent, opening ≤ id ∧ id < after) ∧
      (issued ++ issue sent).Nodup := by
  cases sent with
  | none =>
    cases kept rfl
    exact ⟨Nat.le_refl _, by simpa [issue] using below, by simpa [issue] using distinct⟩
  | some pair =>
    obtain ⟨numbered, moved⟩ := given pair rfl
    cases moved
    refine ⟨Nat.le_succ _, fun id inside => ?_, ?_⟩
    · rcases List.mem_append.mp inside with old | new
      · exact ⟨(below id old).1, Nat.lt_succ_of_lt (below id old).2⟩
      · cases List.mem_singleton.mp new
        rw [numbered]
        exact ⟨least, Nat.lt_succ_self _⟩
    · refine List.nodup_append.mpr ⟨distinct,
        List.nodup_cons.mpr ⟨(fun wrong => nomatch wrong), List.nodup_nil⟩,
        fun id old other new => ?_⟩
      cases List.mem_singleton.mp new
      intro same
      rw [same, numbered] at old
      exact Nat.lt_irrefl _ (below _ old).2

/-- **No identifier is given twice, and the counter is above every identifier given.** For
every state reached with a list of the identifiers given to requests on the way: the next
unused identifier is at least the count of the opening requests; every identifier given is
at least that count and below the next unused one; no identifier occurs twice in the list;
and every identifier that the last release holds, among its commands or its resent
velocities, is below the next unused one. `Reached.counter` states which identifiers were
given. -/
theorem Reached.identifiers {readings : List Reading} {issued : List Nat} {phase : Phase}
    (reached : Reached readings issued phase) :
    opening ≤ phase.next ∧ (∀ id ∈ issued, opening ≤ id ∧ id < phase.next) ∧ issued.Nodup ∧
      ∀ sent, phase.last = some sent → ∀ id ∈ sent.awaited ++ sent.resent, id < phase.next := by
  induction reached with
  | start =>
    exact ⟨Nat.le_refl _, (fun _ wrong => nomatch wrong), List.nodup_nil,
      fun _ wrong => nomatch wrong⟩
  | @hear readings issued calm _ line hold =>
    obtain ⟨least, given, distinct, below⟩ := hold
    have answered : ∀ (id : Nat) (accepted : Bool) (sent : Sent),
        calm.last.map (Sent.answer id accepted) = some sent →
        ∀ other ∈ sent.awaited ++ sent.resent, other < calm.next := by
      intro id accepted sent mapped other inside
      obtain ⟨before, held, rfl⟩ := Option.map_eq_some_iff.mp mapped
      exact below before held other (Sent.answer_subset id accepted before other inside)
    cases line with
    | result id accepted =>
      cases accepted with
      | none => exact ⟨least, given, distinct, below⟩
      | some value => exact ⟨least, given, distinct, answered id value⟩
    | fault id =>
      cases id with
      | none => exact ⟨least, given, distinct, below⟩
      | some number => exact ⟨least, given, distinct, answered number false⟩
    | state _ | depth _ | unread _ | notice | invalid => exact ⟨least, given, distinct, below⟩
  | @tick readings issued calm _ now hold =>
    obtain ⟨least, given, distinct, below⟩ := hold
    have step : ∀ (sent : Sent) (result : Bridge × Option Command), calm.last = some sent →
        (∀ pair, (calm.resend sent result).2 = some pair →
          pair.1 = calm.next ∧ (calm.resend sent result).1.next = calm.next + 1) ∧
        ((calm.resend sent result).2 = none → (calm.resend sent result).1.next = calm.next) ∧
        ∀ other, (calm.resend sent result).1.last = some other →
          ∀ id ∈ other.awaited ++ other.resent, id < (calm.resend sent result).1.next := by
      intro sent result held
      obtain ⟨record, command⟩ := result
      cases command with
      | none =>
        exact ⟨(fun _ wrong => nomatch wrong), fun _ => rfl,
          fun other same id inside => below other same id inside⟩
      | some command =>
        refine ⟨fun pair same => ?_, (fun wrong => nomatch wrong), fun other same id inside => ?_⟩
        · cases Option.some.inj same
          exact ⟨rfl, rfl⟩
        · cases Option.some.inj same
          rcases List.mem_append.mp inside with first | second
          · exact Nat.lt_succ_of_lt (below sent held id (List.mem_append_left _ first))
          · rcases List.mem_cons.mp second with rfl | older
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (below sent held id (List.mem_append_right _ older))
    have whole : (∀ pair, (calm.ticked now).2 = some pair →
          pair.1 = calm.next ∧ (calm.ticked now).1.next = calm.next + 1) ∧
        ((calm.ticked now).2 = none → (calm.ticked now).1.next = calm.next) ∧
        ∀ other, (calm.ticked now).1.last = some other →
          ∀ id ∈ other.awaited ++ other.resent, id < (calm.ticked now).1.next := by
      unfold Calm.ticked
      cases held : calm.last with
      | none =>
        exact ⟨(fun _ wrong => nomatch wrong), fun _ => rfl,
          fun other same => nomatch (held.symm.trans same)⟩
      | some sent => exact step sent _ held
    obtain ⟨moved, kept, held⟩ := whole
    obtain ⟨rose, all, apart⟩ :=
      issue_next calm.next (calm.ticked now).1.next (calm.ticked now).2 moved kept issued given
        distinct least
    exact ⟨Nat.le_trans least rose, all, apart, held⟩
  | @sense readings issued calm _ now poised sensed admitted hold =>
    unfold Calm.sensed at admitted
    split at admitted
    · split at admitted
      · rw [← (Prod.mk.inj (Option.some.inj admitted)).1]
        exact hold
      · exact nomatch admitted
    · exact nomatch admitted
  | @listen readings issued poised _ line hold =>
    cases line <;> exact hold
  | @watch readings issued poised _ now hold =>
    obtain ⟨least, given, distinct, below⟩ := hold
    have step : ∀ (sent : Sent) (result : Bridge × Option Command), poised.last = some sent →
        (∀ pair, (poised.resend sent result).2 = some pair →
          pair.1 = poised.next ∧ (poised.resend sent result).1.next = poised.next + 1) ∧
        ((poised.resend sent result).2 = none →
          (poised.resend sent result).1.next = poised.next) ∧
        ∀ other, (poised.resend sent result).1.last = some other →
          ∀ id ∈ other.awaited ++ other.resent, id < (poised.resend sent result).1.next := by
      intro sent result held
      obtain ⟨record, command⟩ := result
      cases command with
      | none =>
        exact ⟨(fun _ wrong => nomatch wrong), fun _ => rfl,
          fun other same id inside => below other same id inside⟩
      | some command =>
        refine ⟨fun pair same => ?_, (fun wrong => nomatch wrong), fun other same id inside => ?_⟩
        · cases Option.some.inj same
          exact ⟨rfl, rfl⟩
        · cases Option.some.inj same
          rcases List.mem_append.mp inside with first | second
          · exact Nat.lt_succ_of_lt (below sent held id (List.mem_append_left _ first))
          · rcases List.mem_cons.mp second with rfl | older
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (below sent held id (List.mem_append_right _ older))
    have whole : (∀ pair, (poised.ticked now).2 = some pair →
          pair.1 = poised.next ∧ (poised.ticked now).1.next = poised.next + 1) ∧
        ((poised.ticked now).2 = none → (poised.ticked now).1.next = poised.next) ∧
        ∀ other, (poised.ticked now).1.last = some other →
          ∀ id ∈ other.awaited ++ other.resent, id < (poised.ticked now).1.next := by
      unfold Poised.ticked
      cases held : poised.last with
      | none =>
        exact ⟨(fun _ wrong => nomatch wrong), fun _ => rfl,
          fun other same => nomatch (held.symm.trans same)⟩
      | some sent => exact step sent _ held
    obtain ⟨moved, kept, held⟩ := whole
    obtain ⟨rose, all, apart⟩ :=
      issue_next poised.next (poised.ticked now).1.next (poised.ticked now).2 moved kept issued
        given distinct least
    exact ⟨Nat.le_trans least rose, all, apart, held⟩
  | @release readings issued poised _ index now action calm commands admitted hold =>
    obtain ⟨least, given, distinct, _⟩ := hold
    unfold Poised.released at admitted
    split at admitted
    · split at admitted
      · have same := Prod.mk.inj (Option.some.inj admitted)
        rw [← same.1, ← same.2]
        have firsts := List.map_fst_zip (l₁ := List.range' poised.next
          (action.commands poised.sitting).length) (l₂ := action.commands poised.sitting)
          (by rw [List.length_range']; exact Nat.le_refl _)
        show opening ≤ poised.next + (action.commands poised.sitting).length ∧ _
        rw [firsts]
        refine ⟨Nat.le_trans least (Nat.le_add_right _ _), fun id inside => ?_, ?_,
          fun sent same id inside => ?_⟩
        · rcases List.mem_append.mp inside with old | new
          · exact ⟨(given id old).1, Nat.lt_of_lt_of_le (given id old).2 (Nat.le_add_right _ _)⟩
          · obtain ⟨lower, upper⟩ := List.mem_range'_1.mp new
            exact ⟨Nat.le_trans least lower, upper⟩
        · refine List.nodup_append.mpr ⟨distinct, List.nodup_range', fun id old other new => ?_⟩
          intro same
          rw [same] at old
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (given _ old).2 (List.mem_range'_1.mp new).1)
        · cases Option.some.inj same
          rw [List.append_nil] at inside
          exact (List.mem_range'_1.mp inside).2
      · exact nomatch admitted
    · exact nomatch admitted

/-- What a tick of the bridge gives, for what the host holds: the identifiers given are the
consecutive ones from the next unused identifier, and the counter moves past them. -/
private theorem Calm.resend_counter (calm : Calm) (sent : Sent) (result : Bridge × Option Command) :
    ∃ count, issue (calm.resend sent result).2 = List.range' calm.next count ∧
      (calm.resend sent result).1.next = calm.next + count := by
  obtain ⟨record, command⟩ := result
  cases command with
  | none => exact ⟨0, rfl, rfl⟩
  | some command => exact ⟨1, rfl, rfl⟩

/-- What a reading of the clock gives while no percept awaits: the identifiers given are the
consecutive ones from the next unused identifier, and the counter moves past them. -/
private theorem Calm.ticked_counter (now : Instant) (calm : Calm) :
    ∃ count, issue (calm.ticked now).2 = List.range' calm.next count ∧
      (calm.ticked now).1.next = calm.next + count := by
  unfold Calm.ticked
  cases calm.last with
  | none => exact ⟨0, rfl, rfl⟩
  | some sent => exact calm.resend_counter sent _

/-- What a tick of the bridge gives while a percept awaits: the identifiers given are the
consecutive ones from the next unused identifier, and the counter moves past them. -/
private theorem Poised.resend_counter (poised : Poised) (sent : Sent)
    (result : Bridge × Option Command) :
    ∃ count, issue (poised.resend sent result).2 = List.range' poised.next count ∧
      (poised.resend sent result).1.next = poised.next + count := by
  obtain ⟨record, command⟩ := result
  cases command with
  | none => exact ⟨0, rfl, rfl⟩
  | some command => exact ⟨1, rfl, rfl⟩

/-- What a reading of the clock gives while a percept awaits: the identifiers given are the
consecutive ones from the next unused identifier, and the counter moves past them. -/
private theorem Poised.ticked_counter (now : Instant) (poised : Poised) :
    ∃ count, issue (poised.ticked now).2 = List.range' poised.next count ∧
      (poised.ticked now).1.next = poised.next + count := by
  unfold Poised.ticked
  cases poised.last with
  | none => exact ⟨0, rfl, rfl⟩
  | some sent => exact poised.resend_counter sent _

/-- Consecutive identifiers from the opening ones, followed by consecutive identifiers from
the counter, are consecutive identifiers from the opening ones. -/
private theorem counter_step (count next given : Nat) (issued : List Nat)
    (counted : next = opening + count) (consecutive : issued = List.range' opening count) :
    issued ++ List.range' next given = List.range' opening (count + given) := by
  rw [consecutive, counted]
  exact List.range'_append_1

/-- **The identifiers given are the consecutive numbers from the opening ones, in the order
they were given, and the counter is the next one.** For every state reached with the
identifiers given to requests on the way: the next unused identifier is the count of the
opening requests plus the count of the identifiers given, and the identifiers given are the
numbers from the count of the opening requests up, one after another. Each constructor of
`Reached` extends the list of identifiers given, so along a derivation the counter never
decreases, and `counter_rises` states by how much each transition raises it. -/
theorem Reached.counter {readings : List Reading} {issued : List Nat} {phase : Phase}
    (reached : Reached readings issued phase) :
    phase.next = opening + issued.length ∧ issued = List.range' opening issued.length := by
  induction reached with
  | start => exact ⟨rfl, rfl⟩
  | @hear readings issued calm _ line hold =>
    have kept : (calm.heard line).next = calm.next := by
      cases line with
      | result id accepted => cases accepted <;> rfl
      | fault id => cases id <;> rfl
      | state _ | depth _ | unread _ | notice | invalid => rfl
    exact ⟨kept.trans hold.1, hold.2⟩
  | @tick readings issued calm _ now hold =>
    obtain ⟨given, sent, moved⟩ := Calm.ticked_counter now calm
    have counted : calm.next = opening + issued.length := hold.1
    show (calm.ticked now).1.next = opening + (issued ++ issue (calm.ticked now).2).length ∧ _
    rw [sent, List.length_append, List.length_range', moved, counted, Nat.add_assoc]
    exact ⟨rfl, counter_step issued.length _ given issued rfl hold.2⟩
  | @sense readings issued calm _ now poised sensed admitted hold =>
    unfold Calm.sensed at admitted
    split at admitted
    · split at admitted
      · rw [← (Prod.mk.inj (Option.some.inj admitted)).1]
        exact hold
      · exact nomatch admitted
    · exact nomatch admitted
  | @listen readings issued poised _ line hold =>
    cases line <;> exact hold
  | @watch readings issued poised _ now hold =>
    obtain ⟨given, sent, moved⟩ := Poised.ticked_counter now poised
    have counted : poised.next = opening + issued.length := hold.1
    show (poised.ticked now).1.next = opening + (issued ++ issue (poised.ticked now).2).length ∧ _
    rw [sent, List.length_append, List.length_range', moved, counted, Nat.add_assoc]
    exact ⟨rfl, counter_step issued.length _ given issued rfl hold.2⟩
  | @release readings issued poised _ index now action calm commands admitted hold =>
    unfold Poised.released at admitted
    split at admitted
    · split at admitted
      · have same := Prod.mk.inj (Option.some.inj admitted)
        rw [← same.1, ← same.2]
        have firsts := List.map_fst_zip (l₁ := List.range' poised.next
          (action.commands poised.sitting).length) (l₂ := action.commands poised.sitting)
          (by rw [List.length_range']; exact Nat.le_refl _)
        have counted : poised.next = opening + issued.length := hold.1
        show poised.next + (action.commands poised.sitting).length = _ ∧ _
        rw [firsts, List.length_append, List.length_range']
        refine ⟨?_, counter_step issued.length _ _ issued counted hold.2⟩
        rw [counted, Nat.add_assoc]
      · exact nomatch admitted
    · exact nomatch admitted

/-- **The counter never decreases: each transition raises it by the count of the
identifiers it gives.** Hearing a line and sensing a percept leave the next unused
identifier as it was; a reading of the clock, in either phase, raises it by one when it
sends a velocity again and leaves it otherwise; and a release raises it by the count of its
commands. Every derivation is a sequence of these transitions (`Reached`), so the counter
never decreases along one. -/
theorem counter_rises :
    (∀ (idle : Idle) (line : Line), (idle.hear line).calm.next = idle.calm.next) ∧
      (∀ (idle : Idle) (now : Instant),
        (idle.tick now).1.calm.next = idle.calm.next + (issue (idle.tick now).2).length) ∧
      (∀ (idle : Idle) (now : Instant) (awaiting : Awaiting) (sensed : Sensed),
        idle.sense now = some (awaiting, sensed) → awaiting.poised.next = idle.calm.next) ∧
      (∀ (awaiting : Awaiting) (line : Line),
        (awaiting.hear line).poised.next = awaiting.poised.next) ∧
      (∀ (awaiting : Awaiting) (now : Instant),
        (awaiting.tick now).1.poised.next =
          awaiting.poised.next + (issue (awaiting.tick now).2).length) ∧
      (∀ (index : Nat) (now : Instant) (action : Action) (awaiting : Awaiting) (idle : Idle)
        (commands : List (Nat × Command)),
        awaiting.release index now action = some (idle, commands) →
          idle.calm.next = awaiting.poised.next + commands.length) := by
  refine ⟨fun idle line => (Idle.hear_keeps idle line).2.2.2.1, fun idle now => ?_,
    fun idle now awaiting sensed admitted => ?_, fun awaiting line => ?_,
    fun awaiting now => ?_, fun index now action awaiting idle commands admitted => ?_⟩
  · obtain ⟨given, sent, moved⟩ := Calm.ticked_counter now idle.calm
    show (idle.calm.ticked now).1.next = idle.calm.next + (issue (idle.calm.ticked now).2).length
    rw [sent, List.length_range']
    exact moved
  · obtain ⟨_, _, _, poised, _⟩ := (Idle.sense_iff now idle awaiting sensed).mp admitted
    rw [poised]
  · show (awaiting.poised.heard line).next = awaiting.poised.next
    cases line <;> rfl
  · obtain ⟨given, sent, moved⟩ := Poised.ticked_counter now awaiting.poised
    show (awaiting.poised.ticked now).1.next =
      awaiting.poised.next + (issue (awaiting.poised.ticked now).2).length
    rw [sent, List.length_range']
    exact moved
  · obtain ⟨_, _, calm, rfl⟩ :=
      (Awaiting.release_iff index now action awaiting idle commands).mp admitted
    rw [List.length_zip, List.length_range', Nat.min_self, calm]

/-- **The identifiers of a release are new, and were never given before.** For every
admitted release, and every derivation of the host before it with the identifiers given on
the way: each command is given an identifier that is at least the next unused one of the
host before the release, so it is above the opening identifiers, it is none of the
identifiers given earlier on that derivation, and it is held by no earlier release; and the
identifiers of the commands of one release differ. -/
theorem Awaiting.release_fresh (index : Nat) (now : Instant) (action : Action)
    (awaiting : Awaiting) (idle : Idle) (commands : List (Nat × Command))
    (admitted : awaiting.release index now action = some (idle, commands))
    (readings : List Reading) (issued : List Nat)
    (reached : Reached readings issued (.awaiting awaiting.poised)) :
    (commands.map fun pair => pair.1).Nodup ∧
      ∀ pair ∈ commands, awaiting.poised.next ≤ pair.1 ∧ opening ≤ pair.1 ∧
        pair.1 ∉ issued ∧
        ∀ sent, awaiting.poised.last = some sent → pair.1 ∉ sent.awaited ++ sent.resent := by
  obtain ⟨least, given, _, below⟩ := reached.identifiers
  obtain ⟨_, _, _, rfl⟩ :=
    (Awaiting.release_iff index now action awaiting idle commands).mp admitted
  refine ⟨?_, fun pair inside => ?_⟩
  · have firsts := List.map_fst_zip (l₁ := List.range' awaiting.poised.next
      (action.commands awaiting.poised.sitting).length)
      (l₂ := action.commands awaiting.poised.sitting)
      (by rw [List.length_range']; exact Nat.le_refl _)
    rw [firsts]
    exact List.nodup_range'
  · have numbered := (List.mem_range'_1.mp (List.of_mem_zip inside).1).1
    exact ⟨numbered, Nat.le_trans least numbered,
      fun earlier => absurd (given pair.1 earlier).2 (Nat.not_lt.mpr numbered),
      fun sent held within =>
        absurd (below sent held pair.1 within) (Nat.not_lt.mpr numbered)⟩

/-- **After a near reading, no percept is the event of the goal until a clear reading.**
For every host with no percept awaiting that is reached with a history of sensed readings
in which a near reading is followed by readings none of which is clear: the next percept
that the host senses is not the event of the goal. So clear, near, near gives one event,
from the transitions of the host. -/
theorem Idle.sense_held (idle : Idle) (before : List Reading) (first : Reading)
    (later : List Reading) (issued : List Nat)
    (reached : Reached (before ++ first :: later) issued (.idle idle.calm))
    (close : Handcrafted.Microduck.near first = true)
    (narrow : ∀ reading ∈ later, Handcrafted.Microduck.clear reading = false)
    (now : Instant) (awaiting : Awaiting) (sensed : Sensed)
    (admitted : idle.sense now = some (awaiting, sensed)) :
    sensed.percept.frame.achieved = false := by
  obtain ⟨frame, _, _, _, rfl⟩ := (Idle.sense_iff now idle awaiting sensed).mp admitted
  have latch : idle.calm.armed = _ := reached.latch
  show Handcrafted.Microduck.achieved idle.calm.armed _ = false
  rw [latch, List.foldl_append, List.foldl_cons]
  exact Handcrafted.Microduck.arm_held _ first later _ close narrow

/-- **The depth frame of every reading is stamped at or before its state frame, and its age
is the exact difference.** For every percept that a host senses and the depth frame of its
reading, if it has one: the stamp of the depth frame is not after the stamp of the state
frame, and the stamp of the depth frame plus the age of the reading is the stamp of the
state frame. A reading with no depth frame at or before its state frame among the two that
the host holds has none. -/
theorem Idle.sense_age (now : Instant) (idle : Idle) (awaiting : Awaiting) (sensed : Sensed)
    (admitted : idle.sense now = some (awaiting, sensed)) (depth : Depth)
    (paired : sensed.reading.depth = some depth) :
    depth.taken.nanoseconds ≤ sensed.reading.state.taken.nanoseconds ∧
      ∃ age, sensed.reading.age = some age ∧
        depth.taken.nanoseconds + age = sensed.reading.state.taken.nanoseconds := by
  obtain ⟨frame, _, _, _, rfl⟩ := (Idle.sense_iff now idle awaiting sensed).mp admitted
  have ordered := (Pair.of frame idle.calm.depth idle.calm.earlier).ordered depth paired
  exact ⟨ordered, Reading.age_exact _ depth paired ordered⟩

/-- The last release of an idle state is not before the start of its percept's cycle. -/
private def Phase.Begun : Phase → Prop
  | .idle calm => ∀ sent, calm.last = some sent →
    (calm.pace.boundary calm.origin sent.record.index).nanoseconds ≤
      sent.record.released.nanoseconds
  | .awaiting _ => True

/-- Every reachable state has its last release at or after the start of its cycle. -/
private theorem Reached.begun {readings : List Reading} {issued : List Nat} {phase : Phase}
    (reached : Reached readings issued phase) : phase.Begun := by
  induction reached with
  | start => exact fun _ wrong => nomatch wrong
  | @hear readings issued calm _ line hold =>
    have answered : ∀ (id : Nat) (accepted : Bool) (sent : Sent),
        calm.last.map (Sent.answer id accepted) = some sent →
        (calm.pace.boundary calm.origin sent.record.index).nanoseconds ≤
          sent.record.released.nanoseconds := by
      intro id accepted sent mapped
      obtain ⟨before, held, rfl⟩ := Option.map_eq_some_iff.mp mapped
      rw [(before.answer_iff id accepted).1]
      exact hold before held
    cases line with
    | result id accepted =>
      cases accepted with
      | none => exact hold
      | some value => exact answered id value
    | fault id =>
      cases id with
      | none => exact hold
      | some number => exact answered number false
    | state _ | depth _ | unread _ | notice | invalid => exact hold
  | @tick readings issued calm _ now hold =>
    have step : ∀ (sent : Sent) (result : Bridge × Option Command), calm.last = some sent →
        result.1.index = sent.record.index → result.1.released = sent.record.released →
        ∀ other, (calm.resend sent result).1.last = some other →
          ((calm.resend sent result).1.pace.boundary (calm.resend sent result).1.origin
            other.record.index).nanoseconds ≤ other.record.released.nanoseconds := by
      intro sent result held index released
      obtain ⟨record, command⟩ := result
      cases command with
      | none => exact fun other same => hold other same
      | some command =>
        intro other same
        cases Option.some.inj same
        show (calm.pace.boundary calm.origin record.index).nanoseconds ≤
          record.released.nanoseconds
        rw [show record.index = sent.record.index from index,
          show record.released = sent.record.released from released]
        exact hold sent held
    show ∀ sent, (calm.ticked now).1.last = some sent → _
    unfold Calm.ticked
    cases held : calm.last with
    | none => exact fun other same => nomatch (held.symm.trans same)
    | some sent =>
      obtain ⟨index, released, _⟩ :=
        tick_record calm.pace calm.keep calm.origin sent.record now
      exact step sent _ held index released
  | sense => trivial
  | listen => trivial
  | watch => trivial
  | @release readings issued poised _ index now action calm commands admitted hold =>
    unfold Poised.released at admitted
    split at admitted
    · split at admitted
      · rename_i begun
        rw [← (Prod.mk.inj (Option.some.inj admitted)).1]
        intro sent same
        cases Option.some.inj same
        exact begun
      · exact nomatch admitted
    · exact nomatch admitted

/-- **The hold of the last release ends a bounded time after it.** For every host with no
percept awaiting and its last release: the hold of the released action ends no later than
the release plus the action's declared duration, the transit allowance and
`1 + latency + grace` cycles. The hypothesis of `Bridge.ends_bounded` holds of every
reachable host, because a release before the start of its percept's cycle is refused. -/
theorem Idle.hold_bounded (idle : Idle) (sent : Sent) (held : idle.calm.last = some sent) :
    (sent.record.ends idle.calm.pace idle.calm.keep idle.calm.origin).nanoseconds ≤
      sent.record.released.nanoseconds + sent.record.action.duration + idle.calm.keep.transit +
        (1 + idle.calm.pace.latency + idle.calm.keep.grace) * idle.calm.pace.cycle := by
  obtain ⟨readings, issued, reached⟩ := idle.reached
  exact Bridge.ends_bounded idle.calm.pace idle.calm.keep idle.calm.origin sent.record
    (reached.begun sent held)

/-- **Every identifier that a host holds is below its next unused one.** For every host
with no percept awaiting: the next unused identifier is at least the count of the opening
requests, and every identifier that the last release holds is below it. -/
theorem Idle.identifiers (idle : Idle) :
    opening ≤ idle.calm.next ∧
      ∀ sent, idle.calm.last = some sent →
        ∀ id ∈ sent.awaited ++ sent.resent, id < idle.calm.next := by
  obtain ⟨readings, issued, reached⟩ := idle.reached
  exact ⟨reached.identifiers.1, reached.identifiers.2.2.2⟩

/-- **An action is released exactly for the awaited cycle, once it has started.** For every
cycle, instant, action and host with a percept awaiting. -/
theorem Awaiting.release_admitted (index : Nat) (now : Instant) (action : Action)
    (awaiting : Awaiting) :
    (awaiting.release index now action).isSome = true ↔
      index = awaiting.poised.index ∧
        (awaiting.poised.pace.boundary awaiting.poised.origin index).nanoseconds ≤
          now.nanoseconds := by
  constructor
  · intro found
    obtain ⟨⟨idle, commands⟩, same⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨named, begun, _⟩ :=
      (Awaiting.release_iff index now action awaiting idle commands).mp same
    exact ⟨named, begun⟩
  · rintro ⟨rfl, begun⟩
    unfold Awaiting.release
    split
    · rfl
    · rename_i missing
      unfold Poised.released at missing
      simp only [begun, ↓reduceIte] at missing
      exact nomatch missing

/-- A host with a percept awaiting exists: one that started, heard a state frame and sensed
it. -/
instance : Nonempty Awaiting := by
  let frame : State := ⟨⟨0⟩, Vector.replicate 15 ⟨0, by decide⟩, none,
    Vector.replicate 3 ⟨0, by decide⟩, Vector.replicate 3 ⟨0, by decide⟩, ⟨0, by decide⟩,
    .stand, false, false, none, ⟨false, false, false, false⟩⟩
  let idle := (Idle.start Declared.pace Declared.keep ⟨0⟩).hear (.state frame)
  have sensing : (idle.sense ⟨0⟩).isSome = true :=
    (Idle.sense_admitted ⟨0⟩ idle).mpr ⟨⟨frame, rfl⟩, Nat.zero_le _⟩
  obtain ⟨⟨awaiting, _⟩, _⟩ := Option.isSome_iff_exists.mp sensing
  exact ⟨awaiting⟩

end Acorn.Host.Microduck
