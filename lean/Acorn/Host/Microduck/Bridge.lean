/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Microduck.Action

/-!
# The Microduck bridge's state

The control daemon replaces a velocity intent by zero when the intent is 500 ms old, so
a client that wants a velocity to stay in force sends it again. A `Bridge` is what a
bridge holds between two events: the action released last, the posture its caller
stated at that release, the instant its velocity was last sent at, the cycle of the
next percept, and the instant its hold ends.

`Bridge.release` is the release of an action for the percept of a cycle. It gives the
action's commands and a state that depends on no earlier state (`Bridge.release_state`).
The cycle of the next percept is `Action.next` of the instant of the release, so for
every release, timely or late, that cycle starts no earlier than the release plus the
action's declared duration and the transit allowance (`Bridge.release_next`). The hold
ends a declared number of cycles, the grace, after the deadline of the next percept's
action (`Bridge.release_held`), so a next release that meets its deadline is inside the
hold (`Bridge.release_covers`).

`Bridge.tick` is one reading of the clock between two releases. It sends the action's
velocity again when that velocity is not zero, the hold has not ended and the last send
has reached a declared age. A zero velocity is not sent again: the daemon's expiry gives
zero by itself.

## The hold is bounded on purpose

The daemon's expiry is the vendor's protection against a client that has stopped. A
bridge that sent a velocity again without end, for an agent that does not answer, would
remove it. So the bridge keeps the preceding action for the grace and no longer, and the
model of the deadline rule says so: `Bridge.force` is the action with the end of the
hold as its lapse, and the world's declared default, `Declared.rest`, is the action that
stands still. During a fault the action in force is the preceding action up to the end
of the hold and the default from it (`Bridge.fault_named`).

What the bridge sends and what the force names agree at every instant. At the release
the force names the action (`Bridge.release_named`), whose velocity is the first command
of the release (`Action.commands_head`). Over any list of readings, in any order, every
command sent is the velocity of the action that the force names at that reading
(`Bridge.ticks_named`). From the end of the hold the force names the default and a tick
sends nothing (`Bridge.tick_lapsed`). Inside the hold, after a tick, the last send of a
velocity that is not zero is younger than the resend age (`Bridge.tick_fresh`, and
`Bridge.release_fresh` at the release), and until the next reading it stays younger than
the resend age plus the gap to that reading (`Bridge.Fresh.age`).

The force names what the bridge keeps in force, not what the body does. After the end
of the hold the daemon still holds the last velocity it received until its own expiry,
so the body can move for up to that long after the force names the default.

## What became of an action

`Action.outcome` is what became of a released action, one of four outcomes that later
code has to tell apart: `refused`, `unexecuted` (accepted, and the body did not show
it), `unchanged` (accepted and shown, for a posture the body had, so no skill was sent)
and `executed`. A refusal and a missing execution are read first, so an action that
asks for the stated posture still reports them. `Action.Judged` is the specification, in
propositions about the commands the release sent, and `Action.outcome_judged` states
that the function gives an outcome exactly when the specification holds of it.
`Bridge.outcome` reads the posture that the state holds from the release, so the
commands and the outcome of one release read one posture. How sensing shows an action is
not defined here: the outcome takes that fact as an input.

## Assumptions

These are assumptions of the use of the statements, proved nowhere:

- the daemon's expiry, `Declared.expiry` (the observed run saw a velocity zeroed 503 to
  520 ms after the last send; its record is at
  https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895), and that the
  daemon ages a velocity from its receipt;
- the receipt follows the reading of the clock that a send is stamped with by at most
  the transit allowance of the keeping;
- a reading of the clock, and a tick, at least every `Declared.gap`. That needs a reader
  of the clock that runs while the agent's step computes, which is a property of a host
  loop that is not built, and of the operating system's scheduling;
- the posture a caller states is the body's;
- the declared duration of an action covers what the body takes for it.

No executing code keeps a `Bridge`: the functions here are pure, and the host loop that
calls them is not built (https://github.com/rbeauchamp/acorn/issues/95). A host owes
that it senses the next percept at the cycle the state names and no earlier; the state
holds that cycle, and nothing in it refuses an earlier release.
-/
namespace Acorn.Host.Microduck

/-- What a bridge declares about keeping a velocity alive. -/
structure Keep where
  /-- Nanoseconds: the age of the last send at which a velocity is sent again. -/
  resend : Nat
  /-- Cycles after the deadline of the next percept's action during which the bridge
  still sends the velocity. -/
  grace : Nat
  /-- Nanoseconds allowed from the reading of the clock a send is stamped with to the
  daemon's receipt. -/
  transit : Nat
  /-- A velocity is not sent again at the instant it was sent at. -/
  spaced : 0 < resend

/-- What a bridge holds between two events. -/
structure Bridge where
  /-- The action released last. -/
  action : Action
  /-- The posture of the body as the caller stated it at that release. -/
  sitting : Bool
  /-- The instant the action's velocity was last sent at. -/
  sent : Instant
  /-- The cycle of the next percept. -/
  next : Nat
  /-- The instant from which the bridge sends that velocity no more. -/
  ends : Instant

/-- Release an action at an instant for the percept of a cycle, for the posture of the
body as the caller states it: the state after the release, and the action's commands. -/
def Bridge.release (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now : Instant) (sitting : Bool) (action : Action) : Bridge × List Command :=
  (⟨action, sitting, now, action.next pace keep.transit origin index now,
      pace.boundary origin
        (action.next pace keep.transit origin index now + pace.latency + keep.grace)⟩,
    action.commands sitting)

/-- One reading of the clock between two releases: send the action's velocity again when
it is not zero, the hold has not ended and the last send is at least the resend age
old. -/
def Bridge.tick (keep : Keep) (bridge : Bridge) (now : Instant) : Bridge × Option Command :=
  if bridge.action.velocity ≠ .zero ∧ now.nanoseconds < bridge.ends.nanoseconds ∧
      bridge.sent.nanoseconds + keep.resend ≤ now.nanoseconds then
    ({ bridge with sent := now }, some (.move bridge.action.velocity))
  else (bridge, none)

/-- The ticks of a list of readings, in the order of the list: the state after them, and
each command sent with the reading it was sent at. -/
def Bridge.ticks (keep : Keep) (bridge : Bridge) :
    List Instant → Bridge × List (Instant × Command)
  | [] => (bridge, [])
  | now :: rest =>
    match (bridge.tick keep now).2 with
    | some command =>
      (((bridge.tick keep now).1.ticks keep rest).1,
        (now, command) :: ((bridge.tick keep now).1.ticks keep rest).2)
    | none => (bridge.tick keep now).1.ticks keep rest

/-- The last send is younger than the resend age at an instant. -/
def Bridge.Fresh (keep : Keep) (bridge : Bridge) (now : Instant) : Prop :=
  now.nanoseconds < bridge.sent.nanoseconds + keep.resend

/-- The force of a state for the deadline rule: its action, which lapses at the end of
the hold. -/
def Bridge.force (bridge : Bridge) : Force Action := ⟨some bridge.action, some bridge.ends⟩

/-- **The state and the commands of a release.** For every pace, keeping, origin, cycle,
instant, stated posture and action: the state holds the action, the stated posture, the
instant of the release as the last send, the cycle of the next percept, and a hold that
ends at the start of the cycle `latency + grace` cycles after that one; the commands are
the action's. No earlier state is an input. -/
theorem Bridge.release_state (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now : Instant) (sitting : Bool) (action : Action) :
    (Bridge.release pace keep origin index now sitting action).1 =
        ⟨action, sitting, now, action.next pace keep.transit origin index now,
          pace.boundary origin
            (action.next pace keep.transit origin index now + pace.latency + keep.grace)⟩ ∧
      (Bridge.release pace keep origin index now sitting action).2 =
        action.commands sitting :=
  ⟨rfl, rfl⟩

/-- **No percept falls inside the declared duration of the released action.** For every
release, timely or late: the cycle of the next percept is after the cycle of the action's
own percept, and it starts no earlier than the release plus the action's declared
duration and the transit allowance. -/
theorem Bridge.release_next (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now : Instant) (sitting : Bool) (action : Action) :
    index < (Bridge.release pace keep origin index now sitting action).1.next ∧
      now.nanoseconds + action.duration + keep.transit ≤
        (pace.boundary origin
          (Bridge.release pace keep origin index now sitting action).1.next).nanoseconds :=
  ⟨action.next_after pace keep.transit origin index now,
    action.next_covers pace keep.transit origin index now⟩

/-- **The hold ends the grace after the next deadline.** For every release, the hold ends
`grace` cycles after the deadline of the action of the next percept. -/
theorem Bridge.release_held (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now : Instant) (sitting : Bool) (action : Action) :
    (Bridge.release pace keep origin index now sitting action).1.ends.nanoseconds =
      (pace.deadline origin
        (Bridge.release pace keep origin index now sitting action).1.next).nanoseconds +
          keep.grace * pace.cycle := by
  show (pace.boundary origin
    (action.next pace keep.transit origin index now + pace.latency + keep.grace)).nanoseconds =
      (pace.deadline origin (action.next pace keep.transit origin index now)).nanoseconds +
        keep.grace * pace.cycle
  rw [pace.boundary_nanoseconds, pace.deadline_nanoseconds, Nat.add_mul, Nat.add_assoc]

/-- **A release that meets its deadline arrives inside the hold.** For every release:
when the action of the next percept meets its deadline, that next release is before the
end of the hold. -/
theorem Bridge.release_covers (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now second : Instant) (sitting : Bool) (action : Action)
    (met : pace.meets origin
      (Bridge.release pace keep origin index now sitting action).1.next second = true) :
    second.nanoseconds <
      (Bridge.release pace keep origin index now sitting action).1.ends.nanoseconds := by
  have verdict := (pace.meets_iff origin _ second).mp met
  have held := Bridge.release_held pace keep origin index now sitting action
  have due := pace.deadline_nanoseconds origin
    (Bridge.release pace keep origin index now sitting action).1.next
  omega

/-- The velocity is fresh at the instant of its release. -/
theorem Bridge.release_fresh (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now : Instant) (sitting : Bool) (action : Action) :
    (Bridge.release pace keep origin index now sitting action).1.Fresh keep now :=
  Nat.lt_add_of_pos_right keep.spaced

/-- **A tick sends the action's velocity and no other command.** A command that a tick
sends is the velocity of the state's action, which is not zero, at an instant before the
end of the hold. -/
theorem Bridge.tick_command (keep : Keep) (bridge : Bridge) (now : Instant) (command : Command)
    (sent : (bridge.tick keep now).2 = some command) :
    command = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
      now.nanoseconds < bridge.ends.nanoseconds := by
  unfold Bridge.tick at sent
  split at sent
  · rename_i due
    exact ⟨(Option.some.inj sent).symm, due.1, due.2.1⟩
  · cases sent

/-- **A tick keeps the action, the stated posture, the next cycle and the end of the
hold.** -/
theorem Bridge.tick_keeps (keep : Keep) (bridge : Bridge) (now : Instant) :
    (bridge.tick keep now).1.action = bridge.action ∧
      (bridge.tick keep now).1.sitting = bridge.sitting ∧
      (bridge.tick keep now).1.next = bridge.next ∧
      (bridge.tick keep now).1.ends = bridge.ends := by
  unfold Bridge.tick
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Nothing is sent from the end of the hold.** For every state and instant: a tick at
or after the end of the hold sends nothing and changes nothing. -/
theorem Bridge.tick_ended (keep : Keep) (bridge : Bridge) (now : Instant)
    (ended : bridge.ends.nanoseconds ≤ now.nanoseconds) :
    bridge.tick keep now = (bridge, none) := by
  unfold Bridge.tick
  split
  · rename_i due
    exact absurd due.2.1 (Nat.not_lt.mpr ended)
  · rfl

/-- **After a tick inside the hold a velocity that is not zero is fresh.** For every
state whose action has a velocity that is not zero, and every instant before the end of
the hold: after the tick, the last send is younger than the resend age. -/
theorem Bridge.tick_fresh (keep : Keep) (bridge : Bridge) (now : Instant)
    (moving : bridge.action.velocity ≠ .zero)
    (inside : now.nanoseconds < bridge.ends.nanoseconds) :
    (bridge.tick keep now).1.Fresh keep now := by
  unfold Bridge.tick
  split
  · exact Nat.lt_add_of_pos_right keep.spaced
  · rename_i idle
    show now.nanoseconds < bridge.sent.nanoseconds + keep.resend
    have late : ¬bridge.sent.nanoseconds + keep.resend ≤ now.nanoseconds :=
      fun old => idle ⟨moving, inside, old⟩
    omega

/-- **The age of a fresh velocity until the next reading of the clock.** When the
velocity is fresh at one instant, at every instant up to `gap` later the last send is
less than `limit` old, for every `limit` that is at least the resend age plus `gap`. -/
theorem Bridge.Fresh.age {keep : Keep} {bridge : Bridge} {now : Instant}
    (fresh : bridge.Fresh keep now) (later : Instant) (gap limit : Nat)
    (next : later.nanoseconds ≤ now.nanoseconds + gap) (within : keep.resend + gap ≤ limit) :
    later.nanoseconds < bridge.sent.nanoseconds + limit := by
  unfold Bridge.Fresh at fresh
  omega

/-- The ticks of a list of readings keep the action, the stated posture, the next cycle
and the end of the hold. -/
theorem Bridge.ticks_keeps (keep : Keep) (bridge : Bridge) (readings : List Instant) :
    (bridge.ticks keep readings).1.action = bridge.action ∧
      (bridge.ticks keep readings).1.sitting = bridge.sitting ∧
      (bridge.ticks keep readings).1.next = bridge.next ∧
      (bridge.ticks keep readings).1.ends = bridge.ends := by
  induction readings generalizing bridge with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons now rest ih =>
    have kept := bridge.tick_keeps keep now
    have later := ih (bridge.tick keep now).1
    unfold Bridge.ticks
    split
    · exact ⟨later.1.trans kept.1, later.2.1.trans kept.2.1, later.2.2.1.trans kept.2.2.1,
        later.2.2.2.trans kept.2.2.2⟩
    · exact ⟨later.1.trans kept.1, later.2.1.trans kept.2.1, later.2.2.1.trans kept.2.2.1,
        later.2.2.2.trans kept.2.2.2⟩

/-- **Every command of a list of readings is the action's velocity, sent inside the
hold.** For every state and list of readings, in any order: each command sent is the
velocity of the state's action, that velocity is not zero, and the reading it is sent at
is before the end of the state's hold. -/
theorem Bridge.ticks_sent (keep : Keep) (bridge : Bridge) (readings : List Instant)
    (entry : Instant × Command) (member : entry ∈ (bridge.ticks keep readings).2) :
    entry.2 = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
      entry.1.nanoseconds < bridge.ends.nanoseconds := by
  induction readings generalizing bridge with
  | nil => cases member
  | cons now rest ih =>
    have kept := bridge.tick_keeps keep now
    unfold Bridge.ticks at member
    split at member
    · rename_i command sent
      rcases List.mem_cons.mp member with rfl | later
      · exact bridge.tick_command keep now command sent
      · have found := ih (bridge.tick keep now).1 later
        rw [kept.1, kept.2.2.2] at found
        exact found
    · have found := ih (bridge.tick keep now).1 member
      rw [kept.1, kept.2.2.2] at found
      exact found

/-! ## What the bridge sends and what the force names -/

/-- **The force names the action before the end of the hold and the default from it.**
For every state, default and instant. -/
theorem Bridge.force_named (bridge : Bridge) (rest : Option Action) (now : Instant) :
    bridge.force.named rest now =
      if now.nanoseconds < bridge.ends.nanoseconds then some bridge.action else rest :=
  bridge.force.named_lapse rest now bridge.ends rfl

/-- **At its release the force names the action.** For every release and default. -/
theorem Bridge.release_named (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now : Instant) (sitting : Bool) (action : Action) (rest : Option Action) :
    (Bridge.release pace keep origin index now sitting action).1.force.named rest now =
      some action := by
  have covers := (Bridge.release_next pace keep origin index now sitting action).2
  have held := Bridge.release_held pace keep origin index now sitting action
  have later := pace.deadline_lt origin
    (Bridge.release pace keep origin index now sitting action).1.next
  have inside : now.nanoseconds <
      (Bridge.release pace keep origin index now sitting action).1.ends.nanoseconds := by
    omega
  rw [Bridge.force_named]
  split
  · rfl
  · rename_i ended
    exact absurd inside ended

/-- **Every command of a list of readings is the velocity of the action the force
names.** For every state, default and list of readings, in any order: at the reading a
command is sent at, the force names the state's action, and the command is that action's
velocity. -/
theorem Bridge.ticks_named (keep : Keep) (bridge : Bridge) (rest : Option Action)
    (readings : List Instant) (entry : Instant × Command)
    (member : entry ∈ (bridge.ticks keep readings).2) :
    bridge.force.named rest entry.1 = some bridge.action ∧
      entry.2 = .move bridge.action.velocity := by
  have sent := bridge.ticks_sent keep readings entry member
  rw [Bridge.force_named]
  split
  · exact ⟨rfl, sent.1⟩
  · rename_i ended
    exact absurd sent.2.2 ended

/-- **From the end of the hold the force names the default and nothing is sent.** For
every state, default and instant at or after the end of the hold. -/
theorem Bridge.tick_lapsed (keep : Keep) (bridge : Bridge) (rest : Option Action)
    (now : Instant) (ended : bridge.ends.nanoseconds ≤ now.nanoseconds) :
    bridge.force.named rest now = rest ∧ bridge.tick keep now = (bridge, none) := by
  rw [Bridge.force_named]
  split
  · rename_i inside
    exact absurd inside (Nat.not_lt.mpr ended)
  · exact ⟨rfl, bridge.tick_ended keep now ended⟩

/-- **During a fault: the preceding action up to the end of its hold, and the default
from it.** For every pace, origin, default, state of the preceding release, cycle,
release, chosen force and instant of one step at which a fault holds: the action in
force is the state's action before the end of its hold, and the default from the end of
the hold. -/
theorem Bridge.fault_named (pace : Pace) (origin : Instant) (rest : Option Action)
    (bridge : Bridge) (index : Nat) (released : Instant) (chosen : Force Action)
    (now : Instant)
    (fault : (pace.outcome origin rest
      (Standing.during bridge.force index released chosen now) now).fault = true) :
    (pace.outcome origin rest
        (Standing.during bridge.force index released chosen now) now).action =
      if now.nanoseconds < bridge.ends.nanoseconds then some bridge.action else rest := by
  have awaited :=
    ((pace.step_fault origin rest bridge.force index released chosen now).mp fault).2
  rw [pace.step_action origin rest bridge.force index released chosen now]
  split
  · exact bridge.force_named rest now
  · rename_i passed
    exact absurd awaited passed

/-! ## What became of an action -/

/-- The daemon's answer to the commands of a release: refused when it refused one. -/
inductive Reply where
  /-- The daemon accepted every command. -/
  | accepted
  /-- The daemon refused a command. -/
  | refused
  deriving DecidableEq

/-- What became of a released action. -/
inductive Outcome where
  /-- The daemon accepted the action and the body showed it. -/
  | executed
  /-- The daemon accepted the action and the body showed it, and the action asked for
  the stated posture, so no skill was sent. -/
  | unchanged
  /-- The daemon refused the action. -/
  | refused
  /-- The daemon accepted the action and the body did not show it. -/
  | unexecuted
  deriving DecidableEq

/-- What became of an action released for a stated posture, from the daemon's answer and
whether the body showed the action. A refusal and a missing execution are read before
the posture. -/
def Action.outcome (action : Action) (sitting : Bool) (reply : Reply) (shown : Bool) :
    Outcome :=
  match reply with
  | .refused => .refused
  | .accepted =>
    if shown then
      if action.intent = .posture sitting then .unchanged else .executed
    else .unexecuted

/-- What became of the action a state holds, for the posture stated at its release. -/
def Bridge.outcome (bridge : Bridge) (reply : Reply) (shown : Bool) : Outcome :=
  bridge.action.outcome bridge.sitting reply shown

/-- An action that asks for a posture. -/
def Action.Postural (action : Action) : Prop :=
  action.intent = .posture true ∨ action.intent = .posture false

/-- The specification of what became of a release, in propositions about the two facts
and about the commands the release sent. It names no test of `Action.outcome`: where the
function compares the action's intent with the stated posture, the specification says
that a posture action's release sent no toggle. -/
def Action.Judged (action : Action) (sitting : Bool) (reply : Reply) (shown : Bool)
    (outcome : Outcome) : Prop :=
  (outcome = .refused ∧ reply = .refused) ∨
    (outcome = .unexecuted ∧ reply = .accepted ∧ shown = false) ∨
    (outcome = .unchanged ∧ reply = .accepted ∧ shown = true ∧
      action.Postural ∧ Command.perform .sitToggle ∉ action.commands sitting) ∨
    (outcome = .executed ∧ reply = .accepted ∧ shown = true ∧
      ¬(action.Postural ∧ Command.perform .sitToggle ∉ action.commands sitting))

/-- **The outcome is the specified one.** For every action, stated posture, answer,
evidence and outcome: the function gives the outcome exactly when the specification
holds of it. -/
theorem Action.outcome_judged (action : Action) (sitting : Bool) (reply : Reply)
    (shown : Bool) (outcome : Outcome) :
    action.outcome sitting reply shown = outcome ↔
      action.Judged sitting reply shown outcome := by
  unfold Action.Judged Action.Postural
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> cases outcome <;> decide

/-- **The outcome of a release reads that release's commands.** For every release,
answer, evidence and outcome: the outcome of the state of a release is the one the
specification gives for the action and the posture of that same release. -/
theorem Bridge.release_outcome (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (now : Instant) (sitting : Bool) (action : Action) (reply : Reply) (shown : Bool)
    (outcome : Outcome) :
    (Bridge.release pace keep origin index now sitting action).1.outcome reply shown =
        outcome ↔
      action.Judged sitting reply shown outcome :=
  action.outcome_judged sitting reply shown outcome

/-! ## The declared numbers -/

namespace Declared

/-- The declared pace: an action cycle of 200 ms, which is 5 Hz, and a latency of one
cycle. -/
def pace : Pace := ⟨200000000, 1, by decide, by decide⟩

/-- The declared keeping: a velocity is sent again when its last send is 100 ms old, the
hold ends two cycles after the deadline of the next percept's action, and a send may
take 10 ms to reach the daemon. `keep_declared` places these numbers inside the daemon's
expiry. -/
def keep : Keep := ⟨100000000, 2, 10000000, by decide⟩

/-- Nanoseconds after which the daemon replaces a velocity intent by zero: 500 ms. An
assumption about the vendor's daemon. -/
def expiry : Nat := 500000000

/-- Nanoseconds: the largest gap between two readings of the clock that the declared
keeping allows for, 50 ms. An assumption about a host loop and its scheduling. -/
def gap : Nat := 50000000

/-- The world's declared default: the action in force from the lapse of a held action.
It stands still, which is what the daemon's expiry gives (`rest_declared`). -/
def rest : Action := .still

end Declared

/-- **The declared keeping is inside the expiry.** The resend age, the allowed gap and
the transit allowance together are less than the expiry. -/
theorem keep_declared :
    Declared.keep.resend + Declared.gap + Declared.keep.transit < Declared.expiry := by
  decide

/-- **The declared default is the zero velocity, with no duration.** -/
theorem rest_declared :
    Declared.rest.velocity = .zero ∧ Declared.rest.duration = 0 := by
  decide

end Acorn.Host.Microduck
