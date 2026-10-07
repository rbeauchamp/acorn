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
stated at that release, the instant its velocity was last sent at, and the instant its
hold ends.

`Bridge.release` is the release of an action. It gives the action's commands and a
state that depends on no earlier state (`Bridge.release_state`): the hold ends the
action's span and a declared grace after the release. `Bridge.tick` is one reading of
the clock between two releases. It sends the action's velocity again when that velocity
is not zero, the hold has not ended and the last send has reached a declared age. A
zero velocity is not sent again: the daemon's expiry gives zero by itself.

The statements, for every state, instant and list of readings:

- A tick changes neither the action, nor the stated posture, nor the end of the hold
  (`Bridge.tick_keeps`), and what it sends is the action's velocity
  (`Bridge.tick_command`).
- Over any list of readings, in any order, every command sent is the action's velocity,
  which is not zero, at a reading before the end of the hold (`Bridge.ticks_sent`). So
  from the end of the hold nothing is sent (`Bridge.tick_ended`), and the bridge keeps no
  velocity alive for an agent that releases nothing more.
- Inside the hold, after a tick, the last send of a velocity that is not zero is younger
  than the resend age (`Bridge.tick_fresh`, and `Bridge.release_fresh` at the release),
  and until the next reading it stays younger than the resend age plus the gap to that
  reading (`Bridge.Fresh.age`).
- When the grace is at least the latency, the first action is released at or after the
  start of its percept's cycle, and the next action is for the percept `span` cycles
  later and meets its deadline, that next release is before the end of the first
  action's hold (`Bridge.release_covers`).

`Bridge.outcome` is what became of the released action, one of four outcomes, from the
state and two facts that this module takes as inputs: the daemon's answer, and whether
the body showed the action. The posture is the one stated at the release, which the
state holds, so the outcome and the commands of one release read one posture
(`Bridge.outcome_unsent`). How sensing shows an action is not defined here.

Assumptions of the use of these statements, proved nowhere:

- the daemon's expiry, `Declared.expiry` (the observed run saw a velocity zeroed 503 to
  520 ms after the last send; its record is at
  https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895);
- the daemon ages a velocity from its receipt, and the receipt follows the reading of
  the clock that a send is stamped with by at most `Declared.transit`;
- a reading of the clock, and a tick, at least every `Declared.gap`. That needs a reader
  of the clock that runs while the agent's step computes, which is a property of a host
  loop that is not built, and of the operating system's scheduling;
- the posture a caller states is the body's.

No executing code keeps a `Bridge`: the functions here are pure, and the host loop that
calls them is not built (https://github.com/rbeauchamp/acorn/issues/95). A host owes
that it releases the next action for the percept `span` cycles later and no earlier;
nothing in the state refuses an earlier release.
-/
namespace Acorn.Host.Microduck

/-- What a bridge declares about keeping a velocity alive. -/
structure Keep where
  /-- Nanoseconds: the age of the last send at which a velocity is sent again. -/
  resend : Nat
  /-- Cycles after an action's span during which the bridge still sends its velocity. -/
  grace : Nat
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
  /-- The instant from which the bridge sends that velocity no more. -/
  ends : Instant

/-- Release an action at an instant, for the posture of the body as the caller states
it: the state after the release, and the action's commands. -/
def Bridge.release (pace : Pace) (keep : Keep) (now : Instant) (sitting : Bool)
    (action : Action) : Bridge × List Command :=
  (⟨action, sitting, now,
      ⟨now.nanoseconds + (action.span pace + keep.grace) * pace.cycle⟩⟩,
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

/-- **The state and the commands of a release.** For every pace, keeping, instant, stated
posture and action: the state holds the action, the stated posture, the instant of the
release as the last send, and a hold that ends the action's span and the grace after the
release; the commands are the action's. No earlier state is an input. -/
theorem Bridge.release_state (pace : Pace) (keep : Keep) (now : Instant) (sitting : Bool)
    (action : Action) :
    (Bridge.release pace keep now sitting action).1 =
        ⟨action, sitting, now,
          ⟨now.nanoseconds + (action.span pace + keep.grace) * pace.cycle⟩⟩ ∧
      (Bridge.release pace keep now sitting action).2 = action.commands sitting :=
  ⟨rfl, rfl⟩

/-- The velocity is fresh at the instant of its release. -/
theorem Bridge.release_fresh (pace : Pace) (keep : Keep) (now : Instant) (sitting : Bool)
    (action : Action) :
    (Bridge.release pace keep now sitting action).1.Fresh keep now :=
  Nat.lt_add_of_pos_right keep.spaced

/-- **A tick sends the action's velocity and no other command.** -/
theorem Bridge.tick_command (keep : Keep) (bridge : Bridge) (now : Instant) (command : Command)
    (sent : (bridge.tick keep now).2 = some command) :
    command = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
      now.nanoseconds < bridge.ends.nanoseconds := by
  unfold Bridge.tick at sent
  split at sent
  · rename_i due
    exact ⟨(Option.some.inj sent).symm, due.1, due.2.1⟩
  · cases sent

/-- **A tick keeps the action, the stated posture and the end of the hold.** -/
theorem Bridge.tick_keeps (keep : Keep) (bridge : Bridge) (now : Instant) :
    (bridge.tick keep now).1.action = bridge.action ∧
      (bridge.tick keep now).1.sitting = bridge.sitting ∧
      (bridge.tick keep now).1.ends = bridge.ends := by
  unfold Bridge.tick
  split <;> exact ⟨rfl, rfl, rfl⟩

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

/-- The ticks of a list of readings keep the action, the stated posture and the end of
the hold. -/
theorem Bridge.ticks_keeps (keep : Keep) (bridge : Bridge) (readings : List Instant) :
    (bridge.ticks keep readings).1.action = bridge.action ∧
      (bridge.ticks keep readings).1.sitting = bridge.sitting ∧
      (bridge.ticks keep readings).1.ends = bridge.ends := by
  induction readings generalizing bridge with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons now rest ih =>
    have kept := bridge.tick_keeps keep now
    have later := ih (bridge.tick keep now).1
    unfold Bridge.ticks
    split
    · exact ⟨later.1.trans kept.1, later.2.1.trans kept.2.1, later.2.2.trans kept.2.2⟩
    · exact ⟨later.1.trans kept.1, later.2.1.trans kept.2.1, later.2.2.trans kept.2.2⟩

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
        rw [kept.1, kept.2.2] at found
        exact found
    · have found := ih (bridge.tick keep now).1 member
      rw [kept.1, kept.2.2] at found
      exact found

/-- **A release that meets its deadline arrives inside the hold.** For every pace whose
latency is at most the grace: when an action is released at or after the start of its
percept's cycle, and the next action, for the percept `span` cycles later, meets its
deadline, the next release is before the end of the first action's hold. -/
theorem Bridge.release_covers (pace : Pace) (keep : Keep) (origin : Instant) (index : Nat)
    (first second : Instant) (sitting : Bool) (action : Action)
    (covered : pace.latency ≤ keep.grace)
    (sensed : (pace.boundary origin index).nanoseconds ≤ first.nanoseconds)
    (met : pace.meets origin (index + action.span pace) second = true) :
    second.nanoseconds <
      (Bridge.release pace keep first sitting action).1.ends.nanoseconds := by
  have near := pace.met_gap origin index (action.span pace) first second sensed met
  have wider : (action.span pace + pace.latency) * pace.cycle ≤
      (action.span pace + keep.grace) * pace.cycle :=
    Nat.mul_le_mul_right pace.cycle (Nat.add_le_add_left covered _)
  show second.nanoseconds <
    first.nanoseconds + (action.span pace + keep.grace) * pace.cycle
  omega

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
  /-- The action asked for the stated posture, and no skill was sent. -/
  | unchanged
  /-- The daemon refused the action. -/
  | refused
  /-- The daemon accepted the action and the body did not show it. -/
  | unexecuted
  deriving DecidableEq

/-- What became of an action released for a stated posture, from the daemon's answer and
whether the body showed the action. -/
def Action.outcome (action : Action) (sitting : Bool) (reply : Reply) (shown : Bool) :
    Outcome :=
  if action.intent = .posture sitting then .unchanged
  else match reply with
    | .refused => .refused
    | .accepted => if shown then .executed else .unexecuted

/-- What became of the action a state holds, for the posture stated at its release. -/
def Bridge.outcome (bridge : Bridge) (reply : Reply) (shown : Bool) : Outcome :=
  bridge.action.outcome bridge.sitting reply shown

/-- **Each outcome, exactly.** For every action, stated posture, answer and evidence: the
outcome is `unchanged` exactly when the action asks for the stated posture; otherwise it
is `refused` exactly for a refusal, `executed` exactly for an accepted action that the
body showed, and `unexecuted` exactly for an accepted action that it did not show. -/
theorem Action.outcome_iff (action : Action) (sitting : Bool) (reply : Reply) (shown : Bool) :
    (action.outcome sitting reply shown = .unchanged ↔ action.intent = .posture sitting) ∧
      (action.outcome sitting reply shown = .refused ↔
        action.intent ≠ .posture sitting ∧ reply = .refused) ∧
      (action.outcome sitting reply shown = .executed ↔
        action.intent ≠ .posture sitting ∧ reply = .accepted ∧ shown = true) ∧
      (action.outcome sitting reply shown = .unexecuted ↔
        action.intent ≠ .posture sitting ∧ reply = .accepted ∧ shown = false) := by
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> decide

/-- **`unchanged` is the outcome of a posture action whose release sent no skill.** For
every release, answer and evidence: the outcome of the state of a release is `unchanged`
exactly when the action asks for a posture and the commands of that same release hold no
toggle. -/
theorem Bridge.outcome_unsent (pace : Pace) (keep : Keep) (now : Instant) (sitting : Bool)
    (action : Action) (reply : Reply) (shown : Bool) :
    (Bridge.release pace keep now sitting action).1.outcome reply shown = .unchanged ↔
      (action.intent = .posture true ∨ action.intent = .posture false) ∧
        Command.perform .sitToggle ∉ (Bridge.release pace keep now sitting action).2 := by
  show action.outcome sitting reply shown = .unchanged ↔
    (action.intent = .posture true ∨ action.intent = .posture false) ∧
      Command.perform .sitToggle ∉ action.commands sitting
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> decide

/-! ## The declared numbers -/

namespace Declared

/-- The declared pace: an action cycle of 200 ms, which is 5 Hz, and a latency of one
cycle. `span_declared` gives the cycles of each action at this pace. -/
def pace : Pace := ⟨200000000, 1, by decide, by decide⟩

/-- The declared keeping: a velocity is sent again when its last send is 100 ms old,
and for two cycles after an action's span. `keep_declared` places these numbers inside
the daemon's expiry. -/
def keep : Keep := ⟨100000000, 2, by decide⟩

/-- Nanoseconds after which the daemon replaces a velocity intent by zero: 500 ms. An
assumption about the vendor's daemon. -/
def expiry : Nat := 500000000

/-- Nanoseconds: the largest gap between two readings of the clock that the declared
keeping allows for, 50 ms. An assumption about a host loop and its scheduling. -/
def gap : Nat := 50000000

/-- Nanoseconds: the longest time from the reading of the clock that a send is stamped
with to the daemon's receipt that the declared keeping allows for, 10 ms. An assumption
about the transport. -/
def transit : Nat := 10000000

end Declared

/-- **The declared spans.** At the declared pace a velocity lasts one cycle, a kick
four, a posture seven, the roll eight and the pick sixteen. -/
theorem span_declared (action : Action) :
    action.span Declared.pace =
      match action with
      | .still | .forward | .turnLeft | .turnRight => 1
      | .kickLeft | .kickRight => 4
      | .sit | .stand => 7
      | .roll => 8
      | .pick => 16 := by
  cases action <;> decide

/-- **The declared keeping is inside the expiry.** The resend age, the allowed gap and
the allowed transit together are less than the expiry, and the grace is at least the
latency. -/
theorem keep_declared :
    Declared.keep.resend + Declared.gap + Declared.transit < Declared.expiry ∧
      Declared.pace.latency ≤ Declared.keep.grace := by
  decide

/-- **Two timely releases of consecutive cycles are inside the expiry.** At the declared
pace: when an action is released at or after the start of its percept's cycle, and the
action of the next cycle's percept meets its deadline, the second release, with the
allowed transit, is less than the expiry after the first. -/
theorem releases_declared (origin : Instant) (index : Nat) (first second : Instant)
    (sensed : (Declared.pace.boundary origin index).nanoseconds ≤ first.nanoseconds)
    (met : Declared.pace.meets origin (index + 1) second = true) :
    second.nanoseconds + Declared.transit < first.nanoseconds + Declared.expiry := by
  have near := Declared.pace.met_gap origin index 1 first second sensed met
  have value : (1 + Declared.pace.latency) * Declared.pace.cycle = 400000000 := by decide
  rw [value] at near
  show second.nanoseconds + 10000000 < first.nanoseconds + 500000000
  omega

end Acorn.Host.Microduck
