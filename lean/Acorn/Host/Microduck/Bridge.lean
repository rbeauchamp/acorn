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
bridge holds between two events: the record of the last release (the action, the posture
its caller stated, the cycle of the action's percept and the instant of the release) and
the instant the action's velocity was last sent at.

`Bridge.release` is the release of an action for the percept of a cycle. It gives the
action's commands and a state that depends on no earlier state (`Bridge.release_state`).
The cycle of the next percept and the end of the hold are not stored: `Bridge.next` and
`Bridge.ends` are functions of the release record, so no state holds a next cycle or an
end that its release does not give. For every state, the cycle of the next percept is
after the action's own and starts no earlier than the release plus the action's declared
duration and the transit allowance, whether the release was timely or late
(`Bridge.next_covers`). The hold ends a declared number of cycles, the grace, after the
deadline of the next percept's action (`Bridge.ends_held`), so a next release that meets
its deadline is inside the hold (`Bridge.ends_covers`).

`Bridge.tick` is one reading of the clock between two releases. It sends the action's
velocity again when that velocity is not zero, the hold has not ended and the last send
has reached a declared age, and it changes nothing but the instant of the last send
(`Bridge.tick_keeps`). A zero velocity is not sent again: the daemon's expiry gives zero
by itself.

## The hold is bounded on purpose

The daemon's expiry is the vendor's protection against a client that has stopped. A
bridge that sent a velocity again without end, for an agent that does not answer, would
remove it. So the bridge keeps the preceding action for the grace and no longer, and the
model of the deadline rule says so: `Bridge.force` is the action with the end of the
hold as its lapse, and the world's declared default, `Declared.rest`, is the action that
stands still. During a fault the action in force is the preceding action up to the end
of the hold and the default from it (`Bridge.fault_named`).

The bound is a time under one hypothesis, that the release is not before the start of
its percept's cycle:
`(pace.boundary origin bridge.index).nanoseconds ≤ bridge.released.nanoseconds`. The
hold then ends no later than the release plus the action's declared duration, the
transit allowance and `1 + latency + grace` cycles (`Bridge.ends_bounded`). The
hypothesis is what a host owes: the state takes the cycle of the percept as an argument
and does not check it against the instant of the release.

What the bridge sends and what the deadline rule names agree after a release. At every
instant after the instant of a release and before the end of its hold, the outcome of
the step names the released action (`Bridge.release_named`), whose velocity is the first
command of the release (`Action.commands_head`). Over any list of readings, in any
order, every command sent is the velocity of the action that the standing after the
release names at that reading (`Bridge.ticks_named`). From the end of the hold that
standing names the default and a tick sends nothing (`Bridge.tick_lapsed`). At the
instant of a release itself the two differ: the deadline rule counts an action as in
force after the instant it is released at, so the outcome still names the preceding
action there, and the bridge has sent the new velocity.

Inside the hold, after a tick, the last send of a velocity that is not zero is younger
than the resend age (`Bridge.tick_fresh`, and `Bridge.release_fresh` at the release),
and until the next reading it stays younger than the resend age plus the gap to that
reading (`Bridge.Fresh.age`).

The force names what the bridge keeps in force, not what the body does. The last send of
a velocity can be just before the end of the hold. Under the assumptions below the
daemon receives it at most the transit allowance later and holds it for its expiry, so
it replaces the last velocity it received by zero less than the expiry plus the transit
allowance after the end of the hold: 510 ms with the declared numbers.

The observed run saw more than the assumed expiry. The daemon checks the age of an
intent once per 20 ms control tick, so the replacement came 503 to 520 ms after the last
send, and the gait was back at standing 83 and 85 ms after the replacement. How long the
body moves after a lapse is UNKNOWN beyond those observations: it is a property of the
daemon's smoothing of a command and of the body, and no assumption below states it.

## What became of an action

`Action.outcome` is what became of a released action, one of five outcomes that later
code has to tell apart: `refused`, `unanswered` (the daemon's answer was not complete),
`unexecuted` (accepted, and the body did not show it), `unchanged` (accepted and shown,
for a posture the body had, so no skill was sent) and `executed`. The answer is a
`Reply` of three states, pending, accepted and refused. A refusal, a pending answer and a
missing execution are read first, so an action that asks for the stated posture still
reports them. An outcome says that the daemon accepted the action exactly for an
accepted answer (`Action.outcome_accepted`), and it is a refusal or unanswered exactly
for a refused or a pending one (`Action.outcome_reply`). `Action.Judged` is the
specification of all five outcomes, in propositions about the commands the release sent,
and
`Action.outcome_judged` states that the function gives an outcome exactly when the
specification holds of it. `Bridge.outcome` reads the posture that the state holds from
the release, so the commands and the outcome of one release read one posture. How
sensing shows an action is not defined here: the outcome takes that fact as an input,
and `Acorn.Host.Microduck.Session` gives it by a declared table of policy labels.

## Assumptions

These are assumptions of the use of the statements, proved nowhere:

- the daemon's expiry, `Declared.expiry` (the observed run saw a velocity zeroed 503 to
  520 ms after the last send; its record is at
  https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895), and that the
  daemon ages a velocity from its receipt;
- the receipt follows the reading of the clock that a send is stamped with by at most
  the transit allowance of the keeping;
- a reading of the clock, and a tick, at least every `Declared.gap`. That needs a reader
  of the clock that runs while the agent's step computes, which is a property of the
  driver of the host's loop, `Acorn.Host.Microduck.Driver`, and of the operating system's
  scheduling: the driver counts the gaps above it and does not prevent them;
- the posture a caller states is the body's;
- the declared duration of an action covers what the body takes for it.

The functions here are pure. `Acorn.Host.Microduck.Session` holds a `Bridge`, the record of
the last release, in the state of a host and calls them in its own
pure transitions, which refuse a percept before the cycle that `Bridge.next` gives;
`Acorn.Host.Microduck.Loop` calls those in a pure loop, which the executable of
`Acorn.Host.Microduck.Driver` runs (https://github.com/rbeauchamp/acorn/issues/95). Nothing in a `Bridge` itself refuses an
earlier release.
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

/-- What a bridge holds between two events: the record of the last release, and the
instant its velocity was last sent at. -/
structure Bridge where
  /-- The action released last. -/
  action : Action
  /-- The posture of the body as the caller stated it at that release. -/
  sitting : Bool
  /-- The cycle of the percept the action was released for. -/
  index : Nat
  /-- The instant of the release. -/
  released : Instant
  /-- The instant the action's velocity was last sent at. -/
  sent : Instant

/-- Release an action at an instant for the percept of a cycle, for the posture of the
body as the caller states it: the state after the release, and the action's commands. -/
def Bridge.release (index : Nat) (now : Instant) (sitting : Bool) (action : Action) :
    Bridge × List Command :=
  (⟨action, sitting, index, now, now⟩, action.commands sitting)

/-- The cycle of the next percept, from the release record. -/
def Bridge.next (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) : Nat :=
  bridge.action.next pace keep.transit origin bridge.index bridge.released

/-- The instant from which the bridge sends the action's velocity no more: the start of
the cycle `latency + grace` cycles after the next percept's. -/
def Bridge.ends (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) : Instant :=
  pace.boundary origin (bridge.next pace keep origin + pace.latency + keep.grace)

/-- One reading of the clock between two releases: send the action's velocity again when
it is not zero, the hold has not ended and the last send is at least the resend age
old. -/
def Bridge.tick (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) : Bridge × Option Command :=
  if bridge.action.velocity ≠ .zero ∧
      now.nanoseconds < (bridge.ends pace keep origin).nanoseconds ∧
      bridge.sent.nanoseconds + keep.resend ≤ now.nanoseconds then
    ({ bridge with sent := now }, some (.move bridge.action.velocity))
  else (bridge, none)

/-- The ticks of a list of readings, in the order of the list: the state after them, and
each command sent with the reading it was sent at. -/
def Bridge.ticks (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    List Instant → Bridge × List (Instant × Command)
  | [] => (bridge, [])
  | now :: rest =>
    match (bridge.tick pace keep origin now).2 with
    | some command =>
      (((bridge.tick pace keep origin now).1.ticks pace keep origin rest).1,
        (now, command) :: ((bridge.tick pace keep origin now).1.ticks pace keep origin rest).2)
    | none => (bridge.tick pace keep origin now).1.ticks pace keep origin rest

/-- The last send is younger than the resend age at an instant. -/
def Bridge.Fresh (keep : Keep) (bridge : Bridge) (now : Instant) : Prop :=
  now.nanoseconds < bridge.sent.nanoseconds + keep.resend

/-- The force of a state for the deadline rule: its action, which lapses at the end of
the hold. -/
def Bridge.force (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    Force Action :=
  ⟨some bridge.action, some (bridge.ends pace keep origin)⟩

/-- **The state and the commands of a release.** For every cycle, instant, stated posture
and action: the state is the record of the release, with the instant of the release as
the last send, and the commands are the action's. No earlier state is an input. -/
theorem Bridge.release_state (index : Nat) (now : Instant) (sitting : Bool) (action : Action) :
    (Bridge.release index now sitting action).1 = ⟨action, sitting, index, now, now⟩ ∧
      (Bridge.release index now sitting action).2 = action.commands sitting :=
  ⟨rfl, rfl⟩

/-- **No percept falls inside the declared duration of the released action.** For every
state, whether its release was timely or late: the cycle of the next percept is after
the cycle of the action's own percept, and it starts no earlier than the release plus
the action's declared duration and the transit allowance. -/
theorem Bridge.next_covers (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    bridge.index < bridge.next pace keep origin ∧
      bridge.released.nanoseconds + bridge.action.duration + keep.transit ≤
        (pace.boundary origin (bridge.next pace keep origin)).nanoseconds :=
  ⟨bridge.action.next_after pace keep.transit origin bridge.index bridge.released,
    bridge.action.next_covers pace keep.transit origin bridge.index bridge.released⟩

/-- **The hold ends the grace after the next deadline.** For every state, the hold ends
`grace` cycles after the deadline of the action of the next percept. -/
theorem Bridge.ends_held (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    (bridge.ends pace keep origin).nanoseconds =
      (pace.deadline origin (bridge.next pace keep origin)).nanoseconds +
        keep.grace * pace.cycle := by
  unfold Bridge.ends
  rw [pace.boundary_nanoseconds, pace.deadline_nanoseconds, Nat.add_mul, Nat.add_assoc]

/-- **A release that meets its deadline arrives inside the hold.** For every state: when
the action of the next percept meets its deadline, that next release is before the end
of the hold. -/
theorem Bridge.ends_covers (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (second : Instant)
    (met : pace.meets origin (bridge.next pace keep origin) second = true) :
    second.nanoseconds < (bridge.ends pace keep origin).nanoseconds := by
  have verdict := (pace.meets_iff origin _ second).mp met
  have held := bridge.ends_held pace keep origin
  have due := pace.deadline_nanoseconds origin (bridge.next pace keep origin)
  omega

/-- **The hold ends a bounded time after the release.** For every pace, keeping, origin
and state whose release is not before the start of its percept's cycle: the hold ends no
later than the release plus the action's declared duration, the transit allowance and
`1 + latency + grace` cycles. The hypothesis is a host's obligation: `Bridge.release`
takes the cycle as an argument and does not check it against the instant. -/
theorem Bridge.ends_bounded (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (sensed : (pace.boundary origin bridge.index).nanoseconds ≤ bridge.released.nanoseconds) :
    (bridge.ends pace keep origin).nanoseconds ≤
      bridge.released.nanoseconds + bridge.action.duration + keep.transit +
        (1 + pace.latency + keep.grace) * pace.cycle := by
  rw [pace.boundary_nanoseconds origin bridge.index] at sensed
  have started : origin.nanoseconds ≤
      bridge.released.nanoseconds + bridge.action.duration + keep.transit := by
    omega
  have within : origin.nanoseconds +
      pace.first origin
        ⟨bridge.released.nanoseconds + bridge.action.duration + keep.transit⟩ * pace.cycle <
      bridge.released.nanoseconds + bridge.action.duration + keep.transit + pace.cycle :=
    pace.first_within origin
      ⟨bridge.released.nanoseconds + bridge.action.duration + keep.transit⟩ started
  have reach : origin.nanoseconds + bridge.next pace keep origin * pace.cycle ≤
      bridge.released.nanoseconds + bridge.action.duration + keep.transit + pace.cycle := by
    unfold Bridge.next Action.next
    rcases Nat.le_total (bridge.index + 1) (pace.first origin
      ⟨bridge.released.nanoseconds + bridge.action.duration + keep.transit⟩) with later | sooner
    · rw [Nat.max_eq_right later]
      omega
    · rw [Nat.max_eq_left sooner, Nat.add_mul, Nat.one_mul]
      omega
  have split : (bridge.next pace keep origin + pace.latency + keep.grace) * pace.cycle =
      bridge.next pace keep origin * pace.cycle + (pace.latency + keep.grace) * pace.cycle := by
    rw [Nat.add_assoc, Nat.add_mul]
  have whole : (1 + pace.latency + keep.grace) * pace.cycle =
      pace.cycle + (pace.latency + keep.grace) * pace.cycle := by
    rw [Nat.add_assoc, Nat.add_mul, Nat.one_mul]
  unfold Bridge.ends
  rw [pace.boundary_nanoseconds]
  omega

/-- The velocity is fresh at the instant of its release. -/
theorem Bridge.release_fresh (keep : Keep) (index : Nat) (now : Instant) (sitting : Bool)
    (action : Action) : (Bridge.release index now sitting action).1.Fresh keep now :=
  Nat.lt_add_of_pos_right keep.spaced

/-- **A tick sends the action's velocity and no other command.** A command that a tick
sends is the velocity of the state's action, which is not zero, at an instant before the
end of the hold. -/
theorem Bridge.tick_command (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) (command : Command)
    (sent : (bridge.tick pace keep origin now).2 = some command) :
    command = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
      now.nanoseconds < (bridge.ends pace keep origin).nanoseconds := by
  unfold Bridge.tick at sent
  split at sent
  · rename_i due
    exact ⟨(Option.some.inj sent).symm, due.1, due.2.1⟩
  · cases sent

/-- **A tick keeps the release record.** A tick changes neither the action, nor the
stated posture, nor the cycle, nor the instant of the release, so it changes neither the
cycle of the next percept nor the end of the hold. -/
theorem Bridge.tick_keeps (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) :
    (bridge.tick pace keep origin now).1.action = bridge.action ∧
      (bridge.tick pace keep origin now).1.sitting = bridge.sitting ∧
      (bridge.tick pace keep origin now).1.next pace keep origin =
        bridge.next pace keep origin ∧
      (bridge.tick pace keep origin now).1.ends pace keep origin =
        bridge.ends pace keep origin := by
  unfold Bridge.tick
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Nothing is sent from the end of the hold.** For every state and instant: a tick at
or after the end of the hold sends nothing and changes nothing. -/
theorem Bridge.tick_ended (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant)
    (ended : (bridge.ends pace keep origin).nanoseconds ≤ now.nanoseconds) :
    bridge.tick pace keep origin now = (bridge, none) := by
  unfold Bridge.tick
  split
  · rename_i due
    exact absurd due.2.1 (Nat.not_lt.mpr ended)
  · rfl

/-- **After a tick inside the hold a velocity that is not zero is fresh.** For every
state whose action has a velocity that is not zero, and every instant before the end of
the hold: after the tick, the last send is younger than the resend age. -/
theorem Bridge.tick_fresh (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) (moving : bridge.action.velocity ≠ .zero)
    (inside : now.nanoseconds < (bridge.ends pace keep origin).nanoseconds) :
    (bridge.tick pace keep origin now).1.Fresh keep now := by
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

/-- The ticks of a list of readings keep the action, the stated posture, the cycle of
the next percept and the end of the hold. -/
theorem Bridge.ticks_keeps (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (readings : List Instant) :
    (bridge.ticks pace keep origin readings).1.action = bridge.action ∧
      (bridge.ticks pace keep origin readings).1.sitting = bridge.sitting ∧
      (bridge.ticks pace keep origin readings).1.next pace keep origin =
        bridge.next pace keep origin ∧
      (bridge.ticks pace keep origin readings).1.ends pace keep origin =
        bridge.ends pace keep origin := by
  induction readings generalizing bridge with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons now rest ih =>
    have kept := bridge.tick_keeps pace keep origin now
    have later := ih (bridge.tick pace keep origin now).1
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
theorem Bridge.ticks_sent (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (readings : List Instant) (entry : Instant × Command)
    (member : entry ∈ (bridge.ticks pace keep origin readings).2) :
    entry.2 = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
      entry.1.nanoseconds < (bridge.ends pace keep origin).nanoseconds := by
  induction readings generalizing bridge with
  | nil => cases member
  | cons now rest ih =>
    have kept := bridge.tick_keeps pace keep origin now
    unfold Bridge.ticks at member
    split at member
    · rename_i command sent
      rcases List.mem_cons.mp member with rfl | later
      · exact bridge.tick_command pace keep origin now command sent
      · have found := ih (bridge.tick pace keep origin now).1 later
        rw [kept.1, kept.2.2.2] at found
        exact found
    · have found := ih (bridge.tick pace keep origin now).1 member
      rw [kept.1, kept.2.2.2] at found
      exact found

/-! ## What the bridge sends and what the deadline rule names -/

/-- **The force names the action before the end of the hold and the default from it.**
For every state, default and instant. -/
theorem Bridge.force_named (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (rest : Option Action) (now : Instant) :
    (bridge.force pace keep origin).named rest now =
      if now.nanoseconds < (bridge.ends pace keep origin).nanoseconds then some bridge.action
      else rest :=
  (bridge.force pace keep origin).named_lapse rest now (bridge.ends pace keep origin) rfl

/-- **After its release, and before the end of its hold, the outcome names the released
action.** For every step whose action is released at an instant with the force of that
release's state, and every later instant before the end of the hold. At the instant of
the release itself the outcome names what the preceding force names
(`Pace.step_action`). -/
theorem Bridge.release_named (pace : Pace) (keep : Keep) (origin : Instant)
    (rest : Option Action) (prior : Force Action) (index : Nat) (now : Instant)
    (sitting : Bool) (action : Action) (later : Instant)
    (after : now.nanoseconds < later.nanoseconds)
    (inside : later.nanoseconds <
      ((Bridge.release index now sitting action).1.ends pace keep origin).nanoseconds) :
    (pace.outcome origin rest (Standing.during prior index now
      ((Bridge.release index now sitting action).1.force pace keep origin) later)
        later).action = some action := by
  rw [pace.step_action origin rest prior index now _ later]
  split
  · rename_i early
    exact absurd early (Nat.not_le.mpr after)
  · rw [Bridge.force_named]
    split
    · rfl
    · rename_i ended
      exact absurd inside ended

/-- **Every command of a list of readings is the velocity of the action the standing
names.** For every state, default and list of readings, in any order: at the reading a
command is sent at, the outcome of the standing after the release names the state's
action, and the command is that action's velocity. -/
theorem Bridge.ticks_named (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (rest : Option Action) (readings : List Instant) (entry : Instant × Command)
    (member : entry ∈ (bridge.ticks pace keep origin readings).2) :
    (pace.outcome origin rest (Standing.idle (bridge.force pace keep origin))
        entry.1).action = some bridge.action ∧
      entry.2 = .move bridge.action.velocity := by
  have sent := bridge.ticks_sent pace keep origin readings entry member
  rw [pace.outcome_action origin rest]
  show (bridge.force pace keep origin).named rest entry.1 = some bridge.action ∧ _
  rw [Bridge.force_named]
  split
  · exact ⟨rfl, sent.1⟩
  · rename_i ended
    exact absurd sent.2.2 ended

/-- **From the end of the hold the standing names the default and nothing is sent.** For
every state, default and instant at or after the end of the hold. -/
theorem Bridge.tick_lapsed (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (rest : Option Action) (now : Instant)
    (ended : (bridge.ends pace keep origin).nanoseconds ≤ now.nanoseconds) :
    (pace.outcome origin rest (Standing.idle (bridge.force pace keep origin)) now).action =
        rest ∧
      bridge.tick pace keep origin now = (bridge, none) := by
  rw [pace.outcome_action origin rest]
  show (bridge.force pace keep origin).named rest now = rest ∧ _
  rw [Bridge.force_named]
  split
  · rename_i inside
    exact absurd inside (Nat.not_lt.mpr ended)
  · exact ⟨rfl, bridge.tick_ended pace keep origin now ended⟩

/-- **During a fault: the preceding action up to the end of its hold, and the default
from it.** For every pace, keeping, origin, default, state of the preceding release,
cycle, release, chosen force and instant of one step at which a fault holds: the action
in force is the state's action before the end of its hold, and the default from the end
of the hold. -/
theorem Bridge.fault_named (pace : Pace) (keep : Keep) (origin : Instant)
    (rest : Option Action) (bridge : Bridge) (index : Nat) (released : Instant)
    (chosen : Force Action) (now : Instant)
    (fault : (pace.outcome origin rest
      (Standing.during (bridge.force pace keep origin) index released chosen now)
        now).fault = true) :
    (pace.outcome origin rest
        (Standing.during (bridge.force pace keep origin) index released chosen now)
          now).action =
      if now.nanoseconds < (bridge.ends pace keep origin).nanoseconds then some bridge.action
      else rest := by
  have awaited := ((pace.step_fault origin rest (bridge.force pace keep origin) index
    released chosen now).mp fault).2
  rw [pace.step_action origin rest (bridge.force pace keep origin) index released chosen now]
  split
  · exact bridge.force_named pace keep origin rest now
  · rename_i passed
    exact absurd awaited passed

/-! ## What became of an action -/

/-- The daemon's answer to the commands of a release, as far as it was heard. -/
inductive Reply where
  /-- An answer to a command of the release was not heard yet, and none refused. -/
  | pending
  /-- The daemon accepted every command of the release. -/
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
  /-- The daemon's answer to the action was not complete: it says neither that the daemon
  accepted the action nor that it refused it. -/
  | unanswered
  deriving DecidableEq

/-- What became of an action released for a stated posture, from the daemon's answer and
whether the body showed the action. A refusal, a pending answer and a missing execution
are read before the posture, so an outcome that says the daemon accepted the action is
given only for an accepted answer. -/
def Action.outcome (action : Action) (sitting : Bool) (reply : Reply) (shown : Bool) :
    Outcome :=
  match reply with
  | .refused => .refused
  | .pending => .unanswered
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
    (outcome = .unanswered ∧ reply = .pending) ∨
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

/-- **The outcome says that the daemon accepted the action exactly for an accepted
answer.** For every action, stated posture, answer and evidence: the outcome is neither a
refusal nor unanswered, so it is one of the three that say the daemon accepted the action,
exactly when the answer is the accepted one. Neither the posture nor the evidence produces
an acceptance. -/
theorem Action.outcome_accepted (action : Action) (sitting : Bool) (reply : Reply)
    (shown : Bool) :
    (action.outcome sitting reply shown ≠ .refused ∧
        action.outcome sitting reply shown ≠ .unanswered) ↔ reply = .accepted := by
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> decide

/-- **The outcome is a refusal exactly for a refused answer, and unanswered exactly for a
pending one.** For every action, stated posture, answer and evidence. -/
theorem Action.outcome_reply (action : Action) (sitting : Bool) (reply : Reply)
    (shown : Bool) :
    (action.outcome sitting reply shown = .refused ↔ reply = .refused) ∧
      (action.outcome sitting reply shown = .unanswered ↔ reply = .pending) := by
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> decide

/-- **The outcome of a release reads that release's commands.** For every release,
answer, evidence and outcome: the outcome of the state of a release is the one the
specification gives for the action and the posture of that same release. -/
theorem Bridge.release_outcome (index : Nat) (now : Instant) (sitting : Bool)
    (action : Action) (reply : Reply) (shown : Bool) (outcome : Outcome) :
    (Bridge.release index now sitting action).1.outcome reply shown = outcome ↔
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
