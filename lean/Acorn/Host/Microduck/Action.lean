/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Timing

/-!
# The Microduck's actions

The Microduck is a small biped whose control daemon takes intents from a client and
never a joint command: a velocity, or a skill by name. Networks inside the daemon
execute them. This module is the agent's side of that boundary, as a closed table: ten
actions, the intent of each, the commands a release sends and the number of cycles an
action lasts.

The magnitudes and the durations are declared from one observed run of the vendor's
simulator, whose record of commands, skills and timing is at
https://github.com/rbeauchamp/acorn/issues/95#issuecomment-6046235895. In that run
forward at 0.3 m/s and turns at 1.5 rad/s moved the body, and smaller and backward
commands did not; the kicks ran for 0.5 s, the forward roll and standing up for 1.0 s,
and the pick for 2.8 s. The declared durations add a margin to those. How long sitting
down takes is UNKNOWN: that run recorded the label of the sitting network and not the
time the body took to rest, so `sit` is declared with the duration of `stand`. The run
used the networks that the vendor's simulator script loads; a robot can load others, so
whether these magnitudes move a robot is UNKNOWN.

`Command` is everything a bridge can send to the daemon: enable the policy, one of four
velocities, one of five skills. It is a closed finite type. It has no constructor for
cutting power, shutting down or rebooting, and `Command.enable` takes no argument, so
no value asks to disable the policy; a velocity is one of the table's four, so no value
carries another magnitude. This module gives no wire form: the function that renders a
command, which is not built, owes the method and the parameters of each constructor.
The release of an action sends velocities and skills only (`Action.commands_powered`),
so the enable command is the bridge's own.

Every release sends a velocity first (`Action.commands_head`): a skill and a posture are
released with the zero velocity, so that no earlier velocity is in force when they end.
The daemon exposes sitting and standing as one toggle. `sit` and `stand` are two
actions, and `Action.commands` takes the posture of the body as its caller states it:
the toggle is sent exactly when the action asks for the other posture
(`Action.commands_toggle`). That the stated posture is the body's is the caller's
obligation; a wrong one sends the toggle the wrong way.

The cycle of the percept after an action is computed from the instant of the action's
release, whether the release was timely or late: `Action.next` is the first cycle that
starts no earlier than the release plus the action's declared duration and a transit
allowance, and it is after the action's own cycle. So the start of that cycle is never
inside the declared duration of the action (`Action.next_covers`, which has no
hypothesis on the release), and no earlier cycle after the action's own has that
property (`Action.next_least`). A host owes that it senses the next percept at that
cycle and no earlier; this module states the cycle and not what a host does.
-/
namespace Acorn.Host.Microduck

/-- The velocities of the table. -/
inductive Velocity where
  /-- Stand still. -/
  | zero
  /-- Walk forward. -/
  | forward
  /-- Turn to the left in place. -/
  | left
  /-- Turn to the right in place. -/
  | right
  deriving DecidableEq

/-- The magnitudes of a velocity in thousandths: of a metre per second forward and to
the left, and of a radian per second to the left. They are integers, so the table
declares no float. -/
structure Twist where
  /-- Forward speed, in thousandths of a metre per second. -/
  forward : Int
  /-- Speed to the left, in thousandths of a metre per second. -/
  left : Int
  /-- Turning rate to the left, in thousandths of a radian per second. -/
  turn : Int
  deriving DecidableEq

/-- The magnitudes of each velocity: 0.3 m/s forward, and 1.5 rad/s to each side. Only
`Velocity.zero` has no magnitude (`Velocity.twist_zero`). -/
def Velocity.twist : Velocity → Twist
  | .zero => ⟨0, 0, 0⟩
  | .forward => ⟨300, 0, 0⟩
  | .left => ⟨0, 0, 1500⟩
  | .right => ⟨0, 0, -1500⟩

/-- A velocity has the zero magnitudes exactly when it is `Velocity.zero`. -/
theorem Velocity.twist_zero (velocity : Velocity) :
    velocity.twist = ⟨0, 0, 0⟩ ↔ velocity = .zero := by
  cases velocity <;> decide

/-- A skill of the daemon. -/
inductive Skill where
  /-- Pick from the ground. -/
  | groundPick
  /-- Sit when standing, and stand when sitting. -/
  | sitToggle
  /-- Forward roll. -/
  | roulade
  /-- Kick with the left foot. -/
  | kickLeft
  /-- Kick with the right foot. -/
  | kickRight
  deriving DecidableEq

/-- Everything a bridge can send to the control daemon. -/
inductive Command where
  /-- Enable the policy. -/
  | enable
  /-- A velocity intent. -/
  | move (velocity : Velocity)
  /-- A skill. -/
  | perform (skill : Skill)
  deriving DecidableEq

/-- The agent's actions. -/
inductive Action where
  /-- Zero velocity. -/
  | still
  /-- Walk forward. -/
  | forward
  /-- Turn to the left in place. -/
  | turnLeft
  /-- Turn to the right in place. -/
  | turnRight
  /-- Sit down. -/
  | sit
  /-- Stand up from sitting. -/
  | stand
  /-- Kick with the left foot. -/
  | kickLeft
  /-- Kick with the right foot. -/
  | kickRight
  /-- Pick from the ground. -/
  | pick
  /-- Forward roll. -/
  | roll
  deriving DecidableEq

/-- What an action asks of the body. -/
inductive Intent where
  /-- A velocity, which the daemon lets expire. -/
  | velocity (velocity : Velocity)
  /-- A skill of fixed length, which the daemon does not interrupt. -/
  | skill (skill : Skill)
  /-- A posture: sitting, or standing. -/
  | posture (sitting : Bool)
  deriving DecidableEq

/-- The intent of each action. -/
def Action.intent : Action → Intent
  | .still => .velocity .zero
  | .forward => .velocity .forward
  | .turnLeft => .velocity .left
  | .turnRight => .velocity .right
  | .sit => .posture true
  | .stand => .posture false
  | .kickLeft => .skill .kickLeft
  | .kickRight => .skill .kickRight
  | .pick => .skill .groundPick
  | .roll => .skill .roulade

/-- The velocity in force after an action is released: its own for a velocity, and zero
for a skill or a posture. -/
def Action.velocity (action : Action) : Velocity :=
  match action.intent with
  | .velocity velocity => velocity
  | .skill _ | .posture _ => .zero

/-- The commands of releasing an action, for the posture of the body as the caller
states it. -/
def Action.commands (action : Action) (sitting : Bool) : List Command :=
  match action.intent with
  | .velocity velocity => [.move velocity]
  | .skill skill => [.move .zero, .perform skill]
  | .posture wanted =>
    if wanted = sitting then [.move .zero] else [.move .zero, .perform .sitToggle]

/-- **Every release sends its velocity first.** For every action and stated posture, the
first command of a release is the velocity that is in force after it. -/
theorem Action.commands_head (action : Action) (sitting : Bool) :
    (action.commands sitting).head? = some (.move action.velocity) := by
  cases action <;> cases sitting <;> rfl

/-- **A release sends velocities and skills only.** No action, for no stated posture,
sends the enable command. -/
theorem Action.commands_powered (action : Action) (sitting : Bool) :
    Command.enable ∉ action.commands sitting := by
  cases action <;> cases sitting <;> decide

/-- **The toggle is sent exactly for the other posture.** For every action and stated
posture, a release sends the sitting toggle exactly when the action asks for the posture
that is not the stated one. So no skill action sends the toggle. -/
theorem Action.commands_toggle (action : Action) (sitting : Bool) :
    Command.perform .sitToggle ∈ action.commands sitting ↔
      action.intent = .posture (!sitting) := by
  cases action <;> cases sitting <;> decide

/-- Nanoseconds the body takes for an action, as declared: zero for a velocity. -/
def Action.duration : Action → Nat
  | .still | .forward | .turnLeft | .turnRight => 0
  | .kickLeft | .kickRight => 600000000
  | .sit | .stand => 1200000000
  | .roll => 1400000000
  | .pick => 3000000000

/-- The cycle of the percept after an action, from the instant the action is released
at: the first cycle that starts no earlier than the release plus the action's declared
duration and the transit allowance, and after the cycle of the action's own percept. -/
def Action.next (action : Action) (pace : Pace) (transit : Nat) (origin : Instant)
    (index : Nat) (released : Instant) : Nat :=
  max (index + 1)
    (pace.first origin ⟨released.nanoseconds + action.duration + transit⟩)

/-- The percept after an action is of a later cycle than the action's own. -/
theorem Action.next_after (action : Action) (pace : Pace) (transit : Nat) (origin : Instant)
    (index : Nat) (released : Instant) :
    index < action.next pace transit origin index released :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self index) (Nat.le_max_left _ _)

/-- **The next percept's cycle starts after the declared duration, for every release.**
For every action, pace, transit allowance, origin, cycle and instant of release, timely
or late: the cycle of the next percept starts no earlier than the release plus the
action's declared duration and the transit allowance. -/
theorem Action.next_covers (action : Action) (pace : Pace) (transit : Nat) (origin : Instant)
    (index : Nat) (released : Instant) :
    released.nanoseconds + action.duration + transit ≤
      (pace.boundary origin (action.next pace transit origin index released)).nanoseconds := by
  have starts : released.nanoseconds + action.duration + transit ≤
      origin.nanoseconds +
        pace.first origin ⟨released.nanoseconds + action.duration + transit⟩ * pace.cycle :=
    pace.first_starts origin ⟨released.nanoseconds + action.duration + transit⟩
  have later : pace.first origin ⟨released.nanoseconds + action.duration + transit⟩ ≤
      action.next pace transit origin index released := Nat.le_max_right _ _
  have grows := Nat.mul_le_mul_right pace.cycle later
  rw [pace.boundary_nanoseconds]
  omega

/-- **No earlier cycle would do.** For every later cycle than the action's own that starts
no earlier than the release plus the declared duration and the transit allowance, the
cycle of the next percept is not later. -/
theorem Action.next_least (action : Action) (pace : Pace) (transit : Nat) (origin : Instant)
    (index : Nat) (released : Instant) (later : Nat) (after : index < later)
    (covers : released.nanoseconds + action.duration + transit ≤
      (pace.boundary origin later).nanoseconds) :
    action.next pace transit origin index released ≤ later :=
  Nat.max_le.mpr ⟨after, pace.first_least origin
    ⟨released.nanoseconds + action.duration + transit⟩ later covers⟩

end Acorn.Host.Microduck
