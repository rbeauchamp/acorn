import Acorn.Timing

namespace Acorn.Host.Microduck

inductive Velocity where
  | zero
  | forward
  | left
  | right
  deriving DecidableEq

structure Twist where
  forward : Int
  left : Int
  turn : Int
  deriving DecidableEq

def Velocity.twist : Velocity → Twist
  | .zero => ⟨0, 0, 0⟩
  | .forward => ⟨300, 0, 0⟩
  | .left => ⟨0, 0, 1500⟩
  | .right => ⟨0, 0, -1500⟩

theorem Velocity.twist_zero (velocity : Velocity) :
    velocity.twist = ⟨0, 0, 0⟩ ↔ velocity = .zero := by
  cases velocity <;> decide

inductive Skill where
  | groundPick
  | sitToggle
  | roulade
  | kickLeft
  | kickRight
  deriving DecidableEq

inductive Command where
  | enable
  | move (velocity : Velocity)
  | perform (skill : Skill)
  deriving DecidableEq

inductive Action where
  | still
  | forward
  | turnLeft
  | turnRight
  | sit
  | stand
  | kickLeft
  | kickRight
  | pick
  | roll
  deriving DecidableEq

def Action.index : Action → Fin 10
  | .still => 0
  | .forward => 1
  | .turnLeft => 2
  | .turnRight => 3
  | .sit => 4
  | .stand => 5
  | .kickLeft => 6
  | .kickRight => 7
  | .pick => 8
  | .roll => 9

def Action.named : Fin 10 → Action
  | 0 => .still
  | 1 => .forward
  | 2 => .turnLeft
  | 3 => .turnRight
  | 4 => .sit
  | 5 => .stand
  | 6 => .kickLeft
  | 7 => .kickRight
  | 8 => .pick
  | 9 => .roll

theorem Action.named_index (action : Action) : Action.named action.index = action := by
  cases action <;> rfl

theorem Action.index_named : ∀ position : Fin 10, (Action.named position).index = position := by
  decide

inductive Intent where
  | velocity (velocity : Velocity)
  | skill (skill : Skill)
  | posture (sitting : Bool)
  deriving DecidableEq

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

def Action.velocity (action : Action) : Velocity :=
  match action.intent with
  | .velocity velocity => velocity
  | .skill _ | .posture _ => .zero

def Action.commands (action : Action) (sitting : Bool) : List Command :=
  match action.intent with
  | .velocity velocity => [.move velocity]
  | .skill skill => [.move .zero, .perform skill]
  | .posture wanted =>
    if wanted = sitting then [.move .zero] else [.move .zero, .perform .sitToggle]

theorem Action.commands_head (action : Action) (sitting : Bool) :
    (action.commands sitting).head? = some (.move action.velocity) := by
  cases action <;> cases sitting <;> rfl

theorem Action.commands_powered (action : Action) (sitting : Bool) :
    Command.enable ∉ action.commands sitting := by
  cases action <;> cases sitting <;> decide

theorem Action.commands_toggle (action : Action) (sitting : Bool) :
    Command.perform .sitToggle ∈ action.commands sitting ↔
      action.intent = .posture (!sitting) := by
  cases action <;> cases sitting <;> decide

def Action.duration : Action → Nat
  | .still | .forward | .turnLeft | .turnRight => 0
  | .kickLeft | .kickRight => 600000000
  | .sit | .stand => 1200000000
  | .roll => 1400000000
  | .pick => 3000000000

def Action.next (action : Action) (pace : Pace) (transit : Nat) (origin : Instant)
    (index : Nat) (released : Instant) : Nat :=
  max (index + 1)
    (pace.first origin ⟨released.nanoseconds + action.duration + transit⟩)

theorem Action.next_after (action : Action) (pace : Pace) (transit : Nat) (origin : Instant)
    (index : Nat) (released : Instant) :
    index < action.next pace transit origin index released :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self index) (Nat.le_max_left _ _)

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

theorem Action.next_least (action : Action) (pace : Pace) (transit : Nat) (origin : Instant)
    (index : Nat) (released : Instant) (later : Nat) (after : index < later)
    (covers : released.nanoseconds + action.duration + transit ≤
      (pace.boundary origin later).nanoseconds) :
    action.next pace transit origin index released ≤ later :=
  Nat.max_le.mpr ⟨after, pace.first_least origin
    ⟨released.nanoseconds + action.duration + transit⟩ later covers⟩

end Acorn.Host.Microduck
