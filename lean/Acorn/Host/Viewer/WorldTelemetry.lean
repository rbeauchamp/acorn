/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Attempt
import Acorn.Host.Viewer.TelemetryValue

/-!
# World telemetry from the actual capture

Configuration, original task, body, sensor patch and preceding result belong
to the immutable frame captured by the runner. No telemetry function regenerates
terrain, reconstructs a target from a remaining quantity, or advances the world.
-/
namespace Acorn.Host.Viewer

/-- Closed facing-to-wire index mapping. -/
def directionCode : Direction → Nat
  | .north => 0 | .south => 1 | .east => 2 | .west => 3

/-- Independent event bits preserve every combination of public raw event fields. -/
def eventCode (events : StepResult) : Nat :=
  (if events.harvested.isSome then 1 else 0) + (if events.ate then 2 else 0) +
  (if events.crafted.isSome then 4 else 0) + (if events.pickedFood > 0 then 8 else 0) +
  (if events.exhausted then 16 else 0) + (if events.moved then 32 else 0)

/-- Original task arguments determine the exact wire descriptor. -/
def goalTelemetry (goal : Option Goal) : GoalKind × GoalItem × Int × Int × Nat :=
  match goal with
  | none => (none, none, 0, 0, 0)
  | some (.reach target) => (some .reach, none, target.x.val, target.y.val, 0)
  | some (.collect item count) => (some .collect, some (.inl item), 0, 0, count.toNat)
  | some (.craft tool) => (some .craft, some (.inr tool), 0, 0, 0)
  | some (.survive count) => (some .survive, none, 0, 0, count.toNat)

/-- The actual emitted goal tags are admitted for every original task, including
absence and every craftable. Other numeric fields retain their own wire limits. -/
theorem goalTelemetry_admitted (goal : Option Goal) :
    (goalTelemetry goal).1.code ∈ goalKindCodes ∧
      (goalTelemetry goal).2.1.code ∈ goalItemCodes :=
  ⟨goalKind_admitted _, goalItem_admitted _⟩

/-- Decoding both emitted semantic tags preserves their exact meaning. -/
theorem goalTelemetry_meaning (goal : Option Goal) :
    decodeGoalKind (goalTelemetry goal).1.code = some (goalTelemetry goal).1 ∧
      decodeGoalItem (goalTelemetry goal).2.1.code = some (goalTelemetry goal).2.1 :=
  ⟨goalKind_roundtrip _, goalItem_roundtrip _⟩

/-- The family on the wire is derived from the original goal constructor. -/
theorem goalTelemetry_family (goal : Option Goal) :
    (goalTelemetry goal).1 = goal.map Goal.family := by
  cases goal with
  | none => rfl
  | some goal => cases goal <;> rfl

/-- Canonical row-major flattening derives its dimensions from the sensor vectors. -/
def observationVector (observation : Observation) (read : TileObservation → Nat) :
    Vector Nat (patchShape.side * patchShape.side) :=
  Vector.ofFn fun index =>
    let row : Fin patchShape.side := ⟨index.val / patchShape.side,
      Nat.div_lt_of_lt_mul index.isLt⟩
    let col : Fin patchShape.side := ⟨index.val % patchShape.side,
      Nat.mod_lt _ (by decide)⟩
    read ((observation.tiles.get row).get col)

/-- Emit the complete world-facing portion of the protocol from one actual frame. -/
def worldTelemetry {β : Type} (frame : StepFrame β) (terminal : Bool) : List TelemetryField :=
  let config := frame.worldConfig.raw
  let (kind, item, gx, gy, quantity) := goalTelemetry frame.task
  [⟨"world_step", .natural, frame.worldTime.toNat⟩,
   ⟨"seed", .natural, config.seed.toNat⟩,
   ⟨"side", .natural, frame.worldConfig.side⟩,
   ⟨"day_length", .natural, config.dayLength.toNat⟩,
   ⟨"regrow", .natural, config.regrow.toNat⟩,
   ⟨"food_interval", .natural, config.foodInterval.toNat⟩,
   ⟨"food_cap", .natural, config.foodCap.toNat⟩,
   ⟨"deer_cap", .natural, config.deerCap.toNat⟩,
   ⟨"x", .integer, frame.position.x.val⟩,
   ⟨"y", .integer, frame.position.y.val⟩,
   ⟨"facing", .natural, directionCode frame.facing⟩,
   ⟨"energy", .natural, frame.energy.val⟩,
   ⟨"wood", .natural, frame.inventory.wood.toNat⟩,
   ⟨"stone", .natural, frame.inventory.stone.toNat⟩,
   ⟨"food", .natural, frame.inventory.food.toNat⟩,
   ⟨"gold", .natural, frame.inventory.gold.toNat⟩,
   ⟨"axe", .flag, frame.inventory.axe⟩,
   ⟨"boat", .flag, frame.inventory.boat⟩,
   ⟨"action", .natural, frame.action.index.val⟩,
   ⟨"reward", .binary32, frame.result.reward⟩,
   ⟨"done", .flag, frame.result.events.done⟩,
   ⟨"ev", .natural, eventCode frame.result.events⟩,
   ⟨"goal", .natural, frame.goal.index.toNat⟩,
   ⟨"attempt", .natural, frame.goal.attempt.toNat⟩,
   ⟨"tier", .natural, frame.goal.tier.toNat⟩,
   ⟨"cycle", .natural, frame.goal.cycle.toNat⟩,
   ⟨"gkind", .goalKind, kind⟩,
   ⟨"gitem", .goalItem, item⟩,
   ⟨"gx", .integer, gx⟩,
   ⟨"gy", .integer, gy⟩,
   ⟨"gn", .natural, quantity⟩,
   ⟨"tiles", .array (patchShape.side * patchShape.side) .natural,
      observationVector frame.observation (·.kind.toNat)⟩,
   ⟨"tile_extra", .array (patchShape.side * patchShape.side) .natural,
      observationVector frame.observation (fun tile => tile.food.toNat + 2 * tile.deer.toNat)⟩,
   ⟨"end", .flag, terminal⟩]

/-- Facing serialization inverts the host's closed direction constructor. -/
theorem directionCode_roundtrip (direction : Direction) :
    Direction.fromIndex ⟨directionCode direction, by cases direction <;> decide⟩ = direction := by
  cases direction <;> rfl

/-- The original collect target is preserved even after inventory exceeds it. -/
theorem goalTelemetry_collect (item : Item) (count : UInt32) :
    goalTelemetry (some (.collect item count)) = (some .collect, some (.inl item), 0, 0, count.toNat) := rfl

end Acorn.Host.Viewer
