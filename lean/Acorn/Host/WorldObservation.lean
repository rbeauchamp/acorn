/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldDynamics
import Init.Data.Vector.OfFn

/-!
# Current one-way world observation

Occupancy is indexed once, with duplicate entities coalesced into presence
bits. Observation performs no RNG draw or world mutation. The host retains
its raw public observation type, while this constructor supplies legal terrain,
occupancy, energy and day channels and the same task relation used for reward.
-/
namespace Acorn.Host

/-- Coordinate-keyed presence bits; this index is temporary observation storage. -/
abbrev Occupancy := Std.TreeMap (Int × Int) (Bool × Bool) (lexOrd : Ord (Int × Int)).compare

/-- Index food first and deer second without losing either presence bit. -/
def World.occupancy {config : WorldConfig} (world : World config) : Occupancy := Id.run do
  let mut occupied : Occupancy := ∅
  for food in world.food.entries do
    let position := food.position
    let key := (position.x.val, position.y.val)
    let old := occupied[key]?.getD (false, false)
    occupied := occupied.insert key (true, old.2)
  for deer in world.deer.entries do
    let key := (deer.x.val, deer.y.val)
    let old := occupied[key]?.getD (false, false)
    occupied := occupied.insert key (old.1, true)
  return occupied

/-- The actual row-major tile observation with checked signed coordinate offsets. -/
def World.observeTile {config : WorldConfig} (world : World config) (occupied : Occupancy)
    (row column : Fin patchShape.side) : Except WorldError TileObservation := do
  let radius := patchShape.side / 2
  let some position := world.body.position.position.translate
    ((column.val : Int) - radius) ((row.val : Int) - radius) | .error .coordinateOverflow
  let kind ← world.tileKind position
  let (food, deer) := occupied[(position.x.val, position.y.val)]?.getD (false, false)
  return ⟨kind.code, if food then 1 else 0, if deer then 1 else 0⟩

/-- Complete host observation; coordinates at a signed boundary may explicitly refuse. -/
def World.observe {config : WorldConfig} (world : World config) : Except WorldError Observation := do
  let occupied := world.occupancy
  let tiles ← Vector.ofFnM (fun row => Vector.ofFnM (world.observeTile occupied row))
  return ⟨tiles, (min (world.body.energy.val / 100) 10).toUInt8,
    world.dayPhase.val.toUInt8, world.taskObservation, world.body.inventory⟩

/-- Observation's declared task relation is exactly the reward predicate's input. -/
theorem World.observe_task {config : WorldConfig} (world : World config) (observation : Observation)
    (h : world.observe = .ok observation) : observation.task = world.taskObservation := by
  unfold observe at h
  cases ht : Vector.ofFnM (fun row => Vector.ofFnM (world.observeTile world.occupancy row)) with
  | error error => simp [ht, bind, Except.bind] at h
  | ok tiles =>
    simp only [ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    cases h
    rfl

end Acorn.Host
