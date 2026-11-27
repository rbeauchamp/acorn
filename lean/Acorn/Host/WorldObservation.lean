import Acorn.Host.WorldDynamics
import Init.Data.Vector.OfFn

namespace Acorn.Host

abbrev Occupancy := Std.TreeMap (Int × Int) (Bool × Bool) (lexOrd : Ord (Int × Int)).compare

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

def World.observeTile {config : WorldConfig} (world : World config) (occupied : Occupancy)
    (row column : Fin patchSide) : Except WorldError TileObservation := do
  let radius := patchSide / 2
  let some position := world.body.position.position.translate
    ((column.val : Int) - radius) ((row.val : Int) - radius) | .error .coordinateOverflow
  let kind ← world.tileKind position
  let (food, deer) := occupied[(position.x.val, position.y.val)]?.getD (false, false)
  return ⟨kind.code, if food then 1 else 0, if deer then 1 else 0⟩

def World.observe {config : WorldConfig} (world : World config) : Except WorldError Observation := do
  let occupied := world.occupancy
  let tiles ← Vector.ofFnM (fun row => Vector.ofFnM (world.observeTile occupied row))
  return ⟨tiles, (min (world.body.energy.val / 100) 10).toUInt8,
    world.dayPhase.val.toUInt8, world.taskObservation, world.body.inventory⟩

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
