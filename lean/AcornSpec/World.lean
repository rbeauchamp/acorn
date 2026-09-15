/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Std.Data.HashMap
import AcornSpec.Rng
import AcornSpec.WorldSchema
import AcornSpec.Float

/-!
# Executable specification: the big world

Mirrors `src/world.rs` construct by construct: the pure terrain function
(`TileKind::at` and its noise stack), the agent body, energy, inventory,
goals and their exact relations, the observation, and the step/advance
dynamics.

Two representation choices that change nothing observable:

- **Terrain tabulation.** `TileKind::at` is pure, so the world precomputes a
  `(side + 2·margin)²` table of base tile kinds at construction and reads it
  for in-range queries, falling back to the function itself outside — a memo
  of a pure function is that function.
- **Packed entity coordinates.** Deer and food positions are `(i32, i32)`
  pairs packed into one `u64` word; every coordinate the dynamics can reach
  is far inside `i32`.

The harvest log is a hash map used only through `get`/`insert` (never
iterated), exactly like the Rust `HashMap`, so its internal order is
unobservable.
-/

namespace AcornSpec

open AcornSpec.Constants

/-! ## Directions, actions, items -/

/-- `world::Dir`. -/
inductive Dir where
  /-- North (−y). -/
  | north
  /-- South (+y). -/
  | south
  /-- East (+x). -/
  | east
  /-- West (−x). -/
  | west
  deriving DecidableEq, Repr

/-- `Dir::delta`. -/
@[inline]
def Dir.delta : Dir → Int × Int
  | .north => (0, -1)
  | .south => (0, 1)
  | .east => (1, 0)
  | .west => (-1, 0)

/-- `Dir::ALL` order, indexed — the form `advance_world`'s deer draw uses. -/
@[inline]
def Dir.ofIndex (i : UInt64) : Dir :=
  match i with
  | 0 => .north
  | 1 => .south
  | 2 => .east
  | _ => .west

/-- `world::Action` — the closed primitive action vocabulary. -/
inductive Action where
  /-- Step north. -/
  | north
  /-- Step south. -/
  | south
  /-- Step east. -/
  | east
  /-- Step west. -/
  | west
  /-- Do nothing. -/
  | wait
  /-- Harvest the tile in front. -/
  | harvest
  /-- Craft an axe. -/
  | craftAxe
  /-- Craft a boat. -/
  | craftBoat
  /-- Eat one food item. -/
  | eat
  deriving DecidableEq, Repr

/-- `Action::index` — the canonical index (0..9). -/
@[inline]
def Action.index : Action → Nat
  | .north => 0
  | .south => 1
  | .east => 2
  | .west => 3
  | .wait => 4
  | .harvest => 5
  | .craftAxe => 6
  | .craftBoat => 7
  | .eat => 8

/-- `Action::from_index` — total over every index. -/
@[inline]
def Action.fromIndex (i : Nat) : Action :=
  match i with
  | 0 => .north
  | 1 => .south
  | 2 => .east
  | 3 => .west
  | 4 => .wait
  | 5 => .harvest
  | 6 => .craftAxe
  | 7 => .craftBoat
  | _ => .eat

/-- `Action::as_dir`. -/
@[inline]
def Action.asDir : Action → Option Dir
  | .north => some .north
  | .south => some .south
  | .east => some .east
  | .west => some .west
  | _ => none

/-- `Action::energy_cost` at day/night multiplier `mult`. -/
@[inline]
def Action.energyCost (a : Action) (mult : UInt32) : UInt32 :=
  match a with
  | .harvest => 2 * mult
  | _ => mult

/-- `ItemKind::code`. -/
@[inline]
def ItemKind.code : ItemKind → UInt64
  | .wood => 1
  | .stone => 2
  | .food => 3
  | .gold => 4

/-- `Craftable::code`. -/
@[inline]
def Craftable.code : Craftable → UInt64
  | .axe => 11
  | .boat => 12

/-! ## Terrain -/

/-- `world::TileKind` — the closed tile vocabulary. -/
inductive TileKind where
  /-- Impassable water (passable with a boat). -/
  | water
  /-- Beach sand. -/
  | sand
  /-- Plain grass. -/
  | grass
  /-- Wooded ground without a standing tree. -/
  | forest
  /-- A harvestable tree. -/
  | tree
  /-- Impassable mountain. -/
  | mountain
  /-- Harvestable rock. -/
  | stone
  /-- Harvestable ore. -/
  | ore
  deriving DecidableEq, Repr

/-- `TileKind::code` — the stable byte code. -/
@[inline]
def TileKind.code : TileKind → UInt8
  | .water => 0
  | .sand => 1
  | .grass => 2
  | .forest => 3
  | .tree => 4
  | .mountain => 5
  | .stone => 6
  | .ore => 7

/-- `TileKind::from_code` — total inverse over all bytes. -/
@[inline]
def TileKind.fromCode (code : UInt8) : TileKind :=
  match code with
  | 0 => .water
  | 1 => .sand
  | 2 => .grass
  | 3 => .forest
  | 4 => .tree
  | 5 => .mountain
  | 6 => .stone
  | _ => .ore

/-- `TileKind::walkable`. -/
@[inline]
def TileKind.walkable : TileKind → Bool
  | .water | .mountain => false
  | _ => true

/-- `TileKind::harvest_yield`. -/
@[inline]
def TileKind.harvestYield : TileKind → Option ItemKind
  | .tree => some .wood
  | .stone => some .stone
  | .ore => some .gold
  | _ => none

/-- `TileKind::smooth` — smoothstep, the only nonlinearity in the terrain. -/
@[inline]
def smooth (t : Float32) : Float32 :=
  t * t * (natF32 3 - natF32 2 * t)

/-- `TileKind::lattice` — value noise at integer lattice points. The scale
constant is the Rust expression `1.0 / 4_294_967_296.0`, an exact `f32`. -/
@[inline]
def lattice (x y : Int) (seed : UInt64) : Float32 :=
  let h := hash2 (i64bits x) (i64bits y) seed
  UInt64.toFloat32 (h >>> 32) * (natF32 1 / UInt64.toFloat32 4294967296)

/-- `TileKind::value_noise` — bilinear smoothstep blend of lattice noise. -/
def valueNoise (x y : Int) (scale : Float32) (seed : UInt64) : Float32 :=
  let fx := i64ToF32 x / scale
  let fy := i64ToF32 y / scale
  let x0 := floor32 fx
  let y0 := floor32 fy
  let tx := smooth (fx - x0)
  let ty := smooth (fy - y0)
  let xi := rustF32toI64 x0
  let yi := rustF32toI64 y0
  let h00 := lattice xi yi seed
  let h10 := lattice (xi + 1) yi seed
  let h01 := lattice xi (yi + 1) seed
  let h11 := lattice (xi + 1) (yi + 1) seed
  let top := h00 + (h10 - h00) * tx
  let bot := h01 + (h11 - h01) * tx
  top + (bot - top) * ty

/-- `TileKind::fbm` — four-octave value noise. The loop is unrolled to the
same four accumulations the Rust `for _ in 0..4` performs, in order. -/
def fbm (x y : Int) (seed : UInt64) (baseScale : Float32) : Float32 :=
  let half := Float32.ofBits 0x3F000000
  let two := natF32 2
  let sum := f32zero
  let amp := half
  let scale := baseScale
  let sum := sum + amp * valueNoise x y scale seed
  let amp := amp * half
  let scale := scale * two
  let sum := sum + amp * valueNoise x y scale seed
  let amp := amp * half
  let scale := scale * two
  let sum := sum + amp * valueNoise x y scale seed
  let amp := amp * half
  let scale := scale * two
  let sum := sum + amp * valueNoise x y scale seed
  sum

/-- `TileKind::at` — the tile kind at world coordinates, for a seed and base
noise scale. Pure and total; the definitional terrain of the specified
system. -/
def tileAt (x y : Int) (seed : UInt64) (baseScale : Float32) : TileKind :=
  let elev := fbm x y (seed ^^^ 0xE1E0E1E000000001) baseScale
  let moist := fbm x y (seed ^^^ 0xE1E0E1E000000002) baseScale
  if elev < Float32.ofBits band030Bits then .water
  else if elev < Float32.ofBits band0335Bits then .sand
  else if elev < Float32.ofBits band060Bits then .grass
  else if elev < Float32.ofBits band072Bits then
    if Float32.ofBits moist040Bits < moist
        && hash2 (i64bits x) (i64bits y) (seed ^^^ 0x0000000000000007) % 100 < 60 then
      .tree
    else .forest
  else if elev < Float32.ofBits band080Bits then
    if hash2 (i64bits x) (i64bits y) (seed ^^^ 0x0000000000000009) % 100 < 10 then .ore
    else .stone
  else .mountain

/-! ## Goals and their exact relations -/

/-- `Goal::REACH_RADIUS`. -/
def reachRadius : UInt64 := 3

/-- `Goal::cue` — the stable cue word for the featurizer. -/
def GoalKind.cue : GoalKind → UInt64
  | .reach x y => hash3 1 (i64bits x) (i64bits y)
  | .collect item n => hash3 2 item.code n.toUInt64
  | .craft c => hash3 3 c.code 0
  | .survive steps => hash3 4 steps 0

/-- `world::ReachRelation` — exact signed displacement (`i128` in Rust, exact
`Int` here) plus the derived region distance and scale. -/
structure ReachRel where
  /-- Signed x displacement. -/
  dx : Int
  /-- Signed y displacement. -/
  dy : Int
  /-- Chebyshev distance to the rewarded region (saturating at zero). -/
  distanceToRegion : UInt64
  /-- Logarithmic distance level (bit width of the distance). -/
  distanceScale : UInt8

/-- `ReachRelation::between`. -/
def ReachRel.between (px py tx ty : Int) : ReachRel :=
  let dx := tx - px
  let dy := ty - py
  let ax := dx.natAbs
  let ay := dy.natAbs
  let chebyshev := if ax > ay then ax else ay
  let dtr : Nat := chebyshev - reachRadius.toNat
  let scale : UInt8 := if dtr == 0 then 0 else (Nat.log2 dtr + 1).toUInt8
  { dx, dy, distanceToRegion := dtr.toUInt64, distanceScale := scale }

/-- `world::TaskObservation` — agent-visible task semantics. -/
inductive TaskObs where
  /-- No installed task. -/
  | none
  /-- Coordinate goal. -/
  | reach (cue : UInt64) (rel : ReachRel)
  /-- Inventory-count goal: item and saturating remaining count. -/
  | collect (cue : UInt64) (item : ItemKind) (remaining : UInt32)
  /-- Crafting goal: tool and whether it is still required. -/
  | craft (cue : UInt64) (c : Craftable) (remaining : Bool)
  /-- Survival goal: saturating remaining steps. -/
  | survive (cue : UInt64) (remaining : UInt64)

/-- `TaskObservation::cue`. -/
@[inline]
def TaskObs.cueOf : TaskObs → UInt64
  | .none => 0
  | .reach cue _ => cue
  | .collect cue _ _ => cue
  | .craft cue _ _ => cue
  | .survive cue _ => cue

/-- `TaskObservation::is_satisfied`. -/
@[inline]
def TaskObs.isSatisfied : TaskObs → Bool
  | .none => false
  | .reach _ rel => rel.distanceToRegion == 0
  | .collect _ _ remaining => remaining == 0
  | .craft _ _ remaining => !remaining
  | .survive _ remaining => remaining == 0

/-! ## Observation and step result -/

/-- One observed tile, packed: kind code in bits 0–2, food flag bit 3, deer
flag bit 4 — a bounded snapshot equal in content to Rust's `TileObs`. -/
abbrev PackedTile := UInt8

/-- `world::Observation` — the agent's view: an 11×11 window (row-major, the
Rust iteration order), proprioception, typed task semantics, and the
inventory snapshot. -/
structure Obs where
  /-- 121 packed tiles, row-major. -/
  tiles : ByteArray
  /-- Bucketed energy (0..=10). -/
  energyBucket : UInt8
  /-- Day phase (0..=7). -/
  dayPhase : UInt8
  /-- Task identity and relation. -/
  task : TaskObs
  /-- Inventory wood count. -/
  invWood : UInt32
  /-- Inventory stone count. -/
  invStone : UInt32
  /-- Inventory food count. -/
  invFood : UInt32
  /-- Inventory gold count. -/
  invGold : UInt32
  /-- Owns an axe. -/
  invAxe : Bool
  /-- Owns a boat. -/
  invBoat : Bool

/-- `world::StepResult` — what one world step produced. Only the fields the
study path consumes are carried (`moved`/`harvested`/`ate`/`crafted`/
`exhausted`/`picked_food` feed observers only). -/
structure StepRes where
  /-- Reward emitted this step (1.0 iff the goal was achieved). -/
  reward : Float32
  /-- True iff the current goal was achieved this step. -/
  done : Bool

/-- `StepResult::default()`. -/
def StepRes.default : StepRes := ⟨f32zero, false⟩

/-! ## The world -/

/-- Pack a coordinate pair into one word (each far inside `i32`). -/
@[inline]
def packXY (x y : Int) : UInt64 :=
  (((i64bits x).toUInt32.toUInt64) <<< 32) ||| ((i64bits y).toUInt32.toUInt64)

/-- Signed reading of a packed 32-bit half. -/
@[inline]
def i32AsInt (u : UInt32) : Int :=
  if u < 0x80000000 then (u.toNat : Int) else (u.toNat : Int) - 4294967296

/-- Unpack a coordinate pair. -/
@[inline]
def unpackXY (p : UInt64) : Int × Int :=
  (i32AsInt (p >>> 32).toUInt32, i32AsInt p.toUInt32)

/-- Terrain-table margin around the campaign box. Queries outside the padded
box fall back to `tileAt` itself, so the margin affects cost only. -/
def tableMargin : Int := 512

/-- Tail-recursive terrain-table fill: linear index `i` over the padded box,
row-major. -/
def World.buildTableGo (seed : UInt64) (baseScale : Float32) (tOrigin : Int)
    (tSide : Nat) (t : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => t
  | fuel + 1 =>
    let ix := i % tSide
    let iy := i / tSide
    let t := t.push (tileAt (tOrigin + (ix : Int)) (tOrigin + (iy : Int)) seed baseScale).code
    World.buildTableGo seed baseScale tOrigin tSide t (i + 1) fuel

/-- Build the padded terrain table. -/
def World.buildTable (seed : UInt64) (baseScale : Float32) (tOrigin : Int)
    (tSide : Nat) : ByteArray :=
  World.buildTableGo seed baseScale tOrigin tSide
    (ByteArray.emptyWithCapacity (tSide * tSide)) 0 (tSide * tSide)

/-- `world::World` — the complete world state. Constants that
`WorldConfig::new` fixes for every valid side (day length 2048, regrow 400,
food interval 48, food cap 600) are definitional here; the side-derived
fields are stored. -/
structure World where
  /-- Campaign seed. -/
  seed : UInt64
  /-- Side length of the campaign box. -/
  side : Int
  /-- Base noise cell size (`max(side/16, 8)` as f32). -/
  baseScale : Float32
  /-- Deer population target (`side²/512`). -/
  deerCap : UInt32
  /-- World time. -/
  time : UInt64
  /-- Agent x. -/
  bx : Int
  /-- Agent y. -/
  by' : Int
  /-- Agent facing. -/
  facing : Dir
  /-- Energy in units of 0.1, in `0..=2000` by construction. -/
  energy : UInt32
  /-- Wood held. -/
  invWood : UInt32
  /-- Stone held. -/
  invStone : UInt32
  /-- Food held. -/
  invFood : UInt32
  /-- Gold held. -/
  invGold : UInt32
  /-- Owns an axe. -/
  invAxe : Bool
  /-- Owns a boat. -/
  invBoat : Bool
  /-- Installed goal with its cue, if any. -/
  goal : Option (GoalKind × UInt64)
  /-- World time when the goal was installed. -/
  goalStart : UInt64
  /-- Harvest log: packed position → harvest time. Never iterated. -/
  harvested : Std.HashMap UInt64 UInt64
  /-- Deer positions (packed), in spawn order. -/
  deer : Array UInt64
  /-- Ground food positions (packed), in spawn order. -/
  food : Array UInt64
  /-- World dynamics RNG. -/
  rng : Xoshiro256
  /-- Origin (both axes) of the terrain table. -/
  tOrigin : Int
  /-- Side of the terrain table. -/
  tSide : Nat
  /-- Base terrain codes for the padded box. -/
  table : ByteArray

namespace World

/-- `WorldConfig` day length. -/
def dayLength : UInt64 := 2048
/-- `WorldConfig` tree regrow interval. -/
def regrow : UInt64 := 400
/-- `WorldConfig` food spawn interval. -/
def foodInterval : UInt64 := 48
/-- `WorldConfig` ground food cap. -/
def foodCap : Nat := 600
/-- `Energy::MAX`. -/
def energyMax : UInt32 := 2000
/-- `Energy::EAT_RESTORE`. -/
def eatRestore : UInt32 := 400
/-- `Energy::REST_RECOVER`. -/
def restRecover : UInt32 := 20

/-- The base terrain kind at `(x, y)` — table read inside the padded box,
`tileAt` itself outside. -/
@[inline]
def baseKind (w : World) (x y : Int) : TileKind :=
  if w.tOrigin ≤ x ∧ x < w.tOrigin + (w.tSide : Int) ∧
     w.tOrigin ≤ y ∧ y < w.tOrigin + (w.tSide : Int) then
    let ix := (x - w.tOrigin).toNat
    let iy := (y - w.tOrigin).toNat
    TileKind.fromCode (w.table.get! (iy * w.tSide + ix))
  else
    tileAt x y w.seed w.baseScale

/-- `World::tile_kind` — the base modulated by the harvest log. -/
@[inline]
def tileKind (w : World) (x y : Int) : TileKind :=
  let base := w.baseKind x y
  if base == .tree then
    match w.harvested[packXY x y]? with
    | some t => if w.time - t < regrow then .forest else base
    | none => base
  else base

/-- `World::enterable`. -/
@[inline]
def enterable (w : World) (x y : Int) : Bool :=
  match w.tileKind x y with
  | .water => w.invBoat
  | k => k.walkable

/-- `World::count_kind_near` — tiles of one kind within Chebyshev radius. -/
def countKindNear (w : World) (x y : Int) (r : Int) (kind : TileKind) : UInt32 :=
  let rr := r.toNat
  let span := 2 * rr + 1
  let rec
    /-- Column scan of one row. -/
    goX (yy : Int) (n : UInt32) : Nat → UInt32
      | 0 => n
      | k + 1 =>
        let dx : Int := (span - (k + 1) : Nat) - r
        let n := if w.tileKind (x + dx) yy == kind then n + 1 else n
        goX yy n k
  let rec
    /-- Row scan. -/
    goY (n : UInt32) : Nat → UInt32
      | 0 => n
      | k + 1 =>
        let dy : Int := (span - (k + 1) : Nat) - r
        goY (goX (y + dy) n span) k
  goY 0 span

/-- `World::day_phase`. -/
def dayPhase (w : World) : UInt8 :=
  let slot := w.time % dayLength
  let half := dayLength / 2
  let eighth := max (dayLength / 8) 1
  let phase := if slot < half then slot / eighth else 4 + (slot - half) / eighth
  (min phase 7).toUInt8

/-- `World::is_night`. -/
@[inline]
def isNight (w : World) : Bool := 4 ≤ w.dayPhase

/-- `World::energy_multiplier`. -/
@[inline]
def energyMultiplier (w : World) : UInt32 := if w.isNight then 2 else 1

/-- Inventory count of one item. -/
@[inline]
def invCount (w : World) (item : ItemKind) : UInt32 :=
  match item with
  | .wood => w.invWood
  | .stone => w.invStone
  | .food => w.invFood
  | .gold => w.invGold

/-- `World::task_observation` — the installed relation, derived from the
same state the reward predicate reads. -/
def taskObservation (w : World) : TaskObs :=
  match w.goal with
  | none => .none
  | some (kind, cue) =>
    match kind with
    | .reach x y => .reach cue (ReachRel.between w.bx w.by' x y)
    | .collect item n => .collect cue item (n - min n (w.invCount item))
    | .craft c =>
      let owned := match c with | .axe => w.invAxe | .boat => w.invBoat
      .craft cue c (!owned)
    | .survive steps => .survive cue (steps - min steps (w.time - w.goalStart))

/-- `World::goal_is_satisfied` (= the reward predicate `goal_achieved`). -/
@[inline]
def goalAchieved (w : World) : Bool := w.taskObservation.isSatisfied

/-- `World::set_goal`. -/
def setGoal (w : World) (kind : GoalKind) : World :=
  { w with goal := some (kind, kind.cue), goalStart := w.time }

/-- Tail-recursive window fill for `observe`: 121 terrain codes, row-major. -/
def windowGo (w : World) (x0 y0 : Int) (t : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => t
  | fuel + 1 =>
    let row := i / 11
    let col := i % 11
    let t := t.push (w.tileKind (x0 + (col : Int)) (y0 + (row : Int))).code
    windowGo w x0 y0 t (i + 1) fuel

/-- Tail-recursive occupancy stamp for `observe`: set `bit` on the window
cell of every entity inside it — extensionally the Rust occupancy map's
content. -/
def stampGo (x0 y0 : Int) (arr : Array UInt64) (bit : UInt8) (t : ByteArray)
    (i : Nat) : Nat → ByteArray
  | 0 => t
  | fuel + 1 =>
    let (fx, fy) := unpackXY arr[i]!
    let t :=
      if x0 ≤ fx ∧ fx < x0 + 11 ∧ y0 ≤ fy ∧ fy < y0 + 11 then
        let idx := ((fy - y0).toNat * 11 + (fx - x0).toNat)
        t.set! idx (t.get! idx ||| bit)
      else t
    stampGo x0 y0 arr bit t (i + 1) fuel

/-- `World::observe` — the 11×11 window, proprioception, task and inventory.
The occupancy index is realized as a direct window scan over the entity
lists: for each food/deer item inside the window the corresponding packed
flag is set, which is extensionally the Rust occupancy map's content. -/
def observe (w : World) : Obs :=
  let x0 := w.bx - 5
  let y0 := w.by' - 5
  let tiles := windowGo w x0 y0 (ByteArray.emptyWithCapacity 121) 0 121
  let tiles := stampGo x0 y0 w.food 0x08 tiles 0 w.food.size
  let tiles := stampGo x0 y0 w.deer 0x10 tiles 0 w.deer.size
  { tiles
    energyBucket := (min (w.energy / 100) 10).toUInt8
    dayPhase := w.dayPhase
    task := w.taskObservation
    invWood := w.invWood, invStone := w.invStone
    invFood := w.invFood, invGold := w.invGold
    invAxe := w.invAxe, invBoat := w.invBoat }

/-- `World::pickup_food` — remove and count food items on the agent's tile;
`retain` preserves list order, as here. -/
def pickupFood (w : World) : World × UInt32 :=
  let here := packXY w.bx w.by'
  let (kept, picked) := w.food.foldl (init := (Array.emptyWithCapacity w.food.size, 0))
    fun (kept, picked) p =>
      if p == here then (kept, picked + 1) else (kept.push p, picked)
  let w := { w with food := kept }
  if picked > 0 then ({ w with invFood := w.invFood + picked }, picked) else (w, picked)

/-- Tail-recursive deer wander of `advance_world`: one unconditional draw
per deer, a direction draw and a walkability-gated move at 8 %. Reads
terrain through the (immutable) world it is passed; the deer array and RNG
thread linearly. -/
def deerGo (w : World) (deer : Array UInt64) (rng : Xoshiro256) (i : Nat) :
    Nat → Array UInt64 × Xoshiro256
  | 0 => (deer, rng)
  | fuel + 1 =>
    let (draw, rng) := rng.next
    if draw % 100 < 8 then
      let (d, rng) := rng.nextBelow 4
      let (dx, dy) := (Dir.ofIndex d).delta
      let (x, y) := unpackXY deer[i]!
      let (nx, ny) := (x + dx, y + dy)
      if (w.tileKind nx ny).walkable then
        deerGo w (deer.set! i (packXY nx ny)) rng (i + 1) fuel
      else
        deerGo w deer rng (i + 1) fuel
    else
      deerGo w deer rng (i + 1) fuel

/-- `World::advance_world` — time, deer wander, food spawns. -/
def advanceWorld (w : World) : World :=
  let w := { w with time := w.time + 1 }
  -- Deer wander deterministically, in index order.
  let n := w.deer.size
  let (deer, rng) := deerGo w w.deer w.rng 0 n
  let w := { w with deer, rng }
  -- Food spawns.
  if w.time % foodInterval == 0 ∧ w.food.size < foodCap then
    Id.run do
      let mut w := w
      for _ in [0:8] do
        let (xr, r1) := w.rng.nextBelow (i64bits w.side)
        let (yr, r2) := r1.nextBelow (i64bits w.side)
        w := { w with rng := r2 }
        let x : Int := xr.toNat
        let y : Int := yr.toNat
        if w.tileKind x y == .grass then
          w := { w with food := w.food.push (packXY x y) }
          break
      pure w
  else w

/-- `World::step` — advance the world by one agent action. -/
def step (w : World) (action : Action) : World × StepRes :=
  let mult := w.energyMultiplier
  let cost := action.energyCost mult
  if w.energy < cost then
    -- Exhausted: rest, world advances, no action effect.
    let w := { w with energy := min (w.energy + restRecover) energyMax }
    let w := w.advanceWorld
    let done := w.goalAchieved
    (w, ⟨if done then natF32 1 else f32zero, done⟩)
  else
    let w := { w with energy := w.energy - cost }
    let w :=
      match action with
      | .north | .south | .east | .west =>
        let dir := (action.asDir).getD .north
        let (dx, dy) := dir.delta
        let (nx, ny) := (w.bx + dx, w.by' + dy)
        let inBox := 0 ≤ nx ∧ nx < w.side ∧ 0 ≤ ny ∧ ny < w.side
        if inBox ∧ w.enterable nx ny then
          let w := { w with bx := nx, by' := ny, facing := dir }
          (w.pickupFood).1
        else w
      | .wait => w
      | .harvest =>
        let (dx, dy) := w.facing.delta
        let (tx, ty) := (w.bx + dx, w.by' + dy)
        let kind := w.tileKind tx ty
        match kind.harvestYield with
        | some item =>
          let n : UInt32 := if item == ItemKind.wood && w.invAxe then 3 else 1
          let w :=
            match item with
            | .wood => { w with invWood := w.invWood + n }
            | .stone => { w with invStone := w.invStone + n }
            | .food => { w with invFood := w.invFood + n }
            | .gold => { w with invGold := w.invGold + n }
          if kind == TileKind.tree then
            { w with harvested := w.harvested.insert (packXY tx ty) w.time }
          else w
        | none => w
      | .craftAxe =>
        if !w.invAxe ∧ 3 ≤ w.invWood ∧ 2 ≤ w.invStone then
          { w with invWood := w.invWood - 3, invStone := w.invStone - 2, invAxe := true }
        else w
      | .craftBoat =>
        if !w.invBoat ∧ 4 ≤ w.invWood then
          { w with invWood := w.invWood - 4, invBoat := true }
        else w
      | .eat =>
        if 1 ≤ w.invFood then
          { w with invFood := w.invFood - 1,
                   energy := min (w.energy + eatRestore) energyMax }
        else w
    let w := w.advanceWorld
    let done := w.goalAchieved
    (w, ⟨if done then natF32 1 else f32zero, done⟩)

/-- `World::new` — build the world: terrain table, spawn spiral, deer. -/
def new (seed : UInt64) (side : Int) : World :=
  let baseScale := i64ToF32 (max (side / 16) 8)
  let deerCap : UInt32 := ((side * side) / 512).toNat.toUInt32
  let tOrigin := -tableMargin
  let tSide := (side + 2 * tableMargin).toNat
  let table := World.buildTable seed baseScale tOrigin tSide
  let w : World :=
    { seed, side, baseScale, deerCap
      time := 0
      bx := side / 2, by' := side / 2, facing := .north
      energy := energyMax
      invWood := 0, invStone := 0, invFood := 0, invGold := 0
      invAxe := false, invBoat := false
      goal := none, goalStart := 0
      harvested := {}
      deer := #[], food := #[]
      rng := Xoshiro256.new (Xoshiro256.streamKey seed 0x0001)
      tOrigin, tSide, table }
  -- Deterministic spiral search for the spawn tile, exactly the Rust loop:
  -- radius 0..side, four directions, k in -radius..=radius, first walkable
  -- candidate with ≥ 2 trees near wins; otherwise the best-scoring walkable.
  let centre := side / 2
  let spiral : Int × Int := Id.run do
    let mut sx := centre
    let mut sy := centre
    let mut best : Option (Int × Int × UInt32) := none
    let mut found := false
    for radius in [0:side.toNat] do
      if found then break
      for d in [0:4] do
        if found then break
        let (dx, dy) := (Dir.ofIndex d.toUInt64).delta
        let span := 2 * radius + 1
        for kk in [0:span] do
          if found then break
          let k : Int := (kk : Int) - (radius : Int)
          let px := centre + dx * (radius : Int) + dy * k
          let py := centre + dy * (radius : Int) + dx * k
          if 0 ≤ px ∧ px < side ∧ 0 ≤ py ∧ py < side then
            let trees := w.countKindNear px py 4 .tree
            let stone := w.countKindNear px py 4 .stone
            let score := trees + stone
            if (w.tileKind px py).walkable then
              if (best.map (fun (_, _, b) => b < score)).getD true then
                best := some (px, py, score)
              if 2 ≤ trees then
                sx := px
                sy := py
                found := true
    -- The Rust epilogue overrides unconditionally: whenever any walkable
    -- candidate was seen, the spawn is the best-scoring one — the trees ≥ 2
    -- break only ends the search early.
    if let some (px, py, _) := best then
      sx := px
      sy := py
    pure (sx, sy)
  let w := { w with bx := spiral.1, by' := spiral.2 }
  -- Deer spawn on random walkable tiles.
  Id.run do
    let mut w := w
    for _ in [0:deerCap.toNat] do
      let (xr, r1) := w.rng.nextBelow (i64bits side)
      let (yr, r2) := r1.nextBelow (i64bits side)
      w := { w with rng := r2 }
      let x : Int := xr.toNat
      let y : Int := yr.toNat
      if (w.tileKind x y).walkable then
        w := { w with deer := w.deer.push (packXY x y) }
    pure w

end World

end AcornSpec
