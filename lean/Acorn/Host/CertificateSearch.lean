/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Certificate
import Acorn.Host.WorldGeneration

/-!
# Certificate search

These functions propose certificates for the checkers of
`Acorn.Host.Certificate`. Nothing is proved about them: a proposal means nothing
until its checker accepts it, and a search that finds no proposal shows nothing
about the world.

The search is breadth first over the tiles the body can enter without a boat,
reading the executed `terrain` once per tile. `settle` is the only function here
that takes a world step: it replays a planned action list through `World.step`
and issues an action again when the body could not pay for it. The list it
returns is a candidate for the replay checker, which may still reject it.
-/
namespace Acorn.Host.CertificateSearch

/-- Row-major index of an in-box tile. -/
def tileIndex (config : WorldConfig) (tile : BoxPosition config) : Nat :=
  tile.y.val * config.side + tile.x.val

/-- The in-box tile one move from a tile in a direction, if any. -/
def neighbor (config : WorldConfig) (tile : BoxPosition config) (direction : Direction) :
    Option (BoxPosition config) :=
  BoxPosition.checked config ((tile.x.val : Int) + direction.delta.1)
    ((tile.y.val : Int) + direction.delta.2)

/-- The in-box tile from which a move in a direction leads to a tile, if any. -/
def behind (config : WorldConfig) (tile : BoxPosition config) (direction : Direction) :
    Option (BoxPosition config) :=
  BoxPosition.checked config ((tile.x.val : Int) - direction.delta.1)
    ((tile.y.val : Int) - direction.delta.2)

/-- The static terrain of an in-box tile through a cache indexed by tile: zero is not
yet evaluated, nine a terrain refusal, and any other value one more than the kind code. -/
def kindAt (config : WorldConfig) (cache : Array UInt8) (tile : BoxPosition config) :
    Option TileKind × Array UInt8 :=
  let index := tileIndex config tile
  let stored := cache.getD index 0
  if stored == 0 then
    match terrain tile.position config.raw.seed config.raw.baseScale with
    | .ok kind => (some kind, cache.setIfInBounds index (kind.code + 1))
    | .error _ => (none, cache.setIfInBounds index 9)
  else if stored == 9 then (none, cache)
  else (some (TileKind.fromCode (stored - 1)), cache)

/-- The arrival mark of a move in a direction. Zero marks an unvisited tile and five the
start. -/
def arrivalCode : Direction → UInt8
  | .north => 1 | .south => 2 | .east => 3 | .west => 4

/-- The move an arrival mark records, if it records one. -/
def arrivalDirection (code : UInt8) : Option Direction :=
  if code == 1 then some .north else if code == 2 then some .south
  else if code == 3 then some .east else if code == 4 then some .west else none

/-- Whether the executed reach predicate holds on a tile. -/
def inGoalBox {config : WorldConfig} (target : Position) (tile : BoxPosition config) : Bool :=
  ((Goal.reach target).observe tile.position ⟨0, 0, 0, 0, false, false⟩ 0).satisfied

/-- What one search has found: the first tile visited in each goal box, and for each
harvested item the tile from which a move in a direction enters a stance facing it. -/
structure Findings (config : WorldConfig) where
  /-- First visited tile of the near goal box. -/
  near : Option (BoxPosition config) := none
  /-- First visited tile of the far goal box. -/
  far : Option (BoxPosition config) := none
  /-- Approach tile and facing direction of a wood stance. -/
  wood : Option (BoxPosition config × Direction) := none
  /-- Approach tile and facing direction of a stone stance. -/
  stone : Option (BoxPosition config × Direction) := none
  /-- Approach tile and facing direction of a gold stance. -/
  gold : Option (BoxPosition config × Direction) := none

/-- Nothing remains to be found. -/
def Findings.complete {config : WorldConfig} (found : Findings config) : Bool :=
  found.near.isSome && found.far.isSome && found.wood.isSome && found.stone.isSome &&
    found.gold.isSome

/-- Record an approach for the item a faced tile yields, keeping the first one found. -/
def Findings.record {config : WorldConfig} (found : Findings config) (item : Item)
    (approach : BoxPosition config × Direction) : Findings config :=
  match item with
  | .wood => if found.wood.isNone then { found with wood := some approach } else found
  | .stone => if found.stone.isNone then { found with stone := some approach } else found
  | .gold => if found.gold.isNone then { found with gold := some approach } else found
  | .food => found

/-- Breadth-first search from a start tile over the in-box tiles enterable without a
boat. Returns the findings and each visited tile's arrival mark. Every tile is visited at
most once, so the tile count bounds the loop. -/
def explore (config : WorldConfig) (start : BoxPosition config) (near far : Position) :
    Findings config × Array UInt8 := Id.run do
  let area := config.side * config.side
  let mut cache : Array UInt8 := Array.replicate area 0
  let mut arrival : Array UInt8 :=
    (Array.replicate area 0).setIfInBounds (tileIndex config start) 5
  let mut queue : Array (BoxPosition config) := #[start]
  let mut found : Findings config := {}
  for head in [:area] do
    let some tile := queue[head]? | break
    if found.near.isNone && inGoalBox near tile then found := { found with near := some tile }
    if found.far.isNone && inGoalBox far tile then found := { found with far := some tile }
    if found.complete then break
    for direction in Direction.all do
      let some next := neighbor config tile direction | continue
      let (kind, evaluated) := kindAt config cache next
      cache := evaluated
      let some kind := kind | continue
      if !kind.walkable then continue
      if let some faced := neighbor config next direction then
        let (facedKind, evaluated) := kindAt config cache faced
        cache := evaluated
        if let some item := facedKind.bind TileKind.harvestYield then
          found := found.record item (tile, direction)
      let index := tileIndex config next
      if arrival.getD index 0 == 0 then
        arrival := arrival.setIfInBounds index (arrivalCode direction)
        queue := queue.push next
  return (found, arrival)

/-- The moves that lead from the search's start to a visited tile, read back from the
arrival marks. -/
def pathTo (config : WorldConfig) (arrival : Array UInt8) (tile : BoxPosition config) :
    List Action := Id.run do
  let mut actions : List Action := []
  let mut current := tile
  for _ in [:config.side * config.side] do
    let some direction := arrivalDirection (arrival.getD (tileIndex config current) 0) | break
    actions := direction.action :: actions
    let some previous := behind config current direction | break
    current := previous
  return actions

/-- Replay planned actions through the executed step and return the actions issued: each
planned action, and once more when the body could not pay for it and rested instead. The
replay stops at a step the world refuses. -/
def settle {config : WorldConfig} (world : World config) (planned : List Action) :
    List Action := Id.run do
  let mut current := world
  let mut issued : Array Action := #[]
  for action in planned do
    match current.step action with
    | .error _ => return issued.toList
    | .ok (next, events) =>
      issued := issued.push action
      current := next
      if events.exhausted then
        match current.step action with
        | .error _ => return issued.toList
        | .ok (after, _) =>
          issued := issued.push action
          current := after
  return issued.toList

/-- A region to propose as a blocked certificate: the goal box, every tile connected to
it through tiles that are not impassable, and their impassable neighbors. `none` when the
region holds more than `budget` tiles. -/
def region (config : WorldConfig) (boat : Bool) (target : Position) (budget : Nat) :
    Option (List Position) := Id.run do
  let mut marks : Array UInt8 := Array.replicate (config.side * config.side) 0
  let mut pending : Array (BoxPosition config) := #[]
  for dy in boxOffsets do
    for dx in boxOffsets do
      if let some tile := BoxPosition.checked config (target.x.val + dx) (target.y.val + dy) then
        let index := tileIndex config tile
        if marks.getD index 0 == 0 then
          marks := marks.setIfInBounds index 1
          pending := pending.push tile
  for head in [:budget + 1] do
    let some tile := pending[head]? | return some (pending.toList.map (·.position))
    if !impassable config boat tile.position then
      for direction in Direction.all do
        if let some next := neighbor config tile direction then
          let index := tileIndex config next
          if marks.getD index 0 == 0 then
            marks := marks.setIfInBounds index 1
            pending := pending.push next
  return none

end Acorn.Host.CertificateSearch
