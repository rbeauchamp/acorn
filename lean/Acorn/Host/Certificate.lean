/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.WorldDynamics

/-!
# Certificate checkers for selecting properties of a seed

A selecting property is a fact about one generated world that is not a theorem
about every seed and may hold for one seed and fail for another, such as "the
far reach goal can be met from the spawn". Each checker here is an executable
decision over the executed world definitions. `AcornVerif.CurrentCertificates`
proves what an accepted certificate establishes; a rejected certificate
establishes nothing, since no checker is complete.

A replay certificate is an action list: the checker replays it through
`World.advanceActions` from a given world with the goal installed. A blocked
certificate is a finite set of tiles that contains the goal box and whose every
tile is impassable or has all its in-box neighbors in the set. A stance
certificate is a tile and a facing direction whose facing tile yields a named
item and which a move from a walkable in-box tile enters.

Each certificate type carries the proof that its checker accepted it, so a value
of the type cannot be built from a rejected certificate.
-/
namespace Acorn.Host

/-- The four movement directions. -/
def Direction.all : List Direction := [.north, .south, .east, .west]

/-- The move action of a direction. -/
def Direction.action : Direction → Action
  | .north => .north | .south => .south | .east => .east | .west => .west

/-! ## Replay -/

/-- Decide a replay certificate: the action list is nonempty, no longer than the cap,
and the executed action-stream fold from the world with the goal installed succeeds and
ends in a world that satisfies the goal. -/
def replayCertified {config : WorldConfig} (world : World config) (goal : Goal) (cap : Nat)
    (actions : List Action) : Bool :=
  !actions.isEmpty && decide (actions.length ≤ cap) &&
    match (world.setGoal goal).advanceActions actions with
    | .ok final => final.goalSatisfied
    | .error _ => false

/-- An action list the replay checker accepted for this world, goal and cap. -/
structure ReplayCertificate {config : WorldConfig} (world : World config) (goal : Goal)
    (cap : Nat) where
  /-- The actions to replay from the world with the goal installed. -/
  actions : List Action
  /-- The checker's acceptance. -/
  accepted : replayCertified world goal cap actions = true

/-- Run the replay checker on a candidate action list. -/
def ReplayCertificate.check {config : WorldConfig} (world : World config) (goal : Goal)
    (cap : Nat) (actions : List Action) : Option (ReplayCertificate world goal cap) :=
  if accepted : replayCertified world goal cap actions = true then some ⟨actions, accepted⟩
  else none

/-! ## Blocked goal box -/

/-- Whether a tile is one of the listed cells. -/
def inRegion (cells : List Position) (tile : Position) : Bool :=
  cells.any fun cell => decide (cell = tile)

/-- Whether a tile is inside the box the body moves in. -/
def inBox (config : WorldConfig) (tile : Position) : Bool :=
  (BoxPosition.checked config tile.x.val tile.y.val).isSome

/-- A tile whose static terrain the body cannot enter: a mountain, or water when the
certificate is for a body without a boat. A terrain refusal is not counted as
impassable. -/
def impassable (config : WorldConfig) (boat : Bool) (tile : Position) : Bool :=
  match terrain tile config.raw.seed config.raw.baseScale with
  | .ok .mountain => true
  | .ok .water => !boat
  | _ => false

/-- The signed offsets from a reach target to the tiles of its goal box on one axis. -/
def boxOffsets : List Int :=
  (List.range (2 * FeatureConstants.reachRadius + 1)).map fun (index : Nat) =>
    (index : Int) - (FeatureConstants.reachRadius : Int)

/-- A tile the region has to hold is listed, or lies outside the box, or is not a
representable position. -/
def covered (config : WorldConfig) (cells : List Position) : Option Position → Bool
  | some tile => inRegion cells tile || !inBox config tile
  | none => true

/-- Decide a blocked certificate. The start tile is outside the region; every in-box
tile of the goal box is in the region; and every tile of the region is impassable or
has all four in-box neighbors in the region. With `boat` false, water counts as
impassable and the certificate speaks only of a body that owns no boat. -/
def regionBlocked (config : WorldConfig) (boat : Bool) (target : Position)
    (cells : List Position) (start : Position) : Bool :=
  !inRegion cells start &&
    (boxOffsets.all fun dy => boxOffsets.all fun dx =>
      covered config cells (target.translate dx dy)) &&
    cells.all fun cell => impassable config boat cell ||
      Direction.all.all fun direction =>
        covered config cells (cell.translate direction.delta.1 direction.delta.2)

/-- A region the blocked checker accepted for this configuration, boat assumption,
target and start tile. -/
structure BlockedCertificate (config : WorldConfig) (boat : Bool) (target start : Position) where
  /-- The tiles of the region. -/
  cells : List Position
  /-- The checker's acceptance. -/
  accepted : regionBlocked config boat target cells start = true

/-- Run the blocked checker on a candidate region. -/
def BlockedCertificate.check (config : WorldConfig) (boat : Bool) (target start : Position)
    (cells : List Position) : Option (BlockedCertificate config boat target start) :=
  if accepted : regionBlocked config boat target cells start = true then some ⟨cells, accepted⟩
  else none

/-! ## Harvest stance -/

/-- Whether a tile's static terrain is enterable without a boat. A terrain refusal is
not counted as walkable. -/
def walkableTile (config : WorldConfig) (tile : Position) : Bool :=
  match terrain tile config.raw.seed config.raw.baseScale with
  | .ok kind => kind.walkable
  | .error _ => false

/-- Decide a stance certificate. The static terrain of the tile the stance faces yields
the item; the stance tile is walkable; and the tile behind the stance, from which a move
in the facing direction enters it, is in the box and walkable. -/
def stanceCertified (config : WorldConfig) (stance : BoxPosition config) (direction : Direction)
    (item : Item) : Bool :=
  (match terrain (stance.facingPosition direction) config.raw.seed config.raw.baseScale with
    | .ok kind => decide (kind.harvestYield = some item)
    | .error _ => false) &&
    walkableTile config stance.position &&
    match stance.position.translate (-direction.delta.1) (-direction.delta.2) with
    | some approach => inBox config approach && walkableTile config approach
    | none => false

/-- A stance the stance checker accepted for this configuration and item. -/
structure StanceCertificate (config : WorldConfig) (item : Item) where
  /-- The tile the body stands on. -/
  stance : BoxPosition config
  /-- The direction the body faces. -/
  direction : Direction
  /-- The checker's acceptance. -/
  accepted : stanceCertified config stance direction item = true

/-- Run the stance checker on a candidate stance. -/
def StanceCertificate.check (config : WorldConfig) (item : Item) (stance : BoxPosition config)
    (direction : Direction) : Option (StanceCertificate config item) :=
  if accepted : stanceCertified config stance direction item = true then
    some ⟨stance, direction, accepted⟩
  else none

end Acorn.Host
