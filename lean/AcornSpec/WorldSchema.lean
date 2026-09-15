/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Goal vocabulary shared by execution and preserved observations

These closed types describe goal identities and families without importing
terrain, world dynamics, a learner, or floating-point operations. The historical
analysis validates preserved goal literals against this vocabulary.
-/

namespace AcornSpec

/-- `world::ItemKind`. -/
inductive ItemKind where
  /-- Wood. -/
  | wood
  /-- Stone. -/
  | stone
  /-- Food. -/
  | food
  /-- Gold. -/
  | gold
  deriving DecidableEq, Repr

/-- `world::Craftable`. -/
inductive Craftable where
  /-- Axe: 3 wood + 2 stone. -/
  | axe
  /-- Boat: 4 wood. -/
  | boat
  deriving DecidableEq, Repr

/-- `world::GoalKind`. -/
inductive GoalKind where
  /-- Reach the given coordinates. -/
  | reach (x y : Int)
  /-- Collect `n` of `item`. -/
  | collect (item : ItemKind) (n : UInt32)
  /-- Craft the given tool. -/
  | craft (c : Craftable)
  /-- Survive `steps` steps from goal start. -/
  | survive (steps : UInt64)
  deriving DecidableEq, Repr, Inhabited

/-- `task::GoalFamily` (closed set). -/
inductive Family where
  /-- Coordinate-reaching tasks. -/
  | reach
  /-- Inventory-collection tasks. -/
  | collect
  /-- Tool-construction tasks. -/
  | craft
  /-- Fixed-duration survival tasks. -/
  | survive
  deriving DecidableEq, Repr, Inhabited

/-- `GoalKind::family`. -/
@[inline]
def GoalKind.family : GoalKind → Family
  | .reach .. => .reach
  | .collect .. => .collect
  | .craft _ => .craft
  | .survive _ => .survive

end AcornSpec
