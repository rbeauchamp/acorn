/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.Features

/-!
# Declared host observation interface

This is the current input boundary, not a world dynamics implementation.
Byte-valued public sensory fields retain their complete raw domains. Goal
relations carry the invariants established by their host constructors.
-/
namespace Acorn.Host

/-- Exact signed 64-bit coordinate domain. -/
abbrev Coordinate := { value : Int // -(2 ^ 63) ≤ value ∧ value < 2 ^ 63 }

/-- A displacement of two signed 64-bit coordinates. -/
abbrev Displacement := { value : Int // -(2 ^ 64 - 1) ≤ value ∧ value ≤ 2 ^ 64 - 1 }

/-- Goal-relative displacement; distance and scale are derived, never writable copies. -/
structure ReachRelation where
  /-- Horizontal displacement. -/
  dx : Displacement
  /-- Vertical displacement. -/
  dy : Displacement

/-- Exact subtraction covers extreme coordinate pairs without machine overflow. -/
def ReachRelation.between (x y targetX targetY : Coordinate) : ReachRelation :=
  ⟨⟨targetX.val - x.val, by have := targetX.property; have := x.property; omega⟩,
   ⟨targetY.val - y.val, by have := targetY.property; have := y.property; omega⟩⟩

/-- Chebyshev distance to the rewarded region, with saturating subtraction. -/
def ReachRelation.distance (relation : ReachRelation) : Nat :=
  max relation.dx.val.natAbs relation.dy.val.natAbs - Acorn.FeatureConstants.reachRadius

/-- Closed inventory-item domain. -/
inductive Item where
  /-- Wood. -/
  | wood
  /-- Stone. -/
  | stone
  /-- Food. -/
  | food
  /-- Gold. -/
  | gold
  deriving DecidableEq

/-- Stable host item codes. -/
def Item.code : Item → UInt64
  | .wood => 1
  | .stone => 2
  | .food => 3
  | .gold => 4

/-- Closed craftable domain. -/
inductive Craftable where
  /-- Axe. -/
  | axe
  /-- Boat. -/
  | boat
  deriving DecidableEq

/-- Stable host craftable codes. -/
def Craftable.code : Craftable → UInt64
  | .axe => 11
  | .boat => 12

/-- A task cannot omit its own declared relation. -/
inductive TaskObservation where
  /-- No installed goal. -/
  | none
  /-- Coordinate goal. -/
  | reach (cue : UInt64) (relation : ReachRelation)
  /-- Inventory-count goal. -/
  | collect (cue : UInt64) (item : Item) (remaining : UInt32)
  /-- Crafting goal. -/
  | craft (cue : UInt64) (item : Craftable) (remaining : Bool)
  /-- Survival goal. -/
  | survive (cue remaining : UInt64)

/-- Opaque identity, zero only by convention when no goal is installed. -/
def TaskObservation.cue : TaskObservation → UInt64
  | .none => 0
  | .reach cue _ | .collect cue _ _ | .craft cue _ _ | .survive cue _ => cue

/-- Public sensory bytes retain the original observation domain. -/
structure TileObservation where
  /-- Kind code. -/
  kind : UInt8
  /-- Food-present byte. -/
  food : UInt8
  /-- Deer-present byte. -/
  deer : UInt8

/-- Inventory snapshot. -/
structure Inventory where
  /-- Wood count. -/
  wood : UInt32
  /-- Stone count. -/
  stone : UInt32
  /-- Food count. -/
  food : UInt32
  /-- Gold count. -/
  gold : UInt32
  /-- Axe possession. -/
  axe : Bool
  /-- Boat possession. -/
  boat : Bool

/-- Current generated host patch shape. -/
def patchShape : Features.PatchShape :=
  ⟨Acorn.FeatureConstants.patchSide, by decide, by decide⟩

/-- Complete current observation, including all raw public sensory bytes. -/
structure Observation where
  /-- Row-major sensory window. -/
  tiles : Vector (Vector TileObservation patchShape.side) patchShape.side
  /-- Energy bucket byte. -/
  energy : UInt8
  /-- Day-phase byte. -/
  day : UInt8
  /-- Complete task relation. -/
  task : TaskObservation
  /-- Inventory snapshot. -/
  inventory : Inventory

end Acorn.Host
