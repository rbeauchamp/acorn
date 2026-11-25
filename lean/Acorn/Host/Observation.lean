import Acorn.FeatureConstants
import Acorn.Features

namespace Acorn.Host

abbrev Coordinate := { value : Int // -(2 ^ 63) ≤ value ∧ value < 2 ^ 63 }

abbrev Displacement := { value : Int // -(2 ^ 64 - 1) ≤ value ∧ value ≤ 2 ^ 64 - 1 }

structure ReachRelation where
  dx : Displacement
  dy : Displacement

def ReachRelation.between (x y targetX targetY : Coordinate) : ReachRelation :=
  ⟨⟨targetX.val - x.val, by have := targetX.property; have := x.property; omega⟩,
   ⟨targetY.val - y.val, by have := targetY.property; have := y.property; omega⟩⟩

def ReachRelation.distance (relation : ReachRelation) : Nat :=
  max relation.dx.val.natAbs relation.dy.val.natAbs - Acorn.FeatureConstants.reachRadius

inductive Item where
  | wood
  | stone
  | food
  | gold
  deriving DecidableEq

def Item.code : Item → UInt64
  | .wood => 1
  | .stone => 2
  | .food => 3
  | .gold => 4

inductive Craftable where
  | axe
  | boat
  deriving DecidableEq

def Craftable.code : Craftable → UInt64
  | .axe => 11
  | .boat => 12

inductive TaskObservation where
  | none
  | reach (cue : UInt64) (relation : ReachRelation)
  | collect (cue : UInt64) (item : Item) (remaining : UInt32)
  | craft (cue : UInt64) (item : Craftable) (remaining : Bool)
  | survive (cue remaining : UInt64)
  | find (cue : UInt64) (here : Bool)

def TaskObservation.cue : TaskObservation → UInt64
  | .none => 0
  | .reach cue _ | .collect cue _ _ | .craft cue _ _ | .survive cue _ | .find cue _ => cue

structure TileObservation where
  kind : UInt8
  food : UInt8
  deer : UInt8

structure Inventory where
  wood : UInt32
  stone : UInt32
  food : UInt32
  gold : UInt32
  axe : Bool
  boat : Bool

def patchSide : Nat := Acorn.FeatureConstants.patchSide

def patchShape : Features.PatchShape :=
  ⟨patchSide * patchSide + Acorn.FeatureConstants.taskContextWords, by decide, by decide⟩

structure Observation where
  tiles : Vector (Vector TileObservation patchSide) patchSide
  energy : UInt8
  day : UInt8
  task : TaskObservation
  inventory : Inventory

end Acorn.Host
