import Acorn.Handcrafted.Signals
import Acorn.Host.Observation

namespace Acorn.Handcrafted
open Features Host

inductive TaskFeatureMode where
  | complete
  | withoutReachRelation
  deriving DecidableEq

instance : Provenance TaskFeatureMode := ⟨some .featureChannels⟩

def flagWord (flag : Bool) : UInt64 := if flag then 1 else 0

def bitWidth : Nat → UInt64 → Nat
  | 0, _ => 0
  | fuel + 1, word => if word == 0 then 0 else 1 + bitWidth fuel (word >>> 1)

theorem bitWidth_le (fuel : Nat) (word : UInt64) : bitWidth fuel word ≤ fuel := by
  induction fuel generalizing word with
  | zero => simp [bitWidth]
  | succ fuel ih => simp only [bitWidth]; split <;> have := ih (word >>> 1) <;> omega

def resourceBucket (count : UInt32) : UInt64 := (bitWidth 8 count.toUInt64).toUInt64

def split128 (value : Int) : UInt64 × UInt64 :=
  let bits := (value % 2 ^ 128).toNat
  (bits.toUInt64, (bits / 2 ^ 64).toUInt64)

def signCode (value : Int) : UInt64 := if value < 0 then 0 else if value == 0 then 1 else 2

def taskWords (task : TaskObservation) (mode : TaskFeatureMode) : List SensorWord :=
  ⟨0x42, task.cue⟩ :: match task with
  | .none => [⟨0x49, 0⟩]
  | .reach _ relation =>
    ⟨0x49, 1⟩ :: if mode == .withoutReachRelation then [] else
      let x := split128 relation.dx.val
      let y := split128 relation.dy.val
      [⟨0x4A, x.1⟩, ⟨0x4B, x.2⟩, ⟨0x4C, y.1⟩, ⟨0x4D, y.2⟩,
       ⟨0x4E, signCode relation.dx.val⟩, ⟨0x4F, signCode relation.dy.val⟩,
       ⟨0x60, relation.distance.toUInt64⟩,
       ⟨0x61, (bitWidth 64 relation.distance.toUInt64).toUInt64⟩]
  | .collect _ item remaining => [⟨0x49, 2⟩, ⟨0x4A, item.code⟩, ⟨0x4B, remaining.toUInt64⟩]
  | .craft _ item remaining => [⟨0x49, 3⟩, ⟨0x4A, item.code⟩, ⟨0x4B, flagWord remaining⟩]
  | .survive _ remaining =>
    [⟨0x49, 4⟩, ⟨0x4A, remaining⟩, ⟨0x4B, (bitWidth 64 remaining).toUInt64⟩]
  | .find _ here => [⟨0x49, 5⟩, ⟨0x4A, flagWord here⟩]

def positionWord (row col : Fin patchSide) : UInt64 :=
  let dx := col.val.toUInt64 - (patchSide / 2).toUInt64
  let dy := row.val.toUInt64 - (patchSide / 2).toUInt64
  (dx <<< 32) ||| (dy &&& 0xFFFFFFFF)

def tileWords (row col : Fin patchSide) (tile : TileObservation) : List SensorWord :=
  let pos := positionWord row col
  [⟨0x10, (pos <<< 8) ||| tile.kind.toUInt64⟩] ++
    (if tile.food != 0 then [⟨0x20, pos⟩] else []) ++
    (if tile.deer != 0 then [⟨0x30, pos⟩] else [])

def demonDiscount (index : Fin Acorn.FeatureConstants.demonCount) : Discount :=
  if index.val == 0 then .g99 else if index.val ≤ 5 then .g95 else .g90

structure Predictions where
  values : List Binary32
  bounded : values.length ≤ Acorn.FeatureConstants.demonCount

def Predictions.admit (values : List Binary32) : Option Predictions :=
  if h : values.length ≤ Acorn.FeatureConstants.demonCount then some ⟨values, h⟩ else none

def predictionWords (predictions : Predictions) : List SensorWord :=
  (List.finRange predictions.values.length).map fun i =>
    let discount := demonDiscount ⟨i.val, Nat.lt_of_lt_of_le i.isLt predictions.bounded⟩
    ⟨0x50 + i.val.toUInt64,
      (predictionBucket predictions.values[i.val] discount.horizon).val.toUInt64⟩

def sensorWords (obs : Observation) (mode : TaskFeatureMode := .complete) : List SensorWord :=
  (List.finRange patchSide).flatMap (fun row =>
    (List.finRange patchSide).flatMap fun col => tileWords row col ((obs.tiles.get row).get col)) ++
  [⟨0x40, obs.energy.toUInt64⟩, ⟨0x41, obs.day.toUInt64⟩] ++ taskWords obs.task mode ++
  [⟨0x43, resourceBucket obs.inventory.wood⟩, ⟨0x44, resourceBucket obs.inventory.stone⟩,
   ⟨0x45, resourceBucket obs.inventory.food⟩, ⟨0x46, resourceBucket obs.inventory.gold⟩,
   ⟨0x47, flagWord obs.inventory.axe⟩, ⟨0x48, flagWord obs.inventory.boat⟩]

def observationWords (obs : Observation) (predictions : Predictions)
    (mode : TaskFeatureMode := .complete) : List SensorWord :=
  sensorWords obs mode ++ predictionWords predictions

theorem taskWords_fit (task : TaskObservation) (mode : TaskFeatureMode) :
    (taskWords task mode).length ≤ Acorn.FeatureConstants.taskContextWords := by
  cases task <;> cases mode <;>
    simp [taskWords, Acorn.FeatureConstants.taskContextWords]

def contextCode (word : SensorWord) : UInt64 := Rng.hash3 0x7A5C word.channel word.value

def absentContext : UInt64 := Rng.hash3 0x7A5C 0 0

def taskContext (obs : Observation) (mode : TaskFeatureMode) : Vector UInt64 Acorn.FeatureConstants.taskContextWords :=
  Vector.ofFn fun slot => ((taskWords obs.task mode)[slot.val]?.map contextCode).getD absentContext

theorem taskContext_slot (obs : Observation) (mode : TaskFeatureMode)
    (slot : Fin Acorn.FeatureConstants.taskContextWords) :
    (taskContext obs mode)[slot.val] =
      ((taskWords obs.task mode)[slot.val]?.map contextCode).getD absentContext := by
  simp [taskContext]

def observationPatch (obs : Observation) (mode : TaskFeatureMode) : Patch patchShape :=
  (obs.tiles.map (fun row => row.map (·.kind.toUInt64))).flatten ++ taskContext obs mode

def encodeObservation (dimension : Dimension) {config : Features.Config}
    (bank : Bank patchShape config) (obs : Observation) (predictions : Predictions)
    (mode : TaskFeatureMode := .complete) : SwiftTd.ActiveSet dimension :=
  encode dimension bank (observationWords obs predictions mode) (observationPatch obs mode)

inductive SpatialInterest where
  | wood
  | mine
  | forage
  deriving DecidableEq

instance : Provenance SpatialInterest := ⟨some .spatialPotentials⟩

def spatialPotential (interest : SpatialInterest) (obs : Observation) : Bool :=
  obs.tiles.toList.any fun row => row.toList.any fun tile => match interest with
    | .wood => tile.kind == 4
    | .mine => tile.kind == 6 || tile.kind == 7
    | .forage => tile.food != 0

end Acorn.Handcrafted
