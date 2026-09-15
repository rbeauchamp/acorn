/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConstants
import Acorn.Host.Observation
import Acorn.Provenance

/-!
# D1 observation channels and D2 spatial potentials

This composition boundary declares the hand-authored layout in
`docs/learned-only-binding.md`. The learned coder receives only opaque words.
Resource counts and predictions are bucketed; the imprint patch contains kind
alone. These interfaces do not claim lossless reconstruction of observations.
-/
namespace Acorn.Handcrafted
open Features Host

/-- The current task-channel profiles, including the preserved study ablation. -/
inductive TaskFeatureMode where
  /-- All declared task relations. -/
  | complete
  /-- Omit only the coordinate relation. -/
  | withoutReachRelation
  deriving DecidableEq

instance : Provenance TaskFeatureMode := ⟨some .featureChannels⟩

/-- Exact boolean word encoding. -/
def flagWord (flag : Bool) : UInt64 := if flag then 1 else 0

/-- Width of the low retained word, capped by the requested number of bits. -/
def bitWidth : Nat → UInt64 → Nat
  | 0, _ => 0
  | fuel + 1, word => if word == 0 then 0 else 1 + bitWidth fuel (word >>> 1)

/-- The actual capped width never exceeds the supplied bit count. -/
theorem bitWidth_le (fuel : Nat) (word : UInt64) : bitWidth fuel word ≤ fuel := by
  induction fuel generalizing word with
  | zero => simp [bitWidth]
  | succ fuel ih => simp only [bitWidth]; split <;> have := ih (word >>> 1) <;> omega

/-- Resource bucket: the current eight-step right-shift recipe. -/
def resourceBucket (count : UInt32) : UInt64 := (bitWidth 8 count.toUInt64).toUInt64

/-- Full two's-complement 128-bit split, for every signed displacement. -/
def split128 (value : Int) : UInt64 × UInt64 :=
  let bits := (value % 2 ^ 128).toNat
  (bits.toUInt64, (bits / 2 ^ 64).toUInt64)

/-- Three-way sign including equality. -/
def signCode (value : Int) : UInt64 := if value < 0 then 0 else if value == 0 then 1 else 2

/-- Task channels in exactly their current construction order. -/
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

/-- Current position packing uses wrapping words at both shifts. -/
def positionWord (row col : Fin patchShape.side) : UInt64 :=
  let dx := col.val.toUInt64 - (patchShape.side / 2).toUInt64
  let dy := row.val.toUInt64 - (patchShape.side / 2).toUInt64
  (dx <<< 32) ||| (dy &&& 0xFFFFFFFF)

/-- Per-cell word order: kind, then optional food, then optional deer. -/
def tileWords (row col : Fin patchShape.side) (tile : TileObservation) : List SensorWord :=
  let pos := positionWord row col
  [⟨0x10, (pos <<< 8) ||| tile.kind.toUInt64⟩] ++
    (if tile.food != 0 then [⟨0x20, pos⟩] else []) ++
    (if tile.deer != 0 then [⟨0x30, pos⟩] else [])

/-- Closed current horizon layout in canonical demon order (D5). -/
def demonDiscount (index : Fin Acorn.FeatureConstants.demonCount) : Discount :=
  if index.val == 0 then .g99 else if index.val ≤ 5 then .g95 else .g90

/-- The exact division, saturation, multiply, floor and byte-cast recipe.
Standard native float operations, including floor and cast, retain their
explicit runtime trust boundary; the output bound does not assume their accuracy. -/
def predictionBucket (value horizon : Binary32) : Fin Acorn.FeatureConstants.predictionBuckets :=
  let frac := (value.div horizon).saturate .zero ⟨0x3f800000⟩
  let scaled := frac.mul (Binary32.ofUInt64 Acorn.FeatureConstants.predictionBuckets.toUInt64)
  let idx := (Float32.ofBits scaled.bits).floor.toUInt8.toNat
  ⟨min idx (Acorn.FeatureConstants.predictionBuckets - 1), by
    have : 0 < Acorn.FeatureConstants.predictionBuckets := by decide
    have := Nat.min_le_right idx (Acorn.FeatureConstants.predictionBuckets - 1)
    omega⟩

/-- At most the current number of prediction channels may be supplied.
Short prefixes retain the standalone encoder's domain; overlong inputs are
refused rather than indexing beyond the horizon table. -/
structure Predictions where
  /-- Raw values; bucket saturation is total even outside normal prediction ranges. -/
  values : List Binary32
  /-- Every supplied channel has an owning horizon. -/
  bounded : values.length ≤ Acorn.FeatureConstants.demonCount

/-- Exact-or-refused prediction-list admission. -/
def Predictions.admit (values : List Binary32) : Option Predictions :=
  if h : values.length ≤ Acorn.FeatureConstants.demonCount then some ⟨values, h⟩ else none

/-- Prediction channels in their original index order. -/
def predictionWords (predictions : Predictions) : List SensorWord :=
  (List.finRange predictions.values.length).map fun i =>
    let discount := demonDiscount ⟨i.val, Nat.lt_of_lt_of_le i.isLt predictions.bounded⟩
    ⟨0x50 + i.val.toUInt64,
      (predictionBucket predictions.values[i.val] discount.horizon).val.toUInt64⟩

/-- Complete row-major sensor, proprioceptive, task, inventory and prediction stream. -/
def observationWords (obs : Observation) (predictions : Predictions)
    (mode : TaskFeatureMode := .complete) : List SensorWord :=
  (List.finRange patchShape.side).flatMap (fun row =>
    (List.finRange patchShape.side).flatMap fun col => tileWords row col ((obs.tiles.get row).get col)) ++
  [⟨0x40, obs.energy.toUInt64⟩, ⟨0x41, obs.day.toUInt64⟩] ++ taskWords obs.task mode ++
  [⟨0x43, resourceBucket obs.inventory.wood⟩, ⟨0x44, resourceBucket obs.inventory.stone⟩,
   ⟨0x45, resourceBucket obs.inventory.food⟩, ⟨0x46, resourceBucket obs.inventory.gold⟩,
   ⟨0x47, flagWord obs.inventory.axe⟩, ⟨0x48, flagWord obs.inventory.boat⟩] ++
  predictionWords predictions

/-- The imprint patch contains only the kind byte, with both dimensions preserved. -/
def observationPatch (obs : Observation) : Patch patchShape :=
  obs.tiles.map (fun row => row.map (·.kind))

/-- Execute the declared layout followed by the learned opaque encoder. -/
def encodeObservation (dimension : Dimension) {config : Features.Config}
    (bank : Bank patchShape config) (obs : Observation) (predictions : Predictions)
    (mode : TaskFeatureMode := .complete) : SwiftTd.ActiveSet dimension :=
  encode dimension bank (observationWords obs predictions mode) (observationPatch obs)

/-- The current D2 spatial taxonomy. -/
inductive SpatialInterest where
  /-- Any tree in view. -/
  | wood
  /-- Any rock or ore in view. -/
  | mine
  /-- Any food in view. -/
  | forage
  deriving DecidableEq

instance : Provenance SpatialInterest := ⟨some .spatialPotentials⟩

/-- Spatial potentials are Boolean disjunctions, not counts or magnitudes. -/
def spatialPotential (interest : SpatialInterest) (obs : Observation) : Bool :=
  obs.tiles.toList.any fun row => row.toList.any fun tile => match interest with
    | .wood => tile.kind == 4
    | .mine => tile.kind == 6 || tile.kind == 7
    | .forage => tile.food != 0

end Acorn.Handcrafted
