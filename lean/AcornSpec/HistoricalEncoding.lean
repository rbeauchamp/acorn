/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Features
import AcornSpec.Learner
import AcornSpec.World

/-!
# Observation adapter for the retained evaluator

The evaluator renders world observations, task relations, and discounted demon
predictions into the integer featurizer's words and patch. This adapter depends
on the retained world and learner vocabulary. Its dependency is separate from
the pure feature definitions and their universal index proofs.
-/

namespace AcornSpec

/-- `features::bucket_prediction` — resolve a prediction into
`0..PREDICTION_BUCKETS` across its discount's whole range. -/
def bucketPrediction (value horizon : Float32) : UInt8 :=
  let frac := saturate (value / horizon) f32zero (natF32 1)
  let idx := rustF32toU8 (floor32 (frac * natF32 9))
  if 8 < idx then 8 else idx

/-! ## `handcrafted::encoding` -/

/-- `encoding::TaskFeatureMode` — which declared task fields are rendered. -/
inductive TaskFeatureMode where
  /-- Opaque identity plus all host-declared relations. -/
  | complete
  /-- The Reach relation removed (goal-relation ablation). -/
  | withoutReachRelation
  deriving DecidableEq

/-- `encoding::split_i128` — two's-complement words of an exact signed
displacement (`i128` in Rust; exact `Int` here, wrapped at 2¹²⁸). -/
def splitI128 (value : Int) : UInt64 × UInt64 :=
  let m : Nat := (value % (2 : Int) ^ 128).toNat
  ((m % 2 ^ 64).toUInt64, (m / 2 ^ 64).toUInt64)

/-- `encoding::sign_code`. -/
@[inline]
def signCode (value : Int) : UInt64 :=
  if value < 0 then 0 else if value == 0 then 1 else 2

/-- `encoding::task_words` — render the task relation, exhaustively by kind. -/
def taskWords (task : TaskObs) (mode : TaskFeatureMode)
    (out : Array (UInt64 × UInt64)) : Array (UInt64 × UInt64) :=
  let out := out.push (0x42, task.cueOf)
  match task with
  | .none => out.push (0x49, 0)
  | .reach _ rel =>
    let out := out.push (0x49, 1)
    if mode == .withoutReachRelation then out
    else
      let (xl, xh) := splitI128 rel.dx
      let (yl, yh) := splitI128 rel.dy
      ((((((((out.push (0x4A, xl)).push (0x4B, xh)).push (0x4C, yl)).push
        (0x4D, yh)).push (0x4E, signCode rel.dx)).push
        (0x4F, signCode rel.dy)).push (0x60, rel.distanceToRegion)).push
        (0x61, rel.distanceScale.toUInt64))
  | .collect _ item remaining =>
    ((out.push (0x49, 2)).push (0x4A, item.code)).push (0x4B, remaining.toUInt64)
  | .craft _ c remaining =>
    ((out.push (0x49, 3)).push (0x4A, c.code)).push
      (0x4B, if remaining then 1 else 0)
  | .survive _ remaining =>
    let scale : UInt64 :=
      if remaining == 0 then 0 else (Nat.log2 remaining.toNat + 1).toUInt64
    ((out.push (0x49, 4)).push (0x4A, remaining)).push (0x4B, scale)

/-- The demon discounts in `Cumulant::ALL` order — the horizons the
prediction channels bucket against. -/
def cumulantDiscount (d : Nat) : Discount :=
  match d with
  | 0 => .g99                     -- GoalReward
  | 1 | 2 | 3 | 4 | 5 => .g95     -- NearTree/Stone/Ore/Water/Food
  | _ => .g90                     -- EnergyLow/Night/HasWood/HasStone/HasAxe

/-- `encoding::observation_words` (with the evaluator's task mode) — the
window channels, proprioception, task words and demon-prediction channels,
in the exact Rust push order. `demonPreds` holds the 11 prediction bits. -/
def observationWordsWindowGo (obs : Obs) (out : Array (UInt64 × UInt64))
    (i : Nat) : Nat → Array (UInt64 × UInt64)
  | 0 => out
  | fuel + 1 =>
    let row := i / 11
    let col := i % 11
    let tile := obs.tiles.get! i
    let dx : Int := (col : Int) - 5
    let dy : Int := (row : Int) - 5
    let pos := ((i64bits dx) <<< 32) ||| ((i64bits dy) &&& 0xFFFFFFFF)
    let out := out.push (0x10, (pos <<< 8) ||| (tile &&& 0x7).toUInt64)
    let out := if tile &&& 0x08 != 0 then out.push (0x20, pos) else out
    let out := if tile &&& 0x10 != 0 then out.push (0x30, pos) else out
    observationWordsWindowGo obs out (i + 1) fuel

/-- Demon prediction channels of `observation_words`. -/
def observationWordsDemonsGo (demonPreds : Array UInt32)
    (out : Array (UInt64 × UInt64)) (d : Nat) : Nat → Array (UInt64 × UInt64)
  | 0 => out
  | fuel + 1 =>
    let horizon := (cumulantDiscount d).horizon
    let pred := Float32.ofBits demonPreds[d]!
    let out := out.push (0x50 + d.toUInt64, (bucketPrediction pred horizon).toUInt64)
    observationWordsDemonsGo demonPreds out (d + 1) fuel

/-- `encoding::observation_words` (with the evaluator's task mode) — the
window channels, proprioception, task words and demon-prediction channels,
in the exact Rust push order. `demonPreds` holds the 11 prediction bits. -/
def observationWords (obs : Obs) (demonPreds : Array UInt32)
    (mode : TaskFeatureMode) : Array (UInt64 × UInt64) :=
  let out : Array (UInt64 × UInt64) := Array.emptyWithCapacity 256
  let out := observationWordsWindowGo obs out 0 121
  let out := out.push (0x40, obs.energyBucket.toUInt64)
  let out := out.push (0x41, obs.dayPhase.toUInt64)
  let out := taskWords obs.task mode out
  let out := out.push (0x43, (bucket obs.invWood).toUInt64)
  let out := out.push (0x44, (bucket obs.invStone).toUInt64)
  let out := out.push (0x45, (bucket obs.invFood).toUInt64)
  let out := out.push (0x46, (bucket obs.invGold).toUInt64)
  let out := out.push (0x47, if obs.invAxe then 1 else 0)
  let out := out.push (0x48, if obs.invBoat then 1 else 0)
  observationWordsDemonsGo demonPreds out 0 11

/-- Tail-recursive fill of `observation_patch`. -/
def observationPatchGo (obs : Obs) (patch : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => patch
  | fuel + 1 =>
    observationPatchGo obs (patch.push (obs.tiles.get! i &&& 0x7)) (i + 1) fuel

/-- `encoding::observation_patch` — the 121 opaque tile-kind codes. -/
def observationPatch (obs : Obs) : ByteArray :=
  observationPatchGo obs (ByteArray.emptyWithCapacity 121) 0 121

/-- `encoding::encode_observation_with_task_mode` — render, then tile-code. -/
def encodeObservation (f : Featurizer) (obs : Obs) (demonPreds : Array UInt32)
    (mode : TaskFeatureMode) : Array UInt32 :=
  f.encode (observationWords obs demonPreds mode) (observationPatch obs)

end AcornSpec
