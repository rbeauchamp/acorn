/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.PredictionControl

/-!
# Native prediction/control consumer

Calls current encoding, policy selection and prediction/control transitions.
Output is an execution observation, never a correctness oracle or a scientific
learning run. Universal guarantees belong to the same called definitions.
-/
namespace Acorn.ControlDriver
open Features Handcrafted

/-- Small native storage; transition definitions remain dimension-generic. -/
def dimension : Dimension := ⟨8, by decide, ⟨3, rfl⟩, by decide⟩

/-- The full current primitive action domain. -/
def actionCount : Word.Count := ⟨Acorn.FeatureConstants.primitiveCount.toUInt64, by decide⟩

/-- Input observations retain the complete public sensory-byte domain. -/
def observation (word : UInt64) : Host.Observation :=
  ⟨Vector.replicate _ (Vector.replicate _ ⟨word.toUInt8, 0, 0⟩),
    word.toUInt8, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩

/-- Execute a policy draw and two continuing transitions through the same current
state owners. Caller-supplied words keep native storage dynamically allocated. -/
@[noinline] def execute (seed word : UInt64) (criterion : Criterion) : Nat × UInt32 × UInt32 :=
  let profile : FeatureProfile := ⟨.final, .perStep, .perLearner, .learned⟩
  let config : Features.Config := ⟨seed, 1, by decide, ⟨3, by decide, by decide⟩⟩
  let bank := Bank.initial Host.patchShape config
  let state := PredictionControl.initial profile criterion dimension
  let obs := observation word
  let features := state.encode bank obs
  let snapshot : PolicySnapshot actionCount :=
    state.control.controller.snapshot features (SwiftTd.ExploreRate.project ⟨word.toUInt32⟩)
  let decision := snapshot.draw (Rng.Xoshiro256.seed seed)
  let state := state.advance features obs .one decision.1.action true
  let features := state.encode bank obs
  let state := state.advance features obs .one decision.1.action true
  (decision.1.action.val, state.control.average.rate.value.bits,
    (state.control.controller.predictAll features).get decision.1.action |>.bits)

end Acorn.ControlDriver

/-- Parse raw native inputs without wrapping oversized words. -/
def main (arguments : List String) : IO UInt32 := do
  let parsed := match arguments with
    | [] => some (0, 0)
    | [seed, word] => do
      let seed ← seed.toNat?
      let word ← word.toNat?
      if seed < 2^64 && word < 2^64 then some (seed, word) else none
    | _ => none
  match parsed with
  | none => IO.eprintln "usage: control-native [seed raw-word]"; return 2
  | some (seed, word) =>
    let result := Acorn.ControlDriver.execute seed.toUInt64 word.toUInt64 .differential
    IO.println s!"action={result.1} rate={result.2.1} value={result.2.2}"
    return 0
