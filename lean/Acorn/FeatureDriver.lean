/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureReferences
import Acorn.Handcrafted.FeatureProfile

/-!
# Native feature-lifecycle consumer

This executable calls the current encoder, receiver-bound retirement and ranked
refresh directly. It retains only current storage and emits integral execution
observations. The output is not a correctness oracle or a learning-benefit claim;
universal guarantees belong to the called proof-bearing definitions.
-/
namespace Acorn.FeatureDriver
open Features

/-- A small native-consumer dimension; the executing definitions remain generic. -/
def dimension : Dimension := ⟨8, by decide, ⟨3, rfl⟩, by decide⟩

/-- Native execution uses the full learned feature profile. -/
def profile : Handcrafted.FeatureProfile := ⟨.final, .perStep, .perLearner, .learned⟩

/-- Native observation input retains the host's complete sensory shape. -/
def observation (word : UInt64) : Host.Observation :=
  ⟨Vector.replicate _ (Vector.replicate _ ⟨word.toUInt8, 0, 0⟩),
    word.toUInt8, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩

/-- Execute native feature operations for an arbitrary seed and input word.
The generic call prevents the initial consumer arrays becoming shared globals. -/
@[noinline] def execute (seed word : UInt64) (criterion : Criterion) : Nat × UInt64 × Nat :=
  let config : Features.Config := ⟨seed, 1, by decide, ⟨3, by decide, by decide⟩⟩
  let initial : FeatureRuntime Host.patchShape config criterion dimension [.g99] Unit Unit Unit :=
    ⟨⟨Representation.initial _ _, Ensemble.initial config criterion dimension [.g99] (profile.interests config)⟩,
      Refresh.cold true, TemporalReferences.cold config [.g99] ()⟩
  let input := profile.encode dimension initial.lifecycle.representation.bank (observation word) ⟨[], by decide⟩
  let retired := initial.retire
  let refreshed := retired.refreshAtFree
  (input.indices.length, refreshed.lifecycle.representation.bank.checksum,
    refreshed.lifecycle.representation.progress.events.length)

end Acorn.FeatureDriver

/-- Run one direct native feature operation with optional raw seed and sensory word. -/
def main (arguments : List String) : IO UInt32 := do
  let parsed := match arguments with
    | [] => some (0, 0)
    | [seed, word] => do
      let seed ← seed.toNat?
      let word ← word.toNat?
      pure (seed, word)
    | _ => none
  match parsed with
  | none =>
    IO.eprintln "usage: feature-native [seed sensory-word]"
    return 2
  | some (seed, word) =>
    let result := Acorn.FeatureDriver.execute seed.toUInt64 word.toUInt64 .differential
    IO.println s!"active={result.1} bank={result.2.1} events={result.2.2}"
    return 0
