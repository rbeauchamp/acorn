import Acorn.Digits
import Acorn.FeatureReferences
import Acorn.Handcrafted.GridWorld

namespace Acorn.FeatureDriver
open Features

def dimension : Dimension := ⟨8, by decide, ⟨3, rfl⟩, by decide⟩

def profile : Handcrafted.FeatureProfile := ⟨.final, .perStep, .declared, .learned⟩

def observation (word : UInt64) : Host.Observation :=
  ⟨Vector.replicate _ (Vector.replicate _ ⟨word.toUInt8, 0, 0⟩),
    word.toUInt8, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩

@[noinline] def execute (seed word : UInt64) (criterion : Criterion) : Nat × UInt64 × Nat :=
  let config : Features.Config :=
    ⟨seed, 1, by decide, ⟨3, by decide, by decide⟩, Handcrafted.declaredTester⟩
  let initial : FeatureRuntime Host.patchShape Handcrafted.Grid.actions config criterion dimension [.g99]
      Unit Unit Unit :=
    ⟨⟨Representation.initial _ _, Ensemble.initial config criterion dimension [.g99] (profile.interests config)⟩,
      TemporalReferences.cold config [.g99] ()⟩
  let bank := initial.lifecycle.representation.bank
  let input := profile.encode dimension bank (observation word) ⟨[], by decide⟩
  let retired := initial.retire
    (bank.activations (Handcrafted.observationPatch (observation word) profile.taskMode))
  let refreshed := retired.refreshAtFree profile.ranksSubtasks
  (input.indices.length, refreshed.lifecycle.representation.bank.checksum,
    refreshed.lifecycle.representation.progress.replaced.toNat)

end Acorn.FeatureDriver

def _root_.Acorn.FeatureDriver.main (arguments : List String) : IO UInt32 := do
  let parsed := match arguments with
    | [] => some (0, 0)
    | [seed, word] => do
      let seed ← Acorn.Digits.natural seed
      let word ← Acorn.Digits.natural word
      if seed < 2^64 && word < 2^64 then some (seed, word) else none
    | _ => none
  match parsed with
  | none =>
    IO.eprintln s!"usage: feature-native [SEED SENSORY_WORD]\n{Acorn.Digits.usage}"
    return 2
  | some (seed, word) =>
    let result := Acorn.FeatureDriver.execute seed.toUInt64 word.toUInt64 .differential
    IO.println s!"active={result.1} bank={result.2.1} replaced={result.2.2}"
    return 0
