import Acorn.Digits
import Acorn.Handcrafted.GridWorld

namespace Acorn.ControlDriver
open Features Handcrafted

def dimension : Dimension := ⟨8, by decide, ⟨3, rfl⟩, by decide⟩

def actionCount : Word.Count := ⟨Acorn.FeatureConstants.primitiveCount.toUInt64, by decide⟩

def observation (word : UInt64) : Host.Observation :=
  ⟨Vector.replicate _ (Vector.replicate _ ⟨word.toUInt8, 0, 0⟩),
    word.toUInt8, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩

@[noinline] def execute (seed word : UInt64) (criterion : Criterion) : Nat × UInt32 × UInt32 :=
  let profile : FeatureProfile := ⟨.final, .perStep, .declared, .learned⟩
  let config : Features.Config :=
    ⟨seed, 1, by decide, ⟨3, by decide, by decide⟩, Handcrafted.declaredTester⟩
  let bank := Bank.initial Host.patchShape config
  let state := PredictionControl.initial Grid.interface profile criterion dimension
  let obs := observation word
  let features := state.encode bank obs
  let snapshot : PolicySnapshot actionCount :=
    state.control.controller.snapshot features (SwiftTd.ExploreRate.project ⟨word.toUInt32⟩)
  let decision := snapshot.draw (Rng.Xoshiro256.seed seed)
  let frame := Grid.frame profile.taskMode obs false
  let state := state.advance features frame .one decision.1.action true
  let features := state.encode bank obs
  let state := state.advance features frame .one decision.1.action true
  (decision.1.action.val, state.control.average.rate.value.bits,
    (state.control.controller.predictAll features).get decision.1.action |>.bits)

end Acorn.ControlDriver

def _root_.Acorn.ControlDriver.main (arguments : List String) : IO UInt32 := do
  let parsed := match arguments with
    | [] => some (0, 0)
    | [seed, word] => do
      let seed ← Acorn.Digits.natural seed
      let word ← Acorn.Digits.natural word
      if seed < 2^64 && word < 2^64 then some (seed, word) else none
    | _ => none
  match parsed with
  | none => IO.eprintln s!"usage: control-native [SEED RAW_WORD]\n{Acorn.Digits.usage}"; return 2
  | some (seed, word) =>
    let result := Acorn.ControlDriver.execute seed.toUInt64 word.toUInt64 .differential
    IO.println s!"action={result.1} rate={result.2.1} value={result.2.2}"
    return 0
