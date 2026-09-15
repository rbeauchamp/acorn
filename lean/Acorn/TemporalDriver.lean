/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.TemporalControl

/-!
# Native option/exploration consumer

This invokes the actual option policy and persistent sampler on arbitrary raw
inputs. It executes the actual scalar models and planner and is not a full-agent runner.
Output is an execution observation, never a correctness oracle or learning study.
The temporal entry point uses these same concrete definitions.
-/
namespace Acorn.TemporalDriver
open Features Handcrafted

/-- Small diagnostic storage; the policy definitions remain dimension-generic. -/
def dimension : Dimension := ⟨8, by decide, ⟨3, rfl⟩, by decide⟩

/-- Exercise actual native begin, admitted step, termination decision and closing
credit with dynamic inputs. Each current criterion uses the same typed kernel. -/
@[noinline] def execute (seed word : UInt64) (criterion : Criterion) : Nat × Nat × UInt32 :=
  let config : Features.Config := ⟨seed, 1, by decide, ⟨3, by decide, by decide⟩⟩
  let interest : Interest config := .learned (.selected ⟨0, by change 0 < 3; decide⟩ (Prediction.project .g99 ⟨word.toUInt32⟩))
  let skill := Skill.initial config criterion dimension interest
  let features : SwiftTd.ActiveSet dimension := ⟨[FeatIdx.fromHash dimension word], by simp⟩
  let potential := match interest with
    | .learned assignment => assignment.potential features
    | .declared _ _ => false
  let models := modelOperations criterion dimension
  let begun := skill.beginTemporal models features potential true .own
  let stepped := begun.1.stepTemporal models begun.2.1 begun.2.2 ⟨word.toUInt32⟩ (.project .zero) (Rng.Xoshiro256.seed seed)
  let stopped := match stepped.1.decideOption stepped.2.1 features potential (word &&& 1 == 1) .zero .own with
    | .ending reason => stepped.1.endTemporal models ⟨stepped.2.1, potential, reason⟩
        ⟨word.toUInt32⟩ .zero (.project .zero)
    | .continuing next => (stepped.1.stepTemporal models stepped.2.1 next ⟨word.toUInt32⟩ (.project .zero) stepped.2.2.2).1
  let snapshot := stopped.policy.snapshot (count := primitiveCount) features (stopped.policy.exploreRate (count := primitiveCount))
  let persistent := snapshot.drawPersistent stepped.2.2.2
  let planning : PlanningResult criterion dimension :=
    ⟨Controller.initial _ _ _, Vector.replicate _ ModelCache.initial, seed,
      Vector.replicate _ .zero⟩
  let planned := planningBoundary .scalar planning (Vector.replicate _ stopped) features (.project .zero)
  (stepped.2.2.1.action.val, persistent.1.action.val,
    ((planned.controller.predictAll features).get (metaOfSkill ⟨0, by decide⟩)).bits)

end Acorn.TemporalDriver

/-- Admit diagnostic raw words without wrapping oversized inputs. -/
def main (arguments : List String) : IO UInt32 := do
  let parsed := match arguments with
    | [] => some (0, 0)
    | [seed, word] => do
      let seed ← seed.toNat?
      let word ← word.toNat?
      if seed < 2^64 && word < 2^64 then some (seed, word) else none
    | _ => none
  match parsed with
  | none => IO.eprintln "usage: temporal-native [seed raw-word]"; return 2
  | some (seed, word) =>
    let result := Acorn.TemporalDriver.execute seed.toUInt64 word.toUInt64 .differential
    IO.println s!"option-action={result.1} persistent-action={result.2.1} value={result.2.2}"
    return 0
