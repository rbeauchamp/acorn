/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Runner

/-!
# Existing random-policy diagnostic boundary

This is the current explicitly requested demo comparison, not an agent callback
or substitute for the learned composition. It consumes its separate seeded RNG
and resets the result at every goal. Its caller owns the finite supplied goal array.
-/
namespace Acorn.Host

/-- A random diagnostic attempt carries its cap at each state write. -/
structure BaselineAttempt (config : WorldConfig) (cap : UInt64) where
  /-- Current environment. -/
  world : World config
  /-- Separate diagnostic action stream. -/
  rng : Rng.Xoshiro256
  /-- Bounded action count. -/
  steps : Fin (cap.toNat + 1)
  /-- Result local to this goal, initially empty. -/
  result : StepResult
  /-- Ordered binary32 reward accumulation. -/
  reward : Binary32

/-- One current bounded RNG action draw and world transition, until terminal or capped. -/
def BaselineAttempt.tick {config : WorldConfig} {cap : UInt64} (state : BaselineAttempt config cap) :
    Except WorldError (BaselineAttempt config cap) := do
  if state.result.done then return state
  if hs : state.steps.val < cap.toNat then
    let (index, rng) := state.rng.nextBelow ⟨FeatureConstants.primitiveCount.toUInt64, by decide⟩
    let (world, result) ← state.world.step (Action.fromIndex index.val.toNat)
    return ⟨world, rng, ⟨state.steps.val + 1, by omega⟩, result, state.reward.add result.reward⟩
  else return state

/-- Complete public diagnostic over the supplied goals, with explicit world refusal.
The returned row array has exactly the finite caller-supplied goal count on success. -/
def runRandomBaseline (seed : UInt64) (config : WorldConfig) (goals : Array Goal) (cap : UInt64) :
    Except WorldError (Array GoalOutcome) := do
  let mut world ← World.initial config
  let mut rng := Rng.Xoshiro256.seed (Rng.streamKey seed 0xba5e000000000001)
  let mut outcomes := #[]
  for index in List.finRange goals.size do
    let goal := goals[index.val]
    let mut state : BaselineAttempt config cap :=
      ⟨world.setGoal goal, rng, ⟨0, by omega⟩, {}, ⟨0⟩⟩
    for _ in [:cap.toNat] do
      state ← state.tick
      if state.result.done then break
    world := state.world
    rng := state.rng
    outcomes := outcomes.push ⟨index.val.toUInt64, 0, 0, state.steps.val.toUInt64,
      state.result.done, state.reward, ⟨⟨0⟩, ⟨0x3f800000⟩, ⟨0⟩⟩⟩
  return outcomes

end Acorn.Host
