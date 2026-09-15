/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission

/-!
# Current agent mutation checksum

The checksum reads learner knowledge, pending ranking, gain for differential
control, planning count, seed, clock, bank, generator and retirement transcript.
Transient credit, predictions, exploration state and observational lifetime
records are outside this mutation receipt. Equality of hashes is not equality
of state and supplies no correctness or learning-benefit claim.
-/
namespace Acorn.Host
open Features Handcrafted

/-- Fold controller learners once each in their stored action order. -/
def controllerChecksum {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) : UInt64 :=
  controller.learners.foldl (fun hash learner =>
    (hash ^^^ Rng.rotateLeft learner.state.stateChecksum 7) * NumericState.checksumMultiplier)
    Rng.fnvOffset

/-- Model checksum traverses the actual stored criterion-dependent learners. -/
def modelChecksum {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) : UInt64 :=
  match model with
  | .discounted reward continuation =>
    reward.state.stateChecksum ^^^ Rng.rotateLeft continuation.state.stateChecksum 7
  | .differential reward continuation duration =>
    reward.state.stateChecksum ^^^ Rng.rotateLeft continuation.state.stateChecksum 7 ^^^
      Rng.rotateLeft duration.state.stateChecksum 17

/-- Every demon contributes once in horizon order. -/
def demonChecksum {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) (hash : UInt64) : UInt64 :=
  match demons with
  | .nil => hash
  | .cons learner rest => demonChecksum rest (hash ^^^ Rng.rotateLeft learner.state.stateChecksum 17)

/-- Fold the specified low bytes of a word in little-endian order. -/
def checksumBytes (hash word : UInt64) (count : Nat) : UInt64 :=
  (List.range count).foldl (fun hash index =>
    Rng.fnvStep hash ((word >>> (8 * index).toUInt64).toUInt8)) hash

/-- Distinct absolute weight words among the actual hashed unit slots.
Hash aliases and equal magnitudes contribute one value, as required by the census. -/
def imprintCensus {config : Features.Config} {dimension : Dimension} {discounts : List Discount}
    (demons : DemonBank dimension discounts) : Vector Nat discounts.length :=
  match demons with
  | .nil => #v[]
  | .cons learner rest =>
    let words := (List.finRange config.units.count).map fun unit =>
      (learner.state.weights.get (unitFeature dimension config unit)).value.magnitude
    (#v[words.eraseDups.length] ++ imprintCensus (config := config) rest).cast (by simp [Nat.add_comm])

/-- The complete mutation receipt is a read of this receiver's current owners. -/
def agentChecksum {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {planning : PlanningSelection}
    (agent : Agent profile config criterion dimension planning) : UInt64 := Id.run do
  let runtime := agent.control.runtime
  let ensemble := runtime.lifecycle.consumers
  let representation := runtime.lifecycle.representation
  let mut hash := controllerChecksum ensemble.control ^^^
    Rng.rotateLeft (if runtime.refresh.pending then 1 else 0) 43
  match criterion with
  | .discounted => pure ()
  | .differential => hash := hash ^^^ Rng.rotateLeft agent.control.average.rate.value.bits.toUInt64 37
  hash := hash ^^^ Rng.rotateLeft (controllerChecksum ensemble.metaController) 5
  hash := hash ^^^ Rng.rotateLeft runtime.references.planningSteps 31
  for skill in ensemble.skills do
    hash := hash ^^^ Rng.rotateLeft (controllerChecksum skill.policy) 11
    hash := hash ^^^ Rng.rotateLeft (modelChecksum skill.model) 7
  hash := demonChecksum ensemble.demons hash
  hash := hash ^^^ Rng.rotateLeft config.seed 23
  hash := hash ^^^ (representation.progress.clock * 0x9e3779b97f4a7c15)
  hash := hash ^^^ representation.bank.checksum
  hash := hash ^^^ Rng.rotateLeft representation.bank.stream.state 13
  hash := hash ^^^ Rng.rotateLeft representation.progress.events.length.toUInt64 19
  let transcript := representation.progress.events.foldl (fun hash event =>
    checksumBytes (checksumBytes hash event.step 8) event.unit.val.toUInt64 4) Rng.fnvOffset
  return hash ^^^ Rng.rotateLeft transcript 29

end Acorn.Host
