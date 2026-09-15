/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Rng
import AcornSpec.Learner

/-!
# Executable specification: εz-greedy exploration

Mirrors `src/handcrafted/exploration.rs`: the persistent-run `EzGreedy`
policy with its `⌊1/U⌋` duration draw capped at 128, the retired
`EpsilonSchedule`, and the `RatePolicy` that says where each ε-consumer's
rate comes from. `EzGreedy` itself carries no rate — one is supplied at each
decision, by the consumer's own learner under the deployed policy.
-/

namespace AcornSpec

open AcornSpec.Constants

/-- `exploration::EpsilonSchedule` — the retired geometric anneal, present
only as derived-exploration-rate's incumbent evaluator arm. -/
structure EpsilonSchedule where
  /-- Current rate. -/
  eps : Float32
  /-- Floor. -/
  min : Float32
  /-- Per-step multiplier. -/
  decay : Float32

namespace EpsilonSchedule

/-- `EpsilonSchedule::INCUMBENT` — the constants the deployed agent carried
before PAR-10. -/
def incumbent : EpsilonSchedule :=
  { eps := Float32.ofBits epsStartBits
    min := Float32.ofBits epsMinBits
    decay := Float32.ofBits epsDecayBits }

/-- `EpsilonSchedule::advance` — one geometric step, saturated at the floor. -/
def advance (s : EpsilonSchedule) : EpsilonSchedule :=
  { s with eps := saturate (s.eps * s.decay) s.min (natF32 1) }

/-- `EpsilonSchedule::rate` — the current rate as the probability type, i.e.
through `ExploreRate::set`. -/
def rate (s : EpsilonSchedule) : Float32 :=
  saturate s.eps f32zero (natF32 1)

end EpsilonSchedule

/-- `exploration::RatePolicy` — where every ε-consumer's rate comes from,
fixed at agent construction. `perLearner` is the deployed agent (PAR-10);
the other two are derived-exploration-rate evaluator arms. -/
inductive RatePolicy where
  /-- Every consumer derives its rate from its own step sizes (PAR-10). -/
  | perLearner
  /-- One derived rate — the primitive controller's — for every consumer. -/
  | shared
  /-- The retired schedule, evaluator-only. -/
  | annealed (schedule : EpsilonSchedule)

/-- `RatePolicy::advance` — advance whatever clock the policy carries. A
no-op for both derived variants. -/
def RatePolicy.advance : RatePolicy → RatePolicy
  | .perLearner => .perLearner
  | .shared => .shared
  | .annealed s => .annealed s.advance

/-- `exploration::ConsumerRate` — one consumer's rate after its arm has been
consulted: derive from its own learner, or take the rate the arm imposes. -/
inductive ConsumerRate where
  /-- Derive from the consumer's own step sizes. -/
  | ownLearner
  /-- The arm imposes this rate. -/
  | imposed (rate : Float32)

/-- `ConsumerRate::resolve`. -/
def ConsumerRate.resolve (c : ConsumerRate) (own : Float32) : Float32 :=
  match c with
  | .ownLearner => own
  | .imposed rate => rate

/-- `exploration::EzGreedy` at the study's fixed shape: action count 9, cap
128. Duration sampler only — occupancy of a run lives in `Phase`, so a run
and an active option cannot exist together. -/
structure EzGreedy where
  deriving Inhabited

namespace EzGreedy

/-- `EzGreedy::MAX_DURATION`. -/
def maxDuration : UInt32 := 128

/-- `EzGreedy::begin` — decide at a primitive decision point: draw the gate,
then the ζ-tailed duration and the action. Consumes the caller's RNG in the
exact Rust order. Returns `some (action, remaining)` when a run starts;
`remaining` is `duration − 1`, the steps still to serve after this one. -/
def begin (rate : Float32) (rng : Xoshiro256) :
    Option (Nat × UInt32) × Xoshiro256 :=
  -- No projection: `rate` comes from `Sarsa.exploreRate`, already in `[0, 1]`.
  let gate := rate
  let (u1, rng) := rng.next
  let draw1 := UInt64.toFloat (u1 >>> 11) * (natF64 1 / UInt64.toFloat ((1 : UInt64) <<< 53))
  if widen gate ≤ draw1 then (none, rng)
  else
    let (u2, rng) := rng.next
    let draw2 := UInt64.toFloat (u2 >>> 11) * (natF64 1 / UInt64.toFloat ((1 : UInt64) <<< 53))
    let u := natF64 1 - draw2
    let drawn := floor64 (natF64 1 / u)
    let duration : UInt32 :=
      if UInt64.toFloat (maxDuration.toUInt64) ≤ drawn then maxDuration
      else rustF64toU32 drawn
    let (a, rng) := rng.nextBelow 9
    (some (a.toNat, duration - min duration 1), rng)

end EzGreedy

end AcornSpec
