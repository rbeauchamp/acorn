/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.WorldSchema
import AcornSpec.StudySchedule
import AcornSpec.MachineWords
import AcornSpec.Rng
import AcornSpec.Constants

/-!
# Preserved study identities and observation schemas

The registered curriculum, arm identities, attempt rows, and budget constants
are inputs to both the historical evaluator and maintained analysis. Analysis
reconstructs goal identities and validates the observation grid using these
integer definitions; it does not need to construct a world or execute an agent.
-/

namespace AcornSpec

/-! ## Curriculum -/

/-- `curriculum::Curriculum::standard` — the 13 goals in training order for
a campaign seed and world side. Reach targets use deterministic hashed draws. -/
def standardCurriculum (seed : UInt64) (side : Int) : Array GoalKind :=
  let cx := side / 2
  let cy := side / 2
  let nearR : Int := min (max (side / 12) 12) 40
  let farR : Int := min (max (side / 6) 24) 120
  let draw (k : UInt64) (r : Int) : Int :=
    ((hash2 seed k 0xABCD) % (i64bits (2 * r))).toNat - r
  let x1 := cx + draw 1 nearR
  let y1 := cy + draw 2 nearR
  let x2 := cx + draw 3 farR
  let y2 := cy + draw 4 farR
  #[.survive 200,
    .collect .wood 2,
    .collect .stone 2,
    .reach x1 y1,
    .collect .wood 4,
    .craft .axe,
    .collect .food 3,
    .reach x2 y2,
    .collect .gold 2,
    .craft .boat,
    .collect .wood 8,
    .survive 800,
    .collect .gold 4]

/-- `Curriculum` difficulty tiers, in goal order. -/
def curriculumTiers : Array UInt8 := #[0, 0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5]

/-- `agent_baseline::AgentBaselineArm` — the five frozen arms, in execution order. -/
inductive Arm where
  /-- Final hierarchical learner. -/
  | final
  /-- Deterministic pseudorandom primitive comparator. -/
  | random
  /-- Identically initialized hierarchy with learner updates off. -/
  | frozen
  /-- Final learner without the Reach relation. -/
  | ablatedGoalRelation
  /-- Final primitive learner without option/meta control. -/
  | ablatedTemporalAbstraction
  deriving DecidableEq, Repr

/-! ## Attempt rows and the shard -/

/-- `agent_baseline::AttemptRow` — one raw attempt, sufficient to derive every capped
goal-occurrence metric. `reward` is the attempt's summed reward as `f32`
bits. -/
structure Row where
  /-- Curriculum cycle. -/
  cycle : UInt64
  /-- Goal index within the cycle. -/
  goalIndex : Nat
  /-- The goal. -/
  goal : GoalKind
  /-- Difficulty tier. -/
  tier : UInt8
  /-- Goal family. -/
  family : Family
  /-- Attempt index within the occurrence. -/
  attempt : Nat
  /-- Whether the goal was satisfied on the occurrence's first observation. -/
  initiallySatisfied : Bool
  /-- Environment steps consumed by this attempt. -/
  steps : UInt64
  /-- Whether this attempt achieved the goal. -/
  achieved : Bool
  /-- Summed reward (f32 bits). -/
  reward : UInt32
  deriving DecidableEq, Repr

/-- One completed (seed, arm) stream: the raw rows and the integer
action-transcript fold. -/
structure Shard where
  /-- Attempt rows, in execution order. -/
  rows : Array Row
  /-- FNV-style fold over the action indices, in order. -/
  actionFold : UInt64
  deriving DecidableEq, Repr


end AcornSpec
