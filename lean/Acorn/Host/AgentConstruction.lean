/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentPrefix
import Acorn.Timing

/-!
# Immutable full-agent construction

Public construction admits the complete nonzero tiling word and bank-size
domain, every power-of-two feature capacity below the UInt32 limit, all current
profile discriminants, either criterion, either planning selection and every step order. Native
allocation remains a runtime boundary; structural admission is not an allocation
or infinite-run liveness promise.
-/
namespace Acorn.Handcrafted
open Features

/-- Complete immutable construction choices for the current agent. -/
structure AgentConstruction where
  /-- All current mode, credit, rate and subtask alternatives. -/
  profile : FeatureProfile
  /-- Criterion fixes the numeric rules and model arity. -/
  criterion : Criterion
  /-- Explicit planning selection. -/
  planning : PlanningSelection
  /-- Declared order of the two step parts, planning and the world's transition. -/
  order : StepOrder
  /-- Receiver-owned feature salt, tilings and unit capacity. -/
  config : Features.Config
  /-- Compiler-admitted hash and learner dimension. -/
  dimension : Dimension

/-- Full word admission before feature allocation; no truncation or default substitution. -/
def AgentConstruction.admit (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) : Option AgentConstruction :=
  if ht : 0 < tilings.toNat then
    if hu : 0 < units ∧ units ≤ 65535 then
      if he : exponent < 32 then
        some ⟨profile, criterion, planning, order,
          ⟨seed, tilings, ht, ⟨units, hu.1, hu.2⟩, declaredTester⟩,
          ⟨2^exponent, Nat.pow_pos (by decide), ⟨exponent, rfl⟩, Nat.pow_lt_pow_right (by decide) he⟩⟩
      else none
    else none
  else none

/-- Construction rejects exactly the absent positive/capacity conditions. -/
theorem AgentConstruction.admit_iff (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) :
    (admit profile criterion planning order seed tilings units exponent).isSome = true ↔
      0 < tilings.toNat ∧ 0 < units ∧ units ≤ 65535 ∧ exponent < 32 := by
  by_cases ht : 0 < tilings.toNat <;> by_cases hu : 0 < units ∧ units ≤ 65535 <;>
    by_cases he : exponent < 32 <;> simp [admit, ht, hu, he]

/-- Admission keeps the declared step order. -/
theorem AgentConstruction.admit_order (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (order : StepOrder) (seed tilings : UInt64)
    (units exponent : Nat) (construction : AgentConstruction)
    (admitted : admit profile criterion planning order seed tilings units exponent =
      some construction) : construction.order = order := by
  unfold admit at admitted
  split at admitted
  · split at admitted
    · split at admitted
      · cases admitted
        rfl
      · cases admitted
    · cases admitted
  · cases admitted

/-- Every typed dimension lies in the public exponent domain; no admitted shape is omitted. -/
theorem dimension_exponent_complete (dimension : Dimension) :
    ∃ exponent < 32, dimension.capacity = 2^exponent := by
  obtain ⟨exponent, same⟩ := dimension.powerOfTwo
  refine ⟨exponent, ?_, same⟩
  have bound := dimension.wordBound
  rw [same] at bound
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp bound

/-- The CLI default feature configuration is derived from the shared Lean feature constants. -/
def AgentConstruction.standard (seed : UInt64) (selection : Host.AgentSelection)
    (planning : PlanningSelection) (order : StepOrder) : AgentConstruction :=
  ⟨researchProfile selection.profile, selection.criterion, planning, order,
    ⟨seed, Acorn.FeatureConstants.defaultTilings.toUInt64, by decide,
      ⟨Acorn.FeatureConstants.defaultImprintUnits, by decide, by decide⟩, declaredTester⟩,
    ⟨Acorn.FeatureConstants.defaultWeightSpace, by decide, ⟨14, rfl⟩, by decide⟩⟩

/-- The exact image of an agent of one construction. The construction is an index of the
type, so an image of one order and a state of another do not meet by accident. This
project makes an image in two places: the image of a state of the construction
(`Acorn.Checkpoint.stateImage`), and the admission of a decoded payload whose header holds
the word of the construction's order (`Acorn.Checkpoint.admitPayload`). The agent image it
holds carries no order, and the constructor is public: every module can apply it to an
agent image, and no check stops that. An image under another index is the payload of the
first construction with the order word replaced, which the loader of the second
construction admits with the same agent (`AcornVerif.CurrentCheckpoint.relabeled_loaded`). -/
structure AgentConstruction.Image (construction : AgentConstruction) where
  /-- The exact agent image. -/
  image : AgentImage Grid.interface construction.profile construction.config
    construction.criterion construction.dimension

/-- The agent of an image of a construction, under the construction's planning selection. -/
def AgentConstruction.Image.agent {construction : AgentConstruction} (image : construction.Image) :
    Agent Grid.interface construction.profile construction.config construction.criterion
      construction.dimension construction.planning :=
  image.image.agent construction.planning

end Acorn.Handcrafted
