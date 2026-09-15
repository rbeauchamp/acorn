/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Options
import Acorn.Control
import Acorn.FeatureReferences

/-!
# Temporal dispatch interfaces

The option policy kernel uses current managed storage. These internal interfaces
confine model and planning operations to their own storage. The public temporal
entry point instantiates them with `Acorn.Models` and `Acorn.Planning`; generic
dispatch proofs retain their storage-boundary scope. No planning benefit follows
from that confinement or from the concrete model execution contracts.
-/
namespace Acorn.Features

/-- Final reason and elapsed actions are an observation of the removed activation. -/
structure EndEvent where
  /-- Stable receiving option slot. -/
  slot : Fin Acorn.FeatureConstants.skillCount
  /-- Bounded elapsed action count. -/
  age : ModelAge
  /-- Actual termination decision. -/
  reason : OptionEnd

/-- Source of the actual primitive action, with exclusive phase semantics. -/
inductive TemporalSource where
  /-- Fresh primitive greedy action. -/
  | primitive
  /-- First action of a drawn persistent run. -/
  | explorationStart
  /-- A committed remaining action, without a random draw. -/
  | explorationContinuation
  /-- Action sampled by one option's own policy. -/
  | option (slot : Fin Acorn.FeatureConstants.skillCount)
  deriving DecidableEq

/-- Every observation refers to the same action used by credit. -/
structure TemporalDecision where
  /-- Actual branch of the dispatch transition. -/
  source : TemporalSource
  /-- Admitted primitive action. -/
  action : Action primitiveCount.word.toNat
  /-- Pre-update active controller values. -/
  values : Vector Binary32 primitiveCount.word.toNat
  /-- Nominal boundary masses or a served action's point mass. -/
  probabilities : Vector Binary32 primitiveCount.word.toNat
  /-- Option/primitive branch exploration observation. -/
  explored : Bool
  /-- Meta snapshot before subsequent credit. -/
  metaValues : Vector Binary32 metaCount.word.toNat
  /-- Present exactly when a meta decision was drawn at this boundary. -/
  metaDecision : Option (PolicyDecision metaCount)
  /-- Start of a new invocation, distinct from continuation. -/
  started : Option (Fin Acorn.FeatureConstants.skillCount)
  /-- Closing event, possibly followed by a new invocation in this decision. -/
  ended : Option EndEvent

/-- An option-selected action is the only path that uses option primitive credit. -/
def TemporalDecision.own (decision : TemporalDecision) : Bool :=
  match decision.source with | .option _ => false | .primitive | .explorationStart | .explorationContinuation => true

/-- Model operations are confined to the existing model storage. The argument
order preserves first-step omission and the raw host reward rather than its gain-centered value. -/
structure OptionModelOps (criterion : Criterion) (dimension : Dimension) where
  /-- Begin a model trajectory after the policy's transient clear. -/
  begin : Model dimension criterion → SwiftTd.ActiveSet dimension → Model dimension criterion
  /-- Credit a completed non-first transition at its pre-increment age. -/
  step : Model dimension criterion → SwiftTd.ActiveSet dimension → ModelAge → Binary32 → Model dimension criterion
  /-- Terminal model update uses the same sampled or maximum continuation as policy credit. -/
  terminal : Model dimension criterion → Binary32 → Binary32 → Model dimension criterion
  /-- Pre-dispatch observation at age zero. -/
  predict : Model dimension criterion → SwiftTd.ActiveSet dimension → ModelCache

/-- Planning may update only the meta policy and its observer fields. -/
structure PlanningResult (criterion : Criterion) (dimension : Dimension) where
  /-- Meta controller after the admitted planning work. -/
  controller : Controller (criterion.config .control) dimension metaCount.word.toNat
  /-- Current option model observations. -/
  predictions : Vector ModelCache Acorn.FeatureConstants.skillCount
  /-- Bounded machine work clock; updated by the concrete planning owner. -/
  steps : UInt64
  /-- Last planning errors. -/
  errors : Vector Binary32 Acorn.FeatureConstants.skillCount

/-- Required planning interface at a free boundary, before the meta snapshot. -/
abbrev PlanBoundary (config : Config) (criterion : Criterion) (dimension : Dimension) :=
  PlanningResult criterion dimension → Vector (Skill config criterion dimension) Acorn.FeatureConstants.skillCount →
    SwiftTd.ActiveSet dimension → RewardRate → PlanningResult criterion dimension

/-- Ending state carries the original activation and the current coordinate. -/
structure EndingPayload (mode : Bool) where
  /-- Frozen mutation mode and preceding coordinate. -/
  activation : OptionActivation mode
  /-- Current coordinate for the ending objective. -/
  potential : Potential
  /-- The decision's actual stopping cause. -/
  reason : OptionEnd

variable {mode : Bool}

/-- Learning start resets policy transient state and starts its model trajectory. -/
def Skill.beginTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    Skill config criterion dimension × (activation : OptionActivation learning) × OptionContinuation dimension activation :=
  let begun := skill.beginOption features potential learning rate
  let skill := if learning then { begun.1 with model := models.begin begun.1.model features } else begun.1
  (skill, begun.2)

/-- A first returned action has no completed model transition to credit. -/
def Skill.stepTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Skill config criterion dimension × OptionActivation mode × PolicyDecision primitiveCount × Rng.Xoshiro256 :=
  let result := skill.optionStep activation next reward gain rng
  let skill := if activation.learning && activation.age.val > 0 then
    { result.1 with model := models.step result.1.model next.features activation.age reward } else result.1
  (skill, result.2)

/-- The same terminal value reaches policy and model; only policy adds the
objective's attained bonus and inverse potential coordinate. -/
def Skill.endTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) : Skill config criterion dimension :=
  let result := skill.terminateOption ending.activation ending.potential reward terminal gain
  if ending.activation.learning then { result with model := models.terminal result.model reward terminal } else result

/-- Model callbacks cannot rewrite the policy update or alter the returned action. -/
theorem Skill.stepTemporal_policy {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporal models activation next reward gain rng).1.policy =
      (skill.optionStep activation next reward gain rng).1.policy ∧
    (skill.stepTemporal models activation next reward gain rng).2 =
      (skill.optionStep activation next reward gain rng).2 := by
  unfold stepTemporal
  split <;> exact ⟨rfl, rfl⟩

end Acorn.Features
