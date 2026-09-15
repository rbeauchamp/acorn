/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.AgentBaselineSemantics

/-!
# agent-baseline experiment construction

The evaluator has one opportunity record shared by every arm. Arm semantics
are a closed product of four independent switches, which makes each ablation's
scope an equality proof rather than a prose promise. The frozen-transition
result is polymorphic in the learning state: whatever the learner stores, its
constructor carries that value through unchanged.

These theorems concern the model definitions below. External results require
their own source provenance and correspondence to these transitions.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- The complete opportunity budget shared by every evaluator arm. -/
structure Opportunity where
  /-- Square world side. -/
  worldSide : ℕ
  /-- Goal occurrences in one curriculum cycle. -/
  goals : ℕ
  /-- Complete curriculum cycles. -/
  cycles : ℕ
  /-- Attempts available to each occurrence. -/
  attemptsPerGoal : ℕ
  /-- Environment steps available to one attempt. -/
  stepsPerAttempt : ℕ
  deriving DecidableEq, Repr

/-- The opportunity record built from the model constants. -/
def shippedOpportunity : Opportunity where
  worldSide := studyWorldSide
  goals := studyGoals
  cycles := studyCycles
  attemptsPerGoal := studyAttemptsPerGoal
  stepsPerAttempt := studyStepsPerAttempt

/-- Every arm receives the same opportunity object by construction. -/
def opportunityFor (_ : AgentBaselineArm) : Opportunity := shippedOpportunity

/-- Equal opportunity is definitional, for every pair of closed arms. -/
theorem every_arm_has_equal_opportunity (left right : AgentBaselineArm) :
    opportunityFor left = opportunityFor right := rfl

/-- Independent arm switches. -/
structure ArmSemantics where
  /-- Learner state may update. -/
  learns : Bool
  /-- Complete Reach relation enters the feature stream. -/
  reachRelation : Bool
  /-- Option/meta hierarchy participates in selection. -/
  temporalAbstraction : Bool
  /-- Dedicated deterministic pseudorandom primitive policy supplies actions. -/
  randomPolicy : Bool
  deriving DecidableEq, Repr

/-- Exact semantics of each closed evaluator arm. -/
def armSemantics : AgentBaselineArm → ArmSemantics
  | .final => ⟨true, true, true, false⟩
  | .random => ⟨false, false, false, true⟩
  | .frozen => ⟨false, true, true, false⟩
  | .ablatedGoalRelation => ⟨true, false, true, false⟩
  | .ablatedTemporalAbstraction => ⟨true, true, false, false⟩

/-- Tuple spelling of the four model switches. -/
def ArmSemantics.asTuple (semantics : ArmSemantics) : Bool × Bool × Bool × Bool :=
  (semantics.learns, semantics.reachRelation, semantics.temporalAbstraction,
    semantics.randomPolicy)

/-- The closed arm mapping equals the model constant table. -/
theorem arm_semantics_match_rust :
    AgentBaselineArm.all.map (fun arm => (armSemantics arm).asTuple) = studyArmSemantics := by
  decide

/-- Final and frozen differ only in permission to update learning state. -/
theorem frozen_is_exact_learning_ablation :
    (armSemantics .final).reachRelation = (armSemantics .frozen).reachRelation ∧
    (armSemantics .final).temporalAbstraction =
      (armSemantics .frozen).temporalAbstraction ∧
    (armSemantics .final).randomPolicy = (armSemantics .frozen).randomPolicy ∧
    (armSemantics .final).learns ≠ (armSemantics .frozen).learns := by
  decide

/-- The goal-relation arm removes only the Reach relation. -/
theorem goal_relation_is_exact_ablation :
    (armSemantics .final).learns = (armSemantics .ablatedGoalRelation).learns ∧
    (armSemantics .final).temporalAbstraction =
      (armSemantics .ablatedGoalRelation).temporalAbstraction ∧
    (armSemantics .final).randomPolicy =
      (armSemantics .ablatedGoalRelation).randomPolicy ∧
    (armSemantics .final).reachRelation ≠
      (armSemantics .ablatedGoalRelation).reachRelation := by
  decide

/-- The primitive-only arm removes only option/meta selection. -/
theorem temporal_abstraction_is_exact_ablation :
    (armSemantics .final).learns =
      (armSemantics .ablatedTemporalAbstraction).learns ∧
    (armSemantics .final).reachRelation =
      (armSemantics .ablatedTemporalAbstraction).reachRelation ∧
    (armSemantics .final).randomPolicy =
      (armSemantics .ablatedTemporalAbstraction).randomPolicy ∧
    (armSemantics .final).temporalAbstraction ≠
      (armSemantics .ablatedTemporalAbstraction).temporalAbstraction := by
  decide

/-- Every agent-backed arm receives one seed independent of held-out world identity. -/
def agentSeedFor (_worldSeed : ℕ) (_ : AgentBaselineArm) : ℕ := studyAgentSeed

/-- Identical initialization is derivational rather than checked after the
agents have been constructed. -/
theorem final_frozen_initialization_is_identical (seed : ℕ) :
    agentSeedFor seed .final = agentSeedFor seed .frozen := rfl

/-- Held-out world identity cannot leak into agent initialization. -/
theorem agent_initialization_is_world_seed_independent
    (left right : ℕ) (arm : AgentBaselineArm) :
    agentSeedFor left arm = agentSeedFor right arm := rfl

/-- State split required by the frozen evaluator contract. -/
structure EvaluatorState (Learning Behavior : Type) where
  /-- Weights, traces, lag registers, predictions and step sizes. -/
  learning : Learning
  /-- Exploration, RNG, elapsed duration and observational counters. -/
  behavior : Behavior

/-- A frozen step may evolve behavior but cannot construct a replacement
learning state. -/
def frozenTransition {Learning Behavior : Type} (step : Behavior → Behavior)
    (state : EvaluatorState Learning Behavior) : EvaluatorState Learning Behavior :=
  { learning := state.learning, behavior := step state.behavior }

/-- Every frozen transition preserves the entire abstract learning state. -/
theorem frozen_transition_preserves_learning {Learning Behavior : Type}
    (step : Behavior → Behavior) (state : EvaluatorState Learning Behavior) :
    (frozenTransition step state).learning = state.learning := rfl

/-- A structural agent configuration contains no held-out seed. -/
structure StructuralAgentConfig where
  /-- Fixed initialization seed. -/
  seed : ℕ
  /-- Number of sensory tilings. -/
  tilings : ℕ
  /-- Fixed imprint-unit count. -/
  imprintUnits : ℕ
  /-- Weight-space size. -/
  weightSpace : ℕ
  deriving DecidableEq, Repr

/-- Structural configuration used at every held-out seed. -/
def shippedStructuralAgentConfig : StructuralAgentConfig :=
  ⟨studyAgentSeed, studyAgentTilings, studyAgentImprintUnits, weightSpace⟩

/-- Structural agent configuration as a function of held-out world identity. -/
def structuralAgentConfigFor (_worldSeed : Fin studySeedCount) : StructuralAgentConfig :=
  shippedStructuralAgentConfig

/-- Held-out world identity cannot change initialization or feature-bank shape. -/
theorem structural_config_is_seed_independent (left right : Fin studySeedCount) :
    structuralAgentConfigFor left = structuralAgentConfigFor right := rfl

/-- Non-vacuity: the closed arm domain includes both comparison arms. -/
example : AgentBaselineArm.final ∈ AgentBaselineArm.all ∧
    AgentBaselineArm.frozen ∈ AgentBaselineArm.all := by
  decide

end AcornVerif
