/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Acorn.Handcrafted.TemporalControl
import AcornVerif.Resource.ModelWork

/-!
# Work of the options

The bounds of the costed definitions of an option's operations in `Acorn.Options`, of its
operations with its model in `Acorn.Temporal` and of one slot's share of a followed frame
(`Handcrafted.followSlot`), at the model operations of `modelOperations`, the ones the agent runs,
with the adapters the twins read. An option is a policy controller over the world's actions, an
option model and an interest; `Acorn.Cost` names each costed definition.

Each `_within` theorem bounds a costed definition directly. Where that bound grows with an active
set's length, a `_within_capacity` theorem bounds the definition by a function of the configuration
alone, with the capacity of the dimension in place of the length: every active set fits the
dimension (`AcornVerif.CurrentLearner.active_cardinality`), and the set of every index fills it
(`AcornVerif.CurrentLearner.active_cardinality_attained`). An adapter pairs the executed
definition's value with that bound, and its `_costed` theorem checks the bound against the costed
definition.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {mode : Bool}

/-! ## Rates, policies and potentials -/

/-- The rate an option's source resolves to: its own learner's rate, or a fixed one, which reads
nothing. -/
theorem skillRateCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts) (rate : ConsumerRate) :
    (rate.resolveCosted fun _ => skill.policy.exploreRateCosted (count := actions)).Within κ
      (rateBound κ actions.word.toNat dimension.capacity) := by
  cases rate
  · exact exploreRateCosted_within κ skill.policy
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

/-- Bound of an option's frozen policy over `width` features. -/
abbrev frozenBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  rateBound κ rows capacity + (predictAllBound κ rows width + κ .snapshot)

theorem frozenPolicyCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    (skill.frozenPolicyCosted features rate).Within κ
      (frozenBound κ actions.word.toNat dimension.capacity features.indices.length) :=
  Acorn.Costed.bind_within (skillRateCosted_within κ skill rate)
    (snapshotCosted_within κ skill.policy features _)

/-- An option's frozen policy's bound grows with the number of features. -/
theorem frozenBound_mono (κ : Costs) (rows capacity : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    frozenBound κ rows capacity width ≤ frozenBound κ rows capacity limit :=
  Nat.add_le_add_left (Nat.add_le_add_right (Library.vectorMap.work_mono (Nat.le_refl _)
    (Library.foldl.work_mono fits (Nat.le_refl _))) _) _

/-- An option's frozen policy is within a function of the configuration alone: the number of
actions, the capacity of the dimension and the cost model. -/
theorem frozenPolicyCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    (skill.frozenPolicyCosted features rate).Within κ
      (frozenBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (frozenPolicyCosted_within κ skill features rate).mono
    (frozenBound_mono κ _ _ (CurrentLearner.active_cardinality features))

/-- Bound of a potential over `width` features. -/
abbrev potentialBound (κ : Costs) (width : Nat) : Nat :=
  κ .assignmentPotential + Library.contains.control (κ .visit + κ .compare) width +
    κ .declaredPotential

/-- An assignment's potential: its feature slot, then, when it has one, its membership test of
the frame. -/
theorem assignmentPotentialCosted_within (κ : Costs) (assignment : Assignment config)
    (active : SwiftTd.ActiveSet dimension) :
    (assignment.potentialCosted active).Within κ
      (κ .assignmentPotential + Library.contains.control (κ .visit + κ .compare)
        active.indices.length) := by
  unfold Assignment.potentialCosted
  refine Acorn.Costed.charge_within ?_
  split
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)
  · exact Acorn.Costed.mem_within _ _ _ κ

/-- An interest's potential: a learned assignment's potential, or a declared value read. -/
theorem potentialCosted_within (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    (interest.potentialCosted features declared).Within κ
      (potentialBound κ features.indices.length) := by
  cases interest with
  | learned assignment =>
    exact (Acorn.Costed.bind_within (assignmentPotentialCosted_within κ assignment features)
      (Acorn.Costed.pure_within _ κ)).mono (by simp only [potentialBound]; omega)
  | declared origin tag =>
    exact (Acorn.Costed.op_within _ _ κ).mono (by simp only [potentialBound]; omega)

/-- `Interest.potential` with its bound. -/
def interestPotential (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    Costed (Option Potential) :=
  ⟨interest.potential features declared, potentialBound κ features.indices.length⟩

theorem interestPotential_val (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    (interestPotential κ interest features declared).val =
      interest.potential features declared := rfl

theorem interestPotential_work (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    (interestPotential κ interest features declared).work ≤
      potentialBound κ features.indices.length :=
  Nat.le_refl _

theorem interestPotential_costed (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    (interest.potentialCosted features declared).Within κ
      (interestPotential κ interest features declared).work :=
  potentialCosted_within κ interest features declared

/-! ## Decisions and starts -/

/-- Bound of an option's termination decision over `width` features. -/
abbrev decideBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  frozenBound κ rows capacity width + (κ .decide + comparisonBound κ rows)

theorem decideOptionCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (skill.decideOptionCosted activation features potential goal estimate rate).Within κ
      (decideBound κ actions.word.toNat dimension.capacity features.indices.length) := by
  dsimp only [Skill.decideOptionCosted]
  refine Acorn.Costed.Within.mono
    (a := κ .decide + (rateBound κ actions.word.toNat dimension.capacity +
      ((predictAllBound κ actions.word.toNat features.indices.length + κ .snapshot) +
        (comparisonBound κ actions.word.toNat + 0)))) ?_
    (by simp only [decideBound, frozenBound]; omega)
  refine Acorn.Costed.charge_within (Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)) fun _ => ?_)
  refine Acorn.Costed.dite_within (fun _ => ?_)
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)
  refine Acorn.Costed.bind_within (skillRateCosted_within κ skill rate) ?_
  refine Acorn.Costed.bind_within (snapshotCosted_within κ skill.policy features _) ?_
  exact Acorn.Costed.bind_within (comparisonValueCosted_within κ criterion _)
    (Acorn.Costed.ite_within (fun _ => Acorn.Costed.pure_within _ κ)
      fun _ => Acorn.Costed.pure_within _ κ)

/-- An option's termination decision is within a function of the configuration alone: the number
of actions, the capacity of the dimension and the cost model. -/
theorem decideOptionCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (skill.decideOptionCosted activation features potential goal estimate rate).Within κ
      (decideBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (decideOptionCosted_within κ skill activation features potential goal estimate rate).mono
    (Nat.add_le_add_right
      (frozenBound_mono κ _ _ (CurrentLearner.active_cardinality features)) _)

/-- `Skill.decideOption` with its bound. -/
def decideOption (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    Costed (OptionDecision actions dimension activation) :=
  ⟨skill.decideOption activation features potential goal estimate rate,
    decideBound κ actions.word.toNat dimension.capacity features.indices.length⟩

theorem decideOption_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (decideOption κ skill activation features potential goal estimate rate).val =
      skill.decideOption activation features potential goal estimate rate := rfl

theorem decideOption_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (decideOption κ skill activation features potential goal estimate rate).work ≤
      decideBound κ actions.word.toNat dimension.capacity features.indices.length :=
  Nat.le_refl _

theorem decideOption_costed (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (skill.decideOptionCosted activation features potential goal estimate rate).Within κ
      (decideOption κ skill activation features potential goal estimate rate).work :=
  decideOptionCosted_within κ skill activation features potential goal estimate rate

/-- Bound of an option start's policy work over `width` features. -/
abbrev beginOptionBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  clearBound κ rows capacity + (κ .beginOption + frozenBound κ rows capacity width)

theorem beginOptionCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginOptionCosted features potential learning rate).Within κ
      (beginOptionBound κ actions.word.toNat dimension.capacity features.indices.length) := by
  dsimp only [Skill.beginOptionCosted]
  refine Acorn.Costed.Within.mono
    (a := (clearBound κ actions.word.toNat dimension.capacity + 0) +
      (κ .beginOption + (rateBound κ actions.word.toNat dimension.capacity +
        ((predictAllBound κ actions.word.toNat features.indices.length + κ .snapshot) + 0)))) ?_
    (by simp only [beginOptionBound, frozenBound]; omega)
  refine Acorn.Costed.bind_within (Acorn.Costed.ite_within
    (fun _ => Acorn.Costed.bind_within (clearCosted_within κ skill.policy)
      (Acorn.Costed.pure_within _ κ))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)) ?_
  exact Acorn.Costed.charge_within (Acorn.Costed.bind_within (skillRateCosted_within κ _ rate)
    (Acorn.Costed.bind_within (snapshotCosted_within κ _ features _)
      (Acorn.Costed.pure_within _ κ)))

/-- An option's start is within a function of the configuration alone: the number of actions, the
capacity of the dimension and the cost model. -/
theorem beginOptionCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginOptionCosted features potential learning rate).Within κ
      (beginOptionBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (beginOptionCosted_within κ skill features potential learning rate).mono
    (Nat.add_le_add_left (Nat.add_le_add_left
      (frozenBound_mono κ _ _ (CurrentLearner.active_cardinality features)) _) _)

/-- `Skill.beginOption` with its bound. -/
def beginOption (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    Costed (Skill actions config criterion dimension discounts ×
      (activation : OptionActivation learning) × OptionContinuation actions dimension activation) :=
  ⟨skill.beginOption features potential learning rate,
    beginOptionBound κ actions.word.toNat dimension.capacity features.indices.length⟩

theorem beginOption_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (beginOption κ skill features potential learning rate).val =
      skill.beginOption features potential learning rate := rfl

theorem beginOption_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (beginOption κ skill features potential learning rate).work ≤
      beginOptionBound κ actions.word.toNat dimension.capacity features.indices.length :=
  Nat.le_refl _

theorem beginOption_costed (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginOptionCosted features potential learning rate).Within κ
      (beginOption κ skill features potential learning rate).work :=
  beginOptionCosted_within κ skill features potential learning rate

/-! ## Steps and ends -/

/-- Bound of an option step's policy work over `width` features. -/
abbrev optionStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  persistentBound κ rows + (κ .optionStep + policyStepBound κ rows capacity width)

theorem optionStepCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.optionStepCosted activation next reward gain rng).Within κ
      (optionStepBound κ actions.word.toNat dimension.capacity next.features.indices.length) := by
  dsimp only [Skill.optionStepCosted]
  refine Acorn.Costed.Within.mono
    (a := persistentBound κ actions.word.toNat + ((κ .optionStep +
      policyStepBound κ actions.word.toNat dimension.capacity next.features.indices.length) + 0))
    ?_ (by simp only [optionStepBound]; omega)
  refine Acorn.Costed.bind_within (drawPersistentCosted_within κ next.policy rng) ?_
  exact Acorn.Costed.bind_within (Acorn.Costed.charge_within (Acorn.Costed.ite_within
      (fun _ => (Acorn.Costed.bind_within
        (persistentStepCosted_within κ skill.policy next.features next.policy _ _ _)
        (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _)))
      fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)))
    (Acorn.Costed.pure_within _ κ)

/-- A frozen-decision credit's bound grows with the number of features. -/
theorem policyStepBound_mono (κ : Costs) (rows capacity : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    policyStepBound κ rows capacity width ≤ policyStepBound κ rows capacity limit := by
  have := secondLoopBound_mono κ fits
  simp only [policyStepBound, creditStepBound]
  omega

/-- An option step is within a function of the configuration alone: the number of actions, the
capacity of the dimension and the cost model. -/
theorem optionStepCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.optionStepCosted activation next reward gain rng).Within κ
      (optionStepBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (optionStepCosted_within κ skill activation next reward gain rng).mono
    (Nat.add_le_add_left (Nat.add_le_add_left
      (policyStepBound_mono κ _ _ (CurrentLearner.active_cardinality next.features)) _) _)

/-- `Skill.optionStep` with its bound. -/
def optionStep (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Costed (Skill actions config criterion dimension discounts × OptionActivation mode ×
      PersistentDecision actions × Rng.Xoshiro256) :=
  ⟨skill.optionStep activation next reward gain rng,
    optionStepBound κ actions.word.toNat dimension.capacity next.features.indices.length⟩

theorem optionStep_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (optionStep κ skill activation next reward gain rng).val =
      skill.optionStep activation next reward gain rng := rfl

theorem optionStep_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (optionStep κ skill activation next reward gain rng).work ≤
      optionStepBound κ actions.word.toNat dimension.capacity next.features.indices.length :=
  Nat.le_refl _

theorem optionStep_costed (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.optionStepCosted activation next reward gain rng).Within κ
      (optionStep κ skill activation next reward gain rng).work :=
  optionStepCosted_within κ skill activation next reward gain rng

/-- The credit of a drawn decision: the step's records and a learning option's credit, the step's
work without its draw. -/
theorem optionCreditCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    (skill.optionCreditCosted activation next drawn reward gain).Within κ
      (κ .optionStep +
        policyStepBound κ actions.word.toNat dimension.capacity next.features.indices.length) :=
  Acorn.Costed.charge_within (Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within
      (persistentStepCosted_within κ skill.policy next.features next.policy drawn _ _)
      (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _)))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))

/-- The credit of a drawn decision is within a function of the configuration alone: the number of
actions, the capacity of the dimension and the cost model. -/
theorem optionCreditCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    (skill.optionCreditCosted activation next drawn reward gain).Within κ
      (κ .optionStep +
        policyStepBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (optionCreditCosted_within κ skill activation next drawn reward gain).mono
    (Nat.add_le_add_left
      (policyStepBound_mono κ _ _ (CurrentLearner.active_cardinality next.features)) _)

/-- An option's termination: its records and a learning option's terminal credit. -/
theorem terminateOptionCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) :
    (skill.terminateOptionCosted activation potential reward terminal gain).Within κ
      (κ .terminateOption + terminalCreditBound κ actions.word.toNat dimension.capacity) :=
  Acorn.Costed.charge_within (Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within (terminalCosted_within κ skill.policy _)
      (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _)))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))

/-- `Skill.terminateOption` with its bound. -/
def terminateOption (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) : Costed (Skill actions config criterion dimension discounts) :=
  ⟨skill.terminateOption activation potential reward terminal gain,
    κ .terminateOption + terminalCreditBound κ actions.word.toNat dimension.capacity⟩

theorem terminateOption_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) :
    (terminateOption κ skill activation potential reward terminal gain).val =
      skill.terminateOption activation potential reward terminal gain := rfl

theorem terminateOption_work (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) :
    (terminateOption κ skill activation potential reward terminal gain).work ≤
      κ .terminateOption + terminalCreditBound κ actions.word.toNat dimension.capacity :=
  Nat.le_refl _

theorem terminateOption_costed (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) :
    (skill.terminateOptionCosted activation potential reward terminal gain).Within κ
      (terminateOption κ skill activation potential reward terminal gain).work :=
  terminateOptionCosted_within κ skill activation potential reward terminal gain

/-! ## With the option's model

The operations of `Acorn.Temporal` at the model operations of `modelOperations`, the ones the
agent runs. -/

/-- A started option's continuation holds the start frame. -/
theorem beginTemporal_frame (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential learning rate).2.2.features = features := by
  cases learning <;> rfl

/-- Bound of an option start over `width` features. -/
abbrev beginTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  beginOptionBound κ rows capacity width + modelBeginBound κ capacity positions width

/-- An option's start: the option start, then a learning start's model start. -/
theorem beginTemporalCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginTemporalCosted (modelOperations criterion dimension) features potential learning
      rate).Within κ (beginTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length) := by
  unfold Skill.beginTemporalCosted
  refine Acorn.Costed.bind_within
    (beginOptionCosted_within κ skill features potential learning rate)
    (Acorn.Costed.Within.mono (Acorn.Costed.bind_within (Acorn.Costed.ite_within
      (bound := modelBeginBound κ dimension.capacity (rankDimension dimension).capacity
        features.indices.length) (fun _ => ?_)
      fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
      (Acorn.Costed.pure_within _ κ)) (Nat.le_of_eq (Nat.add_zero _)))
  cases (skill.beginOptionCosted features potential learning rate).val.1
  exact Acorn.Costed.Within.mono (Acorn.Costed.bind_within (modelBeginCosted_within κ _ features)
    (Acorn.Costed.pure_within _ κ)) (Nat.le_of_eq (Nat.add_zero _))

/-- Bound of an option step over `width` features. -/
abbrev stepTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  optionStepBound κ rows capacity width + modelStepBound κ capacity positions width

/-- An option's step: the option step, then a learning option's model credit of the completed
transition. -/
theorem stepTemporalCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporalCosted (modelOperations criterion dimension) activation next reward gain
      rng).Within κ (stepTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity next.features.indices.length) := by
  unfold Skill.stepTemporalCosted
  refine Acorn.Costed.bind_within (optionStepCosted_within κ skill activation next reward gain rng)
    ?_
  obtain ⟨⟨interest, policy, model, following, questions⟩, rest⟩ :=
    (skill.optionStepCosted activation next reward gain rng).val
  exact Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within (modelStepCosted_within κ model next.features
      activation.age reward) (Acorn.Costed.pure_within _ κ)).mono (Nat.le_refl _))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

/-- Bound of the credit of a drawn decision over `width` features. -/
abbrev creditTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  (κ .optionStep + policyStepBound κ rows capacity width) +
    modelStepBound κ capacity positions width

/-- The credit of a drawn decision: the option's credit, then a learning option's model credit of
the completed transition. -/
theorem creditTemporalCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    (skill.creditTemporalCosted (modelOperations criterion dimension) activation next drawn reward
      gain).Within κ (creditTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity next.features.indices.length) := by
  unfold Skill.creditTemporalCosted
  refine Acorn.Costed.bind_within
    (optionCreditCosted_within κ skill activation next drawn reward gain) ?_
  obtain ⟨interest, policy, model, following, questions⟩ :=
    (skill.optionCreditCosted activation next drawn reward gain).val
  exact Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within (modelStepCosted_within κ model next.features
      activation.age reward) (Acorn.Costed.pure_within _ κ)).mono (Nat.le_refl _))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

/-- Bound of an option's end over `width` features. -/
abbrev endTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  (κ .terminateOption + terminalCreditBound κ rows capacity) +
    modelTerminalWorkBound κ capacity positions width

/-- An option's end: its termination, then a learning option's model's terminal step. -/
theorem endTemporalCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    (skill.endTemporalCosted (modelOperations criterion dimension) value features ending reward
      terminal gain).Within κ (endTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length) := by
  unfold Skill.endTemporalCosted
  refine Acorn.Costed.bind_within (terminateOptionCosted_within κ skill ending.activation
    ending.potential reward terminal gain) ?_
  obtain ⟨interest, policy, model, following, questions⟩ :=
    (skill.terminateOptionCosted ending.activation ending.potential reward terminal gain).val
  exact Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within (modelTerminalCosted_within κ model value features reward)
      (Acorn.Costed.pure_within _ κ)).mono (Nat.le_refl _))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

/-- Bound of a stopped off-policy trajectory over `width` features. -/
abbrev stopFollowingBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  stopBound κ rows capacity + (κ .stopFollowing + modelStopBound κ capacity positions width)

/-- A stopped off-policy trajectory: the stopping credit of the policy and, along a live run, the
model's stopped trajectory. -/
theorem stopFollowingCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) :
    (skill.stopFollowingCosted (modelOperations criterion dimension) value features following
      potential estimate reward gain).Within κ (stopFollowingBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity features.indices.length) := by
  obtain ⟨interest, policy, model, linked, questions⟩ := skill
  unfold Skill.stopFollowingCosted
  exact Acorn.Costed.bind_within (stopStepCosted_within κ policy _)
    (Acorn.Costed.Within.mono (Acorn.Costed.bind_within (Acorn.Costed.charge_within
      (Acorn.Costed.ite_within (fun _ => modelStopCosted_within κ model value features reward)
        fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)))
      (Acorn.Costed.pure_within _ κ)) (Nat.le_of_eq (Nat.add_zero _)))

/-- Bound of a settled off-policy trajectory over `width` features. -/
abbrev settleBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  decideBound κ rows capacity width + ((κ .settleFollowing + backupErrorBound κ rows) +
    (stopBound κ rows capacity + modelStepBound κ capacity positions width) +
    stopFollowingBound κ rows capacity positions width)

/-- A settled off-policy trajectory: the stopping decision of the stored trajectory, then its
tree-backup stopping credit and a live run's model step, or its stop. -/
theorem settleFollowingCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) :
    (skill.settleFollowingCosted (modelOperations criterion dimension) value features potential
      goal estimate rate reward gain).Within κ (settleBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity features.indices.length) := by
  obtain ⟨interest, policy, model, linked, questions⟩ := skill
  unfold Skill.settleFollowingCosted
  cases linked with
  | none => exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)
  | some following =>
    refine Acorn.Costed.bind_within
      (b := (κ .settleFollowing + backupErrorBound κ actions.word.toNat) +
        (stopBound κ actions.word.toNat dimension.capacity + modelStepBound κ dimension.capacity
          (rankDimension dimension).capacity features.indices.length) + stopFollowingBound κ
          actions.word.toNat dimension.capacity (rankDimension dimension).capacity
          features.indices.length)
      (decideOptionCosted_within κ _ following.activation features potential goal estimate rate) ?_
    split
    · exact Acorn.Costed.Within.mono (Acorn.Costed.bind_within (Acorn.Costed.charge_within
        (backupErrorCosted_within κ policy _ _)) (Acorn.Costed.bind_within
          (stopStepCosted_within κ policy _) (Acorn.Costed.bind_within (Acorn.Costed.ite_within
            (fun _ => modelStepCosted_within κ model features following.age reward)
            fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
            (Acorn.Costed.pure_within _ κ)))) (by omega)
    · exact (stopFollowingCosted_within κ _ value features following potential estimate reward
        gain).mono (Nat.le_add_left _ _)

/-- An invocation start's settling: a learning start settles the stored trajectory. -/
theorem settleTemporalCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (skill.settleTemporalCosted (modelOperations criterion dimension) value features potential
      goal estimate rate reward gain learning).Within κ (settleBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity features.indices.length) :=
  Acorn.Costed.ite_within (fun _ => settleFollowingCosted_within κ skill value features potential
    goal estimate rate reward gain) fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

/-- Bound of a start whose first action is drawn, over `width` features. -/
abbrev startTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  settleBound κ rows capacity positions width +
    (beginTemporalBound κ rows capacity positions width +
      creditTemporalBound κ rows capacity positions width)

/-- A start whose first action is drawn: the settling, the start, then the drawn action's credit
over the start frame. -/
theorem startTemporalCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) (drawn : PersistentDecision actions) :
    (skill.startTemporalCosted (modelOperations criterion dimension) value features potential goal
      estimate rate reward gain learning drawn).Within κ (startTemporalBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity features.indices.length) := by
  unfold Skill.startTemporalCosted
  refine Acorn.Costed.bind_within (settleTemporalCosted_within κ skill value features potential
    goal estimate rate reward gain learning) (Acorn.Costed.bind_within
      (beginTemporalCosted_within κ _ features potential learning rate) ?_)
  exact (creditTemporalCosted_within κ _ _ _ drawn reward gain).mono (Nat.le_of_eq
    (congrArg (fun active : SwiftTd.ActiveSet dimension => creditTemporalBound κ _ _ _
      active.indices.length) (beginTemporal_frame _ _ features potential learning rate)))

/-- Bound of the start of a followed trajectory over `width` features. -/
abbrev startFollowingBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  frozenBound κ rows capacity width + (consistentBound κ rows +
    (startStepBound κ rows capacity width +
      (modelRestartBound κ capacity positions width + κ .startFollowing)))

/-- The start of a followed trajectory: the frozen policy, the consistency test, the policy's start
and, on a consistent frame, the model's restart. -/
theorem startFollowingCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat) (behaviour : Vector Binary32 actions.word.toNat) :
    (skill.startFollowingCosted (modelOperations criterion dimension) features potential rate
      action behaviour).Within κ (startFollowingBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length) := by
  obtain ⟨interest, policy, model, linked, questions⟩ := skill
  unfold Skill.startFollowingCosted
  refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
    (skillRateCosted_within κ ⟨interest, policy, model, linked, questions⟩ rate)
    (Acorn.Costed.bind_within (snapshotCosted_within κ policy features _)
      (Acorn.Costed.bind_within (consistentCosted_within κ _ behaviour)
        (Acorn.Costed.bind_within (startStepCosted_within κ policy features action _)
          (Acorn.Costed.bind_within (Acorn.Costed.ite_within
            (fun _ => modelRestartCosted_within κ model features _)
            fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
            (Acorn.Costed.op_within _ _ κ)))))) ?_
  simp only [startFollowingBound, frozenBound]
  omega

/-- Bound of a followed frame over `width` features. -/
abbrev followTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  decideBound κ rows capacity width + (((consistentBound κ rows +
    (modelStepBound κ capacity positions width + (backupStepBound κ rows rows capacity width +
      (modelRestartBound κ capacity positions width + κ .followStep)))) +
    stopFollowingBound κ rows capacity positions width) +
    startFollowingBound κ rows capacity positions width)

/-- A followed frame: a start where no trajectory is stored, otherwise the stored trajectory's
stopping decision, then the consistency test, a live run's model step, the tree-backup credit and
a restart, or the stop and a new start. -/
theorem followTemporalCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat) (behaviour : Vector Binary32 actions.word.toNat)
    (reward : Binary32) (gain : RewardRate) :
    (skill.followTemporalCosted (modelOperations criterion dimension) value features potential
      goal estimate rate action behaviour reward gain).Within κ
      (followTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length) := by
  obtain ⟨interest, policy, model, linked, questions⟩ := skill
  unfold Skill.followTemporalCosted
  cases linked with
  | none =>
    exact (startFollowingCosted_within κ _ features potential rate action behaviour).mono
      (by simp only [followTemporalBound]; omega)
  | some following =>
    refine Acorn.Costed.bind_within
      (decideOptionCosted_within κ _ following.activation features potential goal estimate rate) ?_
    split
    · exact Acorn.Costed.Within.mono (Acorn.Costed.bind_within
        (consistentCosted_within κ _ behaviour) (Acorn.Costed.bind_within (Acorn.Costed.ite_within
          (fun _ => modelStepCosted_within κ model features following.age reward)
          fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
          (Acorn.Costed.bind_within (backupStepCosted_within κ policy features _ action _)
            (Acorn.Costed.bind_within (Acorn.Costed.ite_within
              (fun _ => modelRestartCosted_within κ _ features following.age)
              fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
              (Acorn.Costed.op_within _ _ κ))))) (by omega)
    · exact Acorn.Costed.Within.mono (Acorn.Costed.bind_within
        (stopFollowingCosted_within κ _ value features following potential estimate reward gain)
        (startFollowingCosted_within κ _ features potential rate action behaviour)) (by omega)

/-! ### Bounds of the configuration -/

/-- A model start's bound grows with the number of features. -/
theorem modelBeginBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelBeginBound κ capacity positions width ≤ modelBeginBound κ capacity positions limit := by
  simp only [modelBeginBound, inputBound, beginBound, secondLoopBound, transitionBeginBound,
    rowInputBound, updateRowsBound, pass, Library.work, Library.control, Library.passes]
  gcongr

/-- A model step's bound grows with the number of features. -/
theorem modelStepBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelStepBound κ capacity positions width ≤ modelStepBound κ capacity positions limit := by
  simp only [modelStepBound, inputBound, stepBound, secondLoopBound, transitionStepBound,
    rowInputBound, updateRowsBound, pass, Library.work, Library.control, Library.passes]
  gcongr

/-- A model's terminal step's bound grows with the number of features. -/
theorem modelTerminalWorkBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelTerminalWorkBound κ capacity positions width ≤
      modelTerminalWorkBound κ capacity positions limit := by
  simp only [modelTerminalWorkBound, outcomeBound, indicatorBound, predictAllBound, Library.work,
    Library.control, Library.passes]
  gcongr

/-- A model's stopped trajectory's bound grows with the number of features. -/
theorem modelStopBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelStopBound κ capacity positions width ≤ modelStopBound κ capacity positions limit := by
  simp only [modelStopBound, outcomeBound, indicatorBound, predictAllBound, Library.work,
    Library.control, Library.passes]
  gcongr

/-- An option start's bound grows with the number of features. -/
theorem beginTemporalBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    beginTemporalBound κ rows capacity positions width ≤
      beginTemporalBound κ rows capacity positions limit := by
  have := frozenBound_mono κ rows capacity fits
  have := modelBeginBound_mono κ capacity positions fits
  simp only [beginTemporalBound, beginOptionBound]
  omega

/-- The bound of the credit of a drawn decision grows with the number of features. -/
theorem creditTemporalBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    creditTemporalBound κ rows capacity positions width ≤
      creditTemporalBound κ rows capacity positions limit := by
  have := policyStepBound_mono κ rows capacity fits
  have := modelStepBound_mono κ capacity positions fits
  simp only [creditTemporalBound]
  omega

/-- The bound of a settled off-policy trajectory grows with the number of features. -/
theorem settleBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    settleBound κ rows capacity positions width ≤ settleBound κ rows capacity positions limit := by
  have := frozenBound_mono κ rows capacity fits
  have := modelStepBound_mono κ capacity positions fits
  have := modelStopBound_mono κ capacity positions fits
  simp only [settleBound, decideBound, stopFollowingBound]
  omega

/-- An option's start is within a function of the configuration alone: the number of actions, the
capacities of the dimension and of its ranked positions, and the cost model. -/
theorem beginTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginTemporalCosted (modelOperations criterion dimension) features potential learning
      rate).Within κ (beginTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (beginTemporalCosted_within κ skill features potential learning rate).mono
    (beginTemporalBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

/-- An option's step is within a function of the configuration alone. -/
theorem stepTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporalCosted (modelOperations criterion dimension) activation next reward gain
      rng).Within κ (stepTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (stepTemporalCosted_within κ skill activation next reward gain rng).mono
    (Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_left
      (policyStepBound_mono κ _ _ (CurrentLearner.active_cardinality next.features)) _) _)
      (modelStepBound_mono κ _ _ (CurrentLearner.active_cardinality next.features)))

/-- The credit of a drawn decision with the option's model is within a function of the
configuration alone. -/
theorem creditTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    (skill.creditTemporalCosted (modelOperations criterion dimension) activation next drawn reward
      gain).Within κ (creditTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (creditTemporalCosted_within κ skill activation next drawn reward gain).mono
    (creditTemporalBound_mono κ _ _ _ (CurrentLearner.active_cardinality next.features))

/-- An option's end is within a function of the configuration alone. -/
theorem endTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    (skill.endTemporalCosted (modelOperations criterion dimension) value features ending reward
      terminal gain).Within κ (endTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (endTemporalCosted_within κ skill value features ending reward terminal gain).mono
    (Nat.add_le_add_left
      (modelTerminalWorkBound_mono κ _ _ (CurrentLearner.active_cardinality features)) _)

/-- A stopped off-policy trajectory is within a function of the configuration alone. -/
theorem stopFollowingCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) :
    (skill.stopFollowingCosted (modelOperations criterion dimension) value features following
      potential estimate reward gain).Within κ (stopFollowingBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity dimension.capacity) :=
  (stopFollowingCosted_within κ skill value features following potential estimate reward
    gain).mono (Nat.add_le_add_left (Nat.add_le_add_left
      (modelStopBound_mono κ _ _ (CurrentLearner.active_cardinality features)) _) _)

/-- A settled off-policy trajectory is within a function of the configuration alone. -/
theorem settleFollowingCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) :
    (skill.settleFollowingCosted (modelOperations criterion dimension) value features potential
      goal estimate rate reward gain).Within κ (settleBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity dimension.capacity) :=
  (settleFollowingCosted_within κ skill value features potential goal estimate rate reward
    gain).mono (settleBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

/-- An invocation start's settling is within a function of the configuration alone. -/
theorem settleTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (skill.settleTemporalCosted (modelOperations criterion dimension) value features potential
      goal estimate rate reward gain learning).Within κ (settleBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity dimension.capacity) :=
  (settleTemporalCosted_within κ skill value features potential goal estimate rate reward gain
    learning).mono (settleBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

/-- A start whose first action is drawn is within a function of the configuration alone. -/
theorem startTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) (drawn : PersistentDecision actions) :
    (skill.startTemporalCosted (modelOperations criterion dimension) value features potential goal
      estimate rate reward gain learning drawn).Within κ (startTemporalBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity dimension.capacity) := by
  have fits := CurrentLearner.active_cardinality features
  exact (startTemporalCosted_within κ skill value features potential goal estimate rate reward gain
    learning drawn).mono (Nat.add_le_add (settleBound_mono κ _ _ _ fits)
      (Nat.add_le_add (beginTemporalBound_mono κ _ _ _ fits)
        (creditTemporalBound_mono κ _ _ _ fits)))

/-- A model restart's bound grows with the number of features. -/
theorem modelRestartBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelRestartBound κ capacity positions width ≤
      modelRestartBound κ capacity positions limit := by
  simp only [modelRestartBound, inputBound, restartTrajectoryBound, stepBound, secondLoopBound,
    transitionRestartBound, rowInputBound, updateRowsBound, pass, Library.work, Library.control,
    Library.passes]
  gcongr

/-- The bound of the start of a followed trajectory grows with the number of features. -/
theorem startFollowingBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    startFollowingBound κ rows capacity positions width ≤
      startFollowingBound κ rows capacity positions limit := by
  have := frozenBound_mono κ rows capacity fits
  have := secondLoopBound_mono κ fits
  have := modelRestartBound_mono κ capacity positions fits
  simp only [startFollowingBound, startStepBound, creditStepBound]
  omega

/-- The bound of a followed frame grows with the number of features. -/
theorem followTemporalBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    followTemporalBound κ rows capacity positions width ≤
      followTemporalBound κ rows capacity positions limit := by
  have := frozenBound_mono κ rows capacity fits
  have := secondLoopBound_mono κ fits
  have := modelStepBound_mono κ capacity positions fits
  have := modelRestartBound_mono κ capacity positions fits
  have := modelStopBound_mono κ capacity positions fits
  have := startFollowingBound_mono κ rows capacity positions fits
  simp only [followTemporalBound, decideBound, backupStepBound, creditStepBound,
    stopFollowingBound]
  omega

/-- The start of a followed trajectory is within a function of the configuration alone. -/
theorem startFollowingCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat) (behaviour : Vector Binary32 actions.word.toNat) :
    (skill.startFollowingCosted (modelOperations criterion dimension) features potential rate
      action behaviour).Within κ (startFollowingBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (startFollowingCosted_within κ skill features potential rate action behaviour).mono
    (startFollowingBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

/-- A followed frame is within a function of the configuration alone. -/
theorem followTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat) (behaviour : Vector Binary32 actions.word.toNat)
    (reward : Binary32) (gain : RewardRate) :
    (skill.followTemporalCosted (modelOperations criterion dimension) value features potential
      goal estimate rate action behaviour reward gain).Within κ
      (followTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (followTemporalCosted_within κ skill value features potential goal estimate rate action
    behaviour reward gain).mono
    (followTemporalBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

/-! ## One slot's share of a followed frame -/

section Slot

variable {interface : Interface}

/-- Bound of one slot's share of a followed frame: its interest's potential, then its off-policy
following. -/
abbrev followSlotBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  potentialBound κ width + followTemporalBound κ rows capacity positions width

/-- One slot's share of a followed frame: nothing for the executing slot, otherwise its interest's
potential and, when the potential has a source, the slot's off-policy following. -/
theorem followSlotCosted_within (κ : Costs) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32)
    (gain : RewardRate) (executing : Bool)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (Handcrafted.followSlotCosted (modelOperations criterion dimension) value features declared
      goal estimate rate action behaviour reward gain executing skill).Within κ
      (followSlotBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length) := by
  unfold Handcrafted.followSlotCosted
  refine Acorn.Costed.ite_within (fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
    fun _ => Acorn.Costed.bind_within (potentialCosted_within κ skill.interest features declared) ?_
  split
  · exact followTemporalCosted_within κ skill value features _ goal estimate rate action behaviour
      reward gain
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

theorem followSlotBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    followSlotBound κ rows capacity positions width ≤
      followSlotBound κ rows capacity positions limit := by
  have := followTemporalBound_mono κ rows capacity positions fits
  have := Library.control_mono .contains (visit := κ .visit + κ .compare) fits
  simp only [followSlotBound, potentialBound]
  omega

/-- One slot's share of a followed frame is within a function of the configuration alone. -/
theorem followSlotCosted_within_capacity (κ : Costs) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action interface.actions.word.toNat)
    (behaviour : Vector Binary32 interface.actions.word.toNat) (reward : Binary32)
    (gain : RewardRate) (executing : Bool)
    (skill : Skill interface.actions config criterion dimension interface.layout) :
    (Handcrafted.followSlotCosted (modelOperations criterion dimension) value features declared
      goal estimate rate action behaviour reward gain executing skill).Within κ
      (followSlotBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (followSlotCosted_within κ value features declared goal estimate rate action behaviour reward
    gain executing skill).mono
    (followSlotBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

end Slot

/-! ### Adapters -/

/-- `Skill.beginTemporal` at the model operations the agent runs, with its bound. -/
def beginTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    Costed (Skill actions config criterion dimension discounts ×
      (activation : OptionActivation learning) × OptionContinuation actions dimension activation) :=
  ⟨skill.beginTemporal (modelOperations criterion dimension) features potential learning rate,
    beginTemporalBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
      features.indices.length⟩

theorem beginTemporal_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (beginTemporal κ skill features potential learning rate).val =
      skill.beginTemporal (modelOperations criterion dimension) features potential learning rate :=
  rfl

theorem beginTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (beginTemporal κ skill features potential learning rate).work ≤
      beginTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length :=
  Nat.le_refl _

theorem beginTemporal_costed (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginTemporalCosted (modelOperations criterion dimension) features potential learning
      rate).Within κ (beginTemporal κ skill features potential learning rate).work :=
  beginTemporalCosted_within κ skill features potential learning rate

/-- `Skill.stepTemporal` at the model operations the agent runs, with its bound. -/
def stepTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Costed (Skill actions config criterion dimension discounts × OptionActivation mode ×
      PersistentDecision actions × Rng.Xoshiro256) :=
  ⟨skill.stepTemporal (modelOperations criterion dimension) activation next reward gain rng,
    stepTemporalBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
      next.features.indices.length⟩

theorem stepTemporal_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (stepTemporal κ skill activation next reward gain rng).val =
      skill.stepTemporal (modelOperations criterion dimension) activation next reward gain rng :=
  rfl

theorem stepTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (stepTemporal κ skill activation next reward gain rng).work ≤
      stepTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity next.features.indices.length :=
  Nat.le_refl _

theorem stepTemporal_costed (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporalCosted (modelOperations criterion dimension) activation next reward gain
      rng).Within κ (stepTemporal κ skill activation next reward gain rng).work :=
  stepTemporalCosted_within κ skill activation next reward gain rng

/-- `Skill.endTemporal` at the model operations the agent runs, with its bound. -/
def endTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    Costed (Skill actions config criterion dimension discounts) :=
  ⟨skill.endTemporal (modelOperations criterion dimension) value features ending reward terminal
      gain,
    endTemporalBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
      features.indices.length⟩

theorem endTemporal_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    (endTemporal κ skill value features ending reward terminal gain).val =
      skill.endTemporal (modelOperations criterion dimension) value features ending reward
        terminal gain :=
  rfl

theorem endTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    (endTemporal κ skill value features ending reward terminal gain).work ≤
      endTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length :=
  Nat.le_refl _

theorem endTemporal_costed (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    (skill.endTemporalCosted (modelOperations criterion dimension) value features ending reward
      terminal gain).Within κ
      (endTemporal κ skill value features ending reward terminal gain).work :=
  endTemporalCosted_within κ skill value features ending reward terminal gain

/-- `Skill.settleTemporal` at the model operations the agent runs, with its bound. -/
def settleTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    Costed (Skill actions config criterion dimension discounts) :=
  ⟨skill.settleTemporal (modelOperations criterion dimension) value features potential goal
      estimate rate reward gain learning,
    settleBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
      features.indices.length⟩

theorem settleTemporal_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (settleTemporal κ skill value features potential goal estimate rate reward gain learning).val =
      skill.settleTemporal (modelOperations criterion dimension) value features potential goal
        estimate rate reward gain learning :=
  rfl

theorem settleTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (settleTemporal κ skill value features potential goal estimate rate reward gain learning).work ≤
      settleBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
        features.indices.length :=
  Nat.le_refl _

theorem settleTemporal_costed (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (skill.settleTemporalCosted (modelOperations criterion dimension) value features potential
      goal estimate rate reward gain learning).Within κ
      (settleTemporal κ skill value features potential goal estimate rate reward gain
        learning).work :=
  settleTemporalCosted_within κ skill value features potential goal estimate rate reward gain
    learning

end AcornVerif.Resource.Twin
