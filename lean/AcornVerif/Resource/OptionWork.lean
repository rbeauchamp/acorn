/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Models
import AcornVerif.Resource.ModelWork

/-!
# Work of the options

The bounds of the costed definitions of an option's operations in `Acorn.Options`, with the
adapters the twins read, and twins of `Interest.potential` and of the operations of
`Acorn.Temporal` with the model operations of `modelOperations`, the ones selection runs. An option
is a policy controller over the world's actions, an option model and an interest; `Acorn.Cost`
names each costed definition.

Each `_within` theorem bounds a costed definition directly. Where that bound grows with an active
set's length, a `_within_capacity` theorem bounds the definition by a function of the configuration
alone, with the capacity of the dimension in place of the length: every active set fits the
dimension (`AcornVerif.CurrentLearner.active_cardinality`), and the set of every index fills it
(`AcornVerif.CurrentLearner.active_cardinality_attained`). An adapter pairs the executed
definition's value with that bound, and its `_costed` theorem checks the bound against the costed
definition. Each twin here is the executed operation's value with the work of a costed run that
follows the operation's control flow: the run tests the conditions the executed operation tests,
reads its intermediate values from the executed definitions, and charges the twin or adapter of
every operation that does work. These operations build their results through private constructors
(`OptionContinuation`, `OptionActivation`), so a run does not rebuild the result; the
correspondence of a run's calls with the executed definition is by reading here, and every call it
charges is a twin whose own value theorem checks it or an adapter whose `_costed` theorem does.
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

/-- The costed run of `Interest.potential`: a learned assignment's feature slot and, when it
has one, its membership test of the frame, or a declared value read. -/
def interestPotentialRun (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    Costed (Option Potential) :=
  match interest with
  | .learned assignment => Costed.via (some (assignment.potential features))
      (Costed.charge (κ .assignmentPotential) (match assignment.feature dimension with
        | none => Costed.pure ()
        | some _ => Costed.scanList .contains (κ .visit + κ .compare) features.indices ()))
  | .declared origin tag => Costed.op (κ .declaredPotential)
      (if origin = declared.origin then some (declared.values.get tag) else none)

theorem interestPotentialRun_val (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    (interestPotentialRun κ interest features declared).val =
      interest.potential features declared := by
  cases interest <;> rfl

/-- Twin of `Interest.potential`. -/
def interestPotential (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    Costed (Option Potential) :=
  Costed.via (interest.potential features declared)
    (interestPotentialRun κ interest features declared)

/-- Bound of a potential over `width` features. -/
abbrev potentialBound (κ : Costs) (width : Nat) : Nat :=
  κ .assignmentPotential + Library.contains.control (κ .visit + κ .compare) width +
    κ .declaredPotential

theorem interestPotential_work (κ : Costs) (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    (interestPotential κ interest features declared).work ≤
      potentialBound κ features.indices.length := by
  change (interestPotentialRun κ interest features declared).work ≤ _
  cases interest with
  | learned assignment =>
    refine Nat.le_trans (Costed.charge_work_le (cost := κ .assignmentPotential)
      (bound := Library.contains.control (κ .visit + κ .compare) features.indices.length) ?_) ?_
    · split
      · exact Nat.zero_le _
      · exact Nat.le_refl _
    · simp only [potentialBound]
      omega
  | declared origin tag =>
    simp only [interestPotentialRun, Costed.op, potentialBound]
    omega

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

/-- The costed run of `Skill.beginTemporal`: the option start, then a learning start's model
start. -/
def beginTemporalRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) : Costed Unit := do
  Costed.discard (beginOption κ skill features potential learning rate)
  let begun := skill.beginOption features potential learning rate
  Costed.ite (learning = true) (Costed.discard (modelBegin κ begun.1.model features))
    (Costed.pure ())

/-- Twin of `Skill.beginTemporal` with the model operations selection runs. -/
def beginTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    Costed (Skill actions config criterion dimension discounts ×
      (activation : OptionActivation learning) × OptionContinuation actions dimension activation) :=
  Costed.via (skill.beginTemporal (modelOperations criterion dimension) features potential
    learning rate) (beginTemporalRun κ skill features potential learning rate)

/-- Bound of an option start over `width` features. -/
abbrev beginTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  beginOptionBound κ rows capacity width + modelBeginBound κ capacity positions width

theorem beginTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (beginTemporal κ skill features potential learning rate).work ≤
      beginTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length := by
  change (beginTemporalRun κ skill features potential learning rate).work ≤ _
  unfold beginTemporalRun
  exact Costed.bind_work_le
    (Costed.discard_work_le (beginOption_work κ skill features potential learning rate)) fun _ =>
    Costed.ite_work_bound _ (Costed.discard_work_le (modelBegin_work κ
      (skill.beginOption features potential learning rate).1.model features))
      (Nat.zero_le _)

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
  have read := Library.map.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .read))
  have sum := Library.foldl.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .sumTerm))
  have second := pass_mono (visit := κ .visit) fits (Nat.le_refl (κ .secondElement))
  simp only [policyStepBound, creditStepBound, secondLoopBound]
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

/-- The costed run of `Skill.stepTemporal`: the option step, then a learning option's model
credit of the completed transition. -/
def stepTemporalRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) : Costed Unit := do
  Costed.discard (optionStep κ skill activation next reward gain rng)
  let stepped := skill.optionStep activation next reward gain rng
  Costed.ite ((activation.learning && activation.age.val > 0) = true)
    (Costed.discard (modelStep κ stepped.1.model next.features activation.age reward))
    (Costed.pure ())

/-- Twin of `Skill.stepTemporal` with the model operations selection runs. -/
def stepTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Costed (Skill actions config criterion dimension discounts × OptionActivation mode ×
      PersistentDecision actions × Rng.Xoshiro256) :=
  Costed.via (skill.stepTemporal (modelOperations criterion dimension) activation next reward
    gain rng) (stepTemporalRun κ skill activation next reward gain rng)

/-- Bound of an option step over `width` features. -/
abbrev stepTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  optionStepBound κ rows capacity width + modelStepBound κ capacity positions width

theorem stepTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (stepTemporal κ skill activation next reward gain rng).work ≤
      stepTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity next.features.indices.length := by
  change (stepTemporalRun κ skill activation next reward gain rng).work ≤ _
  unfold stepTemporalRun
  exact Costed.bind_work_le
    (Costed.discard_work_le (optionStep_work κ skill activation next reward gain rng)) fun _ =>
    Costed.ite_work_bound _ (Costed.discard_work_le (modelStep_work κ
      (skill.optionStep activation next reward gain rng).1.model next.features activation.age
      reward))
      (Nat.zero_le _)

/-- The costed run of `Skill.endTemporal`: a learning option's terminal policy credit and
its model's terminal step. -/
def endTemporalRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    Costed Unit := do
  Costed.discard (terminateOption κ skill ending.activation ending.potential reward terminal gain)
  let result := skill.terminateOption ending.activation ending.potential reward terminal gain
  Costed.ite (ending.activation.learning = true)
    (Costed.discard (modelTerminal κ result.model value features reward)) (Costed.pure ())

/-- Twin of `Skill.endTemporal` with the model operations selection runs. -/
def endTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    Costed (Skill actions config criterion dimension discounts) :=
  Costed.via (skill.endTemporal (modelOperations criterion dimension) value features ending
    reward terminal gain) (endTemporalRun κ skill value features ending reward terminal gain)

/-- Bound of an option's end over `width` features. -/
abbrev endTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  (κ .terminateOption + terminalCreditBound κ rows capacity) +
    modelTerminalWorkBound κ capacity positions width

theorem endTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    (endTemporal κ skill value features ending reward terminal gain).work ≤
      endTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length := by
  change (endTemporalRun κ skill value features ending reward terminal gain).work ≤ _
  unfold endTemporalRun
  exact Costed.bind_work_le (Costed.discard_work_le (terminateOption_work κ skill ending.activation
      ending.potential reward terminal gain)) fun _ =>
    Costed.ite_work_bound _ (Costed.discard_work_le (modelTerminal_work κ
      (skill.terminateOption ending.activation ending.potential reward terminal gain).model value
      features reward))
      (Nat.zero_le _)

/-! ## Off-policy trajectories -/

/-- The costed run of `Skill.stopFollowing`: the stopping credit of the policy and, along a
live run, the model's stopped trajectory. -/
def stopFollowingRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) : Costed Unit := do
  let stopping := (terminalCumulant (criterion.center reward 1 gain)
    (skill.interest.stoppingValue estimate potential) following.previous).sub skill.policy.vOld
  Costed.discard (stopStep κ skill.policy stopping)
  Costed.charge (κ .stopFollowing) (Costed.ite (following.live = true)
    (Costed.discard (modelStop κ skill.model value features reward)) (Costed.pure ()))

/-- Bound of a stopped off-policy trajectory over `width` features. -/
abbrev stopFollowingBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  stopBound κ rows capacity + (κ .stopFollowing + modelStopBound κ capacity positions width)

theorem stopFollowingRun_work (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) :
    (stopFollowingRun κ skill value features following potential estimate reward gain).work ≤
      stopFollowingBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length := by
  unfold stopFollowingRun
  exact Costed.bind_work_le (stopStep_work κ skill.policy ((terminalCumulant
    (criterion.center reward 1 gain) (skill.interest.stoppingValue estimate potential)
    following.previous).sub skill.policy.vOld)) fun _ =>
    Costed.charge_work_le (Costed.ite_work_bound _
      (Costed.discard_work_le (modelStop_work κ skill.model value features reward))
      (Nat.zero_le _))

/-- The costed run of `Skill.settleFollowing`: the stopping decision of the stored
trajectory, then its tree-backup stopping credit and model step, or its stop. -/
def settleFollowingRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) : Costed Unit :=
  match skill.following with
  | none => Costed.pure ()
  | some following => do
    Costed.discard
      (decideOption κ skill following.activation features potential goal estimate rate)
    match skill.decideOption following.activation features potential goal estimate rate with
    | .continuing next => do
      let error ← Costed.charge (κ .settleFollowing) (backupError κ skill.policy next.policy
        (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
          following.previous))
      Costed.discard (stopStep κ skill.policy error)
      Costed.ite (following.live = true)
        (Costed.discard (modelStep κ skill.model features following.age reward))
        (Costed.pure ())
    | .ending _ =>
      stopFollowingRun κ skill value features following potential estimate reward gain

/-- Bound of a settled off-policy trajectory over `width` features. -/
abbrev settleBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  decideBound κ rows capacity width + ((κ .settleFollowing + backupErrorBound κ rows) +
    (stopBound κ rows capacity + modelStepBound κ capacity positions width) +
    stopFollowingBound κ rows capacity positions width)

theorem settleFollowingRun_work (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) :
    (settleFollowingRun κ skill value features potential goal estimate rate reward gain).work ≤
      settleBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
        features.indices.length := by
  unfold settleFollowingRun
  split
  · exact Nat.zero_le _
  · rename_i following _
    refine Costed.bind_work_le
      (decideOption_work κ skill following.activation features potential goal estimate rate)
      fun _ => ?_
    split
    · rename_i next _
      refine Nat.le_trans (Costed.bind_work_le
        (Costed.charge_work_le (backupError_work κ skill.policy next.policy _)) fun _ =>
          Costed.bind_work_le (Costed.discard_work_le (stopStep_work κ skill.policy _)) fun _ =>
            Costed.ite_work_bound _ (Costed.discard_work_le
              (modelStep_work κ skill.model features following.age reward)) (Nat.zero_le _)) ?_
      omega
    · have ending := stopFollowingRun_work κ skill value features following potential estimate
        reward gain
      refine Nat.le_trans ending ?_
      omega

/-- Twin of `Skill.settleTemporal` with the model operations selection runs: a learning start
settles the stored trajectory. -/
def settleTemporal (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    Costed (Skill actions config criterion dimension discounts) :=
  Costed.via (skill.settleTemporal (modelOperations criterion dimension) value features potential
      goal estimate rate reward gain learning)
    (Costed.ite (learning = true)
      (settleFollowingRun κ skill value features potential goal estimate rate reward gain)
      (Costed.pure ()))

theorem settleTemporal_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (settleTemporal κ skill value features potential goal estimate rate reward gain learning).work ≤
      settleBound κ actions.word.toNat dimension.capacity (rankDimension dimension).capacity
        features.indices.length :=
  Nat.le_trans (Costed.ite_work_le _ _ _)
    (Nat.max_le.mpr ⟨settleFollowingRun_work κ skill value features potential goal estimate rate
      reward gain, Nat.zero_le _⟩)

end AcornVerif.Resource.Twin
