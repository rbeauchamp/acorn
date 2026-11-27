import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Acorn.Handcrafted.TemporalControl
import AcornVerif.Resource.ModelWork

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {mode : Bool}

theorem skillRateCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts) (rate : ConsumerRate) :
    (rate.resolveCosted fun _ => skill.policy.exploreRateCosted (count := actions)).Within κ
      (rateBound κ actions.word.toNat dimension.capacity) := by
  cases rate
  · exact exploreRateCosted_within κ skill.policy
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

abbrev frozenBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  rateBound κ rows capacity + (predictAllBound κ rows width + κ .snapshot)

theorem frozenPolicyCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    (skill.frozenPolicyCosted features rate).Within κ
      (frozenBound κ actions.word.toNat dimension.capacity features.indices.length) :=
  Acorn.Costed.bind_within (skillRateCosted_within κ skill rate)
    (snapshotCosted_within κ skill.policy features _)

theorem frozenBound_mono (κ : Costs) (rows capacity : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    frozenBound κ rows capacity width ≤ frozenBound κ rows capacity limit :=
  Nat.add_le_add_left (Nat.add_le_add_right (Library.vectorMap.work_mono (Nat.le_refl _)
    (Library.foldl.work_mono fits (Nat.le_refl _))) _) _

theorem frozenPolicyCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    (skill.frozenPolicyCosted features rate).Within κ
      (frozenBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (frozenPolicyCosted_within κ skill features rate).mono
    (frozenBound_mono κ _ _ (CurrentLearner.active_cardinality features))

abbrev potentialBound (κ : Costs) (width : Nat) : Nat :=
  κ .assignmentPotential + Library.contains.control (κ .visit + κ .compare) width +
    κ .declaredPotential

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

theorem decideOptionCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (skill.decideOptionCosted activation features potential goal estimate rate).Within κ
      (decideBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (decideOptionCosted_within κ skill activation features potential goal estimate rate).mono
    (Nat.add_le_add_right
      (frozenBound_mono κ _ _ (CurrentLearner.active_cardinality features)) _)

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

theorem beginOptionCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginOptionCosted features potential learning rate).Within κ
      (beginOptionBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (beginOptionCosted_within κ skill features potential learning rate).mono
    (Nat.add_le_add_left (Nat.add_le_add_left
      (frozenBound_mono κ _ _ (CurrentLearner.active_cardinality features)) _) _)

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

theorem policyStepBound_mono (κ : Costs) (rows capacity : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    policyStepBound κ rows capacity width ≤ policyStepBound κ rows capacity limit := by
  have := secondLoopBound_mono κ fits
  simp only [policyStepBound, creditStepBound]
  omega

theorem optionStepCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.optionStepCosted activation next reward gain rng).Within κ
      (optionStepBound κ actions.word.toNat dimension.capacity dimension.capacity) :=
  (optionStepCosted_within κ skill activation next reward gain rng).mono
    (Nat.add_le_add_left (Nat.add_le_add_left
      (policyStepBound_mono κ _ _ (CurrentLearner.active_cardinality next.features)) _) _)

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

theorem beginTemporal_frame (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential learning rate).2.2.features = features := by
  cases learning <;> rfl

abbrev beginTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  beginOptionBound κ rows capacity width + modelBeginBound κ capacity positions width

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

abbrev stepTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  optionStepBound κ rows capacity width + modelStepBound κ capacity positions width

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
  obtain ⟨⟨interest, policy, model, following⟩, rest⟩ :=
    (skill.optionStepCosted activation next reward gain rng).val
  exact Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within (modelStepCosted_within κ model next.features
      activation.age reward) (Acorn.Costed.pure_within _ κ)).mono (Nat.le_refl _))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

abbrev creditTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  (κ .optionStep + policyStepBound κ rows capacity width) +
    modelStepBound κ capacity positions width

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
  obtain ⟨interest, policy, model, following⟩ :=
    (skill.optionCreditCosted activation next drawn reward gain).val
  exact Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within (modelStepCosted_within κ model next.features
      activation.age reward) (Acorn.Costed.pure_within _ κ)).mono (Nat.le_refl _))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

abbrev endTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  (κ .terminateOption + terminalCreditBound κ rows capacity) +
    modelTerminalWorkBound κ capacity positions width

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
  obtain ⟨interest, policy, model, following⟩ :=
    (skill.terminateOptionCosted ending.activation ending.potential reward terminal gain).val
  exact Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.bind_within (modelTerminalCosted_within κ model value features reward)
      (Acorn.Costed.pure_within _ κ)).mono (Nat.le_refl _))
    fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

abbrev stopFollowingBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  stopBound κ rows capacity + (κ .stopFollowing + modelStopBound κ capacity positions width)

theorem stopFollowingCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) :
    (skill.stopFollowingCosted (modelOperations criterion dimension) value features following
      potential estimate reward gain).Within κ (stopFollowingBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity features.indices.length) := by
  obtain ⟨interest, policy, model, linked⟩ := skill
  unfold Skill.stopFollowingCosted
  exact Acorn.Costed.bind_within (stopStepCosted_within κ policy _)
    (Acorn.Costed.Within.mono (Acorn.Costed.bind_within (Acorn.Costed.charge_within
      (Acorn.Costed.ite_within (fun _ => modelStopCosted_within κ model value features reward)
        fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)))
      (Acorn.Costed.pure_within _ κ)) (Nat.le_of_eq (Nat.add_zero _)))

abbrev settleBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  decideBound κ rows capacity width + ((κ .settleFollowing + backupErrorBound κ rows) +
    (stopBound κ rows capacity + modelStepBound κ capacity positions width) +
    stopFollowingBound κ rows capacity positions width)

theorem settleFollowingCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) :
    (skill.settleFollowingCosted (modelOperations criterion dimension) value features potential
      goal estimate rate reward gain).Within κ (settleBound κ actions.word.toNat
        dimension.capacity (rankDimension dimension).capacity features.indices.length) := by
  obtain ⟨interest, policy, model, linked⟩ := skill
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

abbrev startTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  settleBound κ rows capacity positions width +
    (beginTemporalBound κ rows capacity positions width +
      creditTemporalBound κ rows capacity positions width)

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

abbrev startFollowingBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  frozenBound κ rows capacity width + (consistentBound κ rows +
    (startStepBound κ rows capacity width +
      (modelRestartBound κ capacity positions width + κ .startFollowing)))

theorem startFollowingCosted_within (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat) (behaviour : Vector Binary32 actions.word.toNat) :
    (skill.startFollowingCosted (modelOperations criterion dimension) features potential rate
      action behaviour).Within κ (startFollowingBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length) := by
  obtain ⟨interest, policy, model, linked⟩ := skill
  unfold Skill.startFollowingCosted
  refine Acorn.Costed.Within.mono (Acorn.Costed.bind_within
    (skillRateCosted_within κ ⟨interest, policy, model, linked⟩ rate)
    (Acorn.Costed.bind_within (snapshotCosted_within κ policy features _)
      (Acorn.Costed.bind_within (consistentCosted_within κ _ behaviour)
        (Acorn.Costed.bind_within (startStepCosted_within κ policy features action _)
          (Acorn.Costed.bind_within (Acorn.Costed.ite_within
            (fun _ => modelRestartCosted_within κ model features _)
            fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
            (Acorn.Costed.op_within _ _ κ)))))) ?_
  simp only [startFollowingBound, frozenBound]
  omega

abbrev followTemporalBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  decideBound κ rows capacity width + (((consistentBound κ rows +
    (modelStepBound κ capacity positions width + (backupStepBound κ rows rows capacity width +
      (modelRestartBound κ capacity positions width + κ .followStep)))) +
    stopFollowingBound κ rows capacity positions width) +
    startFollowingBound κ rows capacity positions width)

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
  obtain ⟨interest, policy, model, linked⟩ := skill
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

theorem modelBeginBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelBeginBound κ capacity positions width ≤ modelBeginBound κ capacity positions limit := by
  simp only [modelBeginBound, inputBound, beginBound, secondLoopBound, transitionBeginBound,
    rowInputBound, updateRowsBound, pass, Library.work, Library.control, Library.passes]
  gcongr

theorem modelStepBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelStepBound κ capacity positions width ≤ modelStepBound κ capacity positions limit := by
  simp only [modelStepBound, inputBound, stepBound, secondLoopBound, transitionStepBound,
    rowInputBound, updateRowsBound, pass, Library.work, Library.control, Library.passes]
  gcongr

theorem modelTerminalWorkBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelTerminalWorkBound κ capacity positions width ≤
      modelTerminalWorkBound κ capacity positions limit := by
  simp only [modelTerminalWorkBound, outcomeBound, indicatorBound, predictAllBound, Library.work,
    Library.control, Library.passes]
  gcongr

theorem modelStopBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelStopBound κ capacity positions width ≤ modelStopBound κ capacity positions limit := by
  simp only [modelStopBound, outcomeBound, indicatorBound, predictAllBound, Library.work,
    Library.control, Library.passes]
  gcongr

theorem beginTemporalBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    beginTemporalBound κ rows capacity positions width ≤
      beginTemporalBound κ rows capacity positions limit := by
  have := frozenBound_mono κ rows capacity fits
  have := modelBeginBound_mono κ capacity positions fits
  simp only [beginTemporalBound, beginOptionBound]
  omega

theorem creditTemporalBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    creditTemporalBound κ rows capacity positions width ≤
      creditTemporalBound κ rows capacity positions limit := by
  have := policyStepBound_mono κ rows capacity fits
  have := modelStepBound_mono κ capacity positions fits
  simp only [creditTemporalBound]
  omega

theorem settleBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    settleBound κ rows capacity positions width ≤ settleBound κ rows capacity positions limit := by
  have := frozenBound_mono κ rows capacity fits
  have := modelStepBound_mono κ capacity positions fits
  have := modelStopBound_mono κ capacity positions fits
  simp only [settleBound, decideBound, stopFollowingBound]
  omega

theorem beginTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (skill.beginTemporalCosted (modelOperations criterion dimension) features potential learning
      rate).Within κ (beginTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (beginTemporalCosted_within κ skill features potential learning rate).mono
    (beginTemporalBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

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

theorem creditTemporalCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    (skill.creditTemporalCosted (modelOperations criterion dimension) activation next drawn reward
      gain).Within κ (creditTemporalBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (creditTemporalCosted_within κ skill activation next drawn reward gain).mono
    (creditTemporalBound_mono κ _ _ _ (CurrentLearner.active_cardinality next.features))

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

theorem modelRestartBound_mono (κ : Costs) (capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    modelRestartBound κ capacity positions width ≤
      modelRestartBound κ capacity positions limit := by
  simp only [modelRestartBound, inputBound, restartTrajectoryBound, stepBound, secondLoopBound,
    transitionRestartBound, rowInputBound, updateRowsBound, pass, Library.work, Library.control,
    Library.passes]
  gcongr

theorem startFollowingBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    startFollowingBound κ rows capacity positions width ≤
      startFollowingBound κ rows capacity positions limit := by
  have := frozenBound_mono κ rows capacity fits
  have := secondLoopBound_mono κ fits
  have := modelRestartBound_mono κ capacity positions fits
  simp only [startFollowingBound, startStepBound, creditStepBound]
  omega

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

theorem startFollowingCosted_within_capacity (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat) (behaviour : Vector Binary32 actions.word.toNat) :
    (skill.startFollowingCosted (modelOperations criterion dimension) features potential rate
      action behaviour).Within κ (startFollowingBound κ actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  (startFollowingCosted_within κ skill features potential rate action behaviour).mono
    (startFollowingBound_mono κ _ _ _ (CurrentLearner.active_cardinality features))

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

section Slot

variable {interface : Interface}

abbrev followSlotBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  potentialBound κ width + (followTemporalBound κ rows capacity positions width + κ .unlinkSlot)

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
  refine Acorn.Costed.ite_within
    (fun _ => (Acorn.Costed.op_within _ _ κ).mono (by simp only [followSlotBound]; omega))
    fun _ => Acorn.Costed.bind_within (potentialCosted_within κ skill.interest features declared) ?_
  split
  · exact (followTemporalCosted_within κ skill value features _ goal estimate rate action behaviour
      reward gain).mono (Nat.le_add_right _ _)
  · exact (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _)

theorem followSlotBound_mono (κ : Costs) (rows capacity positions : Nat) {width limit : Nat}
    (fits : width ≤ limit) :
    followSlotBound κ rows capacity positions width ≤
      followSlotBound κ rows capacity positions limit := by
  have := followTemporalBound_mono κ rows capacity positions fits
  have := Library.control_mono .contains (visit := κ .visit + κ .compare) fits
  simp only [followSlotBound, potentialBound]
  omega

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

section Table

open Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile}

abbrev metaRateBound (κ : Costs) (rows capacity : Nat) : Nat :=
  rateBound κ metaCount.word.toNat capacity + rateBound κ rows capacity

theorem controllerCosted_within {policy : RatePolicy} (κ : Costs) (rate : RateState policy)
    {own primitive : Unit → Acorn.Costed SwiftTd.ExploreRate} {bound : Nat}
    (ownFits : (own ()).Within κ bound) (primitiveFits : (primitive ()).Within κ bound)
    (close : κ .rateClose ≤ bound) : (rate.controllerCosted own primitive).Within κ bound := by
  cases rate
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)
  · exact ownFits
  · exact primitiveFits
  · exact (Acorn.Costed.op_within _ _ κ).mono close

theorem skillCosted_within {policy : RatePolicy} (κ : Costs) (rate : RateState policy)
    {primitive : Unit → Acorn.Costed SwiftTd.ExploreRate} {bound : Nat}
    (primitiveFits : (primitive ()).Within κ bound) :
    (rate.skillCosted primitive).Within κ bound := by
  cases rate
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)
  · exact (Acorn.Costed.bind_within primitiveFits (Acorn.Costed.pure_within _ κ)).mono
      (Nat.le_of_eq (Nat.add_zero _))
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

theorem primitiveRateCosted_within (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.primitiveRateCosted.Within κ
      (rateBound κ interface.actions.word.toNat dimension.capacity) :=
  exploreRateCosted_within κ _

theorem metaRateCosted_within (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.metaRateCosted.Within κ
      (metaRateBound κ interface.actions.word.toNat dimension.capacity) :=
  controllerCosted_within κ state.rate
    ((exploreRateCosted_within (count := metaCount) κ _).mono (Nat.le_add_right _ _))
    ((primitiveRateCosted_within κ state).mono (Nat.le_add_left _ _))
    (by simp only [metaRateBound, rateBound]; omega)

theorem skillSourceCosted_within (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.skillRateCosted.Within κ
      (rateBound κ interface.actions.word.toNat dimension.capacity) :=
  skillCosted_within κ state.rate (primitiveRateCosted_within κ state)

theorem valueFunctionCosted_within (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.valueFunctionCosted.Within κ
      (metaRateBound κ interface.actions.word.toNat dimension.capacity) :=
  (Acorn.Costed.bind_within (metaRateCosted_within κ state)
    (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _))

abbrev stoppingEstimateBound (κ : Costs) (rows capacity : Nat) : Nat :=
  metaRateBound κ rows capacity + comparisonBound κ metaCount.word.toNat

theorem stoppingEstimateCosted_within (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (decision : TemporalDecision interface.actions) :
    (state.stoppingEstimateCosted decision).Within κ
      (stoppingEstimateBound κ interface.actions.word.toNat dimension.capacity) := by
  unfold TemporalControl.stoppingEstimateCosted
  split
  · exact (comparisonValueCosted_within κ criterion _).mono (Nat.le_add_left _ _)
  · exact Acorn.Costed.bind_within (metaRateCosted_within κ state)
      (comparisonValueCosted_within κ criterion _)

abbrev followOptionsBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  stoppingEstimateBound κ rows capacity + (rateBound κ rows capacity +
    (metaRateBound κ rows capacity +
      (Library.mapFinIdx.work (κ .visit) Acorn.FeatureConstants.skillCount
        (followSlotBound κ rows capacity positions width) + κ .followTable)))

theorem followOptionsCosted_within_slots (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) {width : Nat}
    (slots : ∀ (value : ValueFunction criterion dimension) (estimate : Binary32)
      (rate : ConsumerRate) (gain : RewardRate) (executing : Bool)
      (skill : Skill interface.actions config criterion dimension interface.layout),
      (followSlotCosted (modelOperations criterion dimension) value features declared goal
        estimate rate decision.action decision.probabilities reward gain executing skill).Within κ
        (followSlotBound κ interface.actions.word.toNat dimension.capacity
          (rankDimension dimension).capacity width)) :
    (state.followOptionsCosted (modelOperations criterion dimension) features declared reward
      goal decision).Within κ
      (followOptionsBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity width) := by
  unfold TemporalControl.followOptionsCosted
  refine Acorn.Costed.ite_within (fun _ => ?_)
    fun _ => (Acorn.Costed.op_within _ _ κ).mono (by simp only [followOptionsBound]; omega)
  refine Acorn.Costed.bind_within (stoppingEstimateCosted_within κ state decision) ?_
  refine Acorn.Costed.bind_within (skillSourceCosted_within κ state) ?_
  refine Acorn.Costed.bind_within (valueFunctionCosted_within κ state) ?_
  exact Acorn.Costed.bind_within
    (Acorn.Costed.mapFinIdx_within fun _ => slots _ _ _ _ _ _) (Acorn.Costed.op_within _ _ κ)

theorem followOptionsCosted_within (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    (state.followOptionsCosted (modelOperations criterion dimension) features declared reward
      goal decision).Within κ
      (followOptionsBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length) :=
  followOptionsCosted_within_slots κ state features declared reward goal decision
    fun value estimate rate gain executing skill =>
      followSlotCosted_within κ value features declared goal estimate rate decision.action
        decision.probabilities reward gain executing skill

theorem followOptionsCosted_within_capacity (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    (state.followOptionsCosted (modelOperations criterion dimension) features declared reward
      goal decision).Within κ
      (followOptionsBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity dimension.capacity) :=
  followOptionsCosted_within_slots κ state features declared reward goal decision
    fun value estimate rate gain executing skill =>
      followSlotCosted_within_capacity κ value features declared goal estimate rate
        decision.action decision.probabilities reward gain executing skill

end Table

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
