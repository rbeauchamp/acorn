/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Models
import AcornVerif.Resource.ModelWork

/-!
# Work of the options

Twins of an option's operations in `Acorn.Options` and `Acorn.Temporal`, with the model
operations of `modelOperations`, the ones selection runs. An option is a policy controller
over the world's actions, an option model and an interest. Each twin here is the executed
operation's value with the work of a costed run that follows the operation's control flow:
the run tests the conditions the executed operation tests, reads its intermediate values
from the executed definitions, and charges the twin of every operation that does work.
These operations build their results through private constructors (`OptionContinuation`,
`OptionActivation`), so a run does not rebuild the result; the correspondence of a run's
calls with the executed definition is by reading here, and every call it charges is a twin
whose own value theorem checks it.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount} {mode : Bool}

/-! ## Rates, policies and potentials -/

/-- The costed resolution of an option's rate: its own learner's rate, or a fixed one. -/
def skillRateRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (rate : ConsumerRate) : Costed SwiftTd.ExploreRate :=
  match rate with
  | .own => exploreRate (count := actions) κ skill.policy
  | .fixed value => Costed.pure value

theorem skillRateRun_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (rate : ConsumerRate) :
    (skillRateRun κ skill rate).val =
      rate.resolve fun _ => skill.policy.exploreRate (count := actions) := by
  cases rate <;> rfl

/-- Twin of the rate an option's source resolves to. -/
def skillRate (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (rate : ConsumerRate) : Costed SwiftTd.ExploreRate :=
  Costed.via (rate.resolve fun _ => skill.policy.exploreRate (count := actions))
    (skillRateRun κ skill rate)

theorem skillRate_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (rate : ConsumerRate) :
    (skillRate κ skill rate).work ≤ rateBound κ actions.word.toNat dimension.capacity := by
  change (skillRateRun κ skill rate).work ≤ _
  cases rate
  · exact exploreRate_work κ skill.policy
  · exact Nat.zero_le _

/-- Twin of `Skill.frozenPolicy`: the rate, then the snapshot of the option's policy. -/
def frozenPolicy (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    Costed (PolicySnapshot actions) := do
  let epsilon ← skillRate κ skill rate
  snapshot κ skill.policy features epsilon

theorem frozenPolicy_val (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    (frozenPolicy κ skill features rate).val = skill.frozenPolicy features rate := rfl

/-- Bound of an option's frozen policy over `width` features. -/
abbrev frozenBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  rateBound κ rows capacity + (predictAllBound κ rows width + κ .snapshot)

theorem frozenPolicy_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    (frozenPolicy κ skill features rate).work ≤
      frozenBound κ actions.word.toNat dimension.capacity features.indices.length :=
  Costed.bind_work_le (skillRate_work κ skill rate) fun epsilon =>
    snapshot_work κ skill.policy features epsilon

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

/-- The costed run of `Skill.decideOption`: the termination tests on every path and, below
the duration cap and without the goal, the frozen policy and its nominal value. -/
def decideRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (goal : Bool) (rate : ConsumerRate) : Costed Unit :=
  Costed.charge (κ .decide) (Costed.ite (goal = true) (Costed.pure ())
    (Costed.dite (activation.age.val < Acorn.FeatureConstants.optionMaxDuration)
      (fun _ => do
        let policy ← frozenPolicy κ skill features rate
        Costed.discard (comparisonValue κ criterion policy))
      (fun _ => Costed.pure ())))

/-- Twin of `Skill.decideOption`. -/
def decideOption (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    Costed (OptionDecision actions dimension activation) :=
  Costed.via (skill.decideOption activation features potential goal estimate rate)
    (decideRun κ skill activation features goal rate)

/-- Bound of an option's termination decision over `width` features. -/
abbrev decideBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  frozenBound κ rows capacity width + (κ .decide + comparisonBound κ rows)

theorem decideOption_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    (decideOption κ skill activation features potential goal estimate rate).work ≤
      decideBound κ actions.word.toNat dimension.capacity features.indices.length :=
  Nat.le_trans (Costed.charge_work_le (Nat.le_trans (Costed.ite_work_le _ _ _)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Costed.dite_work_le _ _ _ _
      (fun _ => Costed.bind_work_le (frozenPolicy_work κ skill features rate) fun policy =>
        comparisonValue_work κ criterion policy)
      (fun _ => Nat.zero_le _)⟩)))
    (Nat.le_of_eq (Nat.add_left_comm _ _ _))

/-- The costed run of `Skill.beginOption`: a learning start clears the policy's traces,
then the policy is frozen. -/
def beginOptionRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (learning : Bool) (rate : ConsumerRate) :
    Costed Unit := do
  Costed.ite (learning = true) (Costed.discard (clear κ skill.policy)) (Costed.pure ())
  let cleared := if learning then { skill with policy := skill.policy.clear } else skill
  Costed.charge (κ .beginOption) (Costed.discard (frozenPolicy κ cleared features rate))

/-- Bound of an option start's policy work over `width` features. -/
abbrev beginOptionBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  clearBound κ rows capacity + (κ .beginOption + frozenBound κ rows capacity width)

theorem beginOptionRun_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (learning : Bool) (rate : ConsumerRate) :
    (beginOptionRun κ skill features learning rate).work ≤
      beginOptionBound κ actions.word.toNat dimension.capacity features.indices.length :=
  Costed.bind_work_le (Nat.le_trans (Costed.ite_work_le _ _ _)
      (Nat.max_le.mpr ⟨clear_work κ skill.policy, Nat.zero_le _⟩))
    fun _ => Nat.add_le_add_left (frozenPolicy_work κ _ features rate) _

/-- The costed run of `Skill.beginTemporal`: the option start, then a learning start's model
start. -/
def beginTemporalRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) : Costed Unit := do
  beginOptionRun κ skill features learning rate
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
  exact Costed.bind_work_le (beginOptionRun_work κ skill features learning rate) fun _ =>
    Costed.ite_work_bound _ (Costed.discard_work_le (modelBegin_work κ _ features))
      (Nat.zero_le _)

/-! ## Steps and ends -/

/-- The costed run of `Skill.optionStep`: the persistent draw, then a learning option's
credit. -/
def optionStepRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) : Costed Unit := do
  Costed.discard (drawPersistent κ next.policy rng)
  let drawn := next.policy.drawPersistent rng
  Costed.charge (κ .optionStep) (Costed.ite (activation.learning = true)
    (Costed.discard (persistentStep κ skill.policy next.features next.policy drawn.1
      (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next.potential
        activation.previous) 1))
    (Costed.pure ()))

/-- Bound of an option step's policy work over `width` features. -/
abbrev optionStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  persistentBound κ rows + (κ .optionStep + policyStepBound κ rows capacity width)

theorem optionStepRun_work (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (optionStepRun κ skill activation next reward gain rng).work ≤
      optionStepBound κ actions.word.toNat dimension.capacity next.features.indices.length := by
  unfold optionStepRun
  exact Costed.bind_work_le (drawPersistent_work κ next.policy rng) fun _ =>
    Costed.charge_work_le (Costed.ite_work_bound _
      (Costed.discard_work_le (persistentStep_work κ skill.policy _ _ _ _ _)) (Nat.zero_le _))

/-- The costed run of `Skill.stepTemporal`: the option step, then a learning option's model
credit of the completed transition. -/
def stepTemporalRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) : Costed Unit := do
  optionStepRun κ skill activation next reward gain rng
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
  exact Costed.bind_work_le (optionStepRun_work κ skill activation next reward gain rng) fun _ =>
    Costed.ite_work_bound _ (Costed.discard_work_le (modelStep_work κ _ next.features _ reward))
      (Nat.zero_le _)

/-- The costed run of `Skill.endTemporal`: a learning option's terminal policy credit and
its model's terminal step. -/
def endTemporalRun (κ : Costs) (skill : Skill actions config criterion dimension discounts)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    Costed Unit := do
  Costed.charge (κ .terminateOption) (Costed.ite (ending.activation.learning = true)
    (Costed.discard (Twin.terminal κ skill.policy
      (terminalCumulant (criterion.center reward 1 gain)
        (skill.interest.stoppingValue terminal ending.potential) ending.activation.previous)))
    (Costed.pure ()))
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
  exact Costed.bind_work_le (Costed.charge_work_le (Costed.ite_work_bound _
      (Costed.discard_work_le (terminal_work κ skill.policy _)) (Nat.zero_le _))) fun _ =>
    Costed.ite_work_bound _ (Costed.discard_work_le (modelTerminal_work κ _ value features reward))
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
  exact Costed.bind_work_le (stopStep_work κ skill.policy _) fun _ =>
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
      Costed.charge (κ .settleFollowing) (Costed.discard (expected κ next.policy))
      Costed.discard (stopStep κ skill.policy (skill.policy.backupError (count := actions)
        next.policy (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma
          potential following.previous)))
      Costed.ite (following.live = true)
        (Costed.discard (modelStep κ skill.model features following.age reward))
        (Costed.pure ())
    | .ending _ =>
      stopFollowingRun κ skill value features following potential estimate reward gain

/-- Bound of a settled off-policy trajectory over `width` features. -/
abbrev settleBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  decideBound κ rows capacity width + ((κ .settleFollowing + expectedBound κ rows) +
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
        (Costed.charge_work_le (Costed.discard_work_le (expected_work κ next.policy))) fun _ =>
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
