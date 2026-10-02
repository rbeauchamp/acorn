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
dispatch proofs describe the storage boundaries.

An option that is not executing follows the stream through `Skill.followTemporal`:
its policy and model learn off-policy from the action actually taken, under the
executing option's stopping decision applied to the stored trajectory. When the
option starts executing, `Skill.settleFollowing` credits the transition it was
following before the invocation start clears its trajectory state.
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
  /-- Start a trajectory at an age for an option that is not executing, on existing storage. -/
  restart : Model dimension criterion → SwiftTd.ActiveSet dimension → ModelAge → Model dimension criterion
  /-- Close such a trajectory with the terminal entry's reward and continuation. -/
  stop : Model dimension criterion → Binary32 → Binary32 → Model dimension criterion

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

/-- A first returned action has no completed model transition to credit. The
policy step's result is taken apart before the model is credited, and
`Skill.stepTemporal_eq` proves the result equal to the listed composition. The
ordering is meant to let the runtime reuse the model learners' storage when the
skill is referenced nowhere else; that is a performance expectation, not a
proved property. -/
def Skill.stepTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Skill config criterion dimension × OptionActivation mode × PolicyDecision primitiveCount × Rng.Xoshiro256 :=
  let (stepped, rest) := skill.optionStep activation next reward gain rng
  let skill := if activation.learning && activation.age.val > 0 then
    { stepped with model := models.step stepped.model next.features activation.age reward }
    else stepped
  (skill, rest)

/-- Taking the policy step's result apart preserves the composition, for every
skill, activation, reward word and random state. -/
theorem Skill.stepTemporal_eq {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    skill.stepTemporal models activation next reward gain rng =
      let result := skill.optionStep activation next reward gain rng
      let skill := if activation.learning && activation.age.val > 0 then
        { result.1 with model := models.step result.1.model next.features activation.age reward }
        else result.1
      (skill, result.2) := rfl

/-- The same terminal value reaches policy and model; only policy adds the
objective's attained bonus and inverse potential coordinate. -/
def Skill.endTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) : Skill config criterion dimension :=
  let result := skill.terminateOption ending.activation ending.potential reward terminal gain
  if ending.activation.learning then { result with model := models.terminal result.model reward terminal } else result

/-- Link an option that is not executing to the current frame. Every earlier trace
is released before the taken action's traces are laid, so no earlier transition is
credited. The model starts a trajectory at age zero only when the frame's action
was selected with the option's own distribution. -/
def Skill.startFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) : Skill config criterion dimension :=
  let frozen := skill.policy.snapshot (count := primitiveCount) features
    (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount))
  let consistent := frozen.consistent behaviour
  let ⟨interest, policy, model, _⟩ := skill
  ⟨interest,
    policy.startStep (actions := primitiveCount.word.toNat) features action
      (frozen.values.get action),
    if consistent then models.restart model features ⟨0, by decide⟩ else model,
    some ⟨⟨1, by decide⟩, consistent, potential⟩⟩

/-- Stop the stored trajectory where the option's stopping decision fires: the
policy is credited the stopping value at zero trace decay and a live model
trajectory is closed toward the terminal targets. Nothing stays eligible and the
skill is linked to no frame. -/
def Skill.stopFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) : Skill config criterion dimension :=
  let stopping := (terminalCumulant (criterion.center reward 1 gain)
    (skill.interest.stoppingValue estimate potential) following.previous).sub skill.policy.vOld
  let ⟨interest, policy, model, _⟩ := skill
  ⟨interest, policy.stopStep stopping,
    if following.live then models.stop model reward estimate else model, none⟩

/-- One frame of an option that is not executing, learned from the action actually
taken. Sutton, Machado et al., *Reward-respecting subtasks for model-based
reinforcement learning*, Artificial Intelligence 324 (2023), 104001,
arXiv:2202.03466v4, §3, equation (10), and §4, equation (17), update every
subtask's option and model on every step, stopping where the option's own
stopping function does. Acorn applies the executing option's stopping decision to
the stored trajectory, whose age advances on every followed frame, and then:

* the action-value policy takes tree-backup credit (`Controller.backupStep`), so
  every taken action updates it;
* the model, a function of state and age alone, credits the completed transition
  when the preceding frame's action was selected with the option's own
  distribution (Sutton, Precup & Singh, Artificial Intelligence 112 (1999), §5,
  p. 202), which is equation (17) where its importance ratio is one, and starts a
  trajectory at the current age when such a run begins;
* a stop credits the stopping value at zero trace decay and the option continues
  from the current frame, as equation (10) continues after `β = 1`.

The stopping estimate is the caller's nominal meta value in both criteria; no
meta action is drawn for an option that is not executing. -/
def Skill.followTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat)
    (reward : Binary32) (gain : RewardRate) : Skill config criterion dimension :=
  match skill.following with
  | none => skill.startFollowing models features potential rate action behaviour
  | some following =>
    match skill.decideOption following.activation features potential goal estimate rate with
    | .continuing next =>
      let consistent := next.policy.consistent behaviour
      let ⟨interest, policy, model, _⟩ := skill
      let credited := if following.live then
        models.step model features following.age reward else model
      ⟨interest,
        policy.backupStep (count := primitiveCount) features next.policy action
          (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
            following.previous),
        if consistent && !following.live then models.restart credited features following.age
          else credited,
        some ⟨ModelAge.advance following.age, consistent, potential⟩⟩
    | .ending _ =>
      (skill.stopFollowing models following potential estimate reward gain).startFollowing
        models features potential rate action behaviour

/-- Close the stored trajectory at the frame where the option starts executing.
The completed transition is credited exactly as on a followed frame: the stopping
value where the stopping decision fires, the tree-backup error otherwise, and the
model's step along a live run. No new trace is laid and nothing stays eligible,
because the invocation start begins a fresh trajectory. -/
def Skill.settleFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate) :
    Skill config criterion dimension :=
  match skill.following with
  | none => skill
  | some following =>
    match skill.decideOption following.activation features potential goal estimate rate with
    | .continuing next =>
      let ⟨interest, policy, model, _⟩ := skill
      ⟨interest,
        policy.stopStep (policy.backupError (count := primitiveCount) next.policy
          (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
            following.previous)),
        if following.live then models.step model features following.age reward else model,
        none⟩
    | .ending _ => skill.stopFollowing models following potential estimate reward gain

/-- A frozen invocation start settles nothing; a learning one settles the stored
trajectory first. -/
def Skill.settleTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) : Skill config criterion dimension :=
  if learning then skill.settleFollowing models features potential goal estimate rate reward gain
  else skill

/-- Model callbacks cannot rewrite the policy update or alter the returned action. -/
theorem Skill.stepTemporal_policy {config : Config} {criterion : Criterion} {dimension : Dimension}
    (skill : Skill config criterion dimension) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporal models activation next reward gain rng).1.policy =
      (skill.optionStep activation next reward gain rng).1.policy ∧
    (skill.stepTemporal models activation next reward gain rng).2 =
      (skill.optionStep activation next reward gain rng).2 := by
  rw [Skill.stepTemporal_eq]
  split <;> exact ⟨rfl, rfl⟩

/-- Following never replaces the objective whose potential was supplied. -/
theorem Skill.startFollowing_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (rate : ConsumerRate) (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) :
    (skill.startFollowing models features potential rate action behaviour).interest =
      skill.interest := rfl

/-- A stop retains the objective and leaves the skill linked to no frame. -/
theorem Skill.stopFollowing_owner {config : Config} {criterion : Criterion}
    {dimension : Dimension} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (following : Following) (potential : Potential)
    (estimate reward : Binary32) (gain : RewardRate) :
    (skill.stopFollowing models following potential estimate reward gain).interest =
        skill.interest ∧
      (skill.stopFollowing models following potential estimate reward gain).following = none :=
  ⟨rfl, rfl⟩

/-- Every followed frame retains the option's objective, on each stopping branch. -/
theorem Skill.followTemporal_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate) :
    (skill.followTemporal models features potential goal estimate rate action behaviour reward
      gain).interest = skill.interest := by
  unfold Skill.followTemporal
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    split <;> rfl

/-- A followed frame always leaves the skill linked to the current frame's potential. -/
theorem Skill.followTemporal_linked {config : Config} {criterion : Criterion}
    {dimension : Dimension} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action primitiveCount.word.toNat)
    (behaviour : Vector Binary32 primitiveCount.word.toNat) (reward : Binary32)
    (gain : RewardRate) :
    ((skill.followTemporal models features potential goal estimate rate action behaviour reward
      gain).following.map (·.previous)) = some potential := by
  unfold Skill.followTemporal
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    split <;> rfl

/-- Settling retains the objective and leaves the skill linked to no frame, on
every branch. -/
theorem Skill.settleFollowing_owner {config : Config} {criterion : Criterion}
    {dimension : Dimension} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) :
    (skill.settleFollowing models features potential goal estimate rate reward gain).interest =
        skill.interest ∧
      (skill.settleFollowing models features potential goal estimate rate reward gain).following =
        none := by
  unfold Skill.settleFollowing
  cases linked : skill.following with
  | none => exact ⟨rfl, linked⟩
  | some following =>
    dsimp only
    split <;> exact ⟨rfl, rfl⟩

/-- Reduction at an invocation start: a skill linked to no frame is settled to
itself, so the start of an option that was executing, fresh or restored is the
existing on-policy start. -/
theorem Skill.settleFollowing_unlinked {config : Config} {criterion : Criterion}
    {dimension : Dimension} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (unlinked : skill.following = none) :
    skill.settleFollowing models features potential goal estimate rate reward gain = skill := by
  unfold Skill.settleFollowing
  rw [unlinked]

/-- The learning flag cannot change the settled objective. -/
theorem Skill.settleTemporal_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension} (skill : Skill config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (skill.settleTemporal models features potential goal estimate rate reward gain
      learning).interest = skill.interest := by
  unfold Skill.settleTemporal
  split
  · exact (skill.settleFollowing_owner models features potential goal estimate rate reward gain).1
  · rfl

end Acorn.Features
