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

An executing option's draw is the behaviour's persistent draw (PAR-8). When it begins
a run with a step left to serve, the run takes dispatch occupancy and holds the option
until that step (`CommittedRun`), where the option stops executing and continues as
the off-policy trajectory `OptionActivation.following` names.

A model reads the current value function at two places: its terminal targets and
its predictions. Sutton, Machado et al., *Reward-respecting subtasks for model-based
reinforcement learning*, Artificial Intelligence 324 (2023), 104001,
arXiv:2202.03466v4, §5, equation (19), p. 16, backs up `r̂(x, o) + v̂(n̂(x, o), w)` with
the current weights `w`; here `w` is the meta-controller's action-value weights, read
where they are stored and never copied.
-/
namespace Acorn.Features

variable {actions : Word.Count}

/-- The current value function: the meta-controller's action values with the
exploration rate of its nominal policy. -/
structure ValueFunction (criterion : Criterion) (dimension : Dimension) where
  /-- The meta-controller whose weights are the value weights. -/
  controller : Controller (criterion.config .control) dimension metaCount.word.toNat
  /-- Rate of the nominal policy whose mean differential control compares. -/
  epsilon : SwiftTd.ExploreRate

/-- Nominal value of an observed frame: the ordered maximum of the action values
under discounted control and their nominal policy mean under differential control. -/
def ValueFunction.nominal {criterion : Criterion} {dimension : Dimension}
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) : Binary32 :=
  comparisonValue criterion (value.controller.snapshot (count := metaCount) features value.epsilon)

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
  /-- First action of a persistent run primitive control drew. -/
  | explorationStart
  /-- A committed remaining action, without a random draw. -/
  | explorationContinuation
  /-- Action one option's own draw selected, the first action of a run it began included. -/
  | option (slot : Fin Acorn.FeatureConstants.skillCount)
  deriving DecidableEq

/-- Every observation refers to the same action used by credit. -/
structure TemporalDecision (actions : Word.Count) where
  /-- Actual branch of the dispatch transition. -/
  source : TemporalSource
  /-- Admitted primitive action. -/
  action : Action actions.word.toNat
  /-- Pre-update active controller values. -/
  values : Vector Binary32 actions.word.toNat
  /-- Nominal boundary masses or a served action's point mass. -/
  probabilities : Vector Binary32 actions.word.toNat
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

/-- A committed exploratory run in dispatch occupancy. Until its first served step it
also holds the option whose draw began it: that option is the executing invocation of
the frame it drew, and the first served step ends its execution. A held option always
has that step ahead. -/
structure CommittedRun (actions : Word.Count) (mode : Bool) where
  /-- The committed action and its remaining clock. -/
  run : ExploratoryRun actions
  /-- The option whose draw began the run, until the first served step. -/
  origin : Option (Fin Acorn.FeatureConstants.skillCount × OptionActivation mode)
  /-- A held option has a served step ahead, at which it is interrupted. -/
  pending : origin.isSome → 0 < run.remaining.val

/-- A run that holds no option: one primitive control drew, or one already being served. -/
def CommittedRun.bare {mode : Bool} (run : ExploratoryRun actions) : CommittedRun actions mode :=
  ⟨run, none, by simp⟩

/-- Occupancy after an option's draw. A drawn run with a step left to serve takes
occupancy and holds the option until that step. A run with nothing left is one
exploratory step of the option, which keeps occupancy, as it does after a greedy draw. -/
def Occupancy.afterOption {mode : Bool} (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation mode) (run : Option (ExploratoryRun actions)) :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) :=
  match run with
  | some run =>
    if left : 0 < run.remaining.val then .exploring ⟨run, some (slot, activation), fun _ => left⟩
    else .option slot activation
  | none => .option slot activation

/-- Occupancy after primitive control's draw: a drawn run with a step left to serve
takes occupancy and holds no option; otherwise dispatch is free. -/
def Occupancy.afterPrimitive {mode : Bool} (run : Option (ExploratoryRun actions)) :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) :=
  match run with
  | some run => if 0 < run.remaining.val then .exploring (.bare run) else .idle
  | none => .idle

/-- The executing invocation of a dispatch occupancy: a live option, or the option a
committed run holds until its first served step. -/
def Occupancy.executing {mode : Bool} :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) →
      Option (Fin Acorn.FeatureConstants.skillCount)
  | .option slot _ => some slot
  | .exploring committed => committed.origin.map (·.1)
  | .idle => none

/-- Whatever its draw, the drawing option is the executing invocation of its frame. -/
theorem Occupancy.afterOption_executing {mode : Bool} (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation mode) (run : Option (ExploratoryRun actions)) :
    (Occupancy.afterOption slot activation run).executing = some slot := by
  cases run with
  | none => rfl
  | some run =>
    by_cases left : 0 < run.remaining.val <;>
      simp [Occupancy.afterOption, Occupancy.executing, left]

/-- A run that holds no option has no executing invocation. -/
theorem CommittedRun.bare_executing {mode : Bool} (run : ExploratoryRun actions) :
    (Occupancy.exploring (CommittedRun.bare (mode := mode) run) :
      Occupancy (OptionActivation mode) (CommittedRun actions mode)).executing = none := rfl

/-- Primitive control's draw leaves no option executing. -/
theorem Occupancy.afterPrimitive_executing {mode : Bool}
    (run : Option (ExploratoryRun actions)) :
    (Occupancy.afterPrimitive (mode := mode) run).executing = none := by
  cases run with
  | none => rfl
  | some run =>
    by_cases left : 0 < run.remaining.val <;>
      simp [Occupancy.afterPrimitive, Occupancy.executing, CommittedRun.bare, left]

/-- An option-selected action is the only path that uses option primitive credit. -/
def TemporalDecision.own (decision : TemporalDecision actions) : Bool :=
  match decision.source with | .option _ => false | .primitive | .explorationStart | .explorationContinuation => true

/-- Model operations are confined to the existing model storage. The argument
order preserves first-step omission and the raw host reward rather than its gain-centered value. -/
structure OptionModelOps (criterion : Criterion) (dimension : Dimension) where
  /-- Begin a model trajectory after the policy's transient clear. -/
  begin : Model dimension criterion → SwiftTd.ActiveSet dimension → Model dimension criterion
  /-- Credit a completed non-first transition at its pre-increment age. -/
  step : Model dimension criterion → SwiftTd.ActiveSet dimension → ModelAge → Binary32 → Model dimension criterion
  /-- Terminal model update at the terminal frame, with the raw reward. The model reads
  the current value function there; it takes no continuation word from policy credit. -/
  terminal : Model dimension criterion → ValueFunction criterion dimension →
    SwiftTd.ActiveSet dimension → Binary32 → Model dimension criterion
  /-- Pre-dispatch observation at age zero, under the current value function. -/
  predict : Model dimension criterion → ValueFunction criterion dimension →
    SwiftTd.ActiveSet dimension → ModelCache
  /-- Start a trajectory at an age for an option that is not executing, on existing storage. -/
  restart : Model dimension criterion → SwiftTd.ActiveSet dimension → ModelAge → Model dimension criterion
  /-- Close such a trajectory toward the terminal entry's targets at the stopping frame. -/
  stop : Model dimension criterion → ValueFunction criterion dimension →
    SwiftTd.ActiveSet dimension → Binary32 → Model dimension criterion

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
  /-- Recently seen feature vectors and the search-control position among them. -/
  recent : RecentFeatures dimension

/-- Required planning interface at a free boundary, before the meta snapshot. The
last argument is the meta-controller's exploration rate, the rate of the nominal
policy the backed-up value reads. -/
abbrev PlanBoundary (actions : Word.Count) (config : Config) (criterion : Criterion) (dimension : Dimension)
    (discounts : List Discount) :=
  PlanningResult criterion dimension → Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount →
    SwiftTd.ActiveSet dimension → RewardRate → SwiftTd.ExploreRate → PlanningResult criterion dimension

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
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    Skill actions config criterion dimension discounts × (activation : OptionActivation learning) × OptionContinuation actions dimension activation :=
  let begun := skill.beginOption features potential learning rate
  let skill := if learning then { begun.1 with model := models.begin begun.1.model features } else begun.1
  (skill, begun.2)

/-- A start writes the model only after the policy is frozen: the continuation holds the
started option's own policy, its learner's values at the start frame and the rate its
source resolves to. -/
theorem Skill.beginTemporal_policy {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential learning rate).2.2.policy =
      (skill.beginTemporal models features potential learning rate).1.policy.snapshot
        (count := actions) features
        (rate.resolve fun _ => (skill.beginTemporal models features potential learning
          rate).1.policy.exploreRate (count := actions)) := by
  cases learning <;> exact skill.begin_policy features potential _ rate

/-- A first returned action has no completed model transition to credit. The
policy step's result is taken apart before the model is credited, and
`Skill.stepTemporal_eq` proves the result equal to the listed composition. The
ordering is meant to let the runtime reuse the model learners' storage when the
skill is referenced nowhere else; that is a performance expectation, not a
proved property. -/
def Skill.stepTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Skill actions config criterion dimension discounts × OptionActivation mode × PersistentDecision actions × Rng.Xoshiro256 :=
  let (stepped, rest) := skill.optionStep activation next reward gain rng
  let skill := if activation.learning && activation.age.val > 0 then
    { stepped with model := models.step stepped.model next.features activation.age reward }
    else stepped
  (skill, rest)

/-- Taking the policy step's result apart preserves the composition, for every
skill, activation, reward word and random state. -/
theorem Skill.stepTemporal_eq {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    skill.stepTemporal models activation next reward gain rng =
      let result := skill.optionStep activation next reward gain rng
      let skill := if activation.learning && activation.age.val > 0 then
        { result.1 with model := models.step result.1.model next.features activation.age reward }
        else result.1
      (skill, result.2) := rfl

/-- The policy is credited the terminal value with the objective's attained bonus and
inverse potential coordinate. The model is closed at the terminal frame toward the
features observed there and the current value function's nominal value of it. -/
def Skill.endTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  let result := skill.terminateOption ending.activation ending.potential reward terminal gain
  if ending.activation.learning then
    { result with model := models.terminal result.model value features reward } else result

/-- Link an option that is not executing to the current frame. Every earlier trace
is released before the taken action's traces are laid, so no earlier transition is
credited. The model starts a trajectory at age zero only when the frame's action
was selected with the option's own distribution. -/
def Skill.startFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) : Skill actions config criterion dimension discounts :=
  let frozen := skill.policy.snapshot (count := actions) features
    (rate.resolve fun _ => skill.policy.exploreRate (count := actions))
  let consistent := frozen.consistent behaviour
  let ⟨interest, policy, model, _, questions⟩ := skill
  ⟨interest,
    policy.startStep (actions := actions.word.toNat) features action
      (frozen.values.get action),
    if consistent then models.restart model features ⟨0, by decide⟩ else model,
    some ⟨⟨1, by decide⟩, consistent, potential⟩, questions⟩

/-- Stop the stored trajectory where the option's stopping decision fires: the
policy is credited the stopping value at zero trace decay and a live model
trajectory is closed toward the terminal targets. Nothing stays eligible and the
skill is linked to no frame. -/
def Skill.stopFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  let stopping := (terminalCumulant (criterion.center reward 1 gain)
    (skill.interest.stoppingValue estimate potential) following.previous).sub skill.policy.vOld
  let ⟨interest, policy, model, _, questions⟩ := skill
  ⟨interest, policy.stopStep stopping,
    if following.live then models.stop model value features reward else model, none,
    questions⟩

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
meta action is drawn for an option that is not executing. A closing model reads the
supplied current value function at this frame. -/
def Skill.followTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat)
    (reward : Binary32) (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  match skill.following with
  | none => skill.startFollowing models features potential rate action behaviour
  | some following =>
    match skill.decideOption following.activation features potential goal estimate rate with
    | .continuing next =>
      let consistent := next.policy.consistent behaviour
      let ⟨interest, policy, model, _, questions⟩ := skill
      let credited := if following.live then
        models.step model features following.age reward else model
      ⟨interest,
        policy.backupStep (count := actions) features next.policy action
          (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
            following.previous),
        if consistent && !following.live then models.restart credited features following.age
          else credited,
        some ⟨ModelAge.advance following.age, consistent, potential⟩, questions⟩
    | .ending _ =>
      (skill.stopFollowing models value features following potential estimate reward
        gain).startFollowing models features potential rate action behaviour

/-- Close the stored trajectory at the frame where the option starts executing.
The completed transition is credited exactly as on a followed frame: the stopping
value where the stopping decision fires, the tree-backup error otherwise, and the
model's step along a live run. No new trace is laid and nothing stays eligible,
because the invocation start begins a fresh trajectory. -/
def Skill.settleFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate) :
    Skill actions config criterion dimension discounts :=
  match skill.following with
  | none => skill
  | some following =>
    match skill.decideOption following.activation features potential goal estimate rate with
    | .continuing next =>
      let ⟨interest, policy, model, _, questions⟩ := skill
      ⟨interest,
        policy.stopStep (policy.backupError (count := actions) next.policy
          (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
            following.previous)),
        if following.live then models.step model features following.age reward else model,
        none, questions⟩
    | .ending _ =>
      skill.stopFollowing models value features following potential estimate reward gain

/-- A frozen invocation start settles nothing; a learning one settles the stored
trajectory first. -/
def Skill.settleTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) : Skill actions config criterion dimension discounts :=
  if learning then
    skill.settleFollowing models value features potential goal estimate rate reward gain
  else skill

/-- Model callbacks cannot rewrite the policy update or alter the returned action. -/
theorem Skill.stepTemporal_policy {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    (skill.stepTemporal models activation next reward gain rng).1.policy =
      (skill.optionStep activation next reward gain rng).1.policy ∧
    (skill.stepTemporal models activation next reward gain rng).2 =
      (skill.optionStep activation next reward gain rng).2 := by
  rw [Skill.stepTemporal_eq]
  split <;> exact ⟨rfl, rfl⟩

/-- Following never replaces the objective whose potential was supplied. -/
theorem Skill.startFollowing_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) :
    (skill.startFollowing models features potential rate action behaviour).interest =
      skill.interest := rfl

/-- A stop retains the objective and leaves the skill linked to no frame. -/
theorem Skill.stopFollowing_owner {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (following : Following) (potential : Potential)
    (estimate reward : Binary32) (gain : RewardRate) :
    (skill.stopFollowing models value features following potential estimate reward
        gain).interest = skill.interest ∧
      (skill.stopFollowing models value features following potential estimate reward
        gain).following = none :=
  ⟨rfl, rfl⟩

/-- Every followed frame retains the option's objective, on each stopping branch. -/
theorem Skill.followTemporal_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate) :
    (skill.followTemporal models value features potential goal estimate rate action behaviour
      reward gain).interest = skill.interest := by
  unfold Skill.followTemporal
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    split <;> rfl

/-- A followed frame always leaves the skill linked to the current frame's potential. -/
theorem Skill.followTemporal_linked {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) (reward : Binary32)
    (gain : RewardRate) :
    ((skill.followTemporal models value features potential goal estimate rate action behaviour
      reward gain).following.map (·.previous)) = some potential := by
  unfold Skill.followTemporal
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    split <;> rfl

/-- Settling retains the objective and leaves the skill linked to no frame, on
every branch. -/
theorem Skill.settleFollowing_owner {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) :
    (skill.settleFollowing models value features potential goal estimate rate reward
        gain).interest = skill.interest ∧
      (skill.settleFollowing models value features potential goal estimate rate reward
        gain).following = none := by
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
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (unlinked : skill.following = none) :
    skill.settleFollowing models value features potential goal estimate rate reward gain =
      skill := by
  unfold Skill.settleFollowing
  rw [unlinked]

/-- The learning flag cannot change the settled objective. -/
theorem Skill.settleTemporal_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (skill.settleTemporal models value features potential goal estimate rate reward gain
      learning).interest = skill.interest := by
  unfold Skill.settleTemporal
  split
  · exact (skill.settleFollowing_owner models value features potential goal estimate rate reward
      gain).1
  · rfl

end Acorn.Features
