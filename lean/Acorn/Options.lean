/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Exploration
import Acorn.FeatureModelInput

/-!
# Current option policy execution

Ng, Harada & Russell, *Policy invariance under reward transformations*, ICML
(1999), Theorem 1 equation (2), Corollary 2 and Remark 1 (PDF pp. 4–5), supplies
the potential coordinate. Sutton, Machado et al., *Reward-respecting subtasks
for model-based reinforcement learning*, Artificial Intelligence 324 (2023),
104001, arXiv:2202.03466v4, equations (4)–(5), supplies the attained bonus and
undiscounted terminal stopping value. Sutton, Precup & Singh, *Between MDPs and
semi-MDPs*, Artificial Intelligence 112 (1999), Theorem 2, p. 197, supplies the
strict interruption comparison's form, not an improvement theorem for estimates.

Policy storage is the existing managed Skill. Model learning is a separate
consumer of the same begin/continuing/ending boundaries. Frozen invocations
retain their mutation mode. Lean values are persistent, not linear resources:
exactly-once closing is a property of the dispatch transition, not a claim that
a caller cannot duplicate a value. Raw reward and estimate words stay raw.
-/
namespace Acorn.Features

/-- Boolean potential has exactly the two currently executable values. -/
abbrev Potential := Bool

/-- The exact machine indicator, with no caller-supplied scale. -/
def Potential.value (potential : Potential) : Binary32 := if potential then .one else .zero

/-- Opaque declared observations enter with their source's provenance witness. -/
structure DeclaredPotentials where
  /-- Register entry attached to the producer. -/
  origin : Departure
  /-- Closed option-slot order. -/
  values : Vector Potential Acorn.FeatureConstants.skillCount

/-- The potential of an interest with its work: a learned assignment's potential, or the read of
a declared value. -/
def Interest.potentialCosted {config : Config} {dimension : Dimension} (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    Costed (Option Potential) :=
  match interest with
  | .learned assignment => do
    let potential ← assignment.potentialCosted features
    pure (some potential)
  | .declared origin tag => Costed.op .declaredPotential
    (if origin = declared.origin then some (declared.values.get tag) else none)

/-- Learned assignments read their own receiving feature slot; declared choices
read the matching source, refusing a mismatched declaration before execution. -/
def Interest.potential {config : Config} {dimension : Dimension} (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) : Option Potential :=
  (interest.potentialCosted features declared).val

/-- A learned interest has its assignment's potential, and a declared one the declared value
of its tag when the source has its origin. -/
theorem Interest.potential_def {config : Config} {dimension : Dimension}
    (interest : Interest config) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) :
    interest.potential features declared =
      match interest with
      | .learned assignment => some (assignment.potential features)
      | .declared origin tag =>
        if origin = declared.origin then some (declared.values.get tag) else none := by
  cases interest <;> rfl

/-- Held attainment bonuses remain part of learned stopping values, including at goal
termination. Declared spatial subtasks have no attainment bonus. -/
def Interest.stoppingValue {config : Config} (interest : Interest config)
    (estimate : Binary32) (potential : Potential) : Binary32 :=
  match interest with
  | .learned assignment => assignment.stoppingValue estimate potential
  | .declared _ _ => estimate

/-- Continuing shaping uses the exact multiply, add, subtract order. -/
def shapedCumulant (reward gamma : Binary32) (next previous : Potential) : Binary32 :=
  (reward.add (gamma.mul next.value)).sub previous.value

/-- Terminal shaping includes the stopping value without a discount factor. -/
def terminalCumulant (reward stopping : Binary32) (previous : Potential) : Binary32 :=
  (reward.add stopping).sub previous.value

/-- The current closed termination reasons, in observation order. -/
inductive OptionEnd where
  /-- Goal-terminal host feedback. -/
  | goal
  /-- Fixed work bound reached. -/
  | duration
  /-- Control passed elsewhere: a strictly better stopping estimate, or an exploratory
  run the option's own draw began. Such a run takes control before the next frame's
  goal and duration checks, so it is the recorded reason even where one would fire. -/
  | interrupted
  deriving DecidableEq

/-- Trajectory state is created only by begin or as `OptionActivation.first`, the
activation that begin followed by the first step leaves (`Skill.begin_first`); it is
updated by an admitted step, resumed from the off-policy trajectory a skill stores, or read
back from a checkpoint image (`OptionActivation.stored`). -/
structure OptionActivation (mode : Bool) where
  private mk ::
  /-- Number of option actions already returned, bounded at storage. -/
  age : ModelAge
  /-- Potential from the preceding admitted decision. -/
  previous : Potential

/-- The activation that a checkpoint image holds: the stored age and preceding potential.
The checkpoint loader is its one caller, and it rebuilds the activation of the saved agent
(`Checkpoint.activationFormat`). -/
def OptionActivation.stored {mode : Bool} (age : ModelAge) (previous : Potential) :
    OptionActivation mode := ⟨age, previous⟩

/-- Mutation mode is fixed by the activation type, including every admission path. -/
def OptionActivation.learning {mode : Bool} (_activation : OptionActivation mode) : Bool := mode

/-- A stored off-policy trajectory is a learning activation: its age is the number
of actions followed since it began, so the executing option's stopping decision,
duration cap included, applies to it unchanged. -/
def Following.activation (following : Following) : OptionActivation true :=
  ⟨following.age, following.previous⟩

variable {mode : Bool}

/-- The off-policy trajectory an activation continues as when the option stops
executing without ending: the same age and preceding potential. Its model trajectory
is live once an action has been returned, because the option drew that action from
its own distribution. -/
def OptionActivation.following (activation : OptionActivation mode) : Following :=
  ⟨activation.age, decide (0 < activation.age.val), activation.previous⟩

/-- A continuation binds its potential, features and policy snapshot to one
termination decision. Its bound excludes an action after the cap. -/
structure OptionContinuation (actions : Word.Count) (dimension : Dimension) (activation : OptionActivation mode) where
  private mk ::
  /-- Exact active set used to freeze the policy. -/
  features : SwiftTd.ActiveSet dimension
  /-- Exact coordinate used by the stopping comparison. -/
  potential : Potential
  /-- Values and epsilon before learner mutation. -/
  policy : PolicySnapshot actions
  /-- Another action fits within the fixed duration. -/
  room : activation.age.val < Acorn.FeatureConstants.optionMaxDuration

/-- Complete termination decision; no duration-bypassing continuation exists. -/
inductive OptionDecision (actions : Word.Count) (dimension : Dimension) (activation : OptionActivation mode) where
  /-- An admitted continuing step. -/
  | continuing (next : OptionContinuation actions dimension activation)
  /-- A closing transition, with its reason. -/
  | ending (reason : OptionEnd)

/-- The exact source of a consumer's rate. -/
inductive ConsumerRate where
  /-- Read this consumer's own current step sizes. -/
  | own
  /-- Use the declared fixed or shared value. -/
  | fixed (rate : SwiftTd.ExploreRate)

/-- The rate with its work: the consumer's own rate at the work of reading it, or the declared
value, which reads nothing. -/
def ConsumerRate.resolveCosted (source : ConsumerRate) (own : Unit → Costed SwiftTd.ExploreRate) :
    Costed SwiftTd.ExploreRate :=
  match source with | .own => own () | .fixed rate => Costed.pure rate

/-- Resolve lazily, so fixed-rate arms do not scan unrelated learner state. -/
def ConsumerRate.resolve (source : ConsumerRate) (own : Unit → SwiftTd.ExploreRate) : SwiftTd.ExploreRate :=
  match source with | .own => own () | .fixed rate => rate

/-- The costed resolution's value is the resolution of the callback's values. -/
theorem ConsumerRate.resolveCosted_val (source : ConsumerRate)
    (own : Unit → Costed SwiftTd.ExploreRate) :
    (source.resolveCosted own).val = source.resolve fun unused => (own unused).val := by
  cases source <;> rfl

variable {actions : Word.Count} {config : Config} {criterion : Criterion} {dimension : Dimension}
  {discounts : List Discount}

/-- The start with its work: a learning start's clear, then, under the start's records, the rate
its source resolves to and the snapshot. -/
def Skill.beginOptionCosted (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential)
    (learning : Bool) (rate : ConsumerRate) :
    Costed (Skill actions config criterion dimension discounts ×
      (activation : OptionActivation learning) ×
        OptionContinuation actions dimension activation) := do
  let skill ← Costed.ite (learning = true)
    (fun _ => do
      let policy ← skill.policy.clearCosted
      Costed.pure { skill with policy })
    (fun _ => Costed.pure skill)
  let activation : OptionActivation learning := ⟨ ⟨0, by decide⟩, potential⟩
  Costed.charge .beginOption do
    let freeze := skill.policy.snapshotCosted (count := actions) features
    let epsilon ← rate.resolveCosted fun _ => skill.policy.exploreRateCosted (count := actions)
    let policy ← freeze epsilon
    Costed.pure (skill, ⟨activation, ⟨features, potential, policy,
      by change 0 < Acorn.FeatureConstants.optionMaxDuration; decide⟩⟩)

/-- Frozen start retains all learned registers; learning start clears trajectory
state before any snapshot. Model start is handled by its boundary consumer. -/
def Skill.beginOption (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential)
    (learning : Bool) (rate : ConsumerRate) :
    Skill actions config criterion dimension discounts ×
      (activation : OptionActivation learning) × OptionContinuation actions dimension activation :=
  (skill.beginOptionCosted features potential learning rate).val

/-- A start clears a learning skill's policy, then freezes the policy at the rate its source
resolves to. -/
theorem Skill.beginOption_def (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential)
    (learning : Bool) (rate : ConsumerRate) :
    skill.beginOption features potential learning rate =
      let skill := if learning then { skill with policy := skill.policy.clear } else skill
      let activation : OptionActivation learning := ⟨ ⟨0, by decide⟩, potential⟩
      let policy := skill.policy.snapshot (count := actions) features
        (rate.resolve fun _ => skill.policy.exploreRate (count := actions))
      (skill, ⟨activation, ⟨features, potential, policy,
        by change 0 < Acorn.FeatureConstants.optionMaxDuration; decide⟩⟩) := by
  cases rate <;> rfl

/-- The comparison value with its work: the policy mean or the ordered maximum. -/
def comparisonValueCosted (criterion : Criterion) {count : Word.Count}
    (policy : PolicySnapshot count) : Costed Binary32 :=
  match criterion with | .differential => policy.expectedCosted | .discounted => policy.bestCosted

/-- Comparison uses the nominal policy mean for differential control and the
ordered maximum for the discounted comparator; neither is an accuracy claim. -/
def comparisonValue (criterion : Criterion) {count : Word.Count} (policy : PolicySnapshot count) : Binary32 :=
  (comparisonValueCosted criterion policy).val

/-- The comparison value is the policy mean under the differential criterion and the ordered
maximum under the discounted one. -/
theorem comparisonValue_def (criterion : Criterion) {count : Word.Count}
    (policy : PolicySnapshot count) :
    comparisonValue criterion policy =
      match criterion with | .differential => policy.expected | .discounted => policy.best := by
  cases criterion <;> rfl

/-- The termination decision with its work: its tests and, below the duration cap without the
goal, the rate its source resolves to, the snapshot and its comparison value. -/
def Skill.decideOptionCosted (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    Costed (OptionDecision actions dimension activation) :=
  Costed.charge .decide <|
  Costed.ite (goal = true) (fun _ => Costed.pure (.ending .goal)) fun _ =>
  Costed.dite (activation.age.val < Acorn.FeatureConstants.optionMaxDuration)
    (fun h => do
      let freeze := skill.policy.snapshotCosted (count := actions) features
      let epsilon ← rate.resolveCosted fun _ => skill.policy.exploreRateCosted (count := actions)
      let policy ← freeze epsilon
      let comparison ← comparisonValueCosted criterion policy
      let continuing := comparison.add potential.value
      Costed.ite (continuing.less (skill.interest.stoppingValue estimate potential) = true)
        (fun _ => Costed.pure (.ending .interrupted))
        (fun _ => Costed.pure (.continuing ⟨features, potential, policy, h⟩)))
    fun _ => Costed.pure (.ending .duration)

/-- Goal precedes duration, which precedes the strict estimate comparison. -/
def Skill.decideOption (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) : OptionDecision actions dimension activation :=
  (skill.decideOptionCosted activation features potential goal estimate rate).val

/-- The goal ends a decision, then the duration cap; below it the frozen policy's comparison
value against the stopping value interrupts or continues. -/
theorem Skill.decideOption_def (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate) :
    skill.decideOption activation features potential goal estimate rate =
      if goal then .ending .goal
      else if h : activation.age.val < Acorn.FeatureConstants.optionMaxDuration then
        let policy := skill.policy.snapshot (count := actions) features
          (rate.resolve fun _ => skill.policy.exploreRate (count := actions))
        let continuing := (comparisonValue criterion policy).add potential.value
        if continuing.less (skill.interest.stoppingValue estimate potential) then
          .ending .interrupted
        else .continuing ⟨features, potential, policy, h⟩
      else .ending .duration := by
  cases rate <;> rfl

/-- The option step with its work: the persistent draw, then, under the step's records, a
learning option's credit. -/
def Skill.optionStepCosted (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Costed (Skill actions config criterion dimension discounts × OptionActivation mode ×
      PersistentDecision actions × Rng.Xoshiro256) := do
  let drawn ← next.policy.drawPersistentCosted rng
  let skill ← Costed.charge .optionStep <| Costed.ite (activation.learning = true)
    (fun _ => do
      let policy ← skill.policy.persistentStepCosted next.features next.policy drawn.1
        (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next.potential
          activation.previous) 1
      Costed.pure { skill with policy })
    (fun _ => Costed.pure skill)
  Costed.pure (skill, ⟨activation.age.advance, next.potential⟩, drawn.1, drawn.2)

/-- Draw before credit, center with the old host gain, and execute the existing
complete Sarsa update. The draw is the behaviour's persistent draw (PAR-8): its
exploring branch commits a run whose first action is this step's action, a sample of
the option's own nominal distribution, so the update is the on-policy one either way.
Age counts the returned action, including the first one. -/
def Skill.optionStep (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    Skill actions config criterion dimension discounts × OptionActivation mode × PersistentDecision actions × Rng.Xoshiro256 :=
  (skill.optionStepCosted activation next reward gain rng).val

/-- An option step draws, credits a learning option the shaped cumulant at the drawn action, and
advances the activation. -/
theorem Skill.optionStep_def (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    skill.optionStep activation next reward gain rng =
      let drawn := next.policy.drawPersistent rng
      let skill := if activation.learning then
        { skill with policy := (skill.policy.persistentStep next.features next.policy drawn.1
            (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next.potential
              activation.previous) 1) }
        else skill
      (skill, ⟨activation.age.advance, next.potential⟩, drawn.1, drawn.2) := rfl

/-- The activation an admitted step leaves: one more returned action, and the
continuation's potential as the preceding coordinate. It reads no learner and no reward. -/
def OptionActivation.advance (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) : OptionActivation mode :=
  ⟨activation.age.advance, next.potential⟩

/-- The credit with its work: under the step's records, a learning option's credit. -/
def Skill.optionCreditCosted (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    Costed (Skill actions config criterion dimension discounts) :=
  Costed.charge .optionStep <| Costed.ite (activation.learning = true)
    (fun _ => do
      let policy ← skill.policy.persistentStepCosted next.features next.policy drawn
        (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next.potential
          activation.previous) 1
      Costed.pure { skill with policy })
    (fun _ => Costed.pure skill)

/-- The credit half of `optionStep`: the complete Sarsa update of the continuation's
frozen values for a decision that is already drawn. It draws nothing and reads the
decision's action only, so a caller can make the draw before the reward arrives and
credit it afterwards. `Skill.optionStep_credit` proves that `optionStep` is its draw
followed by this credit, and `Skill.optionCredit_frozen` that the credit of a frozen
activation writes nothing, whatever was drawn. -/
def Skill.optionCredit (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (drawn : PersistentDecision actions)
    (reward : Binary32) (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  (skill.optionCreditCosted activation next drawn reward gain).val

/-- A learning option's credit is the Sarsa update at the drawn action and the shaped cumulant;
a frozen option's is no write. -/
theorem Skill.optionCredit_def (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    skill.optionCredit activation next drawn reward gain =
      if activation.learning then
        { skill with policy := (skill.policy.persistentStep next.features next.policy drawn
            (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next.potential
              activation.previous) 1) }
        else skill := rfl

/-- The frozen policy with its work: the rate its source resolves to, then the snapshot. -/
def Skill.frozenPolicyCosted (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    Costed (PolicySnapshot actions) := do
  let freeze := skill.policy.snapshotCosted (count := actions) features
  let epsilon ← rate.resolveCosted fun _ => skill.policy.exploreRateCosted (count := actions)
  freeze epsilon

/-- The frozen policy of a skill at a frame, read from its learner as it stands: the
values there and the rate its source resolves to. No trajectory state is cleared and
nothing is written. It is the snapshot a continuing decision freezes
(`Skill.decide_frozen`). -/
def Skill.frozenPolicy (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) : PolicySnapshot actions :=
  (skill.frozenPolicyCosted features rate).val

/-- The frozen policy is the snapshot of the skill's policy at the rate its source resolves to. -/
theorem Skill.frozenPolicy_def (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    skill.frozenPolicy features rate =
      skill.policy.snapshot (count := actions) features
        (rate.resolve fun _ => skill.policy.exploreRate (count := actions)) := by
  cases rate <;> rfl

/-- The activation of an invocation after its first returned action: age one, and the
start potential as the preceding coordinate. It is the activation the first step of a
started invocation leaves (`Skill.begin_first`), named for a caller that draws the first
action before the invocation start is written. -/
def OptionActivation.first (learning : Bool) (potential : Potential) : OptionActivation learning :=
  ⟨ModelAge.advance ⟨0, by decide⟩, potential⟩

/-- The termination with its work: under its records, a learning option's terminal credit. -/
def Skill.terminateOptionCosted (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) : Costed (Skill actions config criterion dimension discounts) :=
  Costed.charge .terminateOption <| Costed.ite (activation.learning = true)
    (fun _ => do
      let policy ← skill.policy.terminalCosted (terminalCumulant (criterion.center reward 1 gain)
        (skill.interest.stoppingValue terminal potential) activation.previous)
      Costed.pure { skill with policy })
    (fun _ => Costed.pure skill)

/-- Close existing traces with the selected terminal continuation. No new action
trace is inserted, and the model state is left to the model boundary owner. -/
def Skill.terminateOption (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (potential : Potential) (reward terminal : Binary32) (gain : RewardRate) :
    Skill actions config criterion dimension discounts :=
  (skill.terminateOptionCosted activation potential reward terminal gain).val

/-- A learning option's termination is the terminal credit of the terminal cumulant with the
stopping value; a frozen option's is no write. -/
theorem Skill.terminateOption_def (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) :
    skill.terminateOption activation potential reward terminal gain =
      if activation.learning then
        { skill with policy := (skill.policy.terminal
          (terminalCumulant (criterion.center reward 1 gain)
            (skill.interest.stoppingValue terminal potential) activation.previous)) }
      else skill := rfl

/-- Start's predecessor coordinate is exactly the current potential, avoiding
an invented zero-potential transition. -/
theorem Skill.begin_coordinate (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginOption features potential learning rate).2.1.previous = potential ∧
    (skill.beginOption features potential learning rate).2.1.age.val = 0 := ⟨rfl, rfl⟩

/-- Goal feedback always wins, including at the duration boundary. -/
theorem Skill.goal_ends (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32) (rate : ConsumerRate) :
    skill.decideOption activation features potential true estimate rate = .ending .goal := rfl

/-- At the duration cap a nonterminal activation cannot return another action. -/
theorem Skill.cap_ends (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32) (rate : ConsumerRate)
    (full : activation.age.val = Acorn.FeatureConstants.optionMaxDuration) :
    skill.decideOption activation features potential false estimate rate = .ending .duration := by
  simp [Skill.decideOption_def, full]

/-- Every admitted action advances by exactly one, not a saturating no-op at the cap. -/
theorem Skill.step_age (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    (skill.optionStep activation next reward gain rng).2.1.age.val = activation.age.val + 1 := by
  have := next.room
  simp only [Skill.optionStep_def, ModelAge.advance]
  omega

/-- Frozen activation mutation cannot be enabled by a later caller's mode. -/
theorem Skill.step_frozen (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) (frozen : activation.learning = false) :
    (skill.optionStep activation next reward gain rng).1 = skill := by
  simp [Skill.optionStep_def, frozen]

/-- A continuing decision freezes the option's own policy at the decision's frame: its
learner's values there and the rate its source resolves to. -/
theorem Skill.decide_policy (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate = .continuing next) :
    next.policy = skill.policy.snapshot (count := actions) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := actions)) := by
  simp only [Skill.decideOption_def] at continuing
  repeat' split at continuing
  all_goals first
    | (cases continuing; rfl)
    | cases continuing

/-- A continuing decision binds the frame it was taken at: its features and potential. -/
theorem Skill.decide_frame (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate = .continuing next) :
    next.features = features ∧ next.potential = potential := by
  simp only [Skill.decideOption_def] at continuing
  repeat' split at continuing
  all_goals first
    | (cases continuing; exact ⟨rfl, rfl⟩)
    | cases continuing

/-- The step's action, branch and run are those of the persistent draw from the
continuation's frozen policy, at the supplied generator state. -/
theorem Skill.step_drawn (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    (skill.optionStep activation next reward gain rng).2.2 = next.policy.drawPersistent rng := rfl

/-- **The option step is its draw followed by its credit.** For every skill,
activation, continuation, reward word, gain and generator state: the step returns the
credit of the persistent draw from the continuation's frozen policy, the advanced
activation, and that draw with the generator it left. -/
theorem Skill.optionStep_credit (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    skill.optionStep activation next reward gain rng =
      (skill.optionCredit activation next (next.policy.drawPersistent rng).1 reward gain,
        activation.advance next, next.policy.drawPersistent rng) := rfl

/-- The credit of a drawn decision reads the decision's action only: two decisions
with one action give one credited skill. -/
theorem Skill.optionCredit_action (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (first second : PersistentDecision actions)
    (reward : Binary32) (gain : RewardRate) (same : first.action = second.action) :
    skill.optionCredit activation next first reward gain =
      skill.optionCredit activation next second reward gain := by
  simp only [Skill.optionCredit_def, Controller.persistentStep_def, same]

/-- A frozen activation's credit writes nothing, whatever was drawn. -/
theorem Skill.optionCredit_frozen (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (drawn : PersistentDecision actions)
    (reward : Binary32) (gain : RewardRate) (frozen : activation.learning = false) :
    skill.optionCredit activation next drawn reward gain = skill := by
  simp [Skill.optionCredit_def, frozen]

/-- The first step of a started invocation leaves the activation `OptionActivation.first`
names, for every skill, frame, mode and rate source. -/
theorem Skill.begin_first (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginOption features potential learning rate).2.1.advance
        (skill.beginOption features potential learning rate).2.2 =
      OptionActivation.first learning potential := rfl

/-- Under a fixed rate source the frozen policy has that rate, whatever the learner's
trajectory state: the rate of a first action drawn before the invocation reset is the
rate of one drawn after it. -/
theorem Skill.frozenPolicy_fixed (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : SwiftTd.ExploreRate) :
    (skill.frozenPolicy features (.fixed rate)).epsilon = rate := rfl

/-- A continuing decision freezes the frozen policy of the deciding skill. -/
theorem Skill.decide_frozen (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate = .continuing next) :
    next.policy = skill.frozenPolicy features rate := by
  rw [Skill.frozenPolicy_def]
  exact skill.decide_policy activation features potential goal estimate rate next continuing

/-- An invocation start freezes the started option's own policy at the start frame: its
learner's values there and the rate its source resolves to. -/
theorem Skill.begin_policy (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginOption features potential learning rate).2.2.policy =
      (skill.beginOption features potential learning rate).1.policy.snapshot
        (count := actions) features
        (rate.resolve fun _ => (skill.beginOption features potential learning
          rate).1.policy.exploreRate (count := actions)) := by
  cases rate <;> rfl

/-- The trajectory a learning activation continues as resumes to that activation, so the
option's stopping decision reads the same age and preceding potential either way. -/
theorem OptionActivation.following_activation (activation : OptionActivation true) :
    activation.following.activation = activation := rfl

/-- Termination retains the complete objective identity and untouched model owner. -/
theorem Skill.terminal_owners (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (potential : Potential) (reward terminal : Binary32) (gain : RewardRate) :
    (skill.terminateOption activation potential reward terminal gain).interest = skill.interest ∧
    (skill.terminateOption activation potential reward terminal gain).model = skill.model := by
  rw [Skill.terminateOption_def]
  split <;> exact ⟨rfl, rfl⟩

end Acorn.Features
