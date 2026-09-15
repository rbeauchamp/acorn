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

/-- Learned assignments read their own receiving feature slot; declared choices
read the matching source, refusing a mismatched declaration before execution. -/
def Interest.potential {config : Config} {dimension : Dimension} (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) : Option Potential :=
  match interest with
  | .learned assignment => some (assignment.potential features)
  | .declared origin tag => if origin = declared.origin then some (declared.values.get tag) else none

/-- Attained bonuses remain part of learned stopping values, including at goal
termination. Declared spatial subtasks have no attainment bonus. -/
def Interest.stoppingValue {config : Config} (interest : Interest config)
    (estimate : Binary32) (potential : Potential) : Binary32 :=
  match interest with
  | .learned assignment => assignment.stoppingValue estimate potential.value
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
  /-- Strictly better stopping estimate. -/
  | interrupted
  deriving DecidableEq

/-- Trajectory state is created only by begin and updated by an admitted step. -/
structure OptionActivation (mode : Bool) where
  private mk ::
  /-- Number of option actions already returned, bounded at storage. -/
  age : ModelAge
  /-- Potential from the preceding admitted decision. -/
  previous : Potential

/-- Mutation mode is fixed by the activation type, including every admission path. -/
def OptionActivation.learning {mode : Bool} (_activation : OptionActivation mode) : Bool := mode

variable {mode : Bool}

/-- A continuation binds its potential, features and policy snapshot to one
termination decision. Its bound excludes an action after the cap. -/
structure OptionContinuation (dimension : Dimension) (activation : OptionActivation mode) where
  private mk ::
  /-- Exact active set used to freeze the policy. -/
  features : SwiftTd.ActiveSet dimension
  /-- Exact coordinate used by the stopping comparison. -/
  potential : Potential
  /-- Values and epsilon before learner mutation. -/
  policy : PolicySnapshot primitiveCount
  /-- Another action fits within the fixed duration. -/
  room : activation.age.val < Acorn.FeatureConstants.optionMaxDuration

/-- Complete termination decision; no duration-bypassing continuation exists. -/
inductive OptionDecision (dimension : Dimension) (activation : OptionActivation mode) where
  /-- An admitted continuing step. -/
  | continuing (next : OptionContinuation dimension activation)
  /-- A closing transition, with its reason. -/
  | ending (reason : OptionEnd)

/-- The exact source of a consumer's rate. -/
inductive ConsumerRate where
  /-- Read this consumer's own current step sizes. -/
  | own
  /-- Use the declared fixed or shared value. -/
  | fixed (rate : SwiftTd.ExploreRate)

/-- Resolve lazily, so fixed-rate arms do not scan unrelated learner state. -/
def ConsumerRate.resolve (source : ConsumerRate) (own : Unit → SwiftTd.ExploreRate) : SwiftTd.ExploreRate :=
  match source with | .own => own () | .fixed rate => rate

variable {config : Config} {criterion : Criterion} {dimension : Dimension}

/-- Frozen start retains all learned registers; learning start clears trajectory
state before any snapshot. Model start is handled by its boundary consumer. -/
def Skill.beginOption (skill : Skill config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential)
    (learning : Bool) (rate : ConsumerRate) :
    Skill config criterion dimension ×
      (activation : OptionActivation learning) × OptionContinuation dimension activation :=
  let skill := if learning then { skill with policy := skill.policy.clear } else skill
  let activation : OptionActivation learning := ⟨ ⟨0, by decide⟩, potential⟩
  let policy := skill.policy.snapshot (count := primitiveCount) features
    (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount))
  (skill, ⟨activation, ⟨features, potential, policy, by change 0 < Acorn.FeatureConstants.optionMaxDuration; decide⟩⟩)

/-- Comparison uses the nominal policy mean for differential control and the
ordered maximum for the discounted comparator; neither is an accuracy claim. -/
def comparisonValue (criterion : Criterion) {count : Word.Count} (policy : PolicySnapshot count) : Binary32 :=
  match criterion with | .differential => policy.expected | .discounted => policy.best

/-- Goal precedes duration, which precedes the strict estimate comparison. -/
def Skill.decideOption (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) : OptionDecision dimension activation :=
  if goal then .ending .goal
  else if h : activation.age.val < Acorn.FeatureConstants.optionMaxDuration then
    let policy := skill.policy.snapshot (count := primitiveCount) features
      (rate.resolve fun _ => skill.policy.exploreRate (count := primitiveCount))
    let continuing := (comparisonValue criterion policy).add potential.value
    if continuing.less (skill.interest.stoppingValue estimate potential) then .ending .interrupted
    else .continuing ⟨features, potential, policy, h⟩
  else .ending .duration

/-- Draw before credit, center with the old host gain, and execute the existing
complete Sarsa update. Age counts the returned action, including the first one. -/
def Skill.optionStep (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (next : OptionContinuation dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    Skill config criterion dimension × OptionActivation mode × PolicyDecision primitiveCount × Rng.Xoshiro256 :=
  let drawn := next.policy.draw rng
  let skill := if activation.learning then
    { skill with policy := (skill.policy.policyStep next.features drawn.1
        (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next.potential activation.previous) 1) }
    else skill
  (skill, ⟨activation.age.advance, next.potential⟩, drawn.1, drawn.2)

/-- Close existing traces with the selected terminal continuation. No new action
trace is inserted, and the model state is left to the model boundary owner. -/
def Skill.terminateOption (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (potential : Potential) (reward terminal : Binary32) (gain : RewardRate) :
    Skill config criterion dimension :=
  if activation.learning then
    { skill with policy := (skill.policy.terminal
      (terminalCumulant (criterion.center reward 1 gain)
        (skill.interest.stoppingValue terminal potential) activation.previous)) }
  else skill

/-- Start's predecessor coordinate is exactly the current potential, avoiding
an invented zero-potential transition. -/
theorem Skill.begin_coordinate (skill : Skill config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginOption features potential learning rate).2.1.previous = potential ∧
    (skill.beginOption features potential learning rate).2.1.age.val = 0 := ⟨rfl, rfl⟩

/-- Goal feedback always wins, including at the duration boundary. -/
theorem Skill.goal_ends (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32) (rate : ConsumerRate) :
    skill.decideOption activation features potential true estimate rate = .ending .goal := rfl

/-- At the duration cap a nonterminal activation cannot return another action. -/
theorem Skill.cap_ends (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32) (rate : ConsumerRate)
    (full : activation.age.val = Acorn.FeatureConstants.optionMaxDuration) :
    skill.decideOption activation features potential false estimate rate = .ending .duration := by
  simp [Skill.decideOption, full]

/-- Every admitted action advances by exactly one, not a saturating no-op at the cap. -/
theorem Skill.step_age (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (next : OptionContinuation dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    (skill.optionStep activation next reward gain rng).2.1.age.val = activation.age.val + 1 := by
  have := next.room
  simp only [Skill.optionStep, ModelAge.advance]
  omega

/-- Frozen activation mutation cannot be enabled by a later caller's mode. -/
theorem Skill.step_frozen (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (next : OptionContinuation dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) (frozen : activation.learning = false) :
    (skill.optionStep activation next reward gain rng).1 = skill := by
  simp [Skill.optionStep, frozen]

/-- Termination retains the complete objective identity and untouched model owner. -/
theorem Skill.terminal_owners (skill : Skill config criterion dimension) (activation : OptionActivation mode)
    (potential : Potential) (reward terminal : Binary32) (gain : RewardRate) :
    (skill.terminateOption activation potential reward terminal gain).interest = skill.interest ∧
    (skill.terminateOption activation potential reward terminal gain).model = skill.model := by
  unfold terminateOption
  split <;> exact ⟨rfl, rfl⟩

end Acorn.Features
