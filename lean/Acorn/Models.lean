/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Temporal

/-!
# Executable scalar option models

Sutton, Machado et al., *Reward-Respecting Subtasks for Model-Based Reinforcement
Learning*, Artificial Intelligence 324 (2023) 104001, arXiv:2202.03466v4,
section 4, equations (15)–(17): terminal continuation includes gamma, as
required by equation (15). The retained universal
`option_model_terminal_discount_correction` characterizes this correction.
Wan, Naik & Sutton, *Average-Reward Learning and Planning with Options*,
NeurIPS 34 (2021), section 5, equations (18)–(23), supplies the differential
reward, duration and continuation targets. The scalar continuation tracks a
changing controller through scalar approximations.
Every update uses existing managed, criterion-indexed storage, so retirement
and assignment replacement reach the same state. Raw transient words are retained.

Sutton, Precup & Singh, *Between MDPs and semi-MDPs*, Artificial Intelligence 112
(1999), §5, equations (18)–(19), p. 202, learn a model from every action
consistent with its option: selected with the option policy's own distribution.
The restart and stop entries below serve that use: an option that is not executing
learns along runs of frames whose action was so selected.
-/
namespace Acorn.Features

/-- Nonnegative reward range derives from the immutable criterion. -/
def Criterion.modelRewardRange : Criterion → Interval32
  | .discounted => Discount.predictionRange .g99
  | .differential => ⟨.zero, Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64,
      by decide, by decide, by decide⟩

/-- Nonempty capped option duration in primitive steps. -/
def modelDurationRange : Interval32 :=
  ⟨.one, Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64,
    by decide, by decide, by decide⟩

/-- Projected reward and duration with raw signed aggregate continuation. -/
structure ModelPrediction (criterion : Criterion) where
  /-- Producer-projected reward. -/
  reward : Bounded32 criterion.modelRewardRange
  /-- Raw differential sum or discounted projection. -/
  continuation : Binary32
  /-- Positive bounded primitive duration. -/
  duration : Bounded32 modelDurationRange

/-- Cache words are observations, never the source of planning targets. -/
def ModelPrediction.cache {criterion : Criterion} (prediction : ModelPrediction criterion) : ModelCache :=
  ⟨prediction.reward.value, prediction.continuation, prediction.duration.value⟩

/-- Differential continuation retains its raw aggregate coordinate. -/
def Criterion.modelContinuation (criterion : Criterion) (raw : Binary32) : Binary32 :=
  match criterion with
  | .discounted => (Prediction.project .g99 raw).value
  | .differential => raw

/-- Terminal gamma is retained in the exact machine operation order. -/
def Criterion.modelTerminal (criterion : Criterion) (raw : Binary32) : Binary32 :=
  criterion.rule.gamma.mul (criterion.modelContinuation raw)

/-- Evaluate current stored learners at the actual age-augmented input. -/
def Model.predict {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    ModelPrediction criterion :=
  let features := modelInput criterion base age
  match model with
  | .discounted reward continuation =>
    ⟨Bounded32.project _ (reward.state.predict features),
      Criterion.discounted.modelContinuation (continuation.state.linearPrediction features),
      Bounded32.project _ .one⟩
  | .differential reward continuation duration =>
    ⟨Bounded32.project _ (reward.state.predict features), continuation.state.linearPrediction features,
      Bounded32.project _ (duration.state.predict features)⟩

/-- Prime all model learners on initiation features at age zero. -/
def Model.begin {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) : Model dimension criterion :=
  let features := modelInput criterion base ⟨0, by decide⟩
  match model with
  | .discounted r c =>
    .discounted (r.apply (.beginTrajectory features) trivial) (c.apply (.beginTrajectory features) trivial)
  | .differential r c d =>
    .differential (r.apply (.beginTrajectory features) trivial) (c.apply (.beginTrajectory features) trivial)
      (d.apply (.beginTrajectory features) trivial)

/-- Raw reward, zero continuation cumulant, unit duration; no gain enters learning. -/
def Model.step {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) (age : ModelAge)
    (reward : Binary32) : Model dimension criterion :=
  let features := modelInput criterion base age
  match model with
  | .discounted r c =>
    .discounted (r.apply (.step features reward) trivial) (c.apply (.step features .zero) trivial)
  | .differential r c d =>
    .differential (r.apply (.step features reward) trivial) (c.apply (.step features .zero) trivial)
      (d.apply (.step features .one) trivial)

/-- Close every learner through the terminal entry that clears its transient state. -/
def Model.terminal {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (reward terminal : Binary32) : Model dimension criterion :=
  let target := criterion.modelTerminal terminal
  match model with
  | .discounted r c =>
    .discounted (r.apply (.terminal reward) trivial) (c.apply (.terminal target) trivial)
  | .differential r c d =>
    .differential (r.apply (.terminal reward) trivial) (c.apply (.terminal target) trivial)
      (d.apply (.terminal .one) trivial)

/-- Start one learner's trajectory on its existing storage. The remaining traces are
released first, so the ordinary step visits no earlier trace and credits no earlier
transition; it lays the initial traces and both lags. -/
def Managed.restartTrajectory {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (features : SwiftTd.ActiveSet dimension) :
    Managed config dimension :=
  (learner.apply .release trivial).apply (.step features .zero) trivial

/-- Stopping credit for one learner against its own lags, at zero trace decay:
the factor γλ(1 − β) of Sutton, Machado et al. (2023), §3, at β = 1. Whatever the
first loop retained is then released, so nothing stays eligible. -/
def Managed.stopTrajectory {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (target : Binary32) : Managed config dimension :=
  (learner.apply (.first (target.sub learner.state.transient.vOld)
    learner.state.transient.vDelta .zero) trivial).apply .release trivial

/-- Start a model trajectory at the given age for an option that is not executing,
without the full-width transient clear of `Model.begin`. -/
def Model.restart {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    Model dimension criterion :=
  let features := modelInput criterion base age
  match model with
  | .discounted r c => .discounted (r.restartTrajectory features) (c.restartTrajectory features)
  | .differential r c d =>
    .differential (r.restartTrajectory features) (c.restartTrajectory features)
      (d.restartTrajectory features)

/-- Close a live trajectory toward raw reward, the discounted terminal continuation
and unit duration, the targets `Model.terminal` reads. Sutton, Machado et al.
(2023), §4, equation (17), stops every option's model where its stopping function does. -/
def Model.stop {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (reward terminal : Binary32) : Model dimension criterion :=
  let target := criterion.modelTerminal terminal
  match model with
  | .discounted r c => .discounted (r.stopTrajectory reward) (c.stopTrajectory target)
  | .differential r c d =>
    .differential (r.stopTrajectory reward) (c.stopTrajectory target) (d.stopTrajectory .one)

/-- Concrete temporal operations use the current model definitions. -/
def modelOperations (criterion : Criterion) (dimension : Dimension) : OptionModelOps criterion dimension :=
  ⟨Model.begin, Model.step, Model.terminal, fun model features =>
    (model.predict features ⟨0, by decide⟩).cache, Model.restart, Model.stop⟩

/-- Signed differential backup without a gain write; discounted horizon projection. -/
def ModelPrediction.target {criterion : Criterion} (prediction : ModelPrediction criterion)
    (gain : RewardRate) : Binary32 :=
  match criterion with
  | .discounted => (Prediction.project .g99 (prediction.reward.value.add prediction.continuation)).value
  | .differential => (prediction.reward.value.sub (gain.value.mul prediction.duration.value)).add prediction.continuation

/-- Producer ranges hold for every state and input word. -/
theorem Model.predict_ranges {dimension : Dimension} {criterion : Criterion}
    (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) (age : ModelAge) :
    criterion.modelRewardRange.Contains (model.predict base age).reward.value ∧
    modelDurationRange.Contains (model.predict base age).duration.value :=
  ⟨(model.predict base age).reward.legal, (model.predict base age).duration.legal⟩

/-- Differential continuation passes through unchanged before terminal multiplication. -/
theorem differential_model_continuation (raw : Binary32) :
    Criterion.differential.modelContinuation raw = raw := rfl

end Acorn.Features
