/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Temporal

/-!
# Executable option expectation models

Sutton, Machado, Holland, Szepesvari, Timbers, Tanner and White,
*Reward-Respecting Subtasks for Model-Based Reinforcement Learning*, Artificial
Intelligence 324 (2023) 104001, arXiv:2202.03466v4, section 4, pp. 13–14: an
approximate option model has a reward part `r̂(x, o)` (equation (14)) and a
transition part `n̂(x, o) ≈ E[γᴷ x(S_K)]` (equation (15)), an expectation model in
the sense of Wan, Abbas, White, White and Sutton, *Planning with Expectation
Models*, IJCAI 2019, arXiv:1904.01191. Both parts are linear (equation (16)) and
each row of the transition part is learned by TD with cumulant zero (equation
(17)), which is how every row here is updated. Equation (17) passes the terminal
feature `x_j` unscaled to the TD error of equation (5); a row here takes `γ x_j`,
the target equation (15)'s `γᴷ` requires.
`AcornVerif.option_model_terminal_discount_correction` gives the difference for
every input.

Three adaptations are material.

* *Ranked subset.* The source's transition part is a `d × d` matrix. Here it reads
  and predicts only the ranked feature slots (`Acorn.RankedFeatures`), so it stores
  the square of the ranked width, and every row is an ordinary SwiftTD learner over
  the ranked positions. Per-weight step-size adaptation therefore applies to the
  matrix one row at a time, with no new mechanism: a row is one scalar prediction.
  One position is a constant input, so a row has a bias weight
  (`RankedFeatures.bias`).
* *Residual.* The value function reads all features, so the ranked features carry
  only part of an outcome's value. For each meta action the rest is its value at the
  outcome's unranked features, its unranked share. The share is learned in two parts
  whose sum is the share exactly: a shared residual, the outcome's nominal value
  minus the nominal value of its ranked features alone, which the full-width
  continuation learner predicts (`Transition.residual`); and the action's deviation
  from it, which one small learner per meta action predicts from the ranked
  positions and the bias (`Transition.outcome`). The value of the predicted outcome
  for one action is the current weights applied to the predicted ranked features,
  plus the predicted shared residual, plus that action's predicted deviation; the
  maximum or mean over actions is taken after (`Transition.outcomeValues`). Combined
  after instead, one scalar residual would hide a change at a ranked feature whenever
  the ranked values and the complete values are maximal at different actions. These
  are statements before rounding; the executed words follow within the rounding
  contracts of `AcornVerif.CurrentPlanning`. The
  deviations are predicted from the ranked positions alone, which is coarser than a
  full-width learner per action; how accurate they are is not known.
* *Action values.* The source's value function is one linear function of the
  features. Acorn's is the meta-controller's nominal value of four linear action
  values (PAR-2), so each action value of the predicted features is exactly linear
  in them and their nominal combination is not; `AcornVerif.CurrentPlanning` states
  the identity, the inequality that replaces Wan et al.'s §4 equality under the
  maximum, and the same inequality up to the tie window under the differential mean.

Wan, Naik & Sutton, *Average-Reward Learning and Planning with Options*, NeurIPS 34
(2021), section 5, equations (18)–(23), supplies the differential reward and
duration targets. Every update uses existing managed, criterion-indexed storage,
so retirement and assignment replacement reach the same state. Raw transient words
are retained.

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
  /-- Value of the predicted outcome: the current value function at the predicted
  ranked features plus the predicted residual; a raw differential sum or a
  discounted projection. -/
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

variable {dimension : Dimension} {criterion : Criterion}

/-- Each action value of an expected feature vector, read at the ranked slots alone:
`Σ_j w_a[slot j] · n_j` over the occupied positions in position order. Each is the
value function's own weights applied to the predicted features (Sutton, Machado et
al. (2023), §5, equation (19): `v̂(n̂(x, o), w)`), for one meta action. -/
def ValueFunction.rankedValues (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    Vector Binary32 metaCount.word.toNat :=
  let occupied := ranked.occupied
  value.controller.learners.map fun learner =>
    Binary32.sumMap .zero occupied fun entry =>
      (learner.state.weights.get entry.2).value.mul (expected.get entry.1).value

/-- Nominal value of an expected feature vector over the ranked slots: the same
maximum or policy mean `ValueFunction.nominal` takes of a frame's action values. -/
def ValueFunction.rankedNominal (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) : Binary32 :=
  comparisonValue criterion
    (⟨value.rankedValues ranked expected, value.epsilon⟩ : PolicySnapshot metaCount)

/-- The transition part's prediction at a row input: each row's ordered weight sum,
admitted as an expected feature value. -/
def Transition.expectedAt (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    Vector Expectation (rankDimension dimension).capacity :=
  transition.rows.map fun row =>
    Bounded32.project expectationRange (row.state.linearPrediction input)

/-- The transition part's prediction `n̂(x, o)` at a frame: each row's ordered weight
sum over the active ranked positions and the constant input, admitted as an expected
feature value. -/
def Transition.expected (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    Vector Expectation (rankDimension dimension).capacity :=
  transition.expectedAt (transition.ranked.input features)

/-- The value of the predicted outcome for each meta action: the current value weights
applied to the predicted ranked features, plus the predicted shared residual, plus
that action's predicted deviation. Each action's value is complete before any maximum
or mean is taken. The three parts are accumulated in binary64 and the total is
narrowed once, so a shared residual and a deviation that cancel do not absorb the
ranked part: the word is the total rounded at the total's own magnitude, whatever the
magnitudes of the parts (`AcornVerif.CurrentPlanning.outcome_value_rounding`). Before
rounding, a change in a ranked slot's weight for any action moves that action's value
by the change times the slot's predicted activity, at the next query and with no new
experience of the option (`AcornVerif.CurrentPlanning.outcome_value_propagation`); a
change smaller than the binary32 spacing at the word's magnitude can leave the word
as it was. -/
def Transition.outcomeValues (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Vector Binary32 metaCount.word.toNat :=
  let input := transition.ranked.input features
  let ranked := value.rankedValues transition.ranked (transition.expectedAt input)
  let wide := Conversion.widen shared
  Vector.ofFn fun action =>
    Conversion.narrow (((Conversion.widen (ranked.get action)).add wide).add
      (Conversion.widen ((transition.deviations.get action).state.linearPrediction input)))

/-- Nominal value of the predicted outcome: the maximum or policy mean of its
per-action values. -/
def Transition.lookahead (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Binary32 :=
  comparisonValue criterion
    (⟨transition.outcomeValues value features shared, value.epsilon⟩ : PolicySnapshot metaCount)

/-- The part of an observed frame's nominal value its ranked features do not carry:
the frame's nominal value minus the nominal value of its ranked features alone,
both under the same current weights and rate. -/
def Transition.residual (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Binary32 :=
  (value.nominal features).sub
    (value.rankedNominal transition.ranked (transition.ranked.indicator features))

/-- Terminal target of the continuation learner: the discounted residual of the
terminal frame. The terminal discount is retained as equation (15) requires. -/
def Transition.residualTarget (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Binary32 :=
  criterion.rule.gamma.mul (transition.residual value features)

/-- What a model learns from a terminal frame under the current value function: which
ranked slots are active, the discounted shared residual, and each meta action's
discounted deviation. An action's unranked share is its value at the frame minus its
value at the frame's ranked slots; its deviation is that share minus the shared
residual, so shared residual plus deviation is the share. -/
structure Outcome (dimension : Dimension) where
  /-- One at each active ranked position and zero elsewhere. -/
  seen : Vector Expectation (rankDimension dimension).capacity
  /-- Terminal target of the continuation learner. -/
  shared : Binary32
  /-- Terminal target of each meta action's deviation learner. -/
  deviations : Vector Binary32 metaCount.word.toNat

/-- Read a terminal frame once: the frame's action values, their part at the ranked
slots, the shared residual and every deviation, all under the same current weights. -/
def Transition.outcome (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Outcome dimension :=
  let seen := transition.ranked.indicator features
  let complete := value.controller.predictAll features
  let ranked := value.rankedValues transition.ranked seen
  let residual := (comparisonValue criterion
      (⟨complete, value.epsilon⟩ : PolicySnapshot metaCount)).sub
    (comparisonValue criterion (⟨ranked, value.epsilon⟩ : PolicySnapshot metaCount))
  ⟨seen, criterion.rule.gamma.mul residual, Vector.ofFn fun action =>
    criterion.rule.gamma.mul (((complete.get action).sub (ranked.get action)).sub residual)⟩

/-- The shared target an outcome carries is the residual target. -/
theorem Transition.outcome_shared (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (transition.outcome value features).shared = transition.residualTarget value features := rfl

/-- Update the row of every occupied position and every deviation learner. Callers
bind the ranked dimension, the learner configuration and the discount once, outside the
per-learner functions, so no update re-derives the ranked width. A vacant
position models no slot: its row is fresh, predicts nothing that is read, and is left
as it is, so the work of a model update is the number of occupied positions plus the
meta action count, and not the ranked width. -/
def Transition.updateRows (transition : Transition dimension criterion)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension)) :
    Transition dimension criterion :=
  let ⟨ranked, rows, deviations⟩ := transition
  ⟨ranked, rows.mapFinIdx fun index row bound =>
    if (ranked.slots[index]'bound).isSome then update ⟨index, bound⟩ row else row,
    deviations.mapFinIdx fun index learner bound => deviate ⟨index, bound⟩ learner⟩

/-- Start every modeled row's and every deviation learner's trajectory at the frame's
ranked features. -/
def Transition.begin (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Transition dimension criterion :=
  let input := transition.ranked.input features
  let rank := rankDimension dimension
  let config := criterion.config .demon
  transition.updateRows
    (fun _ row => Managed.apply (config := config) (dimension := rank) row
      (.beginTrajectory input) trivial)
    (fun _ learner => Managed.apply (config := config) (dimension := rank) learner
      (.beginTrajectory input) trivial)

/-- Credit a completed transition to every modeled row and deviation learner with
cumulant zero: equation (17) at `β = 0`. -/
def Transition.step (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Transition dimension criterion :=
  let input := transition.ranked.input features
  let rank := rankDimension dimension
  let config := criterion.config .demon
  transition.updateRows
    (fun _ row => Managed.apply (config := config) (dimension := rank) row
      (.step input .zero) trivial)
    (fun _ learner => Managed.apply (config := config) (dimension := rank) learner
      (.step input .zero) trivial)

/-- Close every modeled row toward `γ` times its own slot's indicator at the terminal
frame, equation (17) at `β = 1` with the discount equation (15) requires, and every
deviation learner toward its action's discounted deviation. -/
def Transition.terminal (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Transition dimension criterion :=
  let rank := rankDimension dimension
  let config := criterion.config .demon
  let gamma := criterion.rule.gamma
  transition.updateRows
    (fun position row => Managed.apply (config := config) (dimension := rank) row
      (.terminal (gamma.mul (outcome.seen.get position).value)) trivial)
    (fun action learner => Managed.apply (config := config) (dimension := rank) learner
      (.terminal (outcome.deviations.get action)) trivial)

/-- Evaluate current stored learners at the actual age-augmented input, under the
current value function. The reward and residual read the age-augmented features;
the transition rows read the ranked features, which carry no age. -/
def Model.predict (model : Model dimension criterion) (value : ValueFunction criterion dimension)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) : ModelPrediction criterion :=
  let features := modelInput criterion base age
  match model with
  | .discounted reward continuation transition =>
    ⟨Bounded32.project _ (reward.state.predict features),
      Criterion.discounted.modelContinuation
        (transition.lookahead value base (continuation.state.linearPrediction features)),
      Bounded32.project _ .one⟩
  | .differential reward continuation duration transition =>
    ⟨Bounded32.project _ (reward.state.predict features),
      transition.lookahead value base (continuation.state.linearPrediction features),
      Bounded32.project _ (duration.state.predict features)⟩

/-- Prime all model learners on initiation features at age zero. -/
def Model.begin (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) :
    Model dimension criterion :=
  let features := modelInput criterion base ⟨0, by decide⟩
  match model with
  | .discounted r c t =>
    .discounted (r.apply (.beginTrajectory features) trivial)
      (c.apply (.beginTrajectory features) trivial) (t.begin base)
  | .differential r c d t =>
    .differential (r.apply (.beginTrajectory features) trivial)
      (c.apply (.beginTrajectory features) trivial) (d.apply (.beginTrajectory features) trivial)
      (t.begin base)

/-- Raw reward, zero continuation and transition cumulants, unit duration; no gain
enters learning. -/
def Model.step (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (reward : Binary32) : Model dimension criterion :=
  let features := modelInput criterion base age
  match model with
  | .discounted r c t =>
    .discounted (r.apply (.step features reward) trivial) (c.apply (.step features .zero) trivial)
      (t.step base)
  | .differential r c d t =>
    .differential (r.apply (.step features reward) trivial) (c.apply (.step features .zero) trivial)
      (d.apply (.step features .one) trivial) (t.step base)

/-- Close every learner through the terminal entry that clears its transient state,
at the terminal frame: raw reward, the discounted shared residual of the frame's
nominal value, unit duration, each ranked slot's discounted indicator and each meta
action's discounted deviation. -/
def Model.terminal (model : Model dimension criterion) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) : Model dimension criterion :=
  match model with
  | .discounted r c t =>
    let outcome := t.outcome value features
    .discounted (r.apply (.terminal reward) trivial) (c.apply (.terminal outcome.shared) trivial)
      (t.terminal outcome)
  | .differential r c d t =>
    let outcome := t.outcome value features
    .differential (r.apply (.terminal reward) trivial)
      (c.apply (.terminal outcome.shared) trivial) (d.apply (.terminal .one) trivial)
      (t.terminal outcome)

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

/-- Start every modeled row's and every deviation learner's trajectory on existing
storage, without a transient clear. -/
def Transition.restart (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Transition dimension criterion :=
  let input := transition.ranked.input features
  let rank := rankDimension dimension
  let config := criterion.config .demon
  transition.updateRows
    (fun _ row => Managed.restartTrajectory (config := config) (dimension := rank) row input)
    (fun _ learner =>
      Managed.restartTrajectory (config := config) (dimension := rank) learner input)

/-- Close every modeled row's and every deviation learner's stored trajectory toward
the targets `Transition.terminal` reads. -/
def Transition.stop (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Transition dimension criterion :=
  let rank := rankDimension dimension
  let config := criterion.config .demon
  let gamma := criterion.rule.gamma
  transition.updateRows
    (fun position row => Managed.stopTrajectory (config := config) (dimension := rank) row
      (gamma.mul (outcome.seen.get position).value))
    (fun action learner => Managed.stopTrajectory (config := config) (dimension := rank)
      learner (outcome.deviations.get action))

/-- Start a model trajectory at the given age for an option that is not executing,
without the full-width transient clear of `Model.begin`. -/
def Model.restart (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Model dimension criterion :=
  let features := modelInput criterion base age
  match model with
  | .discounted r c t =>
    .discounted (r.restartTrajectory features) (c.restartTrajectory features) (t.restart base)
  | .differential r c d t =>
    .differential (r.restartTrajectory features) (c.restartTrajectory features)
      (d.restartTrajectory features) (t.restart base)

/-- Close a live trajectory toward the targets `Model.terminal` reads, at the stopping
frame. Sutton, Machado et al. (2023), §4, equation (17), stops every option's model
where its stopping function does. -/
def Model.stop (model : Model dimension criterion) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) : Model dimension criterion :=
  match model with
  | .discounted r c t =>
    let outcome := t.outcome value features
    .discounted (r.stopTrajectory reward) (c.stopTrajectory outcome.shared) (t.stop outcome)
  | .differential r c d t =>
    let outcome := t.outcome value features
    .differential (r.stopTrajectory reward) (c.stopTrajectory outcome.shared)
      (d.stopTrajectory .one) (t.stop outcome)

/-- Concrete temporal operations use the current model definitions. -/
def modelOperations (criterion : Criterion) (dimension : Dimension) : OptionModelOps criterion dimension :=
  ⟨Model.begin, Model.step, Model.terminal, fun model value features =>
    (model.predict value features ⟨0, by decide⟩).cache, Model.restart, Model.stop⟩

/-- The backed-up value of a frame under one option: reward part plus the value of the
predicted outcome (Sutton, Machado et al. (2023), §5, p. 17). The differential form
subtracts gain times duration and writes no gain; the discounted form projects to
the horizon. -/
def ModelPrediction.target {criterion : Criterion} (prediction : ModelPrediction criterion)
    (gain : RewardRate) : Binary32 :=
  match criterion with
  | .discounted => (Prediction.project .g99 (prediction.reward.value.add prediction.continuation)).value
  | .differential => (prediction.reward.value.sub (gain.value.mul prediction.duration.value)).add prediction.continuation

/-- Producer ranges hold for every state, value function and input word. -/
theorem Model.predict_ranges (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    criterion.modelRewardRange.Contains (model.predict value base age).reward.value ∧
    modelDurationRange.Contains (model.predict value base age).duration.value :=
  ⟨(model.predict value base age).reward.legal, (model.predict value base age).duration.legal⟩

/-- Differential continuation passes through unchanged. -/
theorem differential_model_continuation (raw : Binary32) :
    Criterion.differential.modelContinuation raw = raw := rfl

/-- Every predicted feature value is a finite word in `[0, 1]`, for every row state
and every frame, because it is stored through the range's projection. -/
theorem Transition.expected_legal (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) (position : RankIdx dimension) :
    expectationRange.Contains ((transition.expected features).get position).value :=
  ((transition.expected features).get position).legal

/-- A model update changes no ranked slot and no row of a vacant position. -/
theorem Transition.updateRows_frame (transition : Transition dimension criterion)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension)) :
    (transition.updateRows update deviate).ranked = transition.ranked ∧
      ∀ position : RankIdx dimension, transition.ranked.slots[position.val] = none →
        (transition.updateRows update deviate).rows[position.val] =
          transition.rows[position.val] := by
  refine ⟨rfl, fun position vacant => ?_⟩
  simp [Transition.updateRows, vacant]

/-- A model that ranks no slot has no occupied position. -/
theorem RankedFeatures.empty_occupied (dimension : Dimension) :
    (RankedFeatures.empty dimension).occupied = [] := by
  simp [RankedFeatures.occupied, RankedFeatures.empty, RankedFeatures.ofSlots]

end Acorn.Features
