import Acorn.Temporal

namespace Acorn.Features

def Criterion.modelRewardRange : Criterion → Interval32
  | .discounted => Discount.predictionRange .g99
  | .differential => ⟨.zero, Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64,
      by decide, by decide, by decide⟩

def modelDurationRange : Interval32 :=
  ⟨.one, Binary32.ofUInt64 Acorn.FeatureConstants.optionMaxDuration.toUInt64,
    by decide, by decide, by decide⟩

structure ModelPrediction (criterion : Criterion) where
  reward : Bounded32 criterion.modelRewardRange
  continuation : Binary32
  duration : Bounded32 modelDurationRange

def ModelPrediction.cache {criterion : Criterion} (prediction : ModelPrediction criterion) : ModelCache :=
  ⟨prediction.reward.value, prediction.continuation, prediction.duration.value⟩

def Criterion.modelContinuation (criterion : Criterion) (raw : Binary32) : Binary32 :=
  match criterion with
  | .discounted => (Prediction.project .g99 raw).value
  | .differential => raw

variable {dimension : Dimension} {criterion : Criterion}

def ValueFunction.rankedValuesCosted (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    Costed (Vector Binary32 metaCount.word.toNat) := do
  let occupied ← ranked.occupiedCosted
  Costed.mapVector (fun learner => Binary32.sumMapCosted .productTerm .zero occupied fun entry =>
    Costed.pure ((learner.state.weights.get entry.2).value.mul (expected.get entry.1).value))
    value.controller.learners

def ValueFunction.rankedValues (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    Vector Binary32 metaCount.word.toNat :=
  (value.rankedValuesCosted ranked expected).val

theorem ValueFunction.rankedValues_def (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    value.rankedValues ranked expected =
      value.controller.learners.map fun learner =>
        Binary32.sumMap .zero ranked.occupied fun entry =>
          (learner.state.weights.get entry.2).value.mul (expected.get entry.1).value := rfl

def ValueFunction.rankedNominal (value : ValueFunction criterion dimension)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) : Binary32 :=
  comparisonValue criterion
    (⟨value.rankedValues ranked expected, value.epsilon⟩ : PolicySnapshot metaCount)

def Transition.expectedAtCosted (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    Costed (Vector Expectation (rankDimension dimension).capacity) :=
  Costed.mapVector (fun row => do
    let range := expectationRange
    let raw ← row.state.linearPredictionCosted input
    Costed.op .project (Bounded32.project range raw)) transition.rows

def Transition.expectedAt (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    Vector Expectation (rankDimension dimension).capacity :=
  (transition.expectedAtCosted input).val

theorem Transition.expectedAt_def (transition : Transition dimension criterion)
    (input : SwiftTd.ActiveSet (rankDimension dimension)) :
    transition.expectedAt input = transition.rows.map fun row =>
      Bounded32.project expectationRange (row.state.linearPrediction input) := rfl

def Transition.expected (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    Vector Expectation (rankDimension dimension).capacity :=
  transition.expectedAt (transition.ranked.input features)

def Transition.outcomeValuesCosted (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Costed (Vector Binary32 metaCount.word.toNat) := do
  let input ← transition.ranked.inputCosted features
  let expected ← transition.expectedAtCosted input
  let ranked ← value.rankedValuesCosted transition.ranked expected
  let wide := Conversion.widen shared
  Costed.ofFn fun action => do
    let shared64 := (Conversion.widen (ranked.get action)).add wide
    let deviation ← (transition.deviations.get action).state.linearPredictionCosted input
    Costed.op .outcomeValue (Conversion.narrow (shared64.add (Conversion.widen deviation)))

def Transition.outcomeValues (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Vector Binary32 metaCount.word.toNat :=
  (transition.outcomeValuesCosted value features shared).val

theorem Transition.outcomeValues_def (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    transition.outcomeValues value features shared =
      let input := transition.ranked.input features
      let ranked := value.rankedValues transition.ranked (transition.expectedAt input)
      let wide := Conversion.widen shared
      Vector.ofFn fun action =>
        Conversion.narrow (((Conversion.widen (ranked.get action)).add wide).add
          (Conversion.widen ((transition.deviations.get action).state.linearPrediction input))) :=
  rfl

def Transition.lookaheadCosted (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Costed Binary32 := do
  let actions := metaCount
  let values ← transition.outcomeValuesCosted value features shared
  comparisonValueCosted (count := actions) criterion
    (⟨values, value.epsilon⟩ : PolicySnapshot actions)

def Transition.lookahead (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) : Binary32 :=
  (transition.lookaheadCosted value features shared).val

theorem Transition.lookahead_def (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (shared : Binary32) :
    transition.lookahead value features shared = comparisonValue criterion
      (⟨transition.outcomeValues value features shared, value.epsilon⟩ :
        PolicySnapshot metaCount) := rfl

def Transition.residual (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Binary32 :=
  (value.nominal features).sub
    (value.rankedNominal transition.ranked (transition.ranked.indicator features))

def Transition.residualTarget (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Binary32 :=
  criterion.rule.gamma.mul (transition.residual value features)

structure Outcome (dimension : Dimension) where
  seen : Vector Expectation (rankDimension dimension).capacity
  shared : Binary32
  deviations : Vector Binary32 metaCount.word.toNat

def Transition.outcomeCosted (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Costed (Outcome dimension) := do
  let seen ← transition.ranked.indicatorCosted features
  let complete ← value.controller.predictAllCosted features
  let ranked ← value.rankedValuesCosted transition.ranked seen
  let all ← comparisonValueCosted criterion
    (⟨complete, value.epsilon⟩ : PolicySnapshot metaCount)
  let part ← comparisonValueCosted criterion
    (⟨ranked, value.epsilon⟩ : PolicySnapshot metaCount)
  let residual := all.sub part
  let shared := criterion.rule.gamma.mul residual
  let deviations ← Costed.ofFn fun action => Costed.op .deviation
    (criterion.rule.gamma.mul (((complete.get action).sub (ranked.get action)).sub residual))
  Costed.pure ⟨seen, shared, deviations⟩

def Transition.outcome (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    Outcome dimension :=
  (transition.outcomeCosted value features).val

theorem Transition.outcome_def (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    transition.outcome value features =
      let seen := transition.ranked.indicator features
      let complete := value.controller.predictAll features
      let ranked := value.rankedValues transition.ranked seen
      let residual := (comparisonValue criterion
          (⟨complete, value.epsilon⟩ : PolicySnapshot metaCount)).sub
        (comparisonValue criterion (⟨ranked, value.epsilon⟩ : PolicySnapshot metaCount))
      ⟨seen, criterion.rule.gamma.mul residual, Vector.ofFn fun action =>
        criterion.rule.gamma.mul
          (((complete.get action).sub (ranked.get action)).sub residual)⟩ := rfl

theorem Transition.outcome_shared (transition : Transition dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (transition.outcome value features).shared = transition.residualTarget value features := rfl

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

def Transition.updateRowsCosted (transition : Transition dimension criterion)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Costed (Managed (criterion.config .demon) (rankDimension dimension)))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Costed (Managed (criterion.config .demon) (rankDimension dimension))) :
    Costed (Transition dimension criterion) :=
  let ⟨ranked, rows, deviations⟩ := transition
  do
    let updated ← Costed.mapFinIdx rows fun index row bound =>
      Costed.ite ((ranked.slots[index]'bound).isSome = true)
        (fun _ => update ⟨index, bound⟩ row) fun _ => Costed.pure row
    let deviated ← Costed.mapFinIdx deviations fun index learner bound =>
      deviate ⟨index, bound⟩ learner
    Costed.op .modelClose ⟨ranked, updated, deviated⟩

theorem Transition.updateRows_costed (transition : Transition dimension criterion)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension)) :
    transition.updateRows update deviate =
      (transition.updateRowsCosted (fun position row => Costed.pure (update position row))
        (fun action learner => Costed.pure (deviate action learner))).val := by
  cases transition
  rfl

def Transition.beginCosted (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) := do
  let input ← transition.ranked.inputCosted features
  let rank := rankDimension dimension
  let config := criterion.config .demon
  Costed.charge .rankWidth (transition.updateRowsCosted
    (fun _ row => Managed.applyCosted (config := config) (dimension := rank) row
      (.beginTrajectory input) trivial)
    (fun _ learner => Managed.applyCosted (config := config) (dimension := rank) learner
      (.beginTrajectory input) trivial))

def Transition.begin (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Transition dimension criterion :=
  (transition.beginCosted features).val

theorem Transition.begin_def (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    transition.begin features =
      let input := transition.ranked.input features
      let rank := rankDimension dimension
      let config := criterion.config .demon
      transition.updateRows
        (fun _ row => Managed.apply (config := config) (dimension := rank) row
          (.beginTrajectory input) trivial)
        (fun _ learner => Managed.apply (config := config) (dimension := rank) learner
          (.beginTrajectory input) trivial) := by
  cases transition
  rfl

def Transition.stepCosted (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) := do
  let input ← transition.ranked.inputCosted features
  let rank := rankDimension dimension
  let config := criterion.config .demon
  Costed.charge .rankWidth (transition.updateRowsCosted
    (fun _ row => Managed.applyCosted (config := config) (dimension := rank) row
      (.step input .zero) trivial)
    (fun _ learner => Managed.applyCosted (config := config) (dimension := rank) learner
      (.step input .zero) trivial))

def Transition.step (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Transition dimension criterion :=
  (transition.stepCosted features).val

theorem Transition.step_def (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    transition.step features =
      let input := transition.ranked.input features
      let rank := rankDimension dimension
      let config := criterion.config .demon
      transition.updateRows
        (fun _ row => Managed.apply (config := config) (dimension := rank) row
          (.step input .zero) trivial)
        (fun _ learner => Managed.apply (config := config) (dimension := rank) learner
          (.step input .zero) trivial) := by
  cases transition
  rfl

def Transition.terminalCosted (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  let rank := rankDimension dimension
  let config := criterion.config .demon
  let gamma := criterion.rule.gamma
  Costed.charge .rankWidth (transition.updateRowsCosted
    (fun position row =>
      let target := gamma.mul (outcome.seen.get position).value
      Costed.charge .learnerError (Managed.applyCosted (config := config) (dimension := rank) row
        (.terminal target) trivial))
    (fun action learner =>
      let target := outcome.deviations.get action
      Costed.charge .learnerError (Managed.applyCosted (config := config) (dimension := rank)
        learner (.terminal target) trivial)))

def Transition.terminal (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Transition dimension criterion :=
  (transition.terminalCosted outcome).val

theorem Transition.terminal_def (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    transition.terminal outcome =
      let rank := rankDimension dimension
      let config := criterion.config .demon
      let gamma := criterion.rule.gamma
      transition.updateRows
        (fun position row => Managed.apply (config := config) (dimension := rank) row
          (.terminal (gamma.mul (outcome.seen.get position).value)) trivial)
        (fun action learner => Managed.apply (config := config) (dimension := rank) learner
          (.terminal (outcome.deviations.get action)) trivial) := by
  cases transition
  rfl

def Model.predictCosted (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (ModelPrediction criterion) :=
  Costed.bind (modelInputCosted criterion base age) fun features =>
  match model with
  | .discounted reward continuation transition => do
    let range := Criterion.discounted.modelRewardRange
    let r ← reward.state.predictCosted features
    let rewardWord := Bounded32.project range r
    let c ← continuation.state.linearPredictionCosted features
    let look ← transition.lookaheadCosted value base c
    Costed.op .prediction ⟨rewardWord, Criterion.discounted.modelContinuation look,
      Bounded32.project _ .one⟩
  | .differential reward continuation duration transition => do
    let range := Criterion.differential.modelRewardRange
    let r ← reward.state.predictCosted features
    let rewardWord := Bounded32.project range r
    let c ← continuation.state.linearPredictionCosted features
    let look ← transition.lookaheadCosted value base c
    let durationRange := modelDurationRange
    let d ← duration.state.predictCosted features
    Costed.op .prediction ⟨rewardWord, look, Bounded32.project durationRange d⟩

def Model.predict (model : Model dimension criterion) (value : ValueFunction criterion dimension)
    (base : SwiftTd.ActiveSet dimension) (age : ModelAge) : ModelPrediction criterion :=
  (model.predictCosted value base age).val

theorem Model.predict_def (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    model.predict value base age =
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
          Bounded32.project _ (duration.state.predict features)⟩ := by
  cases model <;> rfl

def Model.beginCosted (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) :
    Costed (Model dimension criterion) :=
  Costed.bind (modelInputCosted criterion base ⟨0, by decide⟩) fun features =>
  match model with
  | .discounted r c t => do
    let r ← r.applyCosted (.beginTrajectory features) trivial
    let c ← c.applyCosted (.beginTrajectory features) trivial
    let t ← t.beginCosted base
    Costed.op .modelClose (.discounted r c t)
  | .differential r c d t => do
    let r ← r.applyCosted (.beginTrajectory features) trivial
    let c ← c.applyCosted (.beginTrajectory features) trivial
    let d ← d.applyCosted (.beginTrajectory features) trivial
    let t ← t.beginCosted base
    Costed.op .modelClose (.differential r c d t)

def Model.begin (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) :
    Model dimension criterion :=
  (model.beginCosted base).val

theorem Model.begin_def (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension) :
    model.begin base =
      let features := modelInput criterion base ⟨0, by decide⟩
      match model with
      | .discounted r c t =>
        .discounted (r.apply (.beginTrajectory features) trivial)
          (c.apply (.beginTrajectory features) trivial) (t.begin base)
      | .differential r c d t =>
        .differential (r.apply (.beginTrajectory features) trivial)
          (c.apply (.beginTrajectory features) trivial)
          (d.apply (.beginTrajectory features) trivial) (t.begin base) := by
  cases model <;> rfl

def Model.stepCosted (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (reward : Binary32) : Costed (Model dimension criterion) :=
  Costed.bind (modelInputCosted criterion base age) fun features =>
  match model with
  | .discounted r c t => do
    let r ← r.applyCosted (.step features reward) trivial
    let c ← c.applyCosted (.step features .zero) trivial
    let t ← t.stepCosted base
    Costed.op .modelClose (.discounted r c t)
  | .differential r c d t => do
    let r ← r.applyCosted (.step features reward) trivial
    let c ← c.applyCosted (.step features .zero) trivial
    let d ← d.applyCosted (.step features .one) trivial
    let t ← t.stepCosted base
    Costed.op .modelClose (.differential r c d t)

def Model.step (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (reward : Binary32) : Model dimension criterion :=
  (model.stepCosted base age reward).val

theorem Model.step_def (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) (reward : Binary32) :
    model.step base age reward =
      let features := modelInput criterion base age
      match model with
      | .discounted r c t =>
        .discounted (r.apply (.step features reward) trivial)
          (c.apply (.step features .zero) trivial) (t.step base)
      | .differential r c d t =>
        .differential (r.apply (.step features reward) trivial)
          (c.apply (.step features .zero) trivial) (d.apply (.step features .one) trivial)
          (t.step base) := by
  cases model <;> rfl

def Model.terminalCosted (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  match model with
  | .discounted r c t => do
    let outcome ← t.outcomeCosted value features
    let r ← r.applyCosted (.terminal reward) trivial
    let c ← c.applyCosted (.terminal outcome.shared) trivial
    let t ← t.terminalCosted outcome
    Costed.op .modelClose (.discounted r c t)
  | .differential r c d t => do
    let outcome ← t.outcomeCosted value features
    let r ← r.applyCosted (.terminal reward) trivial
    let c ← c.applyCosted (.terminal outcome.shared) trivial
    let d ← d.applyCosted (.terminal .one) trivial
    let t ← t.terminalCosted outcome
    Costed.op .modelClose (.differential r c d t)

def Model.terminal (model : Model dimension criterion) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) : Model dimension criterion :=
  (model.terminalCosted value features reward).val

theorem Model.terminal_def (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    model.terminal value features reward =
      match model with
      | .discounted r c t =>
        let outcome := t.outcome value features
        .discounted (r.apply (.terminal reward) trivial)
          (c.apply (.terminal outcome.shared) trivial) (t.terminal outcome)
      | .differential r c d t =>
        let outcome := t.outcome value features
        .differential (r.apply (.terminal reward) trivial)
          (c.apply (.terminal outcome.shared) trivial) (d.apply (.terminal .one) trivial)
          (t.terminal outcome) := by
  cases model <;> rfl

def Managed.restartTrajectoryCosted {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (features : SwiftTd.ActiveSet dimension) :
    Costed (Managed config dimension) := do
  let released ← learner.applyCosted .release trivial
  released.applyCosted (.step features .zero) trivial

def Managed.restartTrajectory {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (features : SwiftTd.ActiveSet dimension) :
    Managed config dimension :=
  (learner.restartTrajectoryCosted features).val

theorem Managed.restartTrajectory_def {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (features : SwiftTd.ActiveSet dimension) :
    learner.restartTrajectory features =
      (learner.apply .release trivial).apply (.step features .zero) trivial := rfl

def Managed.stopTrajectoryCosted {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (target : Binary32) : Costed (Managed config dimension) :=
  let error := target.sub learner.state.transient.vOld
  Costed.charge .learnerError do
    let first ← Costed.attach
      (learner.applyCosted (.first error learner.state.transient.vDelta .zero) trivial)
    first.val.applyCosted .release (by rw [first.property]; trivial)

def Managed.stopTrajectory {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (target : Binary32) : Managed config dimension :=
  (learner.stopTrajectoryCosted target).val

theorem Managed.stopTrajectory_def {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (target : Binary32) :
    learner.stopTrajectory target =
      (learner.apply (.first (target.sub learner.state.transient.vOld)
        learner.state.transient.vDelta .zero) trivial).apply .release trivial := rfl

def Transition.restartCosted (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Costed (Transition dimension criterion) := do
  let input ← transition.ranked.inputCosted features
  let rank := rankDimension dimension
  let config := criterion.config .demon
  Costed.charge .rankWidth (transition.updateRowsCosted
    (fun _ row => Managed.restartTrajectoryCosted (config := config) (dimension := rank) row input)
    (fun _ learner =>
      Managed.restartTrajectoryCosted (config := config) (dimension := rank) learner input))

def Transition.restart (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) : Transition dimension criterion :=
  (transition.restartCosted features).val

theorem Transition.restart_def (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) :
    transition.restart features =
      let input := transition.ranked.input features
      let rank := rankDimension dimension
      let config := criterion.config .demon
      transition.updateRows
        (fun _ row => Managed.restartTrajectory (config := config) (dimension := rank) row input)
        (fun _ learner =>
          Managed.restartTrajectory (config := config) (dimension := rank) learner input) := by
  cases transition
  rfl

def Transition.stopCosted (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Costed (Transition dimension criterion) :=
  let rank := rankDimension dimension
  let config := criterion.config .demon
  let gamma := criterion.rule.gamma
  Costed.charge .rankWidth (transition.updateRowsCosted
    (fun position row =>
      let target := gamma.mul (outcome.seen.get position).value
      Costed.charge .learnerError
        (Managed.stopTrajectoryCosted (config := config) (dimension := rank) row target))
    (fun action learner =>
      let target := outcome.deviations.get action
      Costed.charge .learnerError
        (Managed.stopTrajectoryCosted (config := config) (dimension := rank) learner target)))

def Transition.stop (transition : Transition dimension criterion)
    (outcome : Outcome dimension) : Transition dimension criterion :=
  (transition.stopCosted outcome).val

theorem Transition.stop_def (transition : Transition dimension criterion)
    (outcome : Outcome dimension) :
    transition.stop outcome =
      let rank := rankDimension dimension
      let config := criterion.config .demon
      let gamma := criterion.rule.gamma
      transition.updateRows
        (fun position row => Managed.stopTrajectory (config := config) (dimension := rank) row
          (gamma.mul (outcome.seen.get position).value))
        (fun action learner => Managed.stopTrajectory (config := config) (dimension := rank)
          learner (outcome.deviations.get action)) := by
  cases transition
  rfl

def Model.restartCosted (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Costed (Model dimension criterion) :=
  Costed.bind (modelInputCosted criterion base age) fun features =>
  match model with
  | .discounted r c t => do
    let r ← r.restartTrajectoryCosted features
    let c ← c.restartTrajectoryCosted features
    let t ← t.restartCosted base
    Costed.op .modelClose (.discounted r c t)
  | .differential r c d t => do
    let r ← r.restartTrajectoryCosted features
    let c ← c.restartTrajectoryCosted features
    let d ← d.restartTrajectoryCosted features
    let t ← t.restartCosted base
    Costed.op .modelClose (.differential r c d t)

def Model.restart (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) : Model dimension criterion :=
  (model.restartCosted base age).val

theorem Model.restart_def (model : Model dimension criterion) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    model.restart base age =
      let features := modelInput criterion base age
      match model with
      | .discounted r c t =>
        .discounted (r.restartTrajectory features) (c.restartTrajectory features) (t.restart base)
      | .differential r c d t =>
        .differential (r.restartTrajectory features) (c.restartTrajectory features)
          (d.restartTrajectory features) (t.restart base) := by
  cases model <;> rfl

def Model.stopCosted (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) : Costed (Model dimension criterion) :=
  match model with
  | .discounted r c t => do
    let outcome ← t.outcomeCosted value features
    let r ← r.stopTrajectoryCosted reward
    let c ← c.stopTrajectoryCosted outcome.shared
    let t ← t.stopCosted outcome
    Costed.op .modelClose (.discounted r c t)
  | .differential r c d t => do
    let outcome ← t.outcomeCosted value features
    let r ← r.stopTrajectoryCosted reward
    let c ← c.stopTrajectoryCosted outcome.shared
    let d ← d.stopTrajectoryCosted .one
    let t ← t.stopCosted outcome
    Costed.op .modelClose (.differential r c d t)

def Model.stop (model : Model dimension criterion) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) : Model dimension criterion :=
  (model.stopCosted value features reward).val

theorem Model.stop_def (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    model.stop value features reward =
      match model with
      | .discounted r c t =>
        let outcome := t.outcome value features
        .discounted (r.stopTrajectory reward) (c.stopTrajectory outcome.shared) (t.stop outcome)
      | .differential r c d t =>
        let outcome := t.outcome value features
        .differential (r.stopTrajectory reward) (c.stopTrajectory outcome.shared)
          (d.stopTrajectory .one) (t.stop outcome) := by
  cases model <;> rfl

def modelOperations (criterion : Criterion) (dimension : Dimension) : OptionModelOps criterion dimension :=
  ⟨Model.beginCosted, Model.stepCosted, Model.terminalCosted, fun model value features =>
    (model.predict value features ⟨0, by decide⟩).cache, Model.restartCosted, Model.stopCosted⟩

def ModelPrediction.target {criterion : Criterion} (prediction : ModelPrediction criterion)
    (gain : RewardRate) : Binary32 :=
  match criterion with
  | .discounted => (Prediction.project .g99 (prediction.reward.value.add prediction.continuation)).value
  | .differential => (prediction.reward.value.sub (gain.value.mul prediction.duration.value)).add prediction.continuation

theorem Model.predict_ranges (model : Model dimension criterion)
    (value : ValueFunction criterion dimension) (base : SwiftTd.ActiveSet dimension)
    (age : ModelAge) :
    criterion.modelRewardRange.Contains (model.predict value base age).reward.value ∧
    modelDurationRange.Contains (model.predict value base age).duration.value :=
  ⟨(model.predict value base age).reward.legal, (model.predict value base age).duration.legal⟩

theorem differential_model_continuation (raw : Binary32) :
    Criterion.differential.modelContinuation raw = raw := rfl

theorem Transition.expected_legal (transition : Transition dimension criterion)
    (features : SwiftTd.ActiveSet dimension) (position : RankIdx dimension) :
    expectationRange.Contains ((transition.expected features).get position).value :=
  ((transition.expected features).get position).legal

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

theorem RankedFeatures.empty_occupied (dimension : Dimension) :
    (RankedFeatures.empty dimension).occupied = [] := by
  simp [RankedFeatures.occupied_def, RankedFeatures.empty, RankedFeatures.ofSlots]

end Acorn.Features
