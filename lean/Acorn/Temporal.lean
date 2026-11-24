import Acorn.Options
import Acorn.Control
import Acorn.FeatureReferences

namespace Acorn.Features

variable {actions : Word.Count}

structure ValueFunction (criterion : Criterion) (dimension : Dimension) where
  controller : Controller (criterion.config .control) dimension metaCount.word.toNat
  epsilon : SwiftTd.ExploreRate

def ValueFunction.nominal {criterion : Criterion} {dimension : Dimension}
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension) : Binary32 :=
  comparisonValue criterion (value.controller.snapshot (count := metaCount) features value.epsilon)

structure EndEvent where
  slot : Fin Acorn.FeatureConstants.skillCount
  age : ModelAge
  reason : OptionEnd

inductive TemporalSource where
  | primitive
  | explorationStart
  | explorationContinuation
  | option (slot : Fin Acorn.FeatureConstants.skillCount)
  deriving DecidableEq

structure TemporalDecision (actions : Word.Count) where
  source : TemporalSource
  action : Action actions.word.toNat
  values : Vector Binary32 actions.word.toNat
  probabilities : Vector Binary32 actions.word.toNat
  explored : Bool
  metaValues : Vector Binary32 metaCount.word.toNat
  metaDecision : Option (PolicyDecision metaCount)
  started : Option (Fin Acorn.FeatureConstants.skillCount)
  ended : Option EndEvent

structure CommittedRun (actions : Word.Count) (mode : Bool) where
  run : ExploratoryRun actions
  origin : Option (Fin Acorn.FeatureConstants.skillCount × OptionActivation mode)
  pending : origin.isSome → 0 < run.remaining.val

def CommittedRun.bare {mode : Bool} (run : ExploratoryRun actions) : CommittedRun actions mode :=
  ⟨run, none, by simp⟩

def Occupancy.afterOption {mode : Bool} (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation mode) (run : Option (ExploratoryRun actions)) :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) :=
  match run with
  | some run =>
    if left : 0 < run.remaining.val then .exploring ⟨run, some (slot, activation), fun _ => left⟩
    else .option slot activation
  | none => .option slot activation

def Occupancy.afterPrimitive {mode : Bool} (run : Option (ExploratoryRun actions)) :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) :=
  match run with
  | some run => if 0 < run.remaining.val then .exploring (.bare run) else .idle
  | none => .idle

def Occupancy.executing {mode : Bool} :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) →
      Option (Fin Acorn.FeatureConstants.skillCount)
  | .option slot _ => some slot
  | .exploring committed => committed.origin.map (·.1)
  | .idle => none

theorem Occupancy.afterOption_executing {mode : Bool} (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation mode) (run : Option (ExploratoryRun actions)) :
    (Occupancy.afterOption slot activation run).executing = some slot := by
  cases run with
  | none => rfl
  | some run =>
    by_cases left : 0 < run.remaining.val <;>
      simp [Occupancy.afterOption, Occupancy.executing, left]

theorem CommittedRun.bare_executing {mode : Bool} (run : ExploratoryRun actions) :
    (Occupancy.exploring (CommittedRun.bare (mode := mode) run) :
      Occupancy (OptionActivation mode) (CommittedRun actions mode)).executing = none := rfl

theorem Occupancy.afterPrimitive_executing {mode : Bool}
    (run : Option (ExploratoryRun actions)) :
    (Occupancy.afterPrimitive (mode := mode) run).executing = none := by
  cases run with
  | none => rfl
  | some run =>
    by_cases left : 0 < run.remaining.val <;>
      simp [Occupancy.afterPrimitive, Occupancy.executing, CommittedRun.bare, left]

def TemporalDecision.own (decision : TemporalDecision actions) : Bool :=
  match decision.source with | .option _ => false | .primitive | .explorationStart | .explorationContinuation => true

structure OptionModelOps (criterion : Criterion) (dimension : Dimension) where
  begin : Model dimension criterion → SwiftTd.ActiveSet dimension → Costed (Model dimension criterion)
  step : Model dimension criterion → SwiftTd.ActiveSet dimension → ModelAge → Binary32 →
    Costed (Model dimension criterion)
  terminal : Model dimension criterion → ValueFunction criterion dimension →
    SwiftTd.ActiveSet dimension → Binary32 → Costed (Model dimension criterion)
  predict : Model dimension criterion → ValueFunction criterion dimension →
    SwiftTd.ActiveSet dimension → ModelCache
  restart : Model dimension criterion → SwiftTd.ActiveSet dimension → ModelAge →
    Costed (Model dimension criterion)
  stop : Model dimension criterion → ValueFunction criterion dimension →
    SwiftTd.ActiveSet dimension → Binary32 → Costed (Model dimension criterion)

structure PlanningResult (criterion : Criterion) (dimension : Dimension) where
  controller : Controller (criterion.config .control) dimension metaCount.word.toNat
  predictions : Vector ModelCache Acorn.FeatureConstants.skillCount
  steps : UInt64
  errors : Vector Binary32 Acorn.FeatureConstants.skillCount
  recent : RecentFeatures dimension

abbrev PlanBoundary (actions : Word.Count) (config : Config) (criterion : Criterion) (dimension : Dimension)
    (discounts : List Discount) :=
  PlanningResult criterion dimension → Vector (Skill actions config criterion dimension discounts) Acorn.FeatureConstants.skillCount →
    SwiftTd.ActiveSet dimension → RewardRate → SwiftTd.ExploreRate → PlanningResult criterion dimension

structure EndingPayload (mode : Bool) where
  activation : OptionActivation mode
  potential : Potential
  reason : OptionEnd

variable {mode : Bool}

def Skill.beginTemporalCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    Costed (Skill actions config criterion dimension discounts × (activation : OptionActivation learning) ×
      OptionContinuation actions dimension activation) := do
  let begun ← skill.beginOptionCosted features potential learning rate
  let skill ← Costed.ite (learning = true)
    (fun _ =>
      let ⟨interest, policy, model, following⟩ := begun.1
      Costed.bind (models.begin model features) fun model =>
        Costed.pure ⟨interest, policy, model, following⟩)
    fun _ => Costed.pure begun.1
  Costed.pure (skill, begun.2)

def Skill.beginTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    Skill actions config criterion dimension discounts × (activation : OptionActivation learning) × OptionContinuation actions dimension activation :=
  (skill.beginTemporalCosted models features potential learning rate).val

theorem Skill.beginTemporal_def {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    skill.beginTemporal models features potential learning rate =
      let begun := skill.beginOption features potential learning rate
      let skill := if learning then { begun.1 with model := (models.begin begun.1.model features).val }
        else begun.1
      (skill, begun.2) := by
  cases learning <;> rfl

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

def Skill.stepTemporalCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Costed (Skill actions config criterion dimension discounts × OptionActivation mode ×
      PersistentDecision actions × Rng.Xoshiro256) :=
  Costed.bind (skill.optionStepCosted activation next reward gain rng) fun result =>
  let (stepped, rest) := result
  Costed.ite ((activation.learning && activation.age.val > 0) = true)
    (fun _ =>
      let ⟨interest, policy, model, following⟩ := stepped
      Costed.bind (models.step model next.features activation.age reward) fun model =>
        Costed.pure (⟨interest, policy, model, following⟩, rest))
    fun _ => Costed.pure result

def Skill.stepTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    Skill actions config criterion dimension discounts × OptionActivation mode × PersistentDecision actions × Rng.Xoshiro256 :=
  (skill.stepTemporalCosted models activation next reward gain rng).val

theorem Skill.stepTemporal_eq {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    skill.stepTemporal models activation next reward gain rng =
      let result := skill.optionStep activation next reward gain rng
      let skill := if activation.learning && activation.age.val > 0 then
        { result.1 with model := (models.step result.1.model next.features activation.age reward).val }
        else result.1
      (skill, result.2) := by
  unfold Skill.stepTemporal Skill.stepTemporalCosted Skill.optionStep
  generalize skill.optionStepCosted activation next reward gain rng = stepped
  obtain ⟨⟨⟨interest, policy, model, following⟩, rest⟩, work, single⟩ := stepped
  dsimp only [Costed.bind, Costed.ite_val]
  split <;> rfl

def Skill.creditTemporalCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    Costed (Skill actions config criterion dimension discounts) := do
  let credited ← skill.optionCreditCosted activation next drawn reward gain
  Costed.ite ((activation.learning && activation.age.val > 0) = true)
    (fun _ =>
      let ⟨interest, policy, model, following⟩ := credited
      Costed.bind (models.step model next.features activation.age reward) fun model =>
        Costed.pure ⟨interest, policy, model, following⟩)
    fun _ => Costed.pure credited

def Skill.creditTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    Skill actions config criterion dimension discounts :=
  (skill.creditTemporalCosted models activation next drawn reward gain).val

theorem Skill.creditTemporal_def {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    skill.creditTemporal models activation next drawn reward gain =
      let credited := skill.optionCredit activation next drawn reward gain
      if activation.learning && activation.age.val > 0 then
        { credited with model := (models.step credited.model next.features activation.age reward).val }
        else credited := by
  unfold Skill.creditTemporal Skill.creditTemporalCosted Skill.optionCredit
  generalize skill.optionCreditCosted activation next drawn reward gain = credited
  obtain ⟨⟨interest, policy, model, following⟩, work, single⟩ := credited
  dsimp only [Costed.bind_val, Costed.ite_val]
  split <;> rfl

theorem Skill.stepTemporal_credit {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (reward : Binary32) (gain : RewardRate) (rng : Rng.Xoshiro256) :
    skill.stepTemporal models activation next reward gain rng =
      (skill.creditTemporal models activation next (next.policy.drawPersistent rng).1 reward gain,
        activation.advance next, next.policy.drawPersistent rng) := by
  rw [Skill.stepTemporal_eq, Skill.creditTemporal_def, Skill.optionStep_credit]

def Skill.endTemporalCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    Costed (Skill actions config criterion dimension discounts) := do
  let result ← skill.terminateOptionCosted ending.activation ending.potential reward terminal gain
  Costed.ite (ending.activation.learning = true)
    (fun _ =>
      let ⟨interest, policy, model, following⟩ := result
      Costed.bind (models.terminal model value features reward) fun model =>
        Costed.pure ⟨interest, policy, model, following⟩)
    fun _ => Costed.pure result

def Skill.endTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  (skill.endTemporalCosted models value features ending reward terminal gain).val

theorem Skill.endTemporal_def {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (ending : EndingPayload mode) (reward terminal : Binary32) (gain : RewardRate) :
    skill.endTemporal models value features ending reward terminal gain =
      let result := skill.terminateOption ending.activation ending.potential reward terminal gain
      if ending.activation.learning then
        { result with model := (models.terminal result.model value features reward).val }
        else result := rfl

def Skill.startFollowingCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) :
    Costed (Skill actions config criterion dimension discounts) := do
  let freeze := skill.policy.snapshotCosted (count := actions) features
  let epsilon ← rate.resolveCosted fun _ => skill.policy.exploreRateCosted (count := actions)
  let frozen ← freeze epsilon
  let consistent ← frozen.consistentCosted behaviour
  let ⟨interest, policy, model, _⟩ := skill
  let policy ← policy.startStepCosted (actions := actions.word.toNat) features action
    (frozen.values.get action)
  let model ← Costed.ite (consistent = true)
    (fun _ => models.restart model features ⟨0, by decide⟩) fun _ => Costed.pure model
  Costed.op .startFollowing
    ⟨interest, policy, model, some ⟨⟨1, by decide⟩, consistent, potential⟩⟩

def Skill.startFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) : Skill actions config criterion dimension discounts :=
  (skill.startFollowingCosted models features potential rate action behaviour).val

theorem Skill.startFollowing_def {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (rate : ConsumerRate)
    (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) :
    skill.startFollowing models features potential rate action behaviour =
      let frozen := skill.policy.snapshot (count := actions) features
        (rate.resolve fun _ => skill.policy.exploreRate (count := actions))
      let consistent := frozen.consistent behaviour
      let ⟨interest, policy, model, _⟩ := skill
      ⟨interest,
        policy.startStep (actions := actions.word.toNat) features action
          (frozen.values.get action),
        if consistent then (models.restart model features ⟨0, by decide⟩).val else model,
        some ⟨⟨1, by decide⟩, consistent, potential⟩⟩ := by
  cases rate <;> rfl

def Skill.stopFollowingCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) : Costed (Skill actions config criterion dimension discounts) :=
  let stopping := (terminalCumulant (criterion.center reward 1 gain)
    (skill.interest.stoppingValue estimate potential) following.previous).sub skill.policy.vOld
  let ⟨interest, policy, model, _⟩ := skill
  do
    let policy ← policy.stopStepCosted stopping
    let model ← Costed.charge .stopFollowing <| Costed.ite (following.live = true)
      (fun _ => models.stop model value features reward) fun _ => Costed.pure model
    Costed.pure ⟨interest, policy, model, none⟩

def Skill.stopFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  (skill.stopFollowingCosted models value features following potential estimate reward gain).val

theorem Skill.stopFollowing_def {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (following : Following) (potential : Potential) (estimate reward : Binary32)
    (gain : RewardRate) :
    skill.stopFollowing models value features following potential estimate reward gain =
      let stopping := (terminalCumulant (criterion.center reward 1 gain)
        (skill.interest.stoppingValue estimate potential) following.previous).sub skill.policy.vOld
      let ⟨interest, policy, model, _⟩ := skill
      ⟨interest, policy.stopStep stopping,
        if following.live then (models.stop model value features reward).val else model, none⟩ := by
  unfold Skill.stopFollowing Skill.stopFollowingCosted
  cases following.live <;> rfl

def Skill.followTemporalCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat)
    (reward : Binary32) (gain : RewardRate) :
    Costed (Skill actions config criterion dimension discounts) :=
  match skill.following with
  | none => skill.startFollowingCosted models features potential rate action behaviour
  | some following => do
    let decision ← skill.decideOptionCosted following.activation features potential goal estimate rate
    match decision with
    | .continuing next =>
      let consistent ← next.policy.consistentCosted behaviour
      let ⟨interest, policy, model, _⟩ := skill
      let credited ← Costed.ite (following.live = true)
        (fun _ => models.step model features following.age reward) fun _ => Costed.pure model
      let policy ← policy.backupStepCosted (count := actions) features next.policy action
        (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
          following.previous)
      let model ← Costed.ite ((consistent && !following.live) = true)
        (fun _ => models.restart credited features following.age) fun _ => Costed.pure credited
      Costed.op .followStep
        ⟨interest, policy, model, some ⟨ModelAge.advance following.age, consistent, potential⟩⟩
    | .ending _ => do
      let stopped ← skill.stopFollowingCosted models value features following potential estimate
        reward gain
      stopped.startFollowingCosted models features potential rate action behaviour

def Skill.followTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat)
    (reward : Binary32) (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  (skill.followTemporalCosted models value features potential goal estimate rate action behaviour
    reward gain).val

theorem Skill.followTemporal_def {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat)
    (reward : Binary32) (gain : RewardRate) :
    skill.followTemporal models value features potential goal estimate rate action behaviour reward
        gain =
      match skill.following with
      | none => skill.startFollowing models features potential rate action behaviour
      | some following =>
        match skill.decideOption following.activation features potential goal estimate rate with
        | .continuing next =>
          let consistent := next.policy.consistent behaviour
          let ⟨interest, policy, model, _⟩ := skill
          let credited := if following.live then
            (models.step model features following.age reward).val else model
          ⟨interest,
            policy.backupStep (count := actions) features next.policy action
              (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
                following.previous),
            if consistent && !following.live then
              (models.restart credited features following.age).val else credited,
            some ⟨ModelAge.advance following.age, consistent, potential⟩⟩
        | .ending _ =>
          (skill.stopFollowing models value features following potential estimate reward
            gain).startFollowing models features potential rate action behaviour := by
  unfold Skill.followTemporal Skill.followTemporalCosted
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    rw [Costed.bind_val, Skill.decideOption]
    split
    · cases following.live <;> rfl
    · rfl

def Skill.settleFollowingCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate) :
    Costed (Skill actions config criterion dimension discounts) :=
  match skill.following with
  | none => Costed.pure skill
  | some following => do
    let decision ← skill.decideOptionCosted following.activation features potential goal estimate rate
    match decision with
    | .continuing next =>
      let ⟨interest, policy, model, _⟩ := skill
      let error ← Costed.charge .settleFollowing (policy.backupErrorCosted (count := actions)
        next.policy (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
          following.previous))
      let policy ← policy.stopStepCosted error
      let model ← Costed.ite (following.live = true)
        (fun _ => models.step model features following.age reward) fun _ => Costed.pure model
      Costed.pure ⟨interest, policy, model, none⟩
    | .ending _ =>
      skill.stopFollowingCosted models value features following potential estimate reward gain

def Skill.settleFollowing {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate) :
    Skill actions config criterion dimension discounts :=
  (skill.settleFollowingCosted models value features potential goal estimate rate reward gain).val

theorem Skill.settleFollowing_def {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate) :
    skill.settleFollowing models value features potential goal estimate rate reward gain =
      match skill.following with
      | none => skill
      | some following =>
        match skill.decideOption following.activation features potential goal estimate rate with
        | .continuing next =>
          let ⟨interest, policy, model, _⟩ := skill
          ⟨interest,
            policy.stopStep (policy.backupError (count := actions) next.policy
              (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma potential
                following.previous)),
            if following.live then (models.step model features following.age reward).val
              else model,
            none⟩
        | .ending _ =>
          skill.stopFollowing models value features following potential estimate reward gain := by
  unfold Skill.settleFollowing Skill.settleFollowingCosted
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    rw [Costed.bind_val, Skill.decideOption]
    split
    · cases following.live <;> rfl
    · rfl

def Skill.settleTemporalCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) : Costed (Skill actions config criterion dimension discounts) :=
  Costed.ite (learning = true)
    (fun _ => skill.settleFollowingCosted models value features potential goal estimate rate reward
      gain)
    fun _ => Costed.pure skill

def Skill.settleTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) : Skill actions config criterion dimension discounts :=
  (skill.settleTemporalCosted models value features potential goal estimate rate reward gain
    learning).val

theorem Skill.settleTemporal_def {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) :
    skill.settleTemporal models value features potential goal estimate rate reward gain learning =
      if learning then
        skill.settleFollowing models value features potential goal estimate rate reward gain
      else skill := by
  cases learning <;> rfl

def Skill.startTemporalCosted {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) (drawn : PersistentDecision actions) :
    Costed (Skill actions config criterion dimension discounts) := do
  let settled ← skill.settleTemporalCosted models value features potential goal estimate rate
    reward gain learning
  let begun ← settled.beginTemporalCosted models features potential learning rate
  begun.1.creditTemporalCosted models begun.2.1 begun.2.2 drawn reward gain

def Skill.startTemporal {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) (drawn : PersistentDecision actions) :
    Skill actions config criterion dimension discounts :=
  (skill.startTemporalCosted models value features potential goal estimate rate reward gain learning
    drawn).val

theorem Skill.startTemporal_def {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) (drawn : PersistentDecision actions) :
    skill.startTemporal models value features potential goal estimate rate reward gain learning
        drawn =
      let begun := (skill.settleTemporal models value features potential goal estimate rate reward
        gain learning).beginTemporal models features potential learning rate
      begun.1.creditTemporal models begun.2.1 begun.2.2 drawn reward gain := rfl

theorem Skill.startTemporal_step {config : Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) (rng : Rng.Xoshiro256) :
    let begun := (skill.settleTemporal models value features potential goal estimate rate reward
      gain learning).beginTemporal models features potential learning rate
    (begun.1.stepTemporal models begun.2.1 begun.2.2 reward gain rng).1 =
      skill.startTemporal models value features potential goal estimate rate reward gain learning
        (begun.2.2.policy.drawPersistent rng).1 := by
  intro begun
  rw [Skill.stepTemporal_credit, Skill.startTemporal_def]

theorem Skill.creditTemporal_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    (skill.creditTemporal models activation next drawn reward gain).interest = skill.interest := by
  simp only [Skill.creditTemporal_def]
  split <;> simp only [Skill.optionCredit_def] <;> split <;> rfl

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

theorem Skill.startTemporal_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension} {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts) (models : OptionModelOps criterion dimension)
    (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (reward : Binary32) (gain : RewardRate)
    (learning : Bool) (drawn : PersistentDecision actions) :
    (skill.startTemporal models value features potential goal estimate rate reward gain learning
      drawn).interest = skill.interest := by
  rw [Skill.startTemporal_def]
  dsimp only
  rw [Skill.creditTemporal_interest]
  have settled : (skill.settleTemporal models value features potential goal estimate rate reward
      gain learning).interest = skill.interest := by
    rw [Skill.settleTemporal_def]
    split
    · rw [Skill.settleFollowing_def]
      cases skill.following with
      | none => rfl
      | some following =>
        dsimp only
        split <;> rfl
    · rfl
  rw [← settled]
  cases learning <;> rfl

theorem Skill.startFollowing_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) :
    (skill.startFollowing models features potential rate action behaviour).interest =
      skill.interest := rfl

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
  rw [Skill.followTemporal_def]
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    split <;> rfl

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
  rw [Skill.followTemporal_def]
  cases skill.following with
  | none => rfl
  | some following =>
    dsimp only
    split <;> rfl

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
  rw [Skill.settleFollowing_def]
  cases linked : skill.following with
  | none => exact ⟨rfl, linked⟩
  | some following =>
    dsimp only
    split <;> exact ⟨rfl, rfl⟩

theorem Skill.settleFollowing_unlinked {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (unlinked : skill.following = none) :
    skill.settleFollowing models value features potential goal estimate rate reward gain =
      skill := by
  rw [Skill.settleFollowing_def, unlinked]

theorem Skill.settleTemporal_interest {config : Config} {criterion : Criterion}
    {dimension : Dimension}
    {discounts : List Discount} (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (value : ValueFunction criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (goal : Bool) (estimate : Binary32) (rate : ConsumerRate)
    (reward : Binary32) (gain : RewardRate) (learning : Bool) :
    (skill.settleTemporal models value features potential goal estimate rate reward gain
      learning).interest = skill.interest := by
  rw [Skill.settleTemporal_def]
  split
  · exact (skill.settleFollowing_owner models value features potential goal estimate rate reward
      gain).1
  · rfl

end Acorn.Features
