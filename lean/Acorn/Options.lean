import Acorn.Exploration
import Acorn.FeatureModelInput

namespace Acorn.Features

abbrev Potential := Bool

def Potential.value (potential : Potential) : Binary32 := if potential then .one else .zero

structure DeclaredPotentials where
  origin : Departure
  values : Vector Potential Acorn.FeatureConstants.skillCount

def Interest.potentialCosted {config : Config} {dimension : Dimension} (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) :
    Costed (Option Potential) :=
  match interest with
  | .learned assignment => do
    let potential ← assignment.potentialCosted features
    pure (some potential)
  | .declared origin tag => Costed.op .declaredPotential
    (if origin = declared.origin then some (declared.values.get tag) else none)

def Interest.potential {config : Config} {dimension : Dimension} (interest : Interest config)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) : Option Potential :=
  (interest.potentialCosted features declared).val

theorem Interest.potential_def {config : Config} {dimension : Dimension}
    (interest : Interest config) (features : SwiftTd.ActiveSet dimension)
    (declared : DeclaredPotentials) :
    interest.potential features declared =
      match interest with
      | .learned assignment => some (assignment.potential features)
      | .declared origin tag =>
        if origin = declared.origin then some (declared.values.get tag) else none := by
  cases interest <;> rfl

def Interest.stoppingValue {config : Config} (interest : Interest config)
    (estimate : Binary32) (potential : Potential) : Binary32 :=
  match interest with
  | .learned assignment => assignment.stoppingValue estimate potential
  | .declared _ _ => estimate

def shapedCumulant (reward gamma : Binary32) (next previous : Potential) : Binary32 :=
  (reward.add (gamma.mul next.value)).sub previous.value

def terminalCumulant (reward stopping : Binary32) (previous : Potential) : Binary32 :=
  (reward.add stopping).sub previous.value

inductive OptionEnd where
  | goal
  | duration
  | interrupted
  deriving DecidableEq

structure OptionActivation (mode : Bool) where
  private mk ::
  age : ModelAge
  previous : Potential

def OptionActivation.stored {mode : Bool} (age : ModelAge) (previous : Potential) :
    OptionActivation mode := ⟨age, previous⟩

def OptionActivation.learning {mode : Bool} (_activation : OptionActivation mode) : Bool := mode

def Following.activation (following : Following) : OptionActivation true :=
  ⟨following.age, following.previous⟩

variable {mode : Bool}

def OptionActivation.following (activation : OptionActivation mode) : Following :=
  ⟨activation.age, decide (0 < activation.age.val), activation.previous⟩

structure OptionContinuation (actions : Word.Count) (dimension : Dimension) (activation : OptionActivation mode) where
  private mk ::
  features : SwiftTd.ActiveSet dimension
  potential : Potential
  policy : PolicySnapshot actions
  room : activation.age.val < Acorn.FeatureConstants.optionMaxDuration

inductive OptionDecision (actions : Word.Count) (dimension : Dimension) (activation : OptionActivation mode) where
  | continuing (next : OptionContinuation actions dimension activation)
  | ending (reason : OptionEnd)

inductive ConsumerRate where
  | own
  | fixed (rate : SwiftTd.ExploreRate)

def ConsumerRate.resolveCosted (source : ConsumerRate) (own : Unit → Costed SwiftTd.ExploreRate) :
    Costed SwiftTd.ExploreRate :=
  match source with | .own => own () | .fixed rate => Costed.pure rate

def ConsumerRate.resolve (source : ConsumerRate) (own : Unit → SwiftTd.ExploreRate) : SwiftTd.ExploreRate :=
  match source with | .own => own () | .fixed rate => rate

theorem ConsumerRate.resolveCosted_val (source : ConsumerRate)
    (own : Unit → Costed SwiftTd.ExploreRate) :
    (source.resolveCosted own).val = source.resolve fun unused => (own unused).val := by
  cases source <;> rfl

variable {actions : Word.Count} {config : Config} {criterion : Criterion} {dimension : Dimension}
  {discounts : List Discount}

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

def Skill.beginOption (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential)
    (learning : Bool) (rate : ConsumerRate) :
    Skill actions config criterion dimension discounts ×
      (activation : OptionActivation learning) × OptionContinuation actions dimension activation :=
  (skill.beginOptionCosted features potential learning rate).val

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

def comparisonValueCosted (criterion : Criterion) {count : Word.Count}
    (policy : PolicySnapshot count) : Costed Binary32 :=
  match criterion with | .differential => policy.expectedCosted | .discounted => policy.bestCosted

def comparisonValue (criterion : Criterion) {count : Word.Count} (policy : PolicySnapshot count) : Binary32 :=
  (comparisonValueCosted criterion policy).val

theorem comparisonValue_def (criterion : Criterion) {count : Word.Count}
    (policy : PolicySnapshot count) :
    comparisonValue criterion policy =
      match criterion with | .differential => policy.expected | .discounted => policy.best := by
  cases criterion <;> rfl

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

def Skill.decideOption (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) : OptionDecision actions dimension activation :=
  (skill.decideOptionCosted activation features potential goal estimate rate).val

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

def Skill.optionStep (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    Skill actions config criterion dimension discounts × OptionActivation mode × PersistentDecision actions × Rng.Xoshiro256 :=
  (skill.optionStepCosted activation next reward gain rng).val

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

def OptionActivation.advance (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) : OptionActivation mode :=
  ⟨activation.age.advance, next.potential⟩

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

def Skill.optionCredit (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (drawn : PersistentDecision actions)
    (reward : Binary32) (gain : RewardRate) : Skill actions config criterion dimension discounts :=
  (skill.optionCreditCosted activation next drawn reward gain).val

theorem Skill.optionCredit_def (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (next : OptionContinuation actions dimension activation)
    (drawn : PersistentDecision actions) (reward : Binary32) (gain : RewardRate) :
    skill.optionCredit activation next drawn reward gain =
      if activation.learning then
        { skill with policy := (skill.policy.persistentStep next.features next.policy drawn
            (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma next.potential
              activation.previous) 1) }
        else skill := rfl

def Skill.frozenPolicyCosted (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    Costed (PolicySnapshot actions) := do
  let freeze := skill.policy.snapshotCosted (count := actions) features
  let epsilon ← rate.resolveCosted fun _ => skill.policy.exploreRateCosted (count := actions)
  freeze epsilon

def Skill.frozenPolicy (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) : PolicySnapshot actions :=
  (skill.frozenPolicyCosted features rate).val

theorem Skill.frozenPolicy_def (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : ConsumerRate) :
    skill.frozenPolicy features rate =
      skill.policy.snapshot (count := actions) features
        (rate.resolve fun _ => skill.policy.exploreRate (count := actions)) := by
  cases rate <;> rfl

def OptionActivation.first (learning : Bool) (potential : Potential) : OptionActivation learning :=
  ⟨ModelAge.advance ⟨0, by decide⟩, potential⟩

def Skill.terminateOptionCosted (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) : Costed (Skill actions config criterion dimension discounts) :=
  Costed.charge .terminateOption <| Costed.ite (activation.learning = true)
    (fun _ => do
      let policy ← skill.policy.terminalCosted (terminalCumulant (criterion.center reward 1 gain)
        (skill.interest.stoppingValue terminal potential) activation.previous)
      Costed.pure { skill with policy })
    (fun _ => Costed.pure skill)

def Skill.terminateOption (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (potential : Potential) (reward terminal : Binary32) (gain : RewardRate) :
    Skill actions config criterion dimension discounts :=
  (skill.terminateOptionCosted activation potential reward terminal gain).val

theorem Skill.terminateOption_def (skill : Skill actions config criterion dimension discounts)
    (activation : OptionActivation mode) (potential : Potential) (reward terminal : Binary32)
    (gain : RewardRate) :
    skill.terminateOption activation potential reward terminal gain =
      if activation.learning then
        { skill with policy := (skill.policy.terminal
          (terminalCumulant (criterion.center reward 1 gain)
            (skill.interest.stoppingValue terminal potential) activation.previous)) }
      else skill := rfl

theorem Skill.begin_coordinate (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginOption features potential learning rate).2.1.previous = potential ∧
    (skill.beginOption features potential learning rate).2.1.age.val = 0 := ⟨rfl, rfl⟩

theorem Skill.goal_ends (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32) (rate : ConsumerRate) :
    skill.decideOption activation features potential true estimate rate = .ending .goal := rfl

theorem Skill.cap_ends (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (estimate : Binary32) (rate : ConsumerRate)
    (full : activation.age.val = Acorn.FeatureConstants.optionMaxDuration) :
    skill.decideOption activation features potential false estimate rate = .ending .duration := by
  simp [Skill.decideOption_def, full]

theorem Skill.step_age (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    (skill.optionStep activation next reward gain rng).2.1.age.val = activation.age.val + 1 := by
  have := next.room
  simp only [Skill.optionStep_def, ModelAge.advance]
  omega

theorem Skill.step_frozen (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) (frozen : activation.learning = false) :
    (skill.optionStep activation next reward gain rng).1 = skill := by
  simp [Skill.optionStep_def, frozen]

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

theorem Skill.step_drawn (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    (skill.optionStep activation next reward gain rng).2.2 = next.policy.drawPersistent rng := rfl

theorem Skill.optionStep_credit (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (reward : Binary32) (gain : RewardRate)
    (rng : Rng.Xoshiro256) :
    skill.optionStep activation next reward gain rng =
      (skill.optionCredit activation next (next.policy.drawPersistent rng).1 reward gain,
        activation.advance next, next.policy.drawPersistent rng) := rfl

theorem Skill.optionCredit_action (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (first second : PersistentDecision actions)
    (reward : Binary32) (gain : RewardRate) (same : first.action = second.action) :
    skill.optionCredit activation next first reward gain =
      skill.optionCredit activation next second reward gain := by
  simp only [Skill.optionCredit_def, Controller.persistentStep_def, same]

theorem Skill.optionCredit_frozen (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (next : OptionContinuation actions dimension activation) (drawn : PersistentDecision actions)
    (reward : Binary32) (gain : RewardRate) (frozen : activation.learning = false) :
    skill.optionCredit activation next drawn reward gain = skill := by
  simp [Skill.optionCredit_def, frozen]

theorem Skill.begin_first (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginOption features potential learning rate).2.1.advance
        (skill.beginOption features potential learning rate).2.2 =
      OptionActivation.first learning potential := rfl

theorem Skill.frozenPolicy_fixed (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rate : SwiftTd.ExploreRate) :
    (skill.frozenPolicy features (.fixed rate)).epsilon = rate := rfl

theorem Skill.decide_frozen (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (goal : Bool)
    (estimate : Binary32) (rate : ConsumerRate) (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate = .continuing next) :
    next.policy = skill.frozenPolicy features rate := by
  rw [Skill.frozenPolicy_def]
  exact skill.decide_policy activation features potential goal estimate rate next continuing

theorem Skill.begin_policy (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginOption features potential learning rate).2.2.policy =
      (skill.beginOption features potential learning rate).1.policy.snapshot
        (count := actions) features
        (rate.resolve fun _ => (skill.beginOption features potential learning
          rate).1.policy.exploreRate (count := actions)) := by
  cases rate <;> rfl

theorem OptionActivation.following_activation (activation : OptionActivation true) :
    activation.following.activation = activation := rfl

theorem Skill.terminal_owners (skill : Skill actions config criterion dimension discounts) (activation : OptionActivation mode)
    (potential : Potential) (reward terminal : Binary32) (gain : RewardRate) :
    (skill.terminateOption activation potential reward terminal gain).interest = skill.interest ∧
    (skill.terminateOption activation potential reward terminal gain).model = skill.model := by
  rw [Skill.terminateOption_def]
  split <;> exact ⟨rfl, rfl⟩

end Acorn.Features
