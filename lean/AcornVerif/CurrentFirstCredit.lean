/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentCreditHorizon
import AcornVerif.CurrentGridWorld

/-!
# The first reward's credit along the executed agent's run

`AcornVerif.CurrentCreditHorizon` proves, of a primitive controller's own run, that a slot laid at
most 81 steps before a first reward of one has a weight the reward moves. This module carries
that to the executed agent and gives an amount. In a kernel run, after the agent's step on the
first rewarded percept, every slot of a frame it laid at most 81 steps before holds, in the row
of the action taken on that frame, a weight that reads at least the least laid trace decayed once
for each step between (`loop_first_credit`).

An agent's step is one controller step followed by the tester's retirements
(`AcornVerif.CurrentCreditHorizon.learning_step`), and a retirement clears a slot's weight and
trace. So the statement is of the agent's run before a unit of its feature bank matures, when the
tester retires nothing. The names here call such an agent, step or run young.

- **The tester before a unit matures.** A unit is eligible for replacement once its age exceeds
  the tester's maturity threshold (`Acorn.Features.Lifecycle.mature`). While the clock is at most
  that threshold no unit is eligible (`young_ineligible`), a test replaces no unit, writes no
  learner and keeps the feature bank (`idle_test`, `idle_test_bank`), and the tester leaves the
  primitive controller as it was (`young_retire`). The declared tester's threshold is 1000 steps
  (`Acorn.Handcrafted.declaredTester`).
- **The clock.** Under the default order, a step of a profile with no hierarchy advances the
  agent's clock once, before its tester runs (`step_clock`): its selection and its learning part
  keep the representation that holds the clock, and its tester keeps the clock (`retire_clock`).
- **One step.** So before a unit matures, one agent step is exactly one controller step at the
  encoded frame, the executed action and the centred reward (`young_step`). Under the discounted
  criterion the centred reward is the percept's reward word.
- **What the next frame reads of the step.** A frame is encoded under the feature bank, and it
  feeds back the predictions the step before stored. Before a unit matures a step keeps the bank
  (`young_bank`). A step of a learning profile stores the predictions its prediction demons made
  before they learned (`step_predictions`), and a fresh demon predicts positive zero
  (`initial_prediction`, `initial_bank_predictions`). So the cold agent's first step stores the
  predictions it started with (`cold_step_predictions`).
- **A list of percepts.** Over percepts whose reward word is the zero word, the controller stays
  quiet against what it laid (`traced_young`), and a recent slot stays recent, decayed once for
  each step (`traced_recent`).
- **A kernel run.** A kernel run of the executed agent is its traced run over the percepts it
  receives (`traced_loop`), and the steps that run lays are the steps of the traced run
  (`laidAt`, `traced_laid`). So in a kernel run the controller stays quiet while the rewards are
  zero (`loop_quiet`), each of those steps is one controller step at reward zero
  (`loop_silent`), a laid slot stays recent (`loop_recent`), and the step that learns a
  reward of one is one controller step at reward one (`loop_paid`). That step writes at least a
  recent slot's least trace into its weight
  (`AcornVerif.CurrentCreditHorizon.recent_credited`), which gives `loop_first_credit`.

Scope. A profile with no hierarchy under per-step credit and the discounted criterion, at the
default step order, from cold initialization; reward words that are the zero word until a first
one that is the word one; frames of at most 1999 slots, the laid one of at most 1900; and the
whole run, the reward step included, within the tester's maturity threshold.

Not covered. A run past the first maturing unit: a replaced unit's slot is retired, and a slot of
a frame that coincides with it loses its credit. The differential criterion, whose centred reward
is a difference. What later steps do to the weight: the statement is of the state right after
the reward step. And the bound is a lower one: nothing here bounds the weight from above.

Trust. The statements are about executed binary32 words. Lean's kernel, its model of binary32
arithmetic and the agreement of the native operations with that model on finite operands remain
trusted, as for every proof of executed words in this library.
-/

namespace AcornVerif.CurrentFirstCredit
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentCreditHorizon AcornVerif.CurrentGridWorld
open AcornVerif.CurrentPreReward

/-! ## The tester before a unit matures -/

section Tester

variable {shape : PatchShape} {actions : Word.Count} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}

/-- While the clock is at most the maturity threshold, no unit is eligible for replacement. -/
theorem young_ineligible (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (young : state.progress.clock.toNat ≤ config.tester.maturity) :
    state.eligibleCount free = 0 := by
  unfold Lifecycle.eligibleCount
  rw [List.countP_eq_zero]
  intro unit _
  simp only [Lifecycle.eligible, Lifecycle.mature, Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro mature
  omega

/-- A test with no eligible unit replaces no unit and writes no learner. -/
theorem idle_test (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count)
    (none : state.eligibleCount free = 0) :
    (state.test free active).2 = [] ∧ (state.test free active).1.consumers = state.consumers := by
  have scored := state.score_eligible active free
  have credited := (state.score active).withCredit_eligible
    (config.tester.remainder ((state.score active).accrued free)) free
  have idle : ((state.score active).withCredit
      (config.tester.remainder ((state.score active).accrued free))).candidate free =
        Option.none := by
    rw [Lifecycle.candidate_none_iff]
    simp only [Lifecycle.eligibleCount, credited.1, scored.1]
    exact none
  unfold Lifecycle.test
  dsimp only
  cases config.tester.due ((state.score active).accrued free) with
  | zero => exact ⟨rfl, rfl⟩
  | succ rest =>
    have unchanged : Lifecycle.replaceDue free (rest + 1) ((state.score active).withCredit
        (config.tester.remainder ((state.score active).accrued free))) =
          ((state.score active).withCredit
            (config.tester.remainder ((state.score active).accrued free)), []) := by
      simp only [Lifecycle.replaceDue, idle]
    rw [unchanged]
    exact ⟨rfl, rfl⟩

/-- A test with no eligible unit keeps the bank: it rescores the units and stores the credit, and
replaces none. -/
theorem idle_test_bank (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count)
    (none : state.eligibleCount free = 0) :
    (state.test free active).1.representation.bank = state.representation.bank := by
  have scored := state.score_eligible active free
  have credited := (state.score active).withCredit_eligible
    (config.tester.remainder ((state.score active).accrued free)) free
  have idle : ((state.score active).withCredit
      (config.tester.remainder ((state.score active).accrued free))).candidate free =
        Option.none := by
    rw [Lifecycle.candidate_none_iff]
    simp only [Lifecycle.eligibleCount, credited.1, scored.1]
    exact none
  unfold Lifecycle.test
  dsimp only
  cases config.tester.due ((state.score active).accrued free) with
  | zero => rfl
  | succ rest =>
    have unchanged : Lifecycle.replaceDue free (rest + 1) ((state.score active).withCredit
        (config.tester.remainder ((state.score active).accrued free))) =
          ((state.score active).withCredit
            (config.tester.remainder ((state.score active).accrued free)), []) := by
      simp only [Lifecycle.replaceDue, idle]
    rw [unchanged]
    rfl

end Tester

/-! ## What a fresh demon bank predicts -/

section Demons

variable {config : Acorn.Config} {dimension : Dimension}

/-- An ordered sum of positive zeros from positive zero is positive zero. -/
theorem sumFrom_zeros (values : List Binary32) (zeros : ∀ value ∈ values, value = Binary32.zero) :
    Binary32.sumFrom .zero values = .zero := by
  rw [Binary32.sumFrom_def]
  induction values with
  | nil => rfl
  | cons head rest ih =>
    rw [List.foldl_cons, zeros head (List.mem_cons_self ..)]
    exact ih fun value member => zeros value (List.mem_cons_of_mem _ member)

/-- The fresh learner predicts positive zero on every frame: its weights are positive zeros. -/
theorem initial_prediction (features : SwiftTd.ActiveSet dimension) :
    (NumericState.initial config dimension).linearPrediction features = .zero := by
  rw [NumericState.linearPrediction_eq_sumFrom]
  apply sumFrom_zeros
  intro value member
  obtain ⟨idx, _, rfl⟩ := List.mem_map.mp member
  change ((Vector.replicate _ (Weight.project config.rule .zero)).get idx).value = .zero
  rw [get_replicate_vec, Weight.project_zero]

/-- **A step of the fresh demon bank returns the cold prediction cache.** Each demon returns the
prediction it made before it learned, which for a fresh learner is positive zero, the word the
cold cache holds. -/
theorem initial_bank_predictions (features : SwiftTd.ActiveSet dimension) :
    ∀ (discounts : List Discount) (cumulants : Cumulants discounts),
      ((DemonBank.initial dimension discounts).step features cumulants).predictions =
        PredictionCache.initial discounts
  | [], .nil => rfl
  | discount :: rest, .cons origin value tail => by
    rw [DemonBank.step_def]
    change PredictionCache.cons (Prediction.project _
      ((NumericState.initial _ dimension).linearPrediction features))
        ((DemonBank.initial dimension rest).step features tail).predictions = _
    rw [initial_prediction, initial_bank_predictions features rest tail]
    rfl

end Demons

/-! ## One step of the agent before a unit matures -/

section Step

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- While the agent's clock is at most the tester's maturity threshold, the tester writes no
primitive row. -/
theorem young_retire (agent : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count)
    (young : agent.clock.toNat ≤ config.tester.maturity) :
    controlOf (agent.retire active) = controlOf agent := by
  unfold Agent.retire
  split
  · rfl
  · have idle := idle_test agent.control.runtime.lifecycle
      agent.control.runtime.references.phase.free active (young_ineligible _ _ young)
    change ((agent.control.runtime.lifecycle.test agent.control.runtime.references.phase.free
      active).1.consumers.releaseAll (agent.control.runtime.lifecycle.test
        agent.control.runtime.references.phase.free active).2).control = _
    rw [idle.1, idle.2]
    rfl

/-- The tester keeps the agent's clock. -/
theorem retire_clock (agent : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) : (agent.retire active).clock = agent.clock := by
  unfold Agent.retire
  split
  · rfl
  · exact agent.control.runtime.lifecycle.test_clock
      agent.control.runtime.references.phase.free active

/-- Interrupting a held option keeps the representation. -/
theorem interrupt_representation
    (state : TemporalControl interface profile config criterion dimension)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen))) :
    (state.interrupt origin).1.runtime.lifecycle.representation =
      state.runtime.lifecycle.representation := by
  cases origin with
  | none => rfl
  | some held =>
    obtain ⟨slot, activation⟩ := held
    unfold TemporalControl.interrupt
    dsimp only
    split <;> rfl

/-- A served step keeps the representation. -/
theorem serve_representation
    (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : TemporalDecision interface.actions)
    (served : state.serve features = some (next, decision)) :
    next.runtime.lifecycle.representation = state.runtime.lifecycle.representation := by
  unfold TemporalControl.serve at served
  cases phase : state.runtime.references.phase with
  | idle => simp [phase] at served
  | option slot activation => simp [phase] at served
  | exploring committed =>
    simp only [phase] at served
    cases hs : committed.run.serve with
    | none => simp [hs] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq] at served
      cases served
      unfold TemporalControl.skipMeta
      repeat' split
      all_goals exact interrupt_representation state committed.origin

/-- The executed selection of a profile with no hierarchy keeps the representation. -/
theorem select_representation
    (state next : TemporalControl interface profile config criterion dimension)
    (primitive : profile.usesHierarchy = false) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (potentials : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features potentials reward goal =
      some (next, decision)) :
    next.runtime.lifecycle.representation = state.runtime.lifecycle.representation := by
  unfold TemporalControl.selectWithOperations at executed
  have kept : (state.prepareSelection models features reward).runtime.lifecycle.representation =
      state.runtime.lifecycle.representation := by
    simp [TemporalControl.prepareSelection, primitive]
  generalize state.prepareSelection models features reward = prepared at executed kept
  rw [← kept]
  dsimp only at executed
  cases served : prepared.serve features with
  | some result =>
    simp only [served] at executed
    cases executed
    exact serve_representation prepared next features decision served
  | none =>
    simp only [served] at executed
    split at executed
    · have chosen : (prepared.withPhase .idle).choosePrimitive features
          (Vector.replicate _ .zero) none none = (next, decision) := Option.some.inj executed
      exact (congrArg (fun result : TemporalControl interface profile config criterion dimension ×
        TemporalDecision interface.actions => result.1.runtime.lifecycle.representation)
          chosen).symm
    · rename_i hierarchy
      simp [primitive] at hierarchy

/-- The learning part of a local transition keeps the representation. -/
theorem learn_representation
    (selected : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    (selected.learn features obs reward goal decision).runtime.lifecycle.representation =
      selected.runtime.lifecycle.representation := by
  unfold TemporalControl.learn
  dsimp only
  rw [TemporalControl.finish_eq]
  dsimp only
  have followed : (selected.followOptions (modelOperations criterion dimension) features
      obs.declared reward goal decision).runtime.lifecycle.representation =
        selected.runtime.lifecycle.representation := by
    rw [TemporalControl.followOptions_eq]
    split <;> rfl
  rw [← followed]
  generalize selected.followOptions (modelOperations criterion dimension) features
    obs.declared reward goal decision = followed
  cases selected.takeoverValue features obs.declared goal decision with
  | none => rfl
  | some value =>
    rw [TemporalControl.closeSpan_eq]
    rfl

/-- Under the default order, a step of a profile with no hierarchy advances the agent's clock
once, before its tester runs. -/
theorem step_clock (agent : Agent interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (percept : Percept interface) :
    (agent.choose .learnThenAct percept).learned.clock = advanceClock agent.clock ∧
      (agent.choose .learnThenAct percept).learn.clock = advanceClock agent.clock := by
  obtain ⟨selected, ordered, -⟩ := agent.choose_selected .learnThenAct (by decide) percept
  unfold TemporalControl.select at selected
  have chosen := select_representation agent.advanceClock.control _ primitive _ _ _ _ _ _ _
    selected
  have learned : (agent.choose .learnThenAct percept).learned.clock = advanceClock agent.clock := by
    change ((((agent.choose .learnThenAct percept).control.deferred
      (agent.choose .learnThenAct percept).order planning
      (agent.choose .learnThenAct percept).features (agent.choose .learnThenAct percept).owed
      (agent.choose .learnThenAct percept).percept.reward
      (agent.choose .learnThenAct percept).percept.frame.achieved
      (agent.choose .learnThenAct percept).decision).learn
      (agent.choose .learnThenAct percept).features
      (agent.choose .learnThenAct percept).percept.frame
      (agent.choose .learnThenAct percept).percept.reward
      (agent.choose .learnThenAct percept).percept.frame.achieved
      (agent.choose .learnThenAct percept).decision
      ).runtime.lifecycle.representation.progress.clock) = _
    rw [learn_representation, ordered]
    change (agent.choose .learnThenAct percept
      ).control.runtime.lifecycle.representation.progress.clock = _
    rw [chosen]
    rfl
  exact ⟨learned, (retire_clock _ _).trans learned⟩

/-- The completion boundary of a learning profile stores the predictions its demons return. -/
theorem finish_predictions (learning : profile.mode ≠ .frozen)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.references.demonPredictions =
      (state.runtime.lifecycle.consumers.demons.step features
        (signalValues obs reward)).predictions := by
  simp [TemporalControl.finish_eq, TemporalControl.predictionView,
    PredictionControl.advanceWith, TemporalControl.recordEpisodes, learning]

/-- The tester keeps the stored predictions. -/
theorem retire_predictions (agent : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (agent.retire active).control.runtime.references.demonPredictions =
      agent.control.runtime.references.demonPredictions := by
  unfold Agent.retire
  split <;> rfl

/-- **A step of a learning profile stores what its demons predicted before they learned.** The
predictions the next frame feeds back are the ones the demons the step started from return on
the step's frame. -/
theorem step_predictions (learning : profile.mode ≠ .frozen)
    (agent : Agent interface profile config criterion dimension planning) (order : StepOrder)
    (percept : Percept interface) :
    (agent.choose order percept).learn.control.runtime.references.demonPredictions =
      (agent.control.runtime.lifecycle.consumers.demons.step (agent.choose order percept).features
        (signalValues percept.frame percept.reward)).predictions := by
  unfold Chosen.learn
  rw [retire_predictions]
  change ((finishInput (agent.choose order percept)).finish _ _ _
    _).runtime.references.demonPredictions = _
  rw [finish_predictions learning, finishInput_demons, choose_percept]

/-- **The cold agent's first step stores the predictions it started with.** For a learning
profile, under every step order and on every percept: the fresh demons return the cold cache
(`initial_bank_predictions`). -/
theorem cold_step_predictions (learning : profile.mode ≠ .frozen) (order : StepOrder)
    (percept : Percept interface) :
    ((Agent.initial interface profile config criterion dimension planning).choose order
        percept).learn.control.runtime.references.demonPredictions =
      (Agent.initial interface profile config criterion dimension
        planning).control.runtime.references.demonPredictions := by
  rw [step_predictions learning]
  exact initial_bank_predictions _ _ _

/-- **Before a unit matures, a step of a profile with no hierarchy keeps the bank.** At the
default step order, while the agent's clock is below the tester's maturity threshold: selection
and learning keep the representation, and the tester replaces no unit. -/
theorem young_bank (primitive : profile.usesHierarchy = false)
    (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) (young : agent.clock.toNat < config.tester.maturity) :
    (agent.choose .learnThenAct percept).learn.control.runtime.lifecycle.representation.bank =
      agent.control.runtime.lifecycle.representation.bank := by
  obtain ⟨selected, ordered, -⟩ := agent.choose_selected .learnThenAct (by decide) percept
  unfold TemporalControl.select at selected
  have chosen := select_representation agent.advanceClock.control _ primitive _ _ _ _ _ _ _
    selected
  have learned :
      (agent.choose .learnThenAct percept).learned.control.runtime.lifecycle.representation =
        agent.advanceClock.control.runtime.lifecycle.representation := by
    change ((((agent.choose .learnThenAct percept).control.deferred
      (agent.choose .learnThenAct percept).order planning
      (agent.choose .learnThenAct percept).features (agent.choose .learnThenAct percept).owed
      (agent.choose .learnThenAct percept).percept.reward
      (agent.choose .learnThenAct percept).percept.frame.achieved
      (agent.choose .learnThenAct percept).decision).learn
      (agent.choose .learnThenAct percept).features
      (agent.choose .learnThenAct percept).percept.frame
      (agent.choose .learnThenAct percept).percept.reward
      (agent.choose .learnThenAct percept).percept.frame.achieved
      (agent.choose .learnThenAct percept).decision
      ).runtime.lifecycle.representation) = _
    rw [learn_representation, ordered]
    exact chosen
  have clock := (step_clock agent primitive percept).1
  have youngLearned : (agent.choose .learnThenAct percept).learned.clock.toNat ≤
      config.tester.maturity := by
    rw [clock, advanceClock_exact]
    exact Nat.le_trans (Nat.min_le_left _ _) young
  have kept :
      (agent.choose .learnThenAct percept).learn.control.runtime.lifecycle.representation.bank =
        (agent.choose .learnThenAct
          percept).learned.control.runtime.lifecycle.representation.bank := by
    unfold Chosen.learn Agent.retire
    split
    · rfl
    · exact idle_test_bank _ _ _ (young_ineligible _ _ youngLearned)
  rw [kept, learned]
  rfl

end Step

/-! ## A run before a unit matures -/

section Run

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {dimension : Dimension} {planning : PlanningSelection}

/-- A profile with no hierarchy is a learning profile. -/
theorem primitive_learns (primitive : profile.usesHierarchy = false) : profile.mode ≠ .frozen := by
  intro frozen
  simp [FeatureProfile.usesHierarchy, frozen] at primitive

/-- **Before a unit matures, one agent step is one controller step.** For a profile with no
hierarchy under per-step credit, at the default step order, while the agent's clock is below the
tester's maturity threshold: the step leaves the primitive controller that one controller step
leaves, at the encoded frame, the executed action and the centred reward. No retirement follows
it. -/
theorem young_step {criterion : Criterion} (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) (young : agent.clock.toNat < config.tester.maturity) :
    controlOf (agent.choose .learnThenAct percept).learn =
      ((controlOf agent).step (agent.choose .learnThenAct percept).features
        (agent.choose .learnThenAct percept).decision.action
        (criterion.center percept.reward 1
          (finishInput (agent.choose .learnThenAct percept)).average.rate)).1 := by
  have learning := primitive_learns primitive
  have clock := (step_clock agent primitive percept).1
  have youngLearned : (agent.choose .learnThenAct percept).learned.clock.toNat ≤
      config.tester.maturity := by
    rw [clock, advanceClock_exact]
    exact Nat.le_trans (Nat.min_le_left _ _) young
  unfold Chosen.learn
  rw [young_retire _ _ youngLearned]
  change ((finishInput (agent.choose .learnThenAct percept)).finish _ _ _
    _).runtime.lifecycle.consumers.control = _
  rw [finish_control perStep, finishInput_control, choose_percept]
  simp only [learning, ↓reduceIte]

/-- One reward-free step before a unit matures, under the discounted criterion: it is the
controller's step at the zero reward word, it keeps the agent's learners at rest and its primitive
controller quiet against the history extended by the step, and it advances the clock by at most
one. -/
theorem young_quiet_step (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat)) (percept : Percept interface)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (silent : percept.reward = .zero) (young : agent.clock.toNat < config.tester.maturity)
    (fits : (agent.choose .learnThenAct percept).features.indices.length ≤ 1999) :
    controlOf (agent.choose .learnThenAct percept).learn =
        ((controlOf agent).step (agent.choose .learnThenAct percept).features
          (agent.choose .learnThenAct percept).decision.action .zero).1 ∧
      Quiet (agent.choose .learnThenAct percept).learn.control ∧
      CtrlQuiet .discounted (controlOf (agent.choose .learnThenAct percept).learn)
        (history ++ [⟨(agent.choose .learnThenAct percept).features,
          (agent.choose .learnThenAct percept).decision.action⟩]) ∧
      (agent.choose .learnThenAct percept).learn.clock.toNat ≤ agent.clock.toNat + 1 := by
  have stepped := young_step primitive perStep agent percept young
  have centred : Criterion.center .discounted percept.reward 1
      (finishInput (agent.choose .learnThenAct percept)).average.rate = Binary32.zero := silent
  rw [centred] at stepped
  have zero : percept.reward.isZero = true := by
    rw [silent]
    decide
  refine ⟨stepped, quiet.actOrdered .learnThenAct percept (Inert32.ofZero zero), ?_, ?_⟩
  · rw [stepped]
    exact ctrlQuiet_step ctrl _ _ (by decide : Binary32.zero.isZero = true) fits
  · rw [(step_clock agent primitive percept).2, advanceClock_exact]
    exact Nat.min_le_left _ _

/-- **A reward-free run before a unit matures** keeps the agent's learners at rest and its
primitive controller quiet against what it laid, and advances the clock by at most its length. -/
theorem traced_young (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) :
    ∀ (percepts : List (Percept interface))
      (agent : Agent interface profile config .discounted dimension planning)
      (history : List (Laid dimension interface.actions.word.toNat)),
      Quiet agent.control → CtrlQuiet .discounted (controlOf agent) history →
      (∀ percept ∈ percepts, percept.reward = .zero) →
      agent.clock.toNat + percepts.length ≤ config.tester.maturity →
      (∀ step ∈ (traced .learnThenAct agent percepts).2, step.features.indices.length ≤ 1999) →
      Quiet (traced .learnThenAct agent percepts).1.control ∧
        CtrlQuiet .discounted (controlOf (traced .learnThenAct agent percepts).1)
          (history ++ (traced .learnThenAct agent percepts).2) ∧
        (traced .learnThenAct agent percepts).1.clock.toNat ≤
          agent.clock.toNat + percepts.length := by
  intro percepts
  induction percepts with
  | nil =>
    intro agent history quiet ctrl _ _ _
    simp only [traced, List.append_nil, List.length_nil, Nat.add_zero]
    exact ⟨quiet, ctrl, le_rfl⟩
  | cons percept rest ih =>
    intro agent history quiet ctrl silent young fits
    rw [List.length_cons] at young
    obtain ⟨-, quietNext, ctrlNext, clockNext⟩ := young_quiet_step primitive perStep agent history
      percept quiet ctrl (silent percept List.mem_cons_self) (by omega)
      (fits ⟨(agent.choose .learnThenAct percept).features,
        (agent.choose .learnThenAct percept).decision.action⟩ List.mem_cons_self)
    obtain ⟨quietLast, ctrlLast, clockLast⟩ := ih _ _ quietNext ctrlNext
      (fun other member => silent other (List.mem_cons_of_mem _ member)) (by omega)
      (fun step member => fits step (List.mem_cons_of_mem _ member))
    refine ⟨quietLast, ?_, ?_⟩
    · simpa [traced, List.append_assoc] using ctrlLast
    · simp only [traced, List.length_cons]
      omega

/-- **Over a reward-free run before a unit matures, a recent slot stays recent**, decayed once
for each step, while the decayed least laid trace stays above the pruning threshold. -/
theorem traced_recent (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (row : Action interface.actions.word.toNat)
    (slot : FeatIdx dimension) :
    ∀ (percepts : List (Percept interface))
      (agent : Agent interface profile config .discounted dimension planning)
      (history : List (Laid dimension interface.actions.word.toNat)) (i : ℕ),
      Quiet agent.control → CtrlQuiet .discounted (controlOf agent) history →
      Recent (controlOf agent) row slot (lowChain .discounted i) →
      (∀ percept ∈ percepts, percept.reward = .zero) →
      i + percepts.length ≤ 80 →
      agent.clock.toNat + percepts.length ≤ config.tester.maturity →
      (∀ step ∈ (traced .learnThenAct agent percepts).2, step.features.indices.length ≤ 1999) →
      Recent (controlOf (traced .learnThenAct agent percepts).1) row slot
        (lowChain .discounted (i + percepts.length)) := by
  intro percepts
  induction percepts with
  | nil =>
    intro agent history i _ _ recent _ _ _ _
    simpa [traced] using recent
  | cons percept rest ih =>
    intro agent history i quiet ctrl recent silent near young fits
    rw [List.length_cons] at near young
    have fitsHere := fits ⟨(agent.choose .learnThenAct percept).features,
      (agent.choose .learnThenAct percept).decision.action⟩ List.mem_cons_self
    obtain ⟨stepped, quietNext, ctrlNext, clockNext⟩ := young_quiet_step primitive perStep agent
      history percept quiet ctrl (silent percept List.mem_cons_self) (by omega) fitsHere
    have facts := lowChain_facts .discounted i
    have recentNext : Recent (controlOf (agent.choose .learnThenAct percept).learn) row slot
        (lowChain .discounted (i + 1)) := by
      rw [stepped]
      exact recent_after ctrl _ _ fitsHere row slot _ facts.1 facts.2.1 recent
        (lowChain_above .discounted (i + 1) (by omega))
    have result := ih _ _ (i + 1) quietNext ctrlNext recentNext
      (fun other member => silent other (List.mem_cons_of_mem _ member)) (by omega) (by omega)
      (fun step member => fits step (List.mem_cons_of_mem _ member))
    simpa [traced, Nat.add_assoc, Nat.add_comm 1] using result

end Run

/-! ## A kernel run as a traced run -/

section Loop

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- In a kernel run, the executed agent's memory one time later is the agent its step returns on
the percept of that time. -/
theorem loop_step (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    Kernel.memoryAt world (executedAgent agent) start (time + 1) =
      ((Kernel.memoryAt world (executedAgent agent) start time).choose .learnThenAct
        (Kernel.perceptAt world (executedAgent agent) start time)).learn :=
  congrArg Prod.fst (Agent.act_parts (Kernel.memoryAt world (executedAgent agent) start time)
    (Kernel.perceptAt world (executedAgent agent) start time))

/-- **A kernel run of the executed agent is its traced run over the percepts it receives.** From
its memory at one time, the traced run over the percepts of the next `count` times ends in its
memory `count` times later. -/
theorem traced_loop (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) :
    ∀ (count origin : ℕ),
      (traced .learnThenAct (Kernel.memoryAt world (executedAgent agent) start origin)
        ((List.range' origin count).map
          (Kernel.perceptAt world (executedAgent agent) start))).1 =
        Kernel.memoryAt world (executedAgent agent) start (origin + count) := by
  intro count
  induction count with
  | zero => intro origin; rfl
  | succ count ih =>
    intro origin
    rw [List.range'_succ, List.map_cons]
    change (traced .learnThenAct
      ((Kernel.memoryAt world (executedAgent agent) start origin).choose .learnThenAct
        (Kernel.perceptAt world (executedAgent agent) start origin)).learn
      ((List.range' (origin + 1) count).map
        (Kernel.perceptAt world (executedAgent agent) start))).1 = _
    rw [← loop_step, ih (origin + 1)]
    exact congrArg (Kernel.memoryAt world (executedAgent agent) start)
      (show origin + 1 + count = origin + (count + 1) by omega)

/-- What the executed agent's step at a time of a kernel run lays: the frame it encodes and the
action it takes. -/
def laidAt (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    Laid dimension interface.actions.word.toNat :=
  ⟨((Kernel.memoryAt world (executedAgent agent) start time).choose .learnThenAct
      (Kernel.perceptAt world (executedAgent agent) start time)).features,
    ((Kernel.memoryAt world (executedAgent agent) start time).choose .learnThenAct
      (Kernel.perceptAt world (executedAgent agent) start time)).decision.action⟩

/-- The row a step of a kernel run lays is the action the run takes at that time. -/
theorem laidAt_row (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    (laidAt agent world start time).row =
      Kernel.actionAt world (executedAgent agent) start time :=
  (congrArg (fun step => step.2.action)
    (Agent.act_parts (Kernel.memoryAt world (executedAgent agent) start time)
      (Kernel.perceptAt world (executedAgent agent) start time))).symm

/-- The steps a traced run over the percepts of a kernel run lays are the steps of the run. -/
theorem traced_laid (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) :
    ∀ (count origin : ℕ),
      (traced .learnThenAct (Kernel.memoryAt world (executedAgent agent) start origin)
        ((List.range' origin count).map
          (Kernel.perceptAt world (executedAgent agent) start))).2 =
        (List.range' origin count).map (laidAt agent world start) := by
  intro count
  induction count with
  | zero => intro origin; rfl
  | succ count ih =>
    intro origin
    rw [List.range'_succ, List.map_cons, List.map_cons]
    change laidAt agent world start origin :: (traced .learnThenAct
      ((Kernel.memoryAt world (executedAgent agent) start origin).choose .learnThenAct
        (Kernel.perceptAt world (executedAgent agent) start origin)).learn
      ((List.range' (origin + 1) count).map
        (Kernel.perceptAt world (executedAgent agent) start))).2 = _
    rw [← loop_step, ih (origin + 1)]

/-- In a kernel run the clock of a profile with no hierarchy advances by at most one each time. -/
theorem loop_clock (primitive : profile.usesHierarchy = false)
    (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    (Kernel.memoryAt world (executedAgent agent) start time).clock.toNat ≤
      agent.clock.toNat + time := by
  induction time with
  | zero => exact le_rfl
  | succ time ih =>
    have next : (Kernel.memoryAt world (executedAgent agent) start (time + 1)).clock =
        advanceClock (Kernel.memoryAt world (executedAgent agent) start time).clock :=
      (congrArg (fun memory : Agent interface profile config criterion dimension planning =>
        memory.clock) (loop_step agent world start time)).trans
        (step_clock (Kernel.memoryAt world (executedAgent agent) start time) primitive
          (Kernel.perceptAt world (executedAgent agent) start time)).2
    rw [next, advanceClock_exact]
    exact Nat.le_trans (Nat.min_le_left _ _) (by omega)

/-- **A reward-free kernel run before a unit matures.** For a profile with no hierarchy under
per-step credit and the discounted criterion, from an agent state whose learners are at rest and
whose primitive controller is quiet against a history: in a kernel run in which every reward word
before a time is the zero word, over frames of at most 1999 slots and before a unit of the
feature bank matures, the agent's learners are still at rest at that time and its primitive
controller is quiet against the history extended by the steps of the run. It is `traced_young`
on the percepts of the run. -/
theorem loop_quiet (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (time : ℕ)
    (young : agent.clock.toNat + time ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < time →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < time →
      (laidAt agent world start earlier).features.indices.length ≤ 1999) :
    Quiet (Kernel.memoryAt world (executedAgent agent) start time).control ∧
      CtrlQuiet .discounted (controlOf (Kernel.memoryAt world (executedAgent agent) start time))
        (history ++ (List.range' 0 time).map (laidAt agent world start)) := by
  have laid : (traced .learnThenAct agent ((List.range' 0 time).map
      (Kernel.perceptAt world (executedAgent agent) start))).2 =
        (List.range' 0 time).map (laidAt agent world start) := traced_laid agent world start time 0
  have reached : (traced .learnThenAct agent ((List.range' 0 time).map
      (Kernel.perceptAt world (executedAgent agent) start))).1 =
        Kernel.memoryAt world (executedAgent agent) start time := by
    have run := traced_loop agent world start time 0
    rw [Nat.zero_add] at run
    exact run
  have run := traced_young primitive perStep
    ((List.range' 0 time).map (Kernel.perceptAt world (executedAgent agent) start)) agent history
    quiet ctrl
    (fun percept member => by
      obtain ⟨earlier, inside, rfl⟩ := List.mem_map.mp member
      exact silent earlier (by have := (List.mem_range'_1.mp inside).2; omega))
    (by rw [List.length_map, List.length_range']; exact young)
    (fun step member => by
      rw [laid] at member
      obtain ⟨earlier, inside, rfl⟩ := List.mem_map.mp member
      exact fits earlier (by have := (List.mem_range'_1.mp inside).2; omega))
  rw [laid, reached] at run
  exact ⟨run.1, run.2.1⟩

/-- **In a kernel run a laid slot stays recent while the rewards are zero.** Under the
hypotheses of `loop_quiet`, every slot of a frame of at most 1900 slots that the run laid at one
time is, `gap` steps after the step that laid it and for a `gap` of at most 80, still eligible in
the row of the action taken on that frame, with a trace at least the least laid trace decayed
`gap` times. It is `AcornVerif.CurrentCreditHorizon.recent_laid` at the laying step and
`traced_recent` on the percepts after it. -/
theorem loop_recent (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (laid gap : ℕ) (near : gap ≤ 80)
    (young : agent.clock.toNat + (laid + 1 + gap) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < laid + 1 + gap →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < laid + 1 + gap →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsLaid : (laidAt agent world start laid).features.indices.length ≤ 1900)
    (slot : FeatIdx dimension) (held : slot ∈ (laidAt agent world start laid).features.indices) :
    Recent (controlOf (Kernel.memoryAt world (executedAgent agent) start (laid + 1 + gap)))
      (laidAt agent world start laid).row slot (lowChain .discounted gap) := by
  obtain ⟨quietLaid, ctrlLaid⟩ := loop_quiet primitive perStep agent history quiet
    ctrl world start laid (by omega) (fun earlier before => silent earlier (by omega))
    (fun earlier before => fits earlier (by omega))
  have clockLaid := loop_clock primitive agent world start laid
  obtain ⟨stepped, quietNext, ctrlNext, -⟩ := young_quiet_step primitive perStep
    (Kernel.memoryAt world (executedAgent agent) start laid) _
    (Kernel.perceptAt world (executedAgent agent) start laid) quietLaid ctrlLaid
    (silent laid (by omega)) (by omega) (fits laid (by omega))
  have recent : Recent (controlOf ((Kernel.memoryAt world (executedAgent agent) start
      laid).choose .learnThenAct (Kernel.perceptAt world (executedAgent agent) start
        laid)).learn) (laidAt agent world start laid).row slot (lowChain .discounted 0) := by
    rw [stepped]
    exact recent_laid ctrlLaid _ _ fitsLaid slot held
  have next := loop_step agent world start laid
  have clockNext := loop_clock primitive agent world start (laid + 1)
  have later := traced_recent primitive perStep (laidAt agent world start laid).row slot
    ((List.range' (laid + 1) gap).map (Kernel.perceptAt world (executedAgent agent) start))
    (Kernel.memoryAt world (executedAgent agent) start (laid + 1)) _ 0 (next ▸ quietNext)
    (next ▸ ctrlNext) (next ▸ recent)
    (fun percept member => by
      obtain ⟨earlier, inside, rfl⟩ := List.mem_map.mp member
      exact silent earlier (by have := (List.mem_range'_1.mp inside).2; omega))
    (by rw [List.length_map, List.length_range']; omega)
    (by rw [List.length_map, List.length_range']; omega)
    (fun step member => by
      rw [traced_laid] at member
      obtain ⟨earlier, inside, rfl⟩ := List.mem_map.mp member
      exact fits earlier (by have := (List.mem_range'_1.mp inside).2; omega))
  rw [List.length_map, List.length_range', Nat.zero_add, traced_loop] at later
  exact later

/-- **A reward-free step of a kernel run, before a unit matures.** Under the hypotheses of
`loop_quiet` up to and including a time: the primitive controller before the step of that time is
quiet against the frames laid so far, and the step leaves the controller that one controller step
at reward zero leaves, at the frame and the action of that time. -/
theorem loop_silent (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (time : ℕ)
    (young : agent.clock.toNat + (time + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < time + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < time + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999) :
    CtrlQuiet .discounted (controlOf (Kernel.memoryAt world (executedAgent agent) start time))
        (history ++ (List.range' 0 time).map (laidAt agent world start)) ∧
      controlOf (Kernel.memoryAt world (executedAgent agent) start (time + 1)) =
        ((controlOf (Kernel.memoryAt world (executedAgent agent) start time)).step
          (laidAt agent world start time).features (laidAt agent world start time).row
          .zero).1 := by
  obtain ⟨quietHere, ctrlHere⟩ := loop_quiet primitive perStep agent history quiet ctrl world
    start time (by omega) (fun earlier before => silent earlier (by omega))
    (fun earlier before => fits earlier (by omega))
  have clock := loop_clock primitive agent world start time
  obtain ⟨equation, -⟩ := young_quiet_step primitive perStep
    (Kernel.memoryAt world (executedAgent agent) start time) _
    (Kernel.perceptAt world (executedAgent agent) start time) quietHere ctrlHere
    (silent time (by omega)) (by omega) (fits time (by omega))
  exact ⟨ctrlHere, (congrArg (fun memory : Agent interface profile config .discounted
    dimension planning => controlOf memory) (loop_step agent world start time)).trans
      equation⟩

/-- **The step that learns a reward of one, before a unit matures.** For a profile with no
hierarchy under per-step credit and the discounted criterion, in a kernel run: when the percept
of a time carries the reward word one and the agent's clock is still below the tester's maturity
threshold, the step of that time leaves the primitive controller that one controller step at
reward one leaves, at the frame and the action of that time. It is `young_step` on that percept:
under the discounted criterion the centred reward is the reward word. -/
theorem loop_paid (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid < config.tester.maturity)
    (pays : (Kernel.perceptAt world (executedAgent agent) start paid).reward = .one) :
    controlOf (Kernel.memoryAt world (executedAgent agent) start (paid + 1)) =
      ((controlOf (Kernel.memoryAt world (executedAgent agent) start paid)).step
        (laidAt agent world start paid).features (laidAt agent world start paid).row .one).1 := by
  have clock := loop_clock primitive agent world start paid
  have stepped := young_step primitive perStep
    (Kernel.memoryAt world (executedAgent agent) start paid)
    (Kernel.perceptAt world (executedAgent agent) start paid) (by omega)
  have centred : Criterion.center .discounted
      (Kernel.perceptAt world (executedAgent agent) start paid).reward 1
      (finishInput ((Kernel.memoryAt world (executedAgent agent) start paid).choose
        .learnThenAct (Kernel.perceptAt world (executedAgent agent) start
          paid))).average.rate = Binary32.one := pays
  rw [centred] at stepped
  exact (congrArg (fun memory : Agent interface profile config .discounted dimension planning =>
    controlOf memory) (loop_step agent world start paid)).trans stepped

/-- **The first reward's credit in a kernel run.** For a profile with no hierarchy under per-step
credit and the discounted criterion, from cold initialization, in every world of the agent's
interface and from every start: if, for a `gap` of at most 80, every reward word up to the time
`laid + gap` is the zero word and the next one is the word one, all before a unit of the feature
bank matures, over frames of at most 1999 slots and the one laid at the time `laid` of at most
1900, then right after the step that learns that reward, every slot of the frame laid at the
time `laid` holds, in the row of the action taken on it, a weight that reads at least the least
laid trace decayed `gap` times. The slot is recent when the reward comes (`loop_recent`), the
step that learns the reward is one controller step at reward one (`loop_paid`), and that step
writes at least a recent slot's least trace into its weight
(`AcornVerif.CurrentCreditHorizon.recent_credited`). -/
theorem loop_first_credit (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (planning : PlanningSelection)
    (world : Kernel.World interface) (start : world.State) (laid gap : ℕ) (near : gap ≤ 80)
    (young : laid + gap + 2 ≤ config.tester.maturity)
    (silent : ∀ time, time ≤ laid + gap →
      (Kernel.perceptAt world (executedAgent
        (Agent.initial interface profile config .discounted dimension planning)) start
        time).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent
      (Agent.initial interface profile config .discounted dimension planning)) start
      (laid + 1 + gap)).reward = .one)
    (fits : ∀ time, time ≤ laid + gap →
      (laidAt (Agent.initial interface profile config .discounted dimension planning) world start
        time).features.indices.length ≤ 1999)
    (fitsLaid : (laidAt (Agent.initial interface profile config .discounted dimension planning)
      world start laid).features.indices.length ≤ 1900) :
    ∀ slot ∈ (laidAt (Agent.initial interface profile config .discounted dimension planning)
        world start laid).features.indices,
      numerical32 (lowChain .discounted gap) ≤
        numerical32 (((controlOf (Kernel.memoryAt world (executedAgent
          (Agent.initial interface profile config .discounted dimension planning)) start
          (laid + 1 + gap + 1))).learners.get
          (laidAt (Agent.initial interface profile config .discounted dimension planning) world
            start laid).row).state.weights.get slot).value := by
  intro slot held
  have coldClock : (Agent.initial interface profile config .discounted dimension
      planning).clock.toNat = 0 := rfl
  have recent := loop_recent primitive perStep
    (Agent.initial interface profile config .discounted dimension planning) [] Quiet.initial
    ctrlQuiet_initial world start laid gap near (by rw [coldClock]; omega)
    (fun earlier before => silent earlier (by omega))
    (fun earlier before => fits earlier (by omega)) fitsLaid slot held
  obtain ⟨-, ctrl⟩ := loop_quiet primitive perStep
    (Agent.initial interface profile config .discounted dimension planning) [] Quiet.initial
    ctrlQuiet_initial world start (laid + 1 + gap) (by rw [coldClock]; omega)
    (fun earlier before => silent earlier (by omega))
    (fun earlier before => fits earlier (by omega))
  rw [loop_paid primitive perStep
    (Agent.initial interface profile config .discounted dimension planning) world start
    (laid + 1 + gap) (by rw [coldClock]; omega) pays]
  exact recent_credited ctrl _ _ _ slot _ recent (lowChain_positive .discounted gap near)

end Loop

end AcornVerif.CurrentFirstCredit
