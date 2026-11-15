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
that to the executed agent and gives an amount. After the agent's step on the first rewarded
percept, every slot of a frame it laid at most 81 steps before holds, in the row of the action
taken on that frame, a weight that reads at least the least laid trace decayed once for each step
between (`first_reward_credits`; `loop_first_credit` is the same statement of a kernel run).

An agent's step is one controller step followed by the tester's retirements
(`AcornVerif.CurrentCreditHorizon.learning_step`), and a retirement clears a slot's weight and
trace. So the statement is of the agent's run before a unit of its feature bank matures, when the
tester retires nothing. The names here call such an agent, step or run young.

- **The tester before a unit matures.** A unit is eligible for replacement once its age exceeds
  the tester's maturity threshold (`Acorn.Features.Lifecycle.mature`). While the clock is at most
  that threshold no unit is eligible (`young_ineligible`), a test replaces no unit and writes no
  learner (`idle_test`), and the tester leaves the primitive controller as it was
  (`young_retire`). The declared tester's threshold is 1000 steps
  (`Acorn.Handcrafted.declaredTester`).
- **The clock.** Under the default order, a step of a profile with no hierarchy advances the
  agent's clock once, before its tester runs (`step_clock`): its selection and its learning part
  keep the representation that holds the clock, and its tester keeps the clock (`retire_clock`).
- **One step.** So before a unit matures, one agent step is exactly one controller step at the
  encoded frame, the executed action and the centred reward (`young_step`). Under the discounted
  criterion the centred reward is the percept's reward word.
- **A run.** Over percepts whose reward word is the zero word, the controller stays quiet against
  what it laid (`traced_young`), and a recent slot stays recent, decayed once for each step
  (`traced_recent`). A first reward of one then writes at least the slot's least trace into its
  weight (`AcornVerif.CurrentCreditHorizon.recent_credited`).

`traced_loop` says that a kernel run of the executed agent is its traced run over the percepts it
receives, which is how `loop_first_credit` follows.

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

end Tester

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

/-- **The first reward's credit along the executed agent's run.** For a profile with no hierarchy
under per-step credit and the discounted criterion, at the default step order, from cold
initialization: let the agent lay a frame at one step, take at most eighty more steps, and then
receive a first reward of one, all before a unit of its feature bank matures, over frames of at
most 1999 slots, the laid one of at most 1900. Then after the step that learns the reward, every
slot of the laid frame holds, in the row of the action taken on it, a weight that reads at least
the least laid trace decayed once for each step between. -/
theorem first_reward_credits (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (planning : PlanningSelection)
    (before after : List (Percept interface)) (laying paying : Percept interface)
    (silent : ∀ percept ∈ before ++ laying :: after, percept.reward = .zero)
    (pays : paying.reward = .one) (near : after.length ≤ 80)
    (young : before.length + after.length + 2 ≤ config.tester.maturity) :
    let cold := Agent.initial interface profile config .discounted dimension planning
    let prior := traced .learnThenAct cold before
    let laid := prior.1.choose .learnThenAct laying
    let waited := traced .learnThenAct laid.learn after
    let paid := (waited.1.choose .learnThenAct paying).learn
    (∀ step ∈ prior.2, step.features.indices.length ≤ 1999) →
    laid.features.indices.length ≤ 1900 →
    (∀ step ∈ waited.2, step.features.indices.length ≤ 1999) →
    ∀ slot ∈ laid.features.indices,
      numerical32 (lowChain .discounted after.length) ≤
        numerical32 (((controlOf paid).learners.get laid.decision.action).state.weights.get
          slot).value := by
  intro cold prior laid waited paid fitsBefore fitsLaid fitsAfter slot held
  have coldClock : cold.clock.toNat = 0 := rfl
  obtain ⟨quietPrior, ctrlPrior, clockPrior⟩ := traced_young primitive perStep before cold []
    Quiet.initial ctrlQuiet_initial
    (fun percept member => silent percept (List.mem_append_left _ member))
    (by rw [coldClock]; omega) fitsBefore
  rw [List.nil_append] at ctrlPrior
  have priorClock : prior.1.clock.toNat ≤ before.length := by
    rw [coldClock, Nat.zero_add] at clockPrior
    exact clockPrior
  have fitsLaying : laid.features.indices.length ≤ 1999 := Nat.le_trans fitsLaid (by decide)
  obtain ⟨steppedLaid, quietLaid, ctrlLaid, clockLaid⟩ := young_quiet_step primitive perStep
    prior.1 prior.2 laying quietPrior ctrlPrior
    (silent laying (List.mem_append_right _ List.mem_cons_self))
    (Nat.lt_of_le_of_lt priorClock (by omega)) fitsLaying
  have laidClock : laid.learn.clock.toNat ≤ before.length + 1 :=
    Nat.le_trans clockLaid (Nat.succ_le_succ priorClock)
  have recentLaid : Recent (controlOf laid.learn) laid.decision.action slot
      (lowChain .discounted 0) := by
    rw [steppedLaid]
    exact recent_laid ctrlPrior laid.features laid.decision.action fitsLaid slot held
  have silentAfter : ∀ percept ∈ after, percept.reward = .zero := fun percept member =>
    silent percept (List.mem_append_right _ (List.mem_cons_of_mem _ member))
  have youngAfter : laid.learn.clock.toNat + after.length ≤ config.tester.maturity :=
    Nat.le_trans (Nat.add_le_add_right laidClock _) (by omega)
  obtain ⟨quietWaited, ctrlWaited, clockWaited⟩ := traced_young primitive perStep after
    laid.learn _ quietLaid ctrlLaid silentAfter youngAfter fitsAfter
  have waitedClock : waited.1.clock.toNat ≤ before.length + 1 + after.length :=
    Nat.le_trans clockWaited (Nat.add_le_add_right laidClock _)
  have recentWaited := traced_recent primitive perStep laid.decision.action slot after
    laid.learn _ 0 quietLaid ctrlLaid recentLaid silentAfter (by omega) youngAfter fitsAfter
  rw [Nat.zero_add] at recentWaited
  have steppedPaid := young_step primitive perStep waited.1 paying
    (Nat.lt_of_le_of_lt waitedClock (by omega))
  have centred : Criterion.center .discounted paying.reward 1
      (finishInput (waited.1.choose .learnThenAct paying)).average.rate = Binary32.one := pays
  rw [centred] at steppedPaid
  change numerical32 _ ≤ numerical32 (((controlOf
    (waited.1.choose .learnThenAct paying).learn).learners.get _).state.weights.get slot).value
  rw [steppedPaid]
  exact recent_credited ctrlWaited _ _ _ slot _ recentWaited
    (lowChain_positive .discounted after.length near)

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

/-- **The first reward's credit in a kernel run.** For a profile with no hierarchy under per-step
credit and the discounted criterion, from cold initialization, in every world of the agent's
interface and from every start: if, for a `gap` of at most 80, every reward word up to the time
`laid + gap` is the zero word and the next one is the word one, all before a unit of the feature
bank matures and over frames within the sizes above, then right after the step that learns that
reward, every slot of the frame laid at the time `laid` holds, in the row of the action taken on
it, a weight that reads at least the least laid trace decayed `gap` times. It is
`first_reward_credits` on the percepts of the run. -/
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
    (fitsBefore : ∀ step ∈ (traced .learnThenAct
        (Agent.initial interface profile config .discounted dimension planning)
        ((List.range' 0 laid).map (Kernel.perceptAt world (executedAgent
          (Agent.initial interface profile config .discounted dimension planning)) start))).2,
      step.features.indices.length ≤ 1999)
    (fitsLaid : ((Kernel.memoryAt world (executedAgent
        (Agent.initial interface profile config .discounted dimension planning)) start
        laid).choose .learnThenAct (Kernel.perceptAt world (executedAgent
          (Agent.initial interface profile config .discounted dimension planning)) start
          laid)).features.indices.length ≤ 1900)
    (fitsAfter : ∀ step ∈ (traced .learnThenAct (Kernel.memoryAt world (executedAgent
        (Agent.initial interface profile config .discounted dimension planning)) start
        (laid + 1))
        ((List.range' (laid + 1) gap).map (Kernel.perceptAt world (executedAgent
          (Agent.initial interface profile config .discounted dimension planning)) start))).2,
      step.features.indices.length ≤ 1999) :
    ∀ slot ∈ ((Kernel.memoryAt world (executedAgent
        (Agent.initial interface profile config .discounted dimension planning)) start
        laid).choose .learnThenAct (Kernel.perceptAt world (executedAgent
          (Agent.initial interface profile config .discounted dimension planning)) start
          laid)).features.indices,
      numerical32 (lowChain .discounted gap) ≤
        numerical32 (((controlOf (Kernel.memoryAt world (executedAgent
          (Agent.initial interface profile config .discounted dimension planning)) start
          (laid + 1 + gap + 1))).learners.get
          ((Kernel.memoryAt world (executedAgent
            (Agent.initial interface profile config .discounted dimension planning)) start
            laid).choose .learnThenAct (Kernel.perceptAt world (executedAgent
              (Agent.initial interface profile config .discounted dimension planning)) start
              laid)).decision.action).state.weights.get slot).value := by
  have e1 : (traced .learnThenAct (Agent.initial interface profile config .discounted dimension
      planning)
      ((List.range' 0 laid).map (Kernel.perceptAt world (executedAgent (Agent.initial interface
          profile config .discounted dimension planning)) start))).1 =
        Kernel.memoryAt world (executedAgent (Agent.initial interface profile config .discounted
            dimension planning)) start laid := by
    have run := traced_loop (Agent.initial interface profile config .discounted dimension planning)
        world start laid 0
    rw [Nat.zero_add] at run
    exact run
  have e2 : ((Kernel.memoryAt world (executedAgent (Agent.initial interface profile config
      .discounted dimension planning)) start laid).choose .learnThenAct
      (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config .discounted
          dimension planning)) start laid)).learn =
        Kernel.memoryAt world (executedAgent (Agent.initial interface profile config .discounted
            dimension planning)) start (laid + 1) :=
    (loop_step (Agent.initial interface profile config .discounted dimension planning) world start
        laid).symm
  have e3 : (traced .learnThenAct (Kernel.memoryAt world (executedAgent (Agent.initial interface
      profile config .discounted dimension planning)) start (laid + 1))
      ((List.range' (laid + 1) gap).map (Kernel.perceptAt world (executedAgent (Agent.initial
          interface profile config .discounted dimension planning)) start))).1 =
        Kernel.memoryAt world (executedAgent (Agent.initial interface profile config .discounted
            dimension planning)) start (laid + 1 + gap) :=
    traced_loop (Agent.initial interface profile config .discounted dimension planning) world start
        gap (laid + 1)
  have e4 : ((Kernel.memoryAt world (executedAgent (Agent.initial interface profile config
      .discounted dimension planning)) start (laid + 1 + gap)).choose
      .learnThenAct (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config
          .discounted dimension planning)) start (laid + 1 + gap))).learn =
        Kernel.memoryAt world (executedAgent (Agent.initial interface profile config .discounted
            dimension planning)) start (laid + 1 + gap + 1) :=
    (loop_step (Agent.initial interface profile config .discounted dimension planning) world start
        (laid + 1 + gap)).symm
  have quiet : ∀ percept ∈ (List.range' 0 laid).map
      (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config .discounted
          dimension planning)) start) ++
        Kernel.perceptAt world (executedAgent (Agent.initial interface profile config .discounted
            dimension planning)) start laid ::
          (List.range' (laid + 1) gap).map (Kernel.perceptAt world (executedAgent (Agent.initial
              interface profile config .discounted dimension planning)) start),
      percept.reward = .zero := by
    intro percept member
    rcases List.mem_append.mp member with early | late
    · obtain ⟨time, inside, rfl⟩ := List.mem_map.mp early
      have bound := (List.mem_range'_1.mp inside).2
      exact silent time (by omega)
    · rcases List.mem_cons.mp late with rfl | later
      · exact silent laid (by omega)
      · obtain ⟨time, inside, rfl⟩ := List.mem_map.mp later
        have bound := (List.mem_range'_1.mp inside).2
        exact silent time (by omega)
  have key := first_reward_credits (dimension := dimension) primitive perStep planning
    ((List.range' 0 laid).map (Kernel.perceptAt world (executedAgent (Agent.initial interface
        profile config .discounted dimension planning)) start))
    ((List.range' (laid + 1) gap).map (Kernel.perceptAt world (executedAgent (Agent.initial
        interface profile config .discounted dimension planning)) start))
    (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config .discounted
        dimension planning)) start laid)
    (Kernel.perceptAt world (executedAgent (Agent.initial interface profile config .discounted
        dimension planning)) start (laid + 1 + gap))
    quiet pays
    (by rw [List.length_map, List.length_range']; exact near)
    (by rw [List.length_map, List.length_map, List.length_range', List.length_range']; omega)
  simp only [e1, e2, e3, e4, List.length_map, List.length_range'] at key
  exact key fitsBefore fitsLaid fitsAfter

end Loop

end AcornVerif.CurrentFirstCredit
