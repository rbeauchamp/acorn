import AcornVerif.CurrentCreditHorizon
import AcornVerif.CurrentGridWorld

namespace AcornVerif.CurrentFirstCredit
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentCreditHorizon AcornVerif.CurrentGridWorld
open AcornVerif.CurrentPreReward

section Tester

variable {shape : PatchShape} {actions : Word.Count} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}

theorem young_ineligible (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (young : state.progress.clock.toNat ≤ config.tester.maturity) :
    state.eligibleCount free = 0 := by
  unfold Lifecycle.eligibleCount
  rw [List.countP_eq_zero]
  intro unit _
  simp only [Lifecycle.eligible, Lifecycle.mature, Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro mature
  omega

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

section Demons

variable {dimension : Dimension}

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

section Step

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

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

theorem retire_clock (agent : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) : (agent.retire active).clock = agent.clock := by
  unfold Agent.retire
  split
  · rfl
  · exact agent.control.runtime.lifecycle.test_clock
      agent.control.runtime.references.phase.free active

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

theorem finish_predictions (learning : profile.mode ≠ .frozen)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (decision : TemporalDecision interface.actions) :
    (state.finish features obs reward decision).runtime.references.demonPredictions =
      (state.runtime.lifecycle.consumers.demons.step features
        (signalValues obs reward)).predictions := by
  simp [TemporalControl.finish_eq, TemporalControl.predictionView,
    PredictionControl.advanceWith, TemporalControl.recordEpisodes, learning]

theorem retire_predictions (agent : Agent interface profile config criterion dimension planning)
    (active : Vector Bool config.units.count) :
    (agent.retire active).control.runtime.references.demonPredictions =
      agent.control.runtime.references.demonPredictions := by
  unfold Agent.retire
  split <;> rfl

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

theorem cold_step_predictions (learning : profile.mode ≠ .frozen) (order : StepOrder)
    (percept : Percept interface) :
    ((Agent.initial interface profile config criterion dimension planning).choose order
        percept).learn.control.runtime.references.demonPredictions =
      (Agent.initial interface profile config criterion dimension
        planning).control.runtime.references.demonPredictions := by
  rw [step_predictions learning]
  exact initial_bank_predictions _ _ _

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

section Run

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {dimension : Dimension} {planning : PlanningSelection}

theorem primitive_learns (primitive : profile.usesHierarchy = false) : profile.mode ≠ .frozen := by
  intro frozen
  simp [FeatureProfile.usesHierarchy, frozen] at primitive

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

section Loop

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

theorem loop_step (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    Kernel.memoryAt world (executedAgent agent) start (time + 1) =
      ((Kernel.memoryAt world (executedAgent agent) start time).choose .learnThenAct
        (Kernel.perceptAt world (executedAgent agent) start time)).learn :=
  congrArg Prod.fst (Agent.act_parts (Kernel.memoryAt world (executedAgent agent) start time)
    (Kernel.perceptAt world (executedAgent agent) start time))

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

def laidAt (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    Laid dimension interface.actions.word.toNat :=
  ⟨((Kernel.memoryAt world (executedAgent agent) start time).choose .learnThenAct
      (Kernel.perceptAt world (executedAgent agent) start time)).features,
    ((Kernel.memoryAt world (executedAgent agent) start time).choose .learnThenAct
      (Kernel.perceptAt world (executedAgent agent) start time)).decision.action⟩

theorem laidAt_row (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time : ℕ) :
    (laidAt agent world start time).row =
      Kernel.actionAt world (executedAgent agent) start time :=
  (congrArg (fun step => step.2.action)
    (Agent.act_parts (Kernel.memoryAt world (executedAgent agent) start time)
      (Kernel.perceptAt world (executedAgent agent) start time))).symm

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
