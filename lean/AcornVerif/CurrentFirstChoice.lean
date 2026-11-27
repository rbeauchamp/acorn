import AcornVerif.CurrentExplorer
import AcornVerif.CurrentFirstCredit

namespace AcornVerif.CurrentFirstChoice
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds
open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward AcornVerif.CurrentFeatureConsumers
open AcornVerif.CurrentControl AcornVerif.CurrentCreditHorizon
open SwiftTd (ActiveSet)

section Controller

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

theorem reward_writes_traces {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action row : Action actions) (slot : FeatIdx dimension) :
    numerical32 (((controller.step features action .one).1.learners.get row).state.weights.get
      slot).value = numerical32 (slotOf (controller.learners.get row).state slot).z := by
  rw [step_eq]
  have lag := ctrlQuiet_predict quiet features action
  have gamma : (criterion.config .control).rule.gamma.Finite := by cases criterion <;> decide
  rw [one_add_sub_zeros (finite_mul_zero gamma lag) quiet.vOld, creditStep_row, credit_state,
    quiet.restart]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have moved := first_loop_slots
    (fun idx words => SlotQuiet criterion words ∧
      words.z = (slotOf (controller.learners.get row).state idx).z)
    (fun idx words => numerical32 words.weight =
      numerical32 (slotOf (controller.learners.get row).state idx).z)
    (fun idx words => numerical32 words.weight =
      numerical32 (slotOf (controller.learners.get row).state idx).z)
    Binary32.one controller.vDelta (decayOf criterion)
    (StepSizeRails.ofConfig (criterion.config .control)) ?_
    (controller.learners.get row).state (quiet.rows row).rails (row_unique controller row)
    (fun idx _ => ⟨(quiet.rows row).slots idx, rfl⟩)
    (fun idx absent => by
      rw [zero_reads ((quiet.rows row).slots idx).weight, slotOf_z,
        registers_zero_trace _ idx (row_supported controller row idx absent), zero_value])
  · have weight : numerical32 (slotOf ((controller.learners.get row).state.learnFirstLoop
          (criterion.config .control) Binary32.one controller.vDelta (decayOf criterion))
        slot).weight = numerical32 (slotOf (controller.learners.get row).state slot).z := by
      by_cases member : slot ∈ ((controller.learners.get row).state.learnFirstLoop
          (criterion.config .control) Binary32.one controller.vDelta
          (decayOf criterion)).transient.eligible
      · exact moved.2.2.1 slot member
      · exact moved.2.2.2 slot member
    split
    · rw [second_loop_weights]
      exact weight
    · exact weight
  · intro current idx _ pre
    obtain ⟨words, same⟩ := pre
    have zs : Small (slotOf current idx).z :=
      small_between words.zFinite small_zero (small_bound criterion)
        (by rw [zero_value]; exact words.zLow) words.zHigh
    have written : numerical32 (slotOf (current.firstLoopElement idx Binary32.one
        controller.vDelta (decayOf criterion)).1 idx).weight =
        numerical32 (slotOf (controller.learners.get row).state idx).z := by
      rw [first_element_weight, reward_weight_reads (criterion.config .control).rule rfl
        words.weight zs words.zHigh words.zLow words.zDelta quiet.vDelta, same]
    refine ⟨fun _ => ?_, fun _ => written⟩
    have knowledge := clear_feature_knowledge
      (current.firstLoopElement idx Binary32.one controller.vDelta (decayOf criterion)).1 idx idx
    rw [slotOf_weight, knowledge.1, ← slotOf_weight]
    exact written

def traceTotal {cfg : Acorn.Config} (controller : Controller cfg dimension actions)
    (features : ActiveSet dimension) (row : Fin actions) : Binary32 :=
  Binary32.sumFrom .zero (features.indices.map fun slot =>
    ((controller.learners.get row).state.transient.z.get slot).value)

theorem traces_sum_small {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (row : Fin actions)
    (slots : List (FeatIdx dimension)) (fits : slots.length ≤ 1999) :
    Small (Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)) ∧
      0 ≤ numerical32 (Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)) ∧
      numerical32 (Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)) ≤
        numerical32 (repeatSum (traceBound criterion) slots.length) := by
  have words := (quiet.rows row).slots
  have totalSmall : ∀ k ≤ 1999, Small (repeatSum (traceBound criterion) k) := fun k bound =>
    (repeatSum_total criterion k bound).1
  have total := sumFrom_le_repeat (traceBound criterion) (small_bound criterion)
    (slots.map fun slot => ((controller.learners.get row).state.transient.z.get slot).value)
    .zero 0
    (fun k bound => totalSmall k (by simp only [List.length_map] at bound; omega)) small_zero
    (le_of_eq zero_value.symm) (le_of_eq (by rw [repeatSum_zero]))
    (fun term member => by
      obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
      exact ⟨small_between (words slot).zFinite small_zero (small_bound criterion)
        (by rw [zero_value]; exact (words slot).zLow) (words slot).zHigh,
        (words slot).zLow, (words slot).zHigh⟩)
  simpa only [List.length_map, Nat.zero_add] using total

theorem reward_values {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action : Action actions) (next : ActiveSet dimension) (fits : next.indices.length ≤ 1999)
    (row : Fin actions) :
    numerical32 (((controller.step features action .one).1.predictAll next).get row) =
      numerical32 (traceTotal controller next row) := by
  rw [Controller.predictAll_def, get_map_vec, NumericState.linearPrediction_eq_sumFrom]
  unfold traceTotal
  have bounded : ∀ slots : List (FeatIdx dimension), slots.length ≤ next.indices.length →
      numerical32 (Binary32.sumFrom .zero (slots.map fun slot =>
        ((((controller.step features action .one).1.learners.get row).state.weights.get
          slot).value))) =
      numerical32 (Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)) := by
    intro slots
    induction slots using List.reverseRecOn with
    | nil => intro _; rfl
    | append_singleton slots slot ih =>
      intro short
      rw [List.length_append, List.length_singleton] at short
      have previous := ih (by omega)
      have leftFinite := (CurrentPrediction.legal_weight_sum_bound
        (criterion.config .control).rule (slots.map fun slot =>
          ((controller.step features action .one).1.learners.get row).state.weights.get slot)).1
      rw [List.map_map] at leftFinite
      have rightFinite := (traces_sum_small quiet row slots (by omega)).1.1
      have termFinite := (CurrentPrediction.weight_numerical_bound
        (criterion.config .control).rule
        (((controller.step features action .one).1.learners.get row).state.weights.get slot)).1
      have traceFinite := ((quiet.rows row).slots slot).zFinite
      have reads := reward_writes_traces quiet features action row slot
      simp only [List.map_append, List.map_cons, List.map_nil, Binary32.sumFrom_append]
      exact add_same_values _ _ _ _ leftFinite rightFinite termFinite traceFinite previous reads
  exact bounded next.indices le_rfl

theorem trace_le_total {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (row : Fin actions)
    (features : ActiveSet dimension) (fits : features.indices.length ≤ 1999)
    (slot : FeatIdx dimension) (held : slot ∈ features.indices) :
    numerical32 (slotOf (controller.learners.get row).state slot).z ≤
      numerical32 (traceTotal controller features row) := by
  unfold traceTotal
  have words := (quiet.rows row).slots
  have zSmall : ∀ other, Small (slotOf (controller.learners.get row).state other).z :=
    fun other => small_between (words other).zFinite small_zero (small_bound criterion)
      (by rw [zero_value]; exact (words other).zLow) (words other).zHigh
  have bounded : ∀ slots : List (FeatIdx dimension), slots.length ≤ features.indices.length →
      slot ∈ slots →
      numerical32 (slotOf (controller.learners.get row).state slot).z ≤
        numerical32 (Binary32.sumFrom .zero (slots.map fun other =>
          ((controller.learners.get row).state.transient.z.get other).value)) := by
    intro slots
    induction slots using List.reverseRecOn with
    | nil => intro _ member; exact absurd member List.not_mem_nil
    | append_singleton slots last ih =>
      intro short member
      rw [List.length_append, List.length_singleton] at short
      have before := traces_sum_small quiet row slots (by omega)
      simp only [List.map_append, List.map_cons, List.map_nil, Binary32.sumFrom_append]
      change _ ≤ numerical32 ((Binary32.sumFrom .zero (slots.map fun other =>
        ((controller.learners.get row).state.transient.z.get other).value)).add
          (slotOf (controller.learners.get row).state last).z)
      rcases List.mem_append.mp member with earlier | here
      · exact le_trans (ih (by omega) earlier)
          (le_add_right before.1 (zSmall last) (words last).zLow)
      · rw [List.mem_singleton] at here
        subst here
        exact le_add_left before.1 (zSmall slot) before.2.1
  exact bounded features.indices le_rfl held

theorem resting_total {cfg : Acorn.Config} (controller : Controller cfg dimension actions)
    (features : ActiveSet dimension) (row : Fin actions)
    (rest : ∀ slot ∈ features.indices,
      ((controller.learners.get row).state.transient.z.get slot).value.isZero = true) :
    (traceTotal controller features row).isZero = true := by
  unfold traceTotal
  rw [Binary32.sumFrom_def]
  apply zeroWord_foldlAdd _ _ (by decide)
  intro value member
  obtain ⟨slot, held, rfl⟩ := List.mem_map.mp member
  exact rest slot held

theorem unlaid_total {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (row : Fin actions)
    (unlaid : ∀ slot ∈ features.indices, notLaid history row slot (creditReach criterion)) :
    (traceTotal controller features row).isZero = true := by
  apply resting_total
  intro slot held
  have dormant := ctrlQuiet_dormant quiet row slot (unlaid slot held)
  rw [registers_zero_trace _ slot (row_supported controller row slot dormant.1)]
  decide

end Controller

section Policy

variable {criterion : Criterion} {dimension : Dimension} {count : Word.Count}

def tracePolicy {cfg : Acorn.Config} (controller : Controller cfg dimension count.word.toNat)
    (features : ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) : PolicySnapshot count :=
  ⟨Vector.ofFn fun row => traceTotal controller features row, epsilon⟩

theorem tracePolicy_value {cfg : Acorn.Config}
    (controller : Controller cfg dimension count.word.toNat) (features : ActiveSet dimension)
    (epsilon : SwiftTd.ExploreRate) (row : Action count.word.toNat) :
    (tracePolicy controller features epsilon).values.get row =
      traceTotal controller features row := by
  change (Vector.ofFn fun row => traceTotal controller features row).get row = _
  rw [vec_get, Vector.getElem_ofFn]

theorem reward_candidates {history : List (Laid dimension count.word.toNat)}
    {controller : Controller (criterion.config .control) dimension count.word.toNat}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action : Action count.word.toNat) (next : ActiveSet dimension)
    (fits : next.indices.length ≤ 1999) (epsilon : SwiftTd.ExploreRate) :
    ((controller.step features action .one).1.snapshot next epsilon).candidates =
      (tracePolicy controller next epsilon).candidates := by
  apply candidates_related
  intro row
  rw [Controller.snapshot_def, tracePolicy_value]
  dsimp only
  have lf := prediction_finite (controller.step features action .one).1 next row
  have rf := (traces_sum_small quiet row next.indices fits).1.1
  have same := reward_values quiet features action next fits row
  exact ⟨lf, rf, le_antisymm ((numerical32_order _ _ lf rf).mp same.le)
    ((numerical32_order _ _ rf lf).mp same.ge)⟩

end Policy

section Run

open AcornVerif.CurrentFirstCredit AcornVerif.CurrentExplorer AcornVerif.CurrentGridWorld

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

theorem first_reward_weights (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid < config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start paid).reward = .one)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (row : Action interface.actions.word.toNat) (slot : FeatIdx dimension) :
    numerical32 (((controlOf (Kernel.memoryAt world (executedAgent agent) start
        (paid + 1))).learners.get row).state.weights.get slot).value =
      numerical32 (((controlOf (Kernel.memoryAt world (executedAgent agent) start
        paid)).learners.get row).state.transient.z.get slot).value := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent history quiet ctrl world start
    paid (by omega) silent fits
  rw [loop_paid primitive perStep agent world start paid young pays]
  exact reward_writes_traces ctrlPaid _ _ row slot

theorem first_choice (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid < config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start paid).reward = .one)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (paid + 1)).features.indices.length ≤ 1999) :
    Kernel.actionAt world (executedAgent agent) start (paid + 1) =
      (((explorerOf agent.control).after (paid + 1)).stepOver
        (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
          (laidAt agent world start (paid + 1)).features declaredRate)).1 := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent history quiet ctrl world start
    paid (by omega) silent fits
  obtain ⟨rest, tracked, -⟩ := quiet_actions primitive declared agent quiet world start paid
    (fun earlier before => by rw [silent earlier before]; decide)
  have stepped := act_explores (Kernel.memoryAt world (executedAgent agent) start paid)
    primitive declared rest.control (Kernel.perceptAt world (executedAgent agent) start paid)
  have explorer : explorerOf (Kernel.memoryAt world (executedAgent agent) start
      (paid + 1)).control = (explorerOf agent.control).after (paid + 1) := by
    change explorerOf ((Kernel.memoryAt world (executedAgent agent) start paid).act
      (Kernel.perceptAt world (executedAgent agent) start paid)).1.control = _
    rw [stepped.2, tracked]
    rfl
  have drawn := (act_draws (Kernel.memoryAt world (executedAgent agent) start (paid + 1))
    primitive declared (Kernel.perceptAt world (executedAgent agent) start (paid + 1))).1
  have candidates := reward_candidates ctrlPaid (laidAt agent world start paid).features
    (laidAt agent world start paid).row (laidAt agent world start (paid + 1)).features
    fitsNext declaredRate
  rw [← loop_paid primitive perStep agent world start paid young pays] at candidates
  change ((Kernel.memoryAt world (executedAgent agent) start (paid + 1)).act
    (Kernel.perceptAt world (executedAgent agent) start (paid + 1))).2.action = _
  rw [drawn, explorer]
  exact congrArg Prod.fst (Explorer.stepOver_congr _ _ _ rfl candidates)

theorem first_choice_greedy (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid < config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start paid).reward = .one)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (paid + 1)).features.indices.length ≤ 1999)
    (unserved : ((explorerOf agent.control).after (paid + 1)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (paid + 1)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (paid + 1) ∈
      (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
        (laidAt agent world start (paid + 1)).features declaredRate).candidates := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent history quiet ctrl world start
    paid (by omega) silent fits
  have chosen := first_choice primitive perStep declared agent history quiet ctrl world start
    paid young silent pays fits fitsNext
  have greedy := Explorer.stepOver_greedy ((explorerOf agent.control).after (paid + 1))
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
      (laidAt agent world start (paid + 1)).features declaredRate) unserved calm
  have member := greedy_candidate
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
      (laidAt agent world start (paid + 1)).features declaredRate)
    (fun action => by
      rw [tracePolicy_value]
      exact (traces_sum_small ctrlPaid action _ fitsNext).1.1)
    (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (paid + 1)).rng).2
  rw [chosen, greedy]
  exact member

theorem unlaid_window (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time reach : ℕ)
    (other : Action interface.actions.word.toNat) (slot : FeatIdx dimension)
    (apart : ∀ earlier, earlier < time → time ≤ earlier + reach →
      Kernel.actionAt world (executedAgent agent) start earlier = other →
      slot ∉ (laidAt agent world start earlier).features.indices) :
    notLaid ((List.range' 0 time).map (laidAt agent world start)) other slot reach := by
  intro step member lays
  rw [List.length_map, List.length_range'] at member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  rw [List.length_drop, List.length_map, List.length_range'] at bound
  rw [List.getElem_drop, List.getElem_map, List.getElem_range'] at same
  have position : 0 + 1 * (time - reach + index) = time - reach + index := by omega
  rw [position] at same
  subst same
  exact apart (time - reach + index) (by omega) (by omega)
    ((laidAt_row agent world start (time - reach + index)).symm.trans lays.1) lays.2

theorem shared_total (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
    (fitsLaid : (laidAt agent world start laid).features.indices.length ≤ 1900)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (slot : FeatIdx dimension)
    (heldLaid : slot ∈ (laidAt agent world start laid).features.indices)
    (heldFrame : slot ∈ frame.indices) :
    numerical32 (lowChain .discounted 8) ≤
      numerical32 (traceTotal (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
        frame (laidAt agent world start laid).row) := by
  obtain ⟨gap, rfl⟩ : ∃ gap, paid = laid + 1 + gap := ⟨paid - 1 - laid, by omega⟩
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent history quiet ctrl world start
    (laid + 1 + gap) young silent fits
  have recent := loop_recent primitive perStep agent history quiet ctrl world start laid gap
    (by omega) young silent fits fitsLaid slot heldLaid
  have far := lowChain_antitone .discounted gap (8 - gap)
  rw [show gap + (8 - gap) = 8 by omega] at far
  exact le_trans far (le_trans recent.2
    (trace_le_total ctrlPaid _ frame fitsFrame slot heldFrame))

theorem shared_value (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (history : List (Laid dimension interface.actions.word.toNat))
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) history)
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid < config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start paid).reward = .one)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
    (fitsLaid : (laidAt agent world start laid).features.indices.length ≤ 1900)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (slot : FeatIdx dimension)
    (heldLaid : slot ∈ (laidAt agent world start laid).features.indices)
    (heldFrame : slot ∈ frame.indices) :
    numerical32 (lowChain .discounted 8) ≤
      numerical32 (((controlOf (Kernel.memoryAt world (executedAgent agent) start
        (paid + 1))).predictAll frame).get (laidAt agent world start laid).row) := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent history quiet ctrl world start paid
    (by omega) silent fits
  rw [loop_paid primitive perStep agent world start paid young pays,
    reward_values ctrlPaid _ _ frame fitsFrame]
  exact shared_total primitive perStep agent history quiet ctrl world start paid (by omega)
    silent fits laid before near fitsLaid frame fitsFrame slot heldLaid heldFrame

theorem unlaid_excluded (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
    (fitsLaid : (laidAt agent world start laid).features.indices.length ≤ 1900)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (slot : FeatIdx dimension)
    (heldLaid : slot ∈ (laidAt agent world start laid).features.indices)
    (heldFrame : slot ∈ frame.indices) (other : Action interface.actions.word.toNat)
    (apart : ∀ held ∈ frame.indices, ∀ earlier, earlier < paid →
      paid ≤ earlier + creditReach .discounted →
      Kernel.actionAt world (executedAgent agent) start earlier = other →
      held ∉ (laidAt agent world start earlier).features.indices)
    (epsilon : SwiftTd.ExploreRate) :
    other ∉ (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
      frame epsilon).candidates := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start paid
    young silent fits
  rw [List.nil_append] at ctrlPaid
  have leads := shared_total primitive perStep agent [] quiet ctrl world start paid young silent
    fits laid before near fitsLaid frame fitsFrame slot heldLaid heldFrame
  refine zero_excluded _ (fun action => ?_) (laidAt agent world start laid).row other
    (lowChain .discounted 8) (lowChain_facts .discounted 8).1 (low_clears_tie .discounted) ?_ ?_
  · rw [tracePolicy_value]
    exact (traces_sum_small ctrlPaid action frame.indices fitsFrame).1
  · rw [tracePolicy_value]
    exact leads
  · rw [tracePolicy_value]
    exact unlaid_total ctrlPaid frame other fun held inside =>
      unlaid_window agent world start paid _ other held (apart held inside)

theorem sole_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
    (fitsLaid : (laidAt agent world start laid).features.indices.length ≤ 1900)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (slot : FeatIdx dimension)
    (heldLaid : slot ∈ (laidAt agent world start laid).features.indices)
    (heldFrame : slot ∈ frame.indices) (only : Action interface.actions.word.toNat)
    (taken : ∀ held ∈ frame.indices, ∀ earlier, earlier < paid →
      paid ≤ earlier + creditReach .discounted →
      held ∈ (laidAt agent world start earlier).features.indices →
      Kernel.actionAt world (executedAgent agent) start earlier = only)
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid)) frame
        epsilon).candidates = [only] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
        frame epsilon).greedy rng).1 = only := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start paid
    young silent fits
  rw [List.nil_append] at ctrlPaid
  have leads := shared_total primitive perStep agent [] quiet ctrl world start paid young silent
    fits laid before near fitsLaid frame fitsFrame slot heldLaid heldFrame
  have row : (laidAt agent world start laid).row = only :=
    (laidAt_row agent world start laid).trans
      (taken slot heldFrame laid before (by change paid ≤ laid + 119; omega) heldLaid)
  rw [row] at leads
  refine lone_candidate _ only ?_ (lowChain .discounted 8) (lowChain_facts .discounted 8).1
    (low_clears_tie .discounted) ?_ fun action other => ?_
  · rw [tracePolicy_value]
    exact (traces_sum_small ctrlPaid only frame.indices fitsFrame).1
  · rw [tracePolicy_value]
    exact leads
  · rw [tracePolicy_value]
    exact unlaid_total ctrlPaid frame action fun held inside =>
      unlaid_window agent world start paid _ action held fun earlier early reach same member =>
        other (same.symm.trans (taken held inside earlier early reach member))

end Run

end AcornVerif.CurrentFirstChoice
