/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentExplorer
import AcornVerif.CurrentFirstCredit

/-!
# The first decision after a first reward

Before its first reward the executed agent of a profile with no hierarchy takes the actions of an
explorer that reads no percept (`AcornVerif.CurrentExplorer.cold_actions`). This module says what
its next decision reads, right after the step that learns a first reward of one: for such a
profile under per-step credit, the declared rate and the discounted criterion, at the default
step order, before a unit of the feature bank matures.

**What the reward writes.** Before a first reward every primitive weight is a zero word, the
shared lags are zero words, and each row holds a trace on the slots it laid
(`AcornVerif.CurrentCreditHorizon.CtrlQuiet`). The step that learns a reward of one then has
error one, and its first loop adds to each weight the error times the trace. So each row's weight
on each slot reads the trace the row held there before the step (`reward_writes_traces`, and
`first_reward_weights` of a kernel run). The frame and the action of the reward step do not
enter: its second loop writes no weight.

**The values.** After that step, the value of each action at a frame of at most 1999 slots reads
its row's trace total on the frame (`traceTotal`, `reward_values`): the ordered sum, over the
frame's slots, of the traces the row held when the reward came, which is the word the second loop
reads when a row lays a frame. The policy the controller freezes at the frame has the
near-maximum candidates of the policy whose values are those totals (`tracePolicy`,
`reward_candidates`).

**The decision.** In a kernel run in which every reward word before a time is the zero word and
that time's is the word one, the action at the next time is one decision of primitive control
(`AcornVerif.CurrentExplorer.Explorer.stepOver`), from the explorer's state after that many
decisions, over the trace policy at the frame the decision reads (`first_choice`). A committed
run with a step left serves its action; otherwise the decision is one persistent draw from the
trace policy. Outside a run, when the generator begins none, the action is a near-maximum
candidate of the trace policy (`first_choice_greedy`).

**What the trace totals say.** A step lays a trace on the slots of its frame, in the row of its
action, and every later step decays it, whatever the rewards. So a total records which actions the
agent took before the reward, on frames that share slots with the frame the decision reads, and
how long before.

- Take a frame, and a row whose action no step among the last
  `AcornVerif.CurrentCreditHorizon.creditReach` before a time took on a frame holding a slot of
  that frame; a row whose action was taken on none of those steps is one. The row laid no slot of
  the frame on those steps (`unlaid_window`), and its total on the frame is a zero word
  (`unlaid_total`).
- A row that took a step at most nine steps before the reward, on a frame of at most 1900 slots,
  has, on every frame that shares a slot with that one, a total of at least the least laid trace
  decayed eight times (`shared_total`). That word exceeds the tie window by a positive word
  (`low_clears_tie`). So right after the reward step the value of that row's action at such a
  frame is above the tie window (`shared_value`).
- So at a frame that shares such a slot, an action that the last `creditReach` steps before the
  reward took on no frame holding a slot of this one is no candidate (`unlaid_excluded`, through
  `zero_excluded`). Where every one of those steps whose frame holds a slot of this one took one
  action, that action is the one candidate, and the greedy draw returns it whatever the generator
  (`sole_candidate`, through `lone_candidate`).

So the first greedy choice after a first reward follows what the agent did on the frames that
share slots with the present one: an action it took on none of them is excluded, and where it
took one action on all of them, that action is chosen. Where it took several, the choice is the
comparison of their rows' totals. In a world all of whose frames share a slot, every action taken
on the last `creditReach` steps before the reward can hold a total on every frame.

Two frames whose percepts carry a common word share a slot
(`AcornVerif.CurrentFrameSize.shared_slot`).

What this does not say.

- Which action is the candidate when the steps before the reward took several. That is the
  comparison of their rows' trace totals on the frame, and a total depends on how many slots the
  frame shares with each earlier frame. No theorem here evaluates a total.
- Anything of a later decision. After the first reward the weights are not zero words, so the
  errors of the next steps are not, and each moves every weight whose slot holds a trace.
- That the action leads back to where the reward was earned. The traces the reward turns into
  weights were laid before it, and no trace reads a reward.
- A run past the first maturing unit, when a replaced unit's slot is retired; the differential
  criterion; a profile with a hierarchy; another rate policy or step order.

Trust. The statements are about executed binary32 words. Lean's kernel, its model of binary32
arithmetic and the agreement of the native operations with that model on finite operands remain
trusted, as for every proof of executed words in this library.
-/

namespace AcornVerif.CurrentFirstChoice
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds
open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward AcornVerif.CurrentFeatureConsumers
open AcornVerif.CurrentControl AcornVerif.CurrentCreditHorizon
open SwiftTd (ActiveSet)

/-! ## What a first reward of one writes -/

section Controller

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

/-- **A first reward of one writes every trace into its weight.** From a quiet controller, after a
step at reward one, every row's weight on every slot reads the trace the row held there before the
step, whatever the frame and the action of the reward step. A slot outside a row's eligible list
holds a zero weight and a zero trace before the step, and keeps both. -/
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

/-- The total of the traces a row holds on the slots of a frame, in the frame's order: the word
the second loop reads when the row lays the frame. -/
def traceTotal {cfg : Acorn.Config} (controller : Controller cfg dimension actions)
    (features : ActiveSet dimension) (row : Fin actions) : Binary32 :=
  Binary32.sumFrom .zero (features.indices.map fun slot =>
    ((controller.learners.get row).state.transient.z.get slot).value)

/-- On at most 1999 slots, the ordered sum of a quiet row's traces is small, nonnegative and at
most the ordered sum of as many trace bounds. -/
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
  have partials := repeatSum_bound (traceBound criterion) (totalBound criterion) 1999
    (total_check criterion) (by cases criterion <;> decide)
  have totalSmall : ∀ k ≤ 1999, Small (repeatSum (traceBound criterion) k) := fun k bound =>
    small_of_key (partials k bound).1 (le_trans (by decide) (partials k bound).2.1)
      (le_trans (partials k bound).2.2 (by cases criterion <;> decide))
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

/-- **After a first reward of one, a row's value at a frame is its trace total there.** From a
quiet controller, after a step at reward one, the prediction of every row at every frame of at
most 1999 slots reads the total of the traces the row held on that frame's slots before the
step. Each weight reads its trace (`reward_writes_traces`), and the two ordered sums add words of
one value to words of one value. -/
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

/-- A slot's trace is at most the row's trace total on a frame of at most 1999 slots that holds
the slot: the other traces are nonnegative. -/
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

/-- A row that holds zero words for its traces on a frame's slots has a zero word for its trace
total there. -/
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

/-- **A row that has not laid a frame's slots for the credit horizon holds no trace there.** On a
quiet controller, if a row laid no slot of a frame on the last `creditReach criterion` steps, its
trace total on the frame is a zero word: each of those slots is outside the row's eligible list
(`AcornVerif.CurrentCreditHorizon.ctrlQuiet_dormant`), where every register is positive zero. -/
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

/-! ## The greedy candidates -/

section Policy

variable {criterion : Criterion} {dimension : Dimension} {count : Word.Count}

/-- The frozen policy whose value for each action is its row's trace total on a frame. -/
def tracePolicy {cfg : Acorn.Config} (controller : Controller cfg dimension count.word.toNat)
    (features : ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) : PolicySnapshot count :=
  ⟨Vector.ofFn fun row => traceTotal controller features row, epsilon⟩

/-- The value of an action under the trace policy is its row's trace total. -/
theorem tracePolicy_value {cfg : Acorn.Config}
    (controller : Controller cfg dimension count.word.toNat) (features : ActiveSet dimension)
    (epsilon : SwiftTd.ExploreRate) (row : Action count.word.toNat) :
    (tracePolicy controller features epsilon).values.get row =
      traceTotal controller features row := by
  change (Vector.ofFn fun row => traceTotal controller features row).get row = _
  rw [vec_get, Vector.getElem_ofFn]

/-- **The greedy candidates after a first reward of one are those of the trace totals.** From a
quiet controller, after a step at reward one, the policy frozen at any frame of at most 1999 slots
has the near-maximum candidates of the policy whose values are the totals of the traces each row
held on that frame's slots before the step. -/
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

/-- The tie window is small. -/
theorem small_tie : Small tieWindow := small_named (by decide)

/-- **A zero value is no candidate once another value clears the tie window.** In a policy of
small values, if one action's value reads at least a small word whose difference from the tie
window is positive, an action whose value is a zero word is not a near-maximum candidate. -/
theorem zero_excluded (snapshot : PolicySnapshot count)
    (small : ∀ action, Small (snapshot.values.get action))
    (leader other : Action count.word.toNat) (lower : Binary32) (lowerSmall : Small lower)
    (gap : 0 < numerical32 (lower.sub tieWindow))
    (leads : numerical32 lower ≤ numerical32 (snapshot.values.get leader))
    (zero : (snapshot.values.get other).isZero = true) :
    other ∉ snapshot.candidates := by
  obtain ⟨⟨top, best⟩, above⟩ := best_bounds snapshot fun action => (small action).1
  have bestSmall : Small snapshot.best := best ▸ small top
  have leadsBest : numerical32 lower ≤ numerical32 snapshot.best :=
    le_trans leads (num_le (small leader).1 bestSmall.1 (above leader))
  have threshold := sub_mono lowerSmall small_tie bestSmall small_tie leadsBest le_rfl
  have strict := (numerical32_strict_order _ _ (by decide : Binary32.zero.Finite)
    (sub_small bestSmall small_tie).1).mp (by rw [zero_value]; exact lt_of_lt_of_le gap threshold)
  rw [PolicySnapshot.candidates_def]
  dsimp only
  intro member
  have kept := of_decide_eq_true (List.mem_filter.mp member).2
  have order := kept.2.2
  rw [zero_key _ zero] at order
  have zeroKey : Binary32.zero.key = 0 := by decide
  omega

/-- **One value above the tie window over zero values is the one candidate.** In a policy whose
other values are zero words, an action whose small value reads at least a small word whose
difference from the tie window is positive is the one near-maximum candidate, and the greedy draw
returns it whatever the generator. -/
theorem lone_candidate (snapshot : PolicySnapshot count) (leader : Action count.word.toNat)
    (leaderSmall : Small (snapshot.values.get leader)) (lower : Binary32)
    (lowerSmall : Small lower) (gap : 0 < numerical32 (lower.sub tieWindow))
    (leads : numerical32 lower ≤ numerical32 (snapshot.values.get leader))
    (zeros : ∀ action, action ≠ leader → (snapshot.values.get action).isZero = true) :
    snapshot.candidates = [leader] ∧ ∀ rng, (snapshot.greedy rng).1 = leader := by
  apply candidates_of_gap snapshot leader leaderSmall.1
  intro action other
  have threshold := sub_mono lowerSmall small_tie leaderSmall small_tie leads le_rfl
  have finite := (sub_small leaderSmall small_tie).1
  have strict := (numerical32_strict_order _ _ (by decide : Binary32.zero.Finite) finite).mp
    (by rw [zero_value]; exact lt_of_lt_of_le gap threshold)
  have zeroKey : Binary32.zero.key = 0 := by decide
  refine ⟨finite_not_isNaN (CurrentControl.zero_finite _ (zeros action other)),
    finite_not_isNaN finite, ?_⟩
  rw [zero_key _ (zeros action other)]
  omega

/-- The least laid trace decayed eight times exceeds the tie window by a positive word. -/
theorem low_clears_tie (criterion : Criterion) :
    0 < numerical32 ((lowChain criterion 8).sub tieWindow) := by
  have key : Binary32.zero.key < ((lowChain criterion 8).sub tieWindow).key := by
    cases criterion <;> decide +kernel
  rw [← zero_value]
  exact (numerical32_strict_order _ _ (by decide)
    (sub_small (lowChain_facts criterion 8).1 small_tie).1).mpr key

end Policy

/-! ## A kernel run -/

section Run

open AcornVerif.CurrentFirstCredit AcornVerif.CurrentExplorer AcornVerif.CurrentGridWorld

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- **In a kernel run, a first reward of one writes every trace into its weight.** For a profile
with no hierarchy under per-step credit and the discounted criterion, from an agent state whose
learners are at rest and whose primitive controller is quiet: when every reward word before a
time is the zero word and that time's is the word one, over frames of at most 1999 slots and
before a unit of the feature bank matures, then right after the step of that time every row's
weight on every slot reads the trace the row held there when that step began. -/
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

/-- **The first decision after a first reward.** For a profile with no hierarchy under per-step
credit, the declared rate and the discounted criterion, at the default step order, from an agent
state whose learners are at rest and whose primitive controller is quiet: in a kernel run in
which every reward word before a time is the zero word and that time's is the word one, all
before a unit of the feature bank matures and over frames of at most 1999 slots, the action at
the next time is one decision of primitive control, from the explorer's state after that many
decisions, over the policy whose value for each action is the total of the traces its row held,
when the step that learns the reward began, on the slots of the frame the decision reads. -/
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
    (fits : ∀ time, time ≤ paid + 1 →
      (laidAt agent world start time).features.indices.length ≤ 1999) :
    Kernel.actionAt world (executedAgent agent) start (paid + 1) =
      (((explorerOf agent.control).after (paid + 1)).stepOver
        (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
          (laidAt agent world start (paid + 1)).features declaredRate)).1 := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent history quiet ctrl world start
    paid (by omega) silent (fun earlier before => fits earlier (by omega))
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
    (fits (paid + 1) le_rfl) declaredRate
  rw [← loop_paid primitive perStep agent world start paid young pays] at candidates
  change ((Kernel.memoryAt world (executedAgent agent) start (paid + 1)).act
    (Kernel.perceptAt world (executedAgent agent) start (paid + 1))).2.action = _
  rw [drawn, explorer]
  exact congrArg Prod.fst (Explorer.stepOver_congr _ _ _ rfl candidates)

/-- **Outside a run, the first decision after a first reward takes a candidate of the trace
totals.** Under the hypotheses of `first_choice`, when the explorer's state after that many
decisions holds no committed run with a step left and its generator begins none at the declared
rate, the action at the next time is a near-maximum candidate of the trace policy. -/
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
    (fits : ∀ time, time ≤ paid + 1 →
      (laidAt agent world start time).features.indices.length ≤ 1999)
    (unserved : ((explorerOf agent.control).after (paid + 1)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (paid + 1)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (paid + 1) ∈
      (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
        (laidAt agent world start (paid + 1)).features declaredRate).candidates := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent history quiet ctrl world start
    paid (by omega) silent (fun earlier before => fits earlier (by omega))
  have chosen := first_choice primitive perStep declared agent history quiet ctrl world start
    paid young silent pays fits
  have greedy := Explorer.stepOver_greedy ((explorerOf agent.control).after (paid + 1))
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
      (laidAt agent world start (paid + 1)).features declaredRate) unserved calm
  have member := greedy_candidate
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
      (laidAt agent world start (paid + 1)).features declaredRate)
    (fun action => by
      rw [tracePolicy_value]
      exact (traces_sum_small ctrlPaid action _ (fits (paid + 1) le_rfl)).1.1)
    (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (paid + 1)).rng).2
  rw [chosen, greedy]
  exact member

/-! ## What the trace totals say -/

/-- An item of a mapped range after its first `skip` items is the image of a time from `skip`
on. -/
theorem mem_drop_range {α : Type} (f : ℕ → α) (count skip : ℕ) (item : α)
    (member : item ∈ ((List.range' 0 count).map f).drop skip) :
    ∃ time, skip ≤ time ∧ time < count ∧ item = f time := by
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  rw [List.length_drop, List.length_map, List.length_range'] at bound
  refine ⟨skip + index, by omega, by omega, ?_⟩
  rw [← same, List.getElem_drop, List.getElem_map, List.getElem_range']
  simp

/-- In a kernel run, a row laid a slot on none of the last `reach` steps before a time when no
step among them both took the row's action and encoded a frame that holds the slot. -/
theorem unlaid_window (agent : Agent interface profile config criterion dimension planning)
    (world : Kernel.World interface) (start : world.State) (time reach : ℕ)
    (other : Action interface.actions.word.toNat) (slot : FeatIdx dimension)
    (apart : ∀ earlier, earlier < time → time ≤ earlier + reach →
      Kernel.actionAt world (executedAgent agent) start earlier = other →
      slot ∉ (laidAt agent world start earlier).features.indices) :
    notLaid ([] ++ (List.range' 0 time).map (laidAt agent world start)) other slot reach := by
  intro step member lays
  rw [List.nil_append, List.length_map, List.length_range'] at member
  obtain ⟨earlier, low, high, rfl⟩ := mem_drop_range _ _ _ _ member
  exact apart earlier high (by omega)
    ((laidAt_row agent world start earlier).symm.trans lays.1) lays.2

/-- **A frame that shares a recently laid slot gives its row a total that clears the tie
window.** For a profile with no hierarchy under per-step credit and the discounted criterion,
from an agent state whose learners are at rest and whose primitive controller is quiet against
the empty history: in a kernel run in which every reward word before a time is the zero word,
over frames of at most 1900 slots and before a unit of the feature bank matures, let a step at
most nine steps before that time have laid a slot that a frame of at most 1999 slots holds. Then
at that time the row of that step's action has, on that frame, a trace total of at least the
least laid trace decayed eight times. -/
theorem shared_total (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1900)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (slot : FeatIdx dimension)
    (heldLaid : slot ∈ (laidAt agent world start laid).features.indices)
    (heldFrame : slot ∈ frame.indices) :
    numerical32 (lowChain .discounted 8) ≤
      numerical32 (traceTotal (controlOf (Kernel.memoryAt world (executedAgent agent) start paid))
        frame (laidAt agent world start laid).row) := by
  obtain ⟨gap, rfl⟩ : ∃ gap, paid = laid + 1 + gap := ⟨paid - 1 - laid, by omega⟩
  have wide : ∀ earlier, earlier < laid + 1 + gap →
      (laidAt agent world start earlier).features.indices.length ≤ 1999 :=
    fun earlier early => Nat.le_trans (fits earlier early) (by decide)
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start
    (laid + 1 + gap) young silent wide
  have recent := loop_recent primitive perStep agent [] quiet ctrl world start laid gap
    (by omega) young silent wide (fits laid (by omega)) slot heldLaid
  have far := lowChain_antitone .discounted gap (8 - gap)
  rw [show gap + (8 - gap) = 8 by omega] at far
  exact le_trans far (le_trans recent.2
    (trace_le_total ctrlPaid _ frame fitsFrame slot heldFrame))

/-- **After the reward, the value of a recent action clears the tie window where its frame's
slots are.** Under the hypotheses of `shared_total`, when the percept of that time carries the
reward word one and the agent's clock is still below the tester's maturity threshold: right
after the step that learns the reward, the value of the action of a step at most nine steps
before, at a frame that shares a slot with the frame that step laid, reads at least the least
laid trace decayed eight times, which is above the tie window
(`AcornVerif.CurrentCreditHorizon.lowChain_above_tie`). -/
theorem shared_value (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid < config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start paid).reward = .one)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1900)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (slot : FeatIdx dimension)
    (heldLaid : slot ∈ (laidAt agent world start laid).features.indices)
    (heldFrame : slot ∈ frame.indices) :
    numerical32 (lowChain .discounted 8) ≤
      numerical32 (((controlOf (Kernel.memoryAt world (executedAgent agent) start
        (paid + 1))).predictAll frame).get (laidAt agent world start laid).row) := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start paid
    (by omega) silent (fun earlier early => Nat.le_trans (fits earlier early) (by decide))
  rw [loop_paid primitive perStep agent world start paid young pays,
    reward_values ctrlPaid _ _ frame fitsFrame]
  exact shared_total primitive perStep agent quiet ctrl world start paid (by omega) silent fits
    laid before near frame fitsFrame slot heldLaid heldFrame

/-- **An action not taken on the frame's slots for the credit horizon is no candidate.** Under
the hypotheses of `shared_total`, at a frame that shares a slot with a frame laid at most nine
steps before, take an action that no step among the last `creditReach` took on a frame holding a
slot of this one: an action taken on none of those steps is one. It is not a near-maximum
candidate of the trace policy at the frame, at any rate: its total is a zero word, and the total
of the row that laid the shared slot clears the tie window. -/
theorem unlaid_excluded (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1900)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
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
    young silent (fun earlier early => Nat.le_trans (fits earlier early) (by decide))
  have leads := shared_total primitive perStep agent quiet ctrl world start paid young silent
    fits laid before near frame fitsFrame slot heldLaid heldFrame
  refine zero_excluded _ (fun action => ?_) (laidAt agent world start laid).row other
    (lowChain .discounted 8) (lowChain_facts .discounted 8).1 (low_clears_tie .discounted) ?_ ?_
  · rw [tracePolicy_value]
    exact (traces_sum_small ctrlPaid action frame.indices fitsFrame).1
  · rw [tracePolicy_value]
    exact leads
  · rw [tracePolicy_value]
    exact unlaid_total ctrlPaid frame other fun held inside =>
      unlaid_window agent world start paid _ other held (apart held inside)

/-- **Where one action alone was taken on the frame's slots, it is the one candidate.** Under the
hypotheses of `shared_total`, at a frame that shares a slot with a frame laid at most nine steps
before, suppose that every step among the last `creditReach` whose frame holds a slot of this one
took one action. Then that action is the one near-maximum candidate of the trace policy at the
frame, at any rate, and the greedy draw returns it whatever the generator. -/
theorem sole_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (paid : ℕ)
    (young : agent.clock.toNat + paid ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1900)
    (laid : ℕ) (before : laid < paid) (near : paid ≤ laid + 9)
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
    young silent (fun earlier early => Nat.le_trans (fits earlier early) (by decide))
  have leads := shared_total primitive perStep agent quiet ctrl world start paid young silent
    fits laid before near frame fitsFrame slot heldLaid heldFrame
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
