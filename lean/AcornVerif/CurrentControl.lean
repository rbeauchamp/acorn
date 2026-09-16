/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.PredictionControl
import Acorn.Planning
import AcornVerif.CurrentFeatureConsumers
import AcornVerif.CurrentPrediction
import AcornVerif.CurrentRetirement

/-!
# Contracts of the executing prediction/control composition

These theorems reuse the actual numeric learner and its admitted schedule.
The action update is Javed & Sutton, *Swift-Sarsa*, arXiv:2507.19539v1 (2025),
Algorithm 1 / equation (4), with the PAR-2 meta-gradient adaptation owned by
`MetaGradient`. Each theorem identifies its machine-word or ideal-real domain.
-/
namespace AcornVerif.CurrentControl
open Acorn Acorn.Features AcornVerif.CurrentFeatureConsumers AcornVerif.CurrentLearner

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat}

/-- Every live controller row carries the actual learner's support, pruning
reference, unique-eligibility and readiness invariants. -/
theorem controller_schedule (controller : Controller config dimension actions)
    (action : Action actions) :
    ScheduleInv (controller.learners.get action).state
      (controller.learners.get action).phase :=
  managed_schedule (controller.learners.get action)

/-- Complete shared-error execution preserves stored weight/beta legality and
eligibility capacity, for arbitrary raw reward, bootstrap and decay words. -/
theorem values_step_legal (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action observed : Action actions) (reward bootstrap decay : Binary32)
    (index : FeatIdx dimension) :
    let next := controller.valuesStep features values action reward bootstrap decay
    let learner := next.learners.get observed
    config.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  dsimp only
  exact ⟨weight_legal _, (by exact Bounded32.legal _), managed_capacity _⟩

/-- The selected row executes first-loop credit then precisely one second loop. -/
theorem selected_row (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    ((controller.valuesStep features values action reward bootstrap decay).learners.get
      action).state =
      (((controller.learners.get action).credit
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld)
        controller.vDelta decay controller.restartPending).val.state.learnSecondLoop
          config features .zero).1 := by
  simp [Controller.valuesStep, Vector.get, Fin.cast]

/-- Every unselected row receives the same first-loop error, without a second loop. -/
theorem unselected_row (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action other : Action actions) (different : other ≠ action)
    (reward bootstrap decay : Binary32) :
    ((controller.valuesStep features values action reward bootstrap decay).learners.get
      other).state =
      ((controller.learners.get other).credit
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld)
        controller.vDelta decay controller.restartPending).val.state := by
  have indices : other.val ≠ action.val := fun h => different (Fin.ext h)
  simp [Controller.valuesStep, Vector.get, Fin.cast, Ne.symm indices]

/-- An empty worklist performs no numerical operation, for arbitrary stored
state and raw first-loop arguments. Rewrite this whole-state identity before
projecting dependent beta storage. -/
theorem first_loop_empty (state : NumericState config dimension)
    (empty : state.transient.eligible = #[]) (delta vd decay : Binary32) :
    state.learnFirstLoop config delta vd decay = state := by
  unfold NumericState.learnFirstLoop
  rw [empty, NumericState.learnFirstLoopGo]
  simp only [Array.size_empty, Nat.lt_irrefl, ↓reduceDIte]
  cases state with
  | mk rails weights beta transient =>
    cases transient
    simp_all

/-- Empty initial eligibility makes first-loop credit an identity, for every
error, lag, decay and restart flag. In particular, merely receiving the common
Sarsa error cannot expose a row that has never run the second loop. -/
theorem credit_initial (learner : Managed config dimension)
    (cold : learner.state = NumericState.initial config dimension)
    (delta vd decay : Binary32) (restart : Bool) :
    (learner.credit delta vd decay restart).val.state = NumericState.initial config dimension := by
  have first : learner.state.learnFirstLoop config delta vd decay =
      NumericState.initial config dimension := by
    rw [first_loop_empty _ (by rw [cold]; rfl), cold]
  cases restart with
  | false => exact first
  | true =>
    change (learner.state.learnFirstLoop config delta vd decay).clearTransient = _
    rw [first]
    rfl

/-- Until selection, a fresh action row remains exactly fresh under the actual
shared-error update, even if every other row is learning or restart is pending. -/
theorem unselected_initial (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action other : Action actions) (different : other ≠ action)
    (cold : (controller.learners.get other).state = NumericState.initial config dimension)
    (reward bootstrap decay : Binary32) :
    ((controller.valuesStep features values action reward bootstrap decay).learners.get
      other).state =
      NumericState.initial config dimension := by
  rw [unselected_row controller features values action other different]
  exact credit_initial _ cold _ _ _ _

/-- Terminal closeout clears all trajectory registers in every action row. -/
theorem terminal_clears (controller : Controller config dimension actions)
    (reward : Binary32)
    (action : Action actions) :
    ((controller.terminal reward).learners.get action).state.transient =
      TransientState.zero dimension := by
  simp [Controller.terminal, Controller.clear, Vector.get, Managed.apply, SwiftTd.Entry.apply,
    NumericState.clearTransient]

/-- Controller observations are finite because they sum the actual refined weights,
not because the output is clamped or a separately written prediction model is assumed. -/
theorem prediction_finite (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) :
    ((controller.predictAll features).get action).Finite := by
  have result := CurrentPrediction.legal_weight_sum_bound config.rule
    (features.indices.map fun idx => ((controller.learners.get action).state.weights.get idx))
  simpa [Controller.predictAll, Vector.get, NumericState.linearPrediction_eq_sumFrom, List.map_map,
    Fin.cast, Function.comp_def] using result.1

/-- An actual greedy draw returns a threshold candidate whenever one exists;
otherwise its exact raw-domain behavior is the first-action fallback. -/
theorem greedy_support {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    if snapshot.candidates = [] then (snapshot.greedy rng).1 = firstAction count
    else (snapshot.greedy rng).1 ∈ snapshot.candidates := by
  cases h : snapshot.candidates with
  | nil => simp [PolicySnapshot.greedy, h, reservoir]
  | cons action rest =>
    simpa [PolicySnapshot.greedy, h] using reservoir_nonempty action rest (firstAction count) rng

/-- Every finite sequence of actual local control transitions retains the receiver's
same configuration, legal knowledge and resource scheduling; no replay is stored. -/
theorem finite_prefix_schedule (initial : Controller config dimension actions)
    (inputs : List (SwiftTd.ActiveSet dimension × Action actions × Binary32))
    (action : Action actions) :
    let final := inputs.foldl
      (fun state input => (state.step input.1 input.2.1 input.2.2).1) initial
    ScheduleInv (final.learners.get action).state (final.learners.get action).phase := by
  exact controller_schedule _ action

/-- Every actual bank transition preserves the current learner's resource bound
at every heterogeneous reader, independently of its signal discount. -/
theorem demon_step_capacity {discounts : List Discount} (bank : DemonBank dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rewards : Cumulants discounts)
    (reader : PackedLearner dimension)
    (_member : reader ∈ (bank.step features rewards).bank.readers) :
    reader.2.state.eligibleCount ≤ dimension.capacity := managed_capacity reader.2

open AcornVerif.CurrentRetirement

/-- Zero numeric rows and shared Sarsa lags, with no condition on action
selection, exploration rates, restart flags, beta or other raw registers. -/
structure ZeroController (controller : Controller config dimension actions) : Prop where
  /-- All physical action learners inhabit the numerical zero sector. -/
  learners : ∀ action, ZeroKnowledge (controller.learners.get action).state
  /-- The shared preceding prediction is zero. -/
  old : SignedZero controller.vOld
  /-- The shared preceding update accumulator is zero. -/
  delta : SignedZero controller.vDelta

/-- Actual controller construction establishes the zero sector for every row. -/
theorem zero_controller_initial : ZeroController (Controller.initial config dimension actions) := by
  refine ⟨?_, Or.inl rfl, Or.inl rfl⟩
  intro action
  simpa only [Controller.initial, Managed.initial,
    CurrentLearner.vector_get, Vector.getElem_ofFn] using
    (zero_initial (config := config) (dimension := dimension))

/-- Actual retirement resets every stored action row and both shared lags.
The same slot may represent several feature units; no distinctness is assumed. -/
theorem zero_controller_retire (controller : Controller config dimension actions)
    (hz : ZeroController controller) (feature : FeatIdx dimension) :
    ZeroController (controller.retire feature) := by
  refine ⟨?_, Or.inl rfl, Or.inl rfl⟩
  intro action
  simpa only [Controller.retire, CurrentLearner.vector_get, Vector.getElem_map,
    Managed.retire, Managed.apply, SwiftTd.Entry.apply] using
    zero_retire (controller.learners.get action).state (hz.learners action) feature

/-- The actual ordered pre-update prediction is zero for every action. -/
theorem zero_predict_all (controller : Controller config dimension actions)
    (hz : ZeroController controller) (features : SwiftTd.ActiveSet dimension)
    (action : Fin actions) :
    SignedZero ((controller.predictAll features).get action) := by
  simpa only [Controller.predictAll, NumericState.predict,
    CurrentLearner.vector_get, Vector.getElem_map] using
    zero_prediction _ (hz.learners action) features

/-- Controller clearing preserves zero knowledge and clears both shared lags. -/
theorem zero_controller_clear (controller : Controller config dimension actions)
    (hz : ZeroController controller) : ZeroController controller.clear := by
  refine ⟨?_, Or.inl rfl, Or.inl rfl⟩
  intro action
  simpa only [Controller.clear, Managed.apply, SwiftTd.Entry.apply,
    CurrentLearner.vector_get, Vector.getElem_map] using
    zero_clear _ (hz.learners action)

private theorem zero_credit_snapshot (learner : Managed config dimension)
    (hz : ZeroKnowledge learner.state) (reward value old vd bootstrap decay : Binary32)
    (restart : Bool) (hr : SignedZero reward) (hvalue : SignedZero value)
    (hold : SignedZero old) (hv : SignedZero vd) :
    ZeroKnowledge
      (learner.credit ((reward.add (bootstrap.mul value)).sub old) vd decay restart).val.state := by
  have hf := zero_first_snapshot learner.state hz reward value old vd bootstrap decay
    hr hvalue hold hv
  cases restart <;> simp only [Managed.credit, Bool.false_eq_true, if_false, if_true,
    Managed.apply, SwiftTd.Entry.apply]
  · exact hf
  · exact zero_clear _ hf

/-- Actual shared-error credit preserves zero rows and shared lags when the
frozen snapshot and reward are zero. Every row receives first-loop credit before
a pending restart clears it; only the selected row receives second-loop credit.
Bootstrap and decay are arbitrary raw words, including exceptional results. -/
theorem zero_values_step (controller : Controller config dimension actions)
    (hz : ZeroController controller) (features : SwiftTd.ActiveSet dimension)
    (values : Vector Binary32 actions) (hvalues : ∀ i, SignedZero (values.get i))
    (action : Action actions) (reward bootstrap decay : Binary32) (hr : SignedZero reward) :
    ZeroController (controller.valuesStep features values action reward bootstrap decay) := by
  have rows (i : Fin actions) := zero_credit_snapshot (controller.learners.get i) (hz.learners i)
    reward (values.get action) controller.vOld controller.vDelta bootstrap decay
    controller.restartPending hr (hvalues action) hz.old hz.delta
  have second := zero_second_loop _ (rows action) features .zero (Or.inl rfl)
  constructor
  · intro other
    by_cases h : other = action
    · subst other
      rw [selected_row]
      exact second.1
    · rw [unselected_row _ _ _ _ _ h]
      exact rows other
  · exact hvalues action
  · simpa only [Controller.valuesStep, CurrentLearner.vector_get, Vector.getElem_map] using second.2

/-- Primitive control derives its zero snapshot from the actual prior rows
and preserves the sector for every selected action and zero reward. -/
theorem zero_controller_step (controller : Controller config dimension actions)
    (hz : ZeroController controller) (features : SwiftTd.ActiveSet dimension)
    (action : Action actions) (reward : Binary32) (hr : SignedZero reward) :
    ZeroController (controller.step features action reward).1 :=
  zero_values_step controller hz features _ (zero_predict_all controller hz features) action
    reward _ _ hr

/-- Actual terminal credit preserves the zero sector and clears shared lags. -/
theorem zero_controller_terminal (controller : Controller config dimension actions)
    (hz : ZeroController controller) (reward : Binary32) (hr : SignedZero reward) :
    ZeroController (controller.terminal reward) := by
  have hd : SignedZero (reward.sub controller.vOld) := by
    rcases hr with h | h <;> rcases hz.old with ho | ho <;> rw [h, ho] <;> decide
  apply zero_controller_clear
  refine ⟨?_, hz.old, hz.delta⟩
  intro action
  simpa only [Managed.apply, SwiftTd.Entry.apply,
    CurrentLearner.vector_get, Vector.getElem_map] using
    zero_first_loop (controller.learners.get action).state (hz.learners action)
      (reward.sub controller.vOld) controller.vDelta controller.traceDecay hd hz.delta

variable {count : Word.Count}
/-- The actual snapshot maximum is zero when its producing controller has
zero rows. No independent terminal value, rate or action premise is introduced. -/
theorem zero_snapshot_best (controller : Controller config dimension count.word.toNat)
    (hz : ZeroController controller) (features : SwiftTd.ActiveSet dimension)
    (rate : SwiftTd.ExploreRate) : SignedZero (controller.snapshot features rate).best := by
  have fold (values : List Binary32) (best : Binary32)
      (hvalues : ∀ v ∈ values, SignedZero v) (hb : SignedZero best) :
      SignedZero
        (values.foldl (fun best value => if best.less value then value else best) best) := by
    induction values generalizing best with
    | nil => exact hb
    | cons v rest ih =>
      apply ih
      · intro w hw; exact hvalues w (List.mem_cons_of_mem _ hw)
      · dsimp only
        split
        · exact hvalues v (by simp)
        · exact hb
  apply fold
  · intro value hv
    have hm := List.mem_of_mem_drop hv
    have hmvec : value ∈ (controller.snapshot features rate).values := by simpa using hm
    obtain ⟨i, hi, heq⟩ := Vector.mem_iff_getElem.mp hmvec
    rw [← heq]
    exact zero_predict_all controller hz features ⟨i, hi⟩
  · exact zero_predict_all controller hz features (firstAction count)

/-- The executed policy draw retains its producing zero snapshot, so its
SMDP credit preserves zero knowledge for every actual RNG state and duration.
The portable bootstrap is used as executed; no power-finiteness premise is needed. -/
theorem zero_draw_policy_step (controller : Controller config dimension count.word.toNat)
    (hz : ZeroController controller) (features : SwiftTd.ActiveSet dimension)
    (rate : SwiftTd.ExploreRate) (rng : Rng.Xoshiro256) (reward : Binary32)
    (duration : UInt32) (hr : SignedZero reward) :
    let decision := ((controller.snapshot features rate).draw rng).1
    ZeroController (controller.policyStep features decision reward duration) := by
  apply zero_values_step controller hz
  · intro action
    rw [PolicySnapshot.draw_snapshot]
    exact zero_predict_all controller hz features action
  · exact hr

/-- The actual rule's bootstrap power is finite for every stored duration. -/
theorem rule_power_finite (rule : ValueRule) (duration : UInt32) :
    (Portable.pow rule.gamma duration).Finite := by
  apply (CurrentPower.pow_unit _ duration ?_ ?_).1
  · cases rule with
    | discounted discount => cases discount <;> decide
    | differential => decide
  · cases rule with
    | discounted discount => cases discount <;> decide
    | differential => decide

/-- Accumulation preserves zero reward for every saturating gap age and rule. -/
theorem zero_gap_accumulate (gap : CreditGap) (hz : SignedZero gap.reward)
    (reward : Binary32) (hr : SignedZero reward) (rule : ValueRule) :
    SignedZero (gap.accumulate reward rule.gamma).reward := by
  have hm := zero_mul_finite reward _ hr (rule_power_finite rule gap.steps.toUInt32)
  change SignedZero (gap.reward.add _)
  rcases hz with h | h <;> rcases hm with hm | hm <;> rw [h, hm] <;> decide

/-- A zero-target backup from zero rows preserves the complete controller,
including trajectory lags, phases, admission and restart state. -/
theorem zero_controller_plan (controller : Controller config dimension actions)
    (hz : ZeroController controller) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) (ht : SignedZero target) :
    controller.plan action features target = (controller, .zero) := by
  simp only [Controller.plan, zero_plan_identity _ (hz.learners action) features target ht]
  congr 2
  apply Vector.ext
  intro i hi
  by_cases he : i = action.val
  · subst i
    simp [Vector.get]
  · simp [Ne.symm he]

end AcornVerif.CurrentControl
