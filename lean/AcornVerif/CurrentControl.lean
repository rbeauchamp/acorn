/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.PredictionControl
import AcornVerif.CurrentFeatureConsumers
import AcornVerif.CurrentPrediction

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

end AcornVerif.CurrentControl
