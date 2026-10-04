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
Off-policy credit (Precup, Sutton & Singh, ICML (2000), §4, Algorithm 2) and
stopping credit pass raw words to the same learner entries.
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

/-- The shared-error kernel preserves stored weight/beta legality and eligibility
capacity for arbitrary raw lag, error and decay words; tree-backup credit and the
zero-error start of an off-policy trajectory are instances. -/
theorem credit_step_legal (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action observed : Action actions)
    (lag delta decay : Binary32) (index : FeatIdx dimension) :
    let next := controller.creditStep features action lag delta decay
    let learner := next.learners.get observed
    config.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  dsimp only
  exact ⟨weight_legal _, (by exact Bounded32.legal _), managed_capacity _⟩

/-- Stopping credit preserves the same stored legality and eligibility capacity. -/
theorem stop_step_legal (controller : Controller config dimension actions)
    (delta : Binary32) (observed : Action actions) (index : FeatIdx dimension) :
    let learner := (controller.stopStep delta).learners.get observed
    config.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  dsimp only
  exact ⟨weight_legal _, (by exact Bounded32.legal _), managed_capacity _⟩

/-- At zero trace decay a visited finite trace is pruned, for every managed learner
and every error and accumulator word, so the release after stopping credit has
nothing left to visit when the eligible traces are finite. -/
theorem stop_prunes (learner : Managed config dimension) (idx : FeatIdx dimension)
    (delta vDelta : Binary32) (finite : (learner.state.transient.z.get idx).value.Finite) :
    (learner.state.firstLoopElement idx delta vDelta .zero).2 = true := by
  have zero := zero_decay_trace _ finite
  have trace : ((learner.state.firstLoopElement idx delta vDelta .zero).1.transient.z.get
      idx).value = (learner.state.transient.z.get idx).value.mul .zero := by
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self]
  cases retained : (learner.state.firstLoopElement idx delta vDelta .zero).2 with
  | true => rfl
  | false =>
    have kept := first_element_retained_nonzero learner.state idx delta vDelta .zero
      (managed_schedule learner).1.2 retained
    rw [trace, zero] at kept
    contradiction

/-- Work bound at a stop: stopping credit leaves every action learner nothing
eligible, for every state and every trace word, because its last entry releases
the list structurally. The start that follows a stop therefore visits no earlier
trace. -/
theorem stop_step_empty (controller : Controller config dimension actions) (delta : Binary32)
    (action : Action actions) :
    ((controller.stopStep delta).learners.get action).state.eligibleCount = 0 := by
  simp only [Controller.stopStep_eq, vector_get, Vector.getElem_map]
  rfl

/-- A closed span leaves every action learner nothing eligible, and the first loop of
whatever credit comes next is the identity on it, for every error, accumulator and decay
word: no reward delivered after the close reaches an action credited before it. -/
theorem close_step_idle (controller : Controller config dimension actions)
    (reward continuation : Binary32) (duration : UInt32) (action : Action actions)
    (delta vDelta decay : Binary32) :
    ((controller.closeStep reward continuation duration).learners.get action).state.eligibleCount
        = 0 ∧
      ((controller.closeStep reward continuation duration).learners.get
        action).state.learnFirstLoop config delta vDelta decay =
        ((controller.closeStep reward continuation duration).learners.get action).state := by
  unfold Controller.closeStep
  refine ⟨stop_step_empty _ _ action, ?_⟩
  simp only [Controller.stopStep_eq, vector_get, Vector.getElem_map]
  exact release_idle _ delta vDelta decay

/-- A release leaves every action learner nothing eligible and with its weights,
so the first loops of the start that follows read no trace and credit no earlier
transition (`release_idle`). -/
theorem release_rows (controller : Controller config dimension actions) (action : Action actions)
    (idx : FeatIdx dimension) :
    (controller.release.learners.get action).state.eligibleCount = 0 ∧
      (controller.release.learners.get action).state.weights.get idx =
        (controller.learners.get action).state.weights.get idx := by
  simp only [Controller.release, vector_get, Vector.getElem_map]
  exact ⟨rfl, (release_knowledge _ idx).1⟩

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
  simp [Controller.valuesStep, Controller.creditStep_eq, Vector.get, Fin.cast]

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
  simp [Controller.valuesStep, Controller.creditStep_eq, Vector.get, Fin.cast, Ne.symm indices]

/-- Terminal closeout clears all trajectory registers in every action row. -/
theorem terminal_clears (controller : Controller config dimension actions)
    (reward : Binary32)
    (action : Action actions) :
    ((controller.terminal reward).learners.get action).state.transient =
      TransientState.zero dimension := by
  simp [Controller.terminal_eq, Controller.clear, Vector.get, Managed.apply, SwiftTd.Entry.apply,
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
