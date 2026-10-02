/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.FeatureConsumers
import Acorn.Average

/-!
# Executable shared-error Sarsa

Javed & Sutton, *Swift-Sarsa: Fast and Robust Linear Control*, arXiv:2507.19539v1
(2025), Algorithm 1, printed p. 4, equation (4), printed p. 1. Acorn uses the
SwiftTD lagging meta-gradient registers and `p += h` correction documented in
PAR-2 and characterized by `AcornVerif.MetaGradient`. Both loops below execute
the maintained learner; they do not reimplement that algorithm.

Sutton, Precup & Singh, *Between MDPs and semi-MDPs*, Artificial Intelligence
112 (1999), equations (8)–(9), p. 190, supplies the duration bootstrap. The
traced extension uses the machine power of gamma times lambda. Terminal credit
has no continuation and inserts no new action trace. Raw reward and transient
words retain their complete machine domain; only stored knowledge is bounded.
-/
namespace Acorn.Features

/-- One admitted action is shared by observations and every indexed update. -/
abbrev Action (actions : Nat) := Fin actions

/-- Public action admission preserves the index or refuses it. -/
def Action.admit (actions raw : Nat) : Option (Action actions) :=
  if h : raw < actions then some ⟨raw, h⟩ else none

/-- Action admission refuses exactly the indices outside the action space. -/
theorem Action.admit_none (actions raw : Nat) :
    Action.admit actions raw = none ↔ actions ≤ raw := by
  simp [Action.admit]

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat}

/-- All raw values in action order, before any learning is performed. -/
def Controller.predictAll (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) : Vector Binary32 actions :=
  controller.learners.map (fun learner => learner.state.linearPrediction features)

/-- The immutable rule owns both the bootstrap and trace multiplier. -/
def Controller.traceDecay (_controller : Controller config dimension actions) : Binary32 :=
  config.rule.gamma.mul config.lambda

/-- Clear every learner's transient state, both shared lags and the restart flag. -/
def Controller.clear (controller : Controller config dimension actions) :
    Controller config dimension actions :=
  ⟨controller.learners.map (fun learner => learner.apply .clear trivial), .zero, .zero, false⟩

/-- A credited row is ready for a second loop, including a pending identity reset. -/
def Managed.credit (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : { result : Managed config dimension // result.phase = true } :=
  let credited := learner.apply (.first delta vd decay) trivial
  if restart then ⟨credited.apply .clear trivial, rfl⟩ else ⟨credited, rfl⟩

/-- Shared-error update toward a supplied error, trace decay and lag. Every first
loop receives the error and the old shared accumulator; only the taken row runs
loop two, from zero. The caller owns the meaning of the error: the on-policy
update supplies its sampled bootstrap, an off-policy update its corrected one.
The controller is consumed before any row is updated and the taken row is taken
out of the table for its two loops. `Controller.creditStep_eq` proves the result
equal to the listed update. That ordering is meant to let the runtime reuse each
row's storage when the controller and the row are referenced nowhere else; it is
a performance expectation, not a proved property (see `detachedUpdate`). -/
def Controller.creditStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) : Controller config dimension actions :=
  let ⟨learners, _, vDelta, restart⟩ := controller
  let taken := detachedUpdate learners action fun learner =>
    let chosen := learner.credit delta vDelta decay restart
    let second := chosen.val.state.learnSecondLoop config features .zero
    (⟨second.1, false, .transition (.second features .zero) chosen.property chosen.val.admitted⟩,
      second.2)
  ⟨taken.1.mapFinIdx fun index learner _ =>
      if index = action.val then learner else (learner.credit delta vDelta decay restart).val,
    lag, taken.2, false⟩

/-- The executing shared-error update is the listed one: every row takes the first
loop with the old shared accumulator, and only the taken row then runs loop two,
from zero. Rows are independent, so updating the taken row first changes no
word. This holds for every controller, feature list, action and raw
lag, error and decay word. -/
theorem Controller.creditStep_eq (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    controller.creditStep features action lag delta decay =
      let rows := controller.learners.map (fun learner =>
        learner.credit delta controller.vDelta decay controller.restartPending)
      let chosen := rows.get action
      let second := chosen.val.state.learnSecondLoop config features .zero
      let updated : Managed config dimension :=
        ⟨second.1, false, .transition (.second features .zero) chosen.property chosen.val.admitted⟩
      ⟨(rows.map Subtype.val).set action.val updated action.isLt, lag, second.2, false⟩ := by
  cases controller with
  | mk learners vOld vDelta restart =>
    have row : (learners.map fun learner => learner.credit delta vDelta decay restart).get action =
        (learners.get action).credit delta vDelta decay restart :=
      Vector.getElem_map _ action.isLt
    simp only [Controller.creditStep, detachedUpdate_eq, row]
    congr 1
    apply Vector.ext
    intro position inside
    by_cases here : action.val = position
    · subst here
      simp only [Vector.getElem_mapFinIdx, Vector.getElem_set_self, ite_true]
    · have there : ¬position = action.val := fun same => here same.symm
      simp only [Vector.getElem_mapFinIdx, Vector.getElem_map,
        Vector.getElem_set_ne action.isLt inside here, there, ite_false]

/-- Complete shared-error update over a supplied immutable value snapshot.
Every first loop receives the old shared accumulator; only the selected row
runs loop two, from zero. The snapshot belongs to the caller's decision clock.
It is the shared-error update at the sampled bootstrap. -/
def Controller.valuesStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    Controller config dimension actions :=
  controller.creditStep features action (values.get action)
    ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld) decay

/-- Release every row's eligible traces and the shared accumulator, keeping all
knowledge and the previous prediction. The work is the eligible lengths. -/
def Controller.release (controller : Controller config dimension actions) :
    Controller config dimension actions :=
  { controller with
    learners := controller.learners.map (fun learner => learner.apply .release trivial)
    vDelta := .zero }

/-- Start a trajectory at the taken action on existing storage. Every earlier trace
is released first, so no first loop visits one and no earlier transition is
credited; the taken row then lays its traces. -/
def Controller.startStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (lag : Binary32) :
    Controller config dimension actions :=
  controller.release.creditStep features action lag .zero .zero

/-- Stopping credit at zero trace decay: the factor γλ(1 − β) of Sutton, Machado et
al., *Reward-respecting subtasks for model-based reinforcement learning*,
Artificial Intelligence 324 (2023), 104001, arXiv:2202.03466v4, §3, procedure
UpdateWeights&Traces as used in equation (10), at β = 1. Every row takes the
error on its existing traces and then releases whatever the first loop retained,
so nothing stays eligible for any trace word. No row runs loop two and both
shared lags restart. -/
def Controller.stopStep (controller : Controller config dimension actions) (delta : Binary32) :
    Controller config dimension actions :=
  let ⟨learners, _, vDelta, restart⟩ := controller
  ⟨learners.map (fun learner =>
    (learner.credit delta vDelta .zero restart).val.apply .release trivial), .zero, .zero, false⟩

/-- Stopping credit in terms of the controller's own fields. The executing form
consumes the controller before its rows are updated; the rows and both lags are
the same words. Storage reuse is expected only when the controller is referenced
nowhere else, and is not proved. -/
theorem Controller.stopStep_eq (controller : Controller config dimension actions)
    (delta : Binary32) :
    controller.stopStep delta =
      ⟨controller.learners.map (fun learner =>
        (learner.credit delta controller.vDelta .zero controller.restartPending).val.apply
          .release trivial), .zero, .zero, false⟩ := by
  cases controller
  rfl

/-- Primitive continuing update: prediction precedes every weight write. -/
def Controller.step (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (reward : Binary32) :
    Controller config dimension actions × Vector Binary32 actions :=
  let values := controller.predictAll features
  (controller.valuesStep features values action reward config.rule.gamma controller.traceDecay, values)

/-- Duration credit retains the exact portable power and multiplication order. -/
def Controller.smdpStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (reward : Binary32) (duration : UInt32) :
    Controller config dimension actions × Vector Binary32 actions :=
  let values := controller.predictAll features
  (controller.valuesStep features values action reward (Portable.pow config.rule.gamma duration)
    (Portable.pow controller.traceDecay duration), values)

/-- Terminal credit closes existing traces without adding a successor action. -/
def Controller.terminal (controller : Controller config dimension actions) (reward : Binary32) :
    Controller config dimension actions :=
  let decay := controller.traceDecay
  let ⟨learners, vOld, vDelta, restart⟩ := controller
  let delta := reward.sub vOld
  let credited := learners.map
    (fun learner => learner.apply (.first delta vDelta decay) trivial)
  (Controller.mk credited vOld vDelta restart).clear

/-- Terminal credit in terms of the controller's own fields. The executing form
consumes the controller before its rows are updated; every row takes the same
first loop and the same clear. Storage reuse is expected only when the controller
is referenced nowhere else, and is not proved. -/
theorem Controller.terminal_eq (controller : Controller config dimension actions)
    (reward : Binary32) :
    controller.terminal reward =
      (Controller.mk (controller.learners.map fun learner =>
          learner.apply (.first (reward.sub controller.vOld) controller.vDelta
            controller.traceDecay) trivial)
        controller.vOld controller.vDelta controller.restartPending).clear := by
  cases controller
  rfl

/-- Malformed raw action input returns no replacement state. -/
def Controller.stepRaw (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (raw : Nat) (reward : Binary32) :
    Option (Controller config dimension actions × Vector Binary32 actions) :=
  (Action.admit actions raw).map (fun action => controller.step features action reward)

/-- Public refusal occurs before any learner transition or observation. -/
theorem Controller.stepRaw_refuses (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (raw : Nat) (reward : Binary32)
    (outside : actions ≤ raw) : controller.stepRaw features raw reward = none := by
  simp [Controller.stepRaw, Action.admit, Nat.not_lt.mpr outside]

/-- Returned observations are the exact pre-update ordered predictions. -/
theorem Controller.step_observation (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (reward : Binary32) :
    (controller.step features action reward).2 = controller.predictAll features := rfl

/-- The lag stores the selected snapshot word, including its exact rounding. -/
theorem Controller.valuesStep_lag (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (controller.valuesStep features values action reward bootstrap decay).vOld = values.get action := by
  rw [Controller.valuesStep, Controller.creditStep_eq]

/-- The on-policy update is the shared-error update at its sampled bootstrap, for
every state and raw input word. -/
theorem Controller.valuesStep_eq_creditStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    controller.valuesStep features values action reward bootstrap decay =
      controller.creditStep features action (values.get action)
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld) decay := rfl

/-- Stopping credit restarts both shared lags and leaves no pending restart. -/
theorem Controller.stopStep_lags (controller : Controller config dimension actions)
    (delta : Binary32) :
    (controller.stopStep delta).vOld = .zero ∧ (controller.stopStep delta).vDelta = .zero ∧
    (controller.stopStep delta).restartPending = false := by
  rw [Controller.stopStep_eq]
  exact ⟨rfl, rfl, rfl⟩

/-- Terminal and clear boundaries erase both shared trajectory lags. -/
theorem Controller.terminal_lags (controller : Controller config dimension actions) (reward : Binary32) :
    (controller.terminal reward).vOld = .zero ∧
    (controller.terminal reward).vDelta = .zero ∧
    (controller.terminal reward).restartPending = false := by
  rw [Controller.terminal_eq]
  exact ⟨rfl, rfl, rfl⟩

/-- Center using the pre-transition rate, retaining the duration cast and order.
Sutton & Barto, *Reinforcement Learning*, MIT Press (2018), §10.3, supplies the
differential target; the host reward-residual tracker is Acorn's PAR-15 choice. -/
def Criterion.center (criterion : Criterion) (reward : Binary32) (duration : UInt32)
    (rate : RewardRate) : Binary32 :=
  match criterion with
  | .discounted => reward
  | .differential => reward.sub ((Binary32.ofUInt64 duration.toUInt64).mul rate.value)

/-- Host gain advances only after an actual learned primitive transition. -/
def Criterion.observe (criterion : Criterion) (tracker : AverageRewardTracker)
    (pending learning : Bool) (reward : Binary32) : AverageRewardTracker :=
  if pending && learning && criterion == .differential then tracker.observe reward else tracker

/-- No predecessor means no host reward observation, for either criterion. -/
theorem Criterion.observe_initial (criterion : Criterion) (tracker : AverageRewardTracker)
    (learning : Bool) (reward : Binary32) : criterion.observe tracker false learning reward = tracker := by
  simp [Criterion.observe]

end Acorn.Features
