/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Exploration
import Acorn.Planning
import AcornVerif.CurrentFeatureConsumers
import AcornVerif.Resource.LearnerWork

/-!
# Work of the learners' admitted entries, the controllers and the policies

Twins of `Managed.apply` and the shared-error controller of `Acorn.Sarsa`, and the bounds of the
frozen policy's functions in `Acorn.Policy` and `Acorn.Exploration`, which are the values of their
costed definitions; the policy's twins carry those bounds. A learner entry's bound reads the
learner's eligible entries, and every admitted learner has at most the capacity of its dimension
(`AcornVerif.CurrentFeatureConsumers.managed_capacity`), so the bound of an admitted entry is a
function of the capacity and the length of the feature list it reads. A controller's update
visits each of its rows, and a policy's loops visit its actions.

`Controller.creditStep` takes the taken row out of its table (`detachedUpdate`) so that the
runtime can reuse the row's storage, and its twin follows that composition: the taken row's
credit and second loop, then one indexed map that credits every other row.
`Controller.stopStep` and `Controller.terminal` consume the controller before updating its
rows; their twins follow the listed compositions the repository proves equal to them
(`Controller.stopStep_eq`, `Controller.terminal_eq`), which run the same loops. Calls of the
scalar operations that the native resource audit admits, including the bounded halving loop of
`Portable.pow`, are stretches of constant work here.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat} {count : Word.Count}

/-! ## Learner entries -/

/-- Twin of `Managed.apply`: the executed learner, with the work of its entry and of the
learner's record. -/
def managedApply (κ : Costs) (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) : Costed (Managed config dimension) :=
  Costed.via (learner.apply entry permitted)
    (Costed.charge (κ .managedEntry) (entryApply κ entry learner.state))

/-- The entry's twin computes the learner's executed state. -/
theorem managedApply_run (κ : Costs) (learner : Managed config dimension)
    (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry learner.phase) :
    (entryApply κ entry learner.state).val = (learner.apply entry permitted).state :=
  entryApply_val κ entry learner.state

/-- An admitted learner's entry is bounded at the capacity of its dimension. -/
theorem managedApply_work (κ : Costs) (learner : Managed config dimension)
    (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry learner.phase) :
    (managedApply κ learner entry permitted).work ≤
      κ .managedEntry + entryBound κ dimension.capacity dimension.capacity entry :=
  Nat.add_le_add_left (Nat.le_trans (entryApply_work κ entry learner.state)
    (entryBound_mono κ _ (CurrentFeatureConsumers.managed_capacity learner) entry)) _

/-- The costed composition of `Managed.credit`: a first loop, then the restart test and a
clear on a pending restart. -/
def creditRun (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : Costed (Managed config dimension) := do
  let credited ← managedApply κ learner (.first delta vd decay) trivial
  Costed.charge (κ .creditRestart)
    (Costed.ite (restart = true) (managedApply κ credited .clear trivial) (Costed.pure credited))

theorem creditRun_val (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    (creditRun κ learner delta vd decay restart).val =
      (learner.credit delta vd decay restart).val := by
  cases restart <;> rfl

/-- Twin of `Managed.credit`. -/
def credit (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : Costed { result : Managed config dimension // result.phase = true } :=
  Costed.via (learner.credit delta vd decay restart) (creditRun κ learner delta vd decay restart)

/-- Bound of a row's credit: its first loop, the restart test and a possible clear. -/
abbrev creditBound (κ : Costs) (capacity : Nat) : Nat :=
  κ .managedEntry + firstLoopBound κ capacity +
    (κ .creditRestart + (κ .managedEntry + zeroBound κ capacity))

theorem credit_work (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    (credit κ learner delta vd decay restart).work ≤ creditBound κ dimension.capacity :=
  Costed.bind_work_le (managedApply_work κ learner (.first delta vd decay) trivial) fun credited =>
    Costed.charge_work_le (Nat.le_trans (Costed.ite_work_le _ _ _)
      (Nat.max_le.mpr ⟨managedApply_work κ credited .clear trivial, Nat.zero_le _⟩))

/-! ## The shared-error controller -/

/-- Twin of `Controller.predictAll`: one prediction for each row. -/
def predictAll (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) : Costed (Vector Binary32 actions) :=
  Costed.mapVector (κ .visit) (fun learner => linearPrediction κ learner.state features)
    controller.learners

theorem predictAll_val (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) :
    (predictAll κ controller features).val = controller.predictAll features := rfl

/-- Bound of the predictions of `rows` rows over `width` features. -/
abbrev predictAllBound (κ : Costs) (rows width : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows (Library.foldl.work (κ .visit) width (κ .sumTerm))

theorem predictAll_work (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) :
    (predictAll κ controller features).work ≤
      predictAllBound κ actions features.indices.length :=
  Costed.mapVector_work_le _ _ _ _ fun learner _ => linearPrediction_work κ learner.state features

/-- Twin of `Controller.clear`: one clear for each row. -/
def clear (κ : Costs) (controller : Controller config dimension actions) :
    Costed (Controller config dimension actions) := do
  let learners ← Costed.mapVector (κ .visit) (fun learner => managedApply κ learner .clear trivial)
    controller.learners
  Costed.op (κ .controllerClose) ⟨learners, .zero, .zero, false⟩

theorem clear_val (κ : Costs) (controller : Controller config dimension actions) :
    (clear κ controller).val = controller.clear := rfl

/-- Bound of a controller clear of `rows` rows. -/
abbrev clearBound (κ : Costs) (rows capacity : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows (κ .managedEntry + zeroBound κ capacity) +
    κ .controllerClose

theorem clear_work (κ : Costs) (controller : Controller config dimension actions) :
    (clear κ controller).work ≤ clearBound κ actions dimension.capacity :=
  Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ => managedApply_work κ learner .clear trivial)
    fun _ => Nat.le_refl _

/-- Twin of `Controller.creditStep`: the taken row's credit and second loop, which
`detachedUpdate` runs on the row it takes out of the table, then one indexed map that credits
every other row and keeps the taken one. -/
def creditStep (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) : Costed (Controller config dimension actions) := do
  let vDelta := controller.vDelta
  let restart := controller.restartPending
  let chosen ← credit κ (controller.learners.get action) delta vDelta decay restart
  Costed.discard (secondLoop κ config chosen.val.state features .zero)
  let taken := detachedUpdate controller.learners action fun learner =>
    let chosen := learner.credit delta vDelta decay restart
    let second := chosen.val.state.learnSecondLoop config features .zero
    (⟨second.1, false,
        .transition (.second features .zero) chosen.property chosen.val.admitted⟩, second.2)
  let rows ← Costed.mapFinIdx (κ .visit)
    (fun index (learner : Managed config dimension) _ =>
      Costed.ite (index = action.val) (Costed.pure learner)
        (Costed.via (learner.credit delta vDelta decay restart).val
          (credit κ learner delta vDelta decay restart)))
    taken.1
  Costed.op (κ .creditClose) ⟨rows, lag, taken.2, false⟩

theorem creditStep_val (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (creditStep κ controller features action lag delta decay).val =
      controller.creditStep features action lag delta decay := by
  cases controller
  rfl

/-- Bound of a shared-error update of `rows` rows over `width` features: the taken row's credit
and second loop, then the indexed map at a credit for each row. -/
abbrev creditStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  creditBound κ capacity + (secondLoopBound κ width +
    (Library.mapFinIdx.work (κ .visit) rows (creditBound κ capacity) + κ .creditClose))

theorem creditStep_work (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (creditStep κ controller features action lag delta decay).work ≤
      creditStepBound κ actions dimension.capacity features.indices.length :=
  Costed.bind_work_le
    (credit_work κ (controller.learners.get action) delta controller.vDelta decay
      controller.restartPending)
    fun chosen => Costed.bind_work_le
      (Costed.discard_work_le (secondLoop_work κ config chosen.val.state features .zero))
      fun _ => Costed.bind_work_le
        (Costed.mapFinIdx_work_le (κ .visit) (creditBound κ dimension.capacity) _ _
          fun _ learner _ => Nat.le_trans (Costed.ite_work_le _ _ _)
            (Nat.max_le.mpr ⟨Nat.zero_le _,
              credit_work κ learner delta controller.vDelta decay controller.restartPending⟩))
        fun _ => Nat.le_refl _

/-- Twin of `Controller.valuesStep`. -/
def valuesStep (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    Costed (Controller config dimension actions) :=
  Costed.charge (κ .valuesOpen)
    (creditStep κ controller features action (values.get action)
      ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld) decay)

theorem valuesStep_val (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (valuesStep κ controller features values action reward bootstrap decay).val =
      controller.valuesStep features values action reward bootstrap decay :=
  creditStep_val ..

theorem valuesStep_work (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (valuesStep κ controller features values action reward bootstrap decay).work ≤
      κ .valuesOpen + creditStepBound κ actions dimension.capacity features.indices.length :=
  Nat.add_le_add_left (creditStep_work ..) _

/-- Twin of `Controller.release`: one release for each row. -/
def release (κ : Costs) (controller : Controller config dimension actions) :
    Costed (Controller config dimension actions) := do
  let learners ← Costed.mapVector (κ .visit)
    (fun learner => managedApply κ learner .release trivial) controller.learners
  Costed.op (κ .controllerClose) { controller with learners := learners, vDelta := .zero }

theorem release_val (κ : Costs) (controller : Controller config dimension actions) :
    (release κ controller).val = controller.release := rfl

/-- Bound of the release of one row at a capacity. -/
abbrev releaseBound (κ : Costs) (capacity : Nat) : Nat :=
  Library.foldlArray.work (κ .visit) capacity (κ .clearRegisters) + κ .releaseClose

theorem release_work (κ : Costs) (controller : Controller config dimension actions) :
    (release κ controller).work ≤
      Library.vectorMap.work (κ .visit) actions
        (κ .managedEntry + releaseBound κ dimension.capacity) + κ .controllerClose :=
  Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ =>
      managedApply_work κ learner .release trivial)
    fun _ => Nat.le_refl _

/-- Twin of `Controller.stopStep`, in the listed composition of `Controller.stopStep_eq`:
each row's credit and then its release. -/
def stopStep (κ : Costs) (controller : Controller config dimension actions) (delta : Binary32) :
    Costed (Controller config dimension actions) := do
  let learners ← Costed.mapVector (κ .visit)
    (fun learner => do
      let credited ← credit κ learner delta controller.vDelta .zero controller.restartPending
      managedApply κ credited.val .release trivial)
    controller.learners
  Costed.op (κ .controllerClose) ⟨learners, .zero, .zero, false⟩

theorem stopStep_val (κ : Costs) (controller : Controller config dimension actions)
    (delta : Binary32) : (stopStep κ controller delta).val = controller.stopStep delta := by
  rw [Controller.stopStep_eq]
  rfl

/-- Bound of a stopping credit of `rows` rows. -/
abbrev stopBound (κ : Costs) (rows capacity : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows
    (creditBound κ capacity + (κ .managedEntry + releaseBound κ capacity)) + κ .controllerClose

theorem stopStep_work (κ : Costs) (controller : Controller config dimension actions)
    (delta : Binary32) :
    (stopStep κ controller delta).work ≤ stopBound κ actions dimension.capacity :=
  Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ =>
      Costed.bind_work_le
        (credit_work κ learner delta controller.vDelta .zero controller.restartPending)
        fun credited => managedApply_work κ credited.val .release trivial)
    fun _ => Nat.le_refl _

/-- Twin of `Controller.terminal`, in the listed composition of `Controller.terminal_eq`:
the terminal error and trace decay, each row's first loop, then the controller's clear. -/
def terminal (κ : Costs) (controller : Controller config dimension actions) (reward : Binary32) :
    Costed (Controller config dimension actions) :=
  Costed.charge (κ .learnerError) (do
    let credited ← Costed.mapVector (κ .visit)
      (fun learner => managedApply κ learner
        (.first (reward.sub controller.vOld) controller.vDelta controller.traceDecay) trivial)
      controller.learners
    clear κ (Controller.mk credited controller.vOld controller.vDelta controller.restartPending))

theorem terminal_val (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) : (terminal κ controller reward).val = controller.terminal reward := by
  rw [Controller.terminal_eq]
  rfl

/-- Bound of a terminal credit of `rows` rows. -/
abbrev terminalCreditBound (κ : Costs) (rows capacity : Nat) : Nat :=
  κ .learnerError + (Library.vectorMap.work (κ .visit) rows
    (κ .managedEntry + firstLoopBound κ capacity) + clearBound κ rows capacity)

theorem terminal_work (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) :
    (terminal κ controller reward).work ≤ terminalCreditBound κ actions dimension.capacity :=
  Costed.charge_work_le (Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ => managedApply_work κ learner
      (.first (reward.sub controller.vOld) controller.vDelta controller.traceDecay) trivial)
    fun _ => clear_work κ _)

/-- Twin of `Controller.retire`: one retirement for each row. -/
def retire (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) : Costed (Controller config dimension actions) := do
  let learners ← Costed.mapVector (κ .visit)
    (fun learner => managedApply κ learner (.retire feature) trivial) controller.learners
  Costed.op (κ .controllerClose)
    ⟨learners, controller.vOld, controller.vDelta, controller.restartPending⟩

theorem retire_val (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) :
    (retire κ controller feature).val = controller.retire feature := by
  cases controller
  rfl

theorem retire_work (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) :
    (retire κ controller feature).work ≤
      Library.vectorMap.work (κ .visit) actions (κ .managedEntry +
        (κ .retire + Library.findIdx.work (κ .visit) dimension.capacity (κ .compare))) +
        κ .controllerClose :=
  Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ =>
      managedApply_work κ learner (.retire feature) trivial)
    fun _ => Nat.le_refl _

/-- Twin of `Controller.plan`: the planned row's planning step. -/
def plan (κ : Costs) (controller : Controller config dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    Costed (Controller config dimension actions × Binary32) :=
  let learner := controller.learners.get action
  Costed.bind (planStep κ config learner.state features target) fun _ =>
    let result := learner.state.planStep config features target
    let updated : Managed config dimension :=
      ⟨result.1, learner.phase, SwiftTd.Entry.apply_plan features target learner.state ▸
        .transition (.plan features target) trivial learner.admitted⟩
    Costed.op (κ .planClose)
      ({ controller with learners := controller.learners.set action.val updated action.isLt },
        result.2)

theorem plan_val (κ : Costs) (controller : Controller config dimension actions)
    (action : Action actions) (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    (plan κ controller action features target).val = controller.plan action features target := rfl

theorem plan_work (κ : Costs) (controller : Controller config dimension actions)
    (action : Action actions) (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    (plan κ controller action features target).work ≤
      planBound κ features.indices.length + κ .planClose :=
  Costed.bind_work_le (planStep_work κ config _ features target) fun _ => Nat.le_refl _

/-! ## Policies -/

/-- Bound of an ordered maximum over `size` values. -/
abbrev bestBound (κ : Costs) (size : Nat) : Nat :=
  κ .read + (Library.toList.control (κ .visit) size +
    (Library.drop.control (κ .visit) 1 + Library.foldl.work (κ .visit) size (κ .compare)))

theorem bestCosted_within (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.bestCosted.Within κ (bestBound κ count.word.toNat) := by
  unfold PolicySnapshot.bestCosted bestBound
  refine Acorn.Costed.bind_within (Acorn.Costed.op_within _ _ κ) ?_
  refine Acorn.Costed.bind_within (Acorn.Costed.toList_within _ κ) ?_
  refine Acorn.Costed.bind_within (Acorn.Costed.drop_within _ _ κ) ?_
  refine (Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ).mono ?_
  exact Library.foldl.work_mono (by simp [Acorn.Costed.drop_val, Acorn.Costed.toList_val])
    (Nat.le_refl _)

/-- Bound of the near-maximum candidates over `size` values. -/
abbrev candidatesBound (κ : Costs) (size : Nat) : Nat :=
  bestBound κ size + (κ .tieThreshold + (Library.finRange.control (κ .visit) size +
    Library.filter.work (κ .visit) size (κ .candidate)))

theorem candidatesCosted_within (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.candidatesCosted.Within κ (candidatesBound κ count.word.toNat) := by
  unfold PolicySnapshot.candidatesCosted candidatesBound
  refine Acorn.Costed.bind_within (bestCosted_within κ snapshot) ?_
  refine Acorn.Costed.bind_within (Acorn.Costed.op_within _ _ κ) ?_
  refine Acorn.Costed.bind_within (Acorn.Costed.finRange_within _ κ) ?_
  refine (Acorn.Costed.filter_within fun _ _ => Acorn.Costed.op_within _ _ κ).mono ?_
  simp [Acorn.Costed.finRange_val]

theorem candidates_length (snapshot : PolicySnapshot count) :
    snapshot.candidates.length ≤ count.word.toNat := by
  have filtered := List.length_filter_le
    (fun action => decide ((snapshot.best.sub tieWindow).LessOrEqual (snapshot.values.get action)))
    (List.finRange count.word.toNat)
  simpa only [PolicySnapshot.candidates_def, List.length_finRange] using filtered

theorem reservoirCosted_within (κ : Costs) (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoirCosted pending seen pick rng).Within κ
      (pass (κ .visit) pending.length (κ .reservoirDraw)) := by
  induction pending generalizing seen pick rng with
  | nil => exact (Acorn.Costed.op_within _ _ κ).mono (by simp [pass])
  | cons action rest ih =>
    have restFits := ih (seen + 1)
      (if (rng.nextBelow (Word.Count.ofWord (seen + 1))).1.val == 0 then action else pick)
      (rng.nextBelow (Word.Count.ofWord (seen + 1))).2
    refine (Acorn.Costed.charge_within (Acorn.Costed.charge_within restFits)).mono ?_
    simp only [pass, List.length_cons, Nat.succ_mul]
    omega

/-- Bound of a greedy draw over `size` values. -/
abbrev greedyBound (κ : Costs) (size : Nat) : Nat :=
  candidatesBound κ size + pass (κ .visit) size (κ .reservoirDraw)

theorem greedyCosted_within (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.greedyCosted rng).Within κ (greedyBound κ count.word.toNat) :=
  Acorn.Costed.bind_within (candidatesCosted_within κ snapshot)
    ((reservoirCosted_within κ _ 0 _ rng).mono
      (pass_mono (candidates_length snapshot) (Nat.le_refl _)))

/-- Bound of the nominal masses over `size` values. -/
abbrev probabilitiesBound (κ : Costs) (size : Nat) : Nat :=
  candidatesBound κ size + Library.length.control (κ .visit) size + bestBound κ size +
    κ .probabilitiesOpen +
    Library.vectorMap.work (κ .visit) size (κ .probability)

theorem probabilitiesCosted_within (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.probabilitiesCosted.Within κ (probabilitiesBound κ count.word.toNat) := by
  have size : Library.length.control (κ .visit) snapshot.candidatesCosted.val.length ≤
      Library.length.control (κ .visit) count.word.toNat :=
    Library.control_mono _ (candidates_length snapshot)
  refine (Acorn.Costed.bind_within (candidatesCosted_within κ snapshot)
    (Acorn.Costed.bind_within (Acorn.Costed.length_within _ κ)
      (Acorn.Costed.bind_within (bestCosted_within κ snapshot)
        (Acorn.Costed.charge_within
          (Acorn.Costed.mapVector_within fun _ _ => Acorn.Costed.op_within _ _ κ))))).mono ?_
  simp only [probabilitiesBound]
  omega

theorem drawCosted_within (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.drawCosted rng).Within κ
      (κ .drawClose + max (κ .uniform) (greedyBound κ count.word.toNat)) :=
  Acorn.Costed.charge_within ((Acorn.Costed.bind_within_all
    (Acorn.Costed.within_ite (bound := max (κ .uniform) (greedyBound κ count.word.toNat))
      ((Acorn.Costed.op_within _ _ κ).mono (Nat.le_max_left _ _))
      ((greedyCosted_within κ snapshot _).mono (Nat.le_max_right _ _)))
    fun _ => Acorn.Costed.pure_within _ κ).mono (Nat.le_of_eq (Nat.add_zero _)))

/-- Bound of a persistent draw over `size` values. -/
abbrev persistentBound (κ : Costs) (size : Nat) : Nat :=
  κ .explorationBegin + (greedyBound κ size + probabilitiesBound κ size)

theorem drawPersistentCosted_within (κ : Costs) (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    (snapshot.drawPersistentCosted rng).Within κ (persistentBound κ count.word.toNat) := by
  unfold PolicySnapshot.drawPersistentCosted
  refine Acorn.Costed.charge_within ?_
  split
  · exact (Acorn.Costed.bind_within_all (probabilitiesCosted_within κ snapshot) fun _ =>
      Acorn.Costed.pure_within _ κ).mono (by omega)
  · exact (Acorn.Costed.bind_within_all (greedyCosted_within κ snapshot _) fun _ =>
      Acorn.Costed.bind_within_all (probabilitiesCosted_within κ snapshot) fun _ =>
        Acorn.Costed.pure_within _ κ).mono (by omega)

/-! ### The policies in the twins' accounting

Each definition below is the executed policy function with the bound proved above of its costed
definition as its work; its `_costed` theorem checks that the costed definition is within that
work. -/

/-- `PolicySnapshot.best` with its bound. -/
def best (κ : Costs) (snapshot : PolicySnapshot count) : Costed Binary32 :=
  ⟨snapshot.best, bestBound κ count.word.toNat⟩

theorem best_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (best κ snapshot).val = snapshot.best := rfl

theorem best_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (best κ snapshot).work ≤ bestBound κ count.word.toNat := Nat.le_refl _

theorem best_costed (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.bestCosted.Within κ (best κ snapshot).work := bestCosted_within κ snapshot

/-- `PolicySnapshot.candidates` with its bound. -/
def candidates (κ : Costs) (snapshot : PolicySnapshot count) :
    Costed (List (Action count.word.toNat)) :=
  ⟨snapshot.candidates, candidatesBound κ count.word.toNat⟩

theorem candidates_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (candidates κ snapshot).val = snapshot.candidates := rfl

theorem candidates_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (candidates κ snapshot).work ≤ candidatesBound κ count.word.toNat := Nat.le_refl _

theorem candidates_costed (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.candidatesCosted.Within κ (candidates κ snapshot).work :=
  candidatesCosted_within κ snapshot

/-- `PolicySnapshot.greedy` with its bound. -/
def greedy (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (Action count.word.toNat × Rng.Xoshiro256) :=
  ⟨snapshot.greedy rng, greedyBound κ count.word.toNat⟩

theorem greedy_val (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (greedy κ snapshot rng).val = snapshot.greedy rng := rfl

theorem greedy_work (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (greedy κ snapshot rng).work ≤ greedyBound κ count.word.toNat := Nat.le_refl _

theorem greedy_costed (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.greedyCosted rng).Within κ (greedy κ snapshot rng).work :=
  greedyCosted_within κ snapshot rng

/-- `PolicySnapshot.probabilities` with its bound. -/
def probabilities (κ : Costs) (snapshot : PolicySnapshot count) :
    Costed (Vector Binary32 count.word.toNat) :=
  ⟨snapshot.probabilities, probabilitiesBound κ count.word.toNat⟩

theorem probabilities_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (probabilities κ snapshot).val = snapshot.probabilities := rfl

theorem probabilities_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (probabilities κ snapshot).work ≤ probabilitiesBound κ count.word.toNat := Nat.le_refl _

theorem probabilities_costed (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.probabilitiesCosted.Within κ (probabilities κ snapshot).work :=
  probabilitiesCosted_within κ snapshot

/-- `PolicySnapshot.draw` with its bound. -/
def draw (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (PolicyDecision count × Rng.Xoshiro256) :=
  ⟨snapshot.draw rng, κ .drawClose + max (κ .uniform) (greedyBound κ count.word.toNat)⟩

theorem draw_work (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (draw κ snapshot rng).work ≤
      κ .drawClose + max (κ .uniform) (greedyBound κ count.word.toNat) := Nat.le_refl _

theorem draw_costed (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.drawCosted rng).Within κ (draw κ snapshot rng).work :=
  drawCosted_within κ snapshot rng

/-- `PolicySnapshot.drawPersistent` with its bound. -/
def drawPersistent (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (PersistentDecision count × Rng.Xoshiro256) :=
  ⟨snapshot.drawPersistent rng, persistentBound κ count.word.toNat⟩

theorem drawPersistent_val (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (drawPersistent κ snapshot rng).val = snapshot.drawPersistent rng := rfl

theorem drawPersistent_work (κ : Costs) (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    (drawPersistent κ snapshot rng).work ≤ persistentBound κ count.word.toNat := Nat.le_refl _

theorem drawPersistent_costed (κ : Costs) (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    (snapshot.drawPersistentCosted rng).Within κ (drawPersistent κ snapshot rng).work :=
  drawPersistentCosted_within κ snapshot rng

/-- Twin of `Controller.snapshot`. -/
def snapshot (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    Costed (PolicySnapshot count) := do
  let values ← predictAll κ controller features
  Costed.op (κ .snapshot) ⟨values, epsilon⟩

theorem snapshot_val (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    (snapshot κ controller features epsilon).val = controller.snapshot features epsilon := rfl

theorem snapshot_work (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    (snapshot κ controller features epsilon).work ≤
      predictAllBound κ count.word.toNat features.indices.length + κ .snapshot :=
  Costed.bind_work_le (predictAll_work κ controller features) fun _ => Nat.le_refl _

/-- Twin of `Controller.policyStep`. -/
def policyStep (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    Costed (Controller config dimension count.word.toNat) :=
  Costed.charge (κ .policyOpen)
    (valuesStep κ controller features decision.snapshot.values decision.action reward
      (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration))

theorem policyStep_val (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    (policyStep κ controller features decision reward duration).val =
      controller.policyStep features decision reward duration :=
  valuesStep_val ..

/-- Bound of a frozen-decision credit of `rows` rows over `width` features. -/
abbrev policyStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  κ .policyOpen + (κ .valuesOpen + creditStepBound κ rows capacity width)

theorem policyStep_work (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    (policyStep κ controller features decision reward duration).work ≤
      policyStepBound κ count.word.toNat dimension.capacity features.indices.length :=
  Nat.add_le_add_left (valuesStep_work ..) _

/-- Twin of `Controller.persistentStep`. -/
def persistentStep (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    Costed (Controller config dimension count.word.toNat) :=
  Costed.charge (κ .policyOpen)
    (valuesStep κ controller features snapshot.values drawn.action reward
      (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration))

theorem persistentStep_val (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    (persistentStep κ controller features snapshot drawn reward duration).val =
      controller.persistentStep features snapshot drawn reward duration :=
  valuesStep_val ..

theorem persistentStep_work (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    (persistentStep κ controller features snapshot drawn reward duration).work ≤
      policyStepBound κ count.word.toNat dimension.capacity features.indices.length :=
  Nat.add_le_add_left (valuesStep_work ..) _

/-- Twin of `NumericState.normalizedStepSizeSum`: one term for each eligible entry. -/
def normalizedStepSizeSum (κ : Costs) (state : NumericState config dimension) :
    Costed (Binary32 × Nat) :=
  Costed.ite (state.transient.eligible.isEmpty = true) (Costed.op (κ .normalizedOpen) (.zero, 0))
    (do
      let lo := state.rails.range.lower
      let span := state.rails.range.upper.sub lo
      let entries ← Costed.scanArray .toList (κ .visit) state.transient.eligible
        state.transient.eligible.toList
      let terms ← Costed.map (κ .visit)
        (fun idx => Costed.op (κ .normalizedTerm) (((state.beta.get idx).value.sub lo).div span))
        entries
      let total ← sumFrom κ .zero terms
      Costed.op (κ .normalizedOpen) (total, state.transient.eligible.size))

theorem normalizedStepSizeSum_val (κ : Costs) (state : NumericState config dimension) :
    (normalizedStepSizeSum κ state).val = state.normalizedStepSizeSum := rfl

/-- Bound of a normalized step-size sum over `size` eligible entries. -/
abbrev normalizedBound (κ : Costs) (size : Nat) : Nat :=
  Library.toList.control (κ .visit) size +
    (Library.map.work (κ .visit) size (κ .normalizedTerm)) +
    Library.foldl.work (κ .visit) size (κ .sumTerm) + κ .normalizedOpen

theorem normalizedStepSizeSum_work (κ : Costs) (state : NumericState config dimension) :
    (normalizedStepSizeSum κ state).work ≤ normalizedBound κ state.transient.eligible.size := by
  have terms := Costed.map_work_le (κ .visit) (κ .normalizedTerm)
    (fun idx => Costed.op (κ .normalizedTerm)
      (((state.beta.get idx).value.sub state.rails.range.lower).div
        (state.rails.range.upper.sub state.rails.range.lower)))
    state.transient.eligible.toList (fun _ _ => Nat.le_refl _)
  have total := sumFrom_work κ .zero
    (state.transient.eligible.toList.map fun idx =>
      ((state.beta.get idx).value.sub state.rails.range.lower).div
        (state.rails.range.upper.sub state.rails.range.lower))
  simp only [List.length_map, Array.length_toList] at terms total
  unfold normalizedStepSizeSum
  refine Costed.ite_work_bound _ (Nat.le_add_left _ _) ?_
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _) (Costed.bind_work_le_at terms
    (Costed.bind_work_le_at total (Nat.le_refl _)))) ?_
  simp only [normalizedBound]
  omega

/-- Twin of `Controller.exploreRate`: each row's normalized sum, then the projection. -/
def exploreRate (κ : Costs) (controller : Controller config dimension count.word.toNat) :
    Costed SwiftTd.ExploreRate := do
  let rows ← Costed.scanVector .toList (κ .visit) controller.learners controller.learners.toList
  let totals ← Costed.foldl (κ .visit)
    (fun (sum, size) learner => do
      let contribution ← normalizedStepSizeSum κ learner.state
      Costed.op (κ .rateTerm) (sum.add contribution.1, size + contribution.2))
    (Binary32.zero, 0) rows
  Costed.op (κ .rateClose) (SwiftTd.ExploreRate.project <| if totals.2 == 0 then
      (controller.learners.get (firstAction count)).state.initialNormalizedStepSize config
    else totals.1.div (Binary32.ofUInt64 totals.2.toUInt64))

theorem exploreRate_val (κ : Costs) (controller : Controller config dimension count.word.toNat) :
    (exploreRate κ controller).val = controller.exploreRate := rfl

/-- Bound of a derived exploration rate of `rows` rows at a capacity. -/
abbrev rateBound (κ : Costs) (rows capacity : Nat) : Nat :=
  Library.toList.control (κ .visit) rows +
    Library.foldl.work (κ .visit) rows (normalizedBound κ capacity + κ .rateTerm) + κ .rateClose

/-- A normalized sum's bound grows with the number of eligible entries. -/
theorem normalizedBound_mono (κ : Costs) {size limit : Nat} (fits : size ≤ limit) :
    normalizedBound κ size ≤ normalizedBound κ limit := by
  have := Library.toList.control_mono (visit := κ .visit) fits
  have := Library.map.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .normalizedTerm))
  have := Library.foldl.work_mono (visit := κ .visit) fits (Nat.le_refl (κ .sumTerm))
  simp only [normalizedBound]
  omega

theorem exploreRate_work (κ : Costs) (controller : Controller config dimension count.word.toNat) :
    (exploreRate κ controller).work ≤ rateBound κ count.word.toNat dimension.capacity := by
  unfold exploreRate
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _) (Costed.bind_work_le_at
    (Costed.foldl_work_le (κ .visit) (normalizedBound κ dimension.capacity + κ .rateTerm) _ _ _
      fun acc learner _ => ?_) (Nat.le_refl _))) ?_
  · obtain ⟨sum, size⟩ := acc
    exact Costed.bind_work_le_at (Nat.le_trans (normalizedStepSizeSum_work κ learner.state)
      (normalizedBound_mono κ (CurrentFeatureConsumers.managed_capacity learner))) (Nat.le_refl _)
  · simp only [Vector.length_toList, rateBound]
    omega

/-- Bound of a policy mean over `size` values. -/
abbrev expectedBound (κ : Costs) (size : Nat) : Nat :=
  κ .read + (Library.toList.control (κ .visit) size +
    (Library.foldl.work (κ .visit) size (κ .compare) + (bestBound κ size + (κ .tieThreshold +
      (Library.foldl.work (κ .visit) size (κ .expectedTerm) + κ .expectedClose)))))

theorem expectedCosted_within (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.expectedCosted.Within κ (expectedBound κ count.word.toNat) := by
  unfold PolicySnapshot.expectedCosted expectedBound
  refine Acorn.Costed.bind_within (Acorn.Costed.op_within _ _ κ) ?_
  refine Acorn.Costed.bind_within (Acorn.Costed.toList_within _ κ) ?_
  refine Acorn.Costed.bind_within
    ((Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ).mono ?_) ?_
  · simp [Acorn.Costed.toList_val]
  refine Acorn.Costed.bind_within (bestCosted_within κ snapshot) ?_
  refine Acorn.Costed.bind_within (Acorn.Costed.op_within _ _ κ) ?_
  refine Acorn.Costed.bind_within
    ((Acorn.Costed.foldl_within (bound := κ .expectedTerm) fun acc _ _ => ?_).mono ?_) ?_
  · obtain ⟨_, _, _⟩ := acc
    exact Acorn.Costed.op_within _ _ κ
  · simp [Acorn.Costed.toList_val]
  · exact Acorn.Costed.op_within _ _ κ

/-- `PolicySnapshot.expected` with its bound. -/
def expected (κ : Costs) (snapshot : PolicySnapshot count) : Costed Binary32 :=
  ⟨snapshot.expected, expectedBound κ count.word.toNat⟩

theorem expected_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (expected κ snapshot).val = snapshot.expected := rfl

theorem expected_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (expected κ snapshot).work ≤ expectedBound κ count.word.toNat := Nat.le_refl _

theorem expected_costed (κ : Costs) (snapshot : PolicySnapshot count) :
    snapshot.expectedCosted.Within κ (expected κ snapshot).work := expectedCosted_within κ snapshot

theorem servedProbabilitiesCosted_within (κ : Costs) (action : Action count.word.toNat) :
    (Features.servedProbabilitiesCosted action).Within κ
      (Library.ofFn.work (κ .visit) count.word.toNat (κ .read)) :=
  Acorn.Costed.ofFn_within fun _ => Acorn.Costed.op_within _ _ κ

/-- `servedProbabilities` with its bound. -/
def servedProbabilities (κ : Costs) (action : Action count.word.toNat) :
    Costed (Vector Binary32 count.word.toNat) :=
  ⟨Features.servedProbabilities action, Library.ofFn.work (κ .visit) count.word.toNat (κ .read)⟩

theorem servedProbabilities_val (κ : Costs) (action : Action count.word.toNat) :
    (servedProbabilities κ action).val = Features.servedProbabilities action := rfl

theorem servedProbabilities_work (κ : Costs) (action : Action count.word.toNat) :
    (servedProbabilities κ action).work ≤ Library.ofFn.work (κ .visit) count.word.toNat (κ .read) :=
  Nat.le_refl _

theorem servedProbabilities_costed (κ : Costs) (action : Action count.word.toNat) :
    (Features.servedProbabilitiesCosted action).Within κ (servedProbabilities κ action).work :=
  servedProbabilitiesCosted_within κ action

end AcornVerif.Resource.Twin
