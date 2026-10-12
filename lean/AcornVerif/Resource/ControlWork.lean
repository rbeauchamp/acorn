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

The bounds of the costed definitions of a learner record (its entry, retirement and credit), of the
shared-error controller (its predictions, clear, release, snapshot and derived rate and its updates
`Controller.creditStep`, `Controller.valuesStep`, `Controller.stopStep`, `Controller.terminal`,
`Controller.retire`, `Controller.plan`, `Controller.policyStep`, `Controller.persistentStep`,
`Controller.startStep`, `Controller.step`, `Controller.smdpStep`, `Controller.closeStep` and
`Controller.backupStep` with the tree-backup error and an action's mass), of the normalized
step-size sum and of the frozen policy's functions in `Acorn.Policy` and `Acorn.Exploration`. The
controller's initial value and reset (`Controller.initial`, `Controller.resetAction`) are not yet
costed and have twins in `AcornVerif.Resource.RefreshWork`. Each definition here is the executed
function with the bound proved of its costed definition as its work, and its `_costed` theorem
checks that the costed definition is within it. The updates `Controller.startStep`,
`Controller.step`, `Controller.smdpStep`, `Controller.closeStep` and `Controller.backupStep` have
bounds of their costed definitions and no adapter. A learner entry's bound reads the learner's
eligible entries, and every admitted learner has at most the capacity of its dimension
(`AcornVerif.CurrentFeatureConsumers.managed_capacity`), so the bound of an admitted entry is a
function of the capacity and the length of the feature list it reads. A controller's update
visits each of its rows, and a policy's loops visit its actions.

`Controller.creditStep` takes the taken row out of its table so that the runtime can reuse the
row's storage, and its costed definition does the same (`detachedUpdateCosted`): the taken row's
credit and second loop, then one indexed map that credits every other row. Calls of the scalar
operations that the native resource audit admits, including the bounded halving loop of
`Portable.pow`, are stretches of constant work here.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat} {count : Word.Count}

/-! ## Learner entries -/

/-- `Managed.apply` with the bound of its costed definition: the learner's record and the
entry at the learner's eligible entries. -/
def managedApply (κ : Costs) (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) : Costed (Managed config dimension) :=
  ⟨learner.apply entry permitted,
    κ .managedEntry + entryBound κ dimension.capacity learner.state.transient.eligible.size entry⟩

theorem managedApply_costed (κ : Costs) (learner : Managed config dimension)
    (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry learner.phase) :
    (learner.applyCosted entry permitted).Within κ
      (managedApply κ learner entry permitted).work := by
  unfold Managed.applyCosted
  refine Acorn.Costed.charge_within ?_
  refine (Acorn.Costed.bind_within (b := 0)
    (Acorn.Costed.attach_within (applyCosted_within κ entry learner.state)) ?_).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact Acorn.Costed.pure_within _ κ

/-- An admitted learner's entry is bounded at the capacity of its dimension. -/
theorem managedApply_work (κ : Costs) (learner : Managed config dimension)
    (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry learner.phase) :
    (managedApply κ learner entry permitted).work ≤
      κ .managedEntry + entryBound κ dimension.capacity dimension.capacity entry :=
  Nat.add_le_add_left
    (entryBound_mono κ _ (CurrentFeatureConsumers.managed_capacity learner) entry) _

/-- Bound of a row's credit: its first loop, the restart test and a possible clear. -/
abbrev creditBound (κ : Costs) (capacity : Nat) : Nat :=
  κ .managedEntry + firstLoopBound κ capacity +
    (κ .creditRestart + (κ .managedEntry + zeroBound κ capacity))

theorem creditCosted_within (κ : Costs) (learner : Managed config dimension)
    (delta vd decay : Binary32) (restart : Bool) :
    (learner.creditCosted delta vd decay restart).Within κ (creditBound κ dimension.capacity) := by
  unfold Managed.creditCosted creditBound
  refine Acorn.Costed.bind_within ((Acorn.Costed.attach_within
    (managedApply_costed κ learner (.first delta vd decay) trivial)).mono
    (managedApply_work κ learner (.first delta vd decay) trivial)) ?_
  refine Acorn.Costed.charge_within ?_
  split
  · refine (Acorn.Costed.bind_within (b := 0) ((Acorn.Costed.attach_within
      (managedApply_costed κ _ .clear trivial)).mono
        (managedApply_work κ _ .clear trivial)) ?_).mono (Nat.le_of_eq (Nat.add_zero _))
    exact Acorn.Costed.pure_within _ κ
  · exact (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _)

/-- `Managed.credit` with its bound. -/
def credit (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : Costed { result : Managed config dimension // result.phase = true } :=
  ⟨learner.credit delta vd decay restart, creditBound κ dimension.capacity⟩

theorem credit_work (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    (credit κ learner delta vd decay restart).work ≤ creditBound κ dimension.capacity :=
  Nat.le_refl _

theorem credit_costed (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    (learner.creditCosted delta vd decay restart).Within κ
      (credit κ learner delta vd decay restart).work :=
  creditCosted_within κ learner delta vd decay restart

/-! ## The shared-error controller -/

/-- Bound of the predictions of `rows` rows over `width` features. -/
abbrev predictAllBound (κ : Costs) (rows width : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows (Library.foldl.work (κ .visit) width (κ .sumTerm))

theorem predictAllCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) :
    (controller.predictAllCosted features).Within κ
      (predictAllBound κ actions features.indices.length) :=
  Acorn.Costed.mapVector_within fun learner _ =>
    linearPredictionCosted_within κ learner.state features

/-- `Controller.predictAll` with its bound. -/
def predictAll (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) : Costed (Vector Binary32 actions) :=
  ⟨controller.predictAll features, predictAllBound κ actions features.indices.length⟩

theorem predictAll_val (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) :
    (predictAll κ controller features).val = controller.predictAll features := rfl

theorem predictAll_work (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) :
    (predictAll κ controller features).work ≤
      predictAllBound κ actions features.indices.length := Nat.le_refl _

theorem predictAll_costed (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) :
    (controller.predictAllCosted features).Within κ (predictAll κ controller features).work :=
  predictAllCosted_within κ controller features

/-- Bound of a controller clear of `rows` rows. -/
abbrev clearBound (κ : Costs) (rows capacity : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows (κ .managedEntry + zeroBound κ capacity) +
    κ .controllerClose

theorem clearCosted_within (κ : Costs) (controller : Controller config dimension actions) :
    controller.clearCosted.Within κ (clearBound κ actions dimension.capacity) := by
  unfold Controller.clearCosted clearBound
  exact Acorn.Costed.bind_within (Acorn.Costed.mapVector_within fun learner _ =>
    (managedApply_costed κ learner .clear trivial).mono
      (managedApply_work κ learner .clear trivial))
    (Acorn.Costed.op_within _ _ κ)

/-- `Controller.clear` with its bound. -/
def clear (κ : Costs) (controller : Controller config dimension actions) :
    Costed (Controller config dimension actions) :=
  ⟨controller.clear, clearBound κ actions dimension.capacity⟩

theorem clear_val (κ : Costs) (controller : Controller config dimension actions) :
    (clear κ controller).val = controller.clear := rfl

theorem clear_work (κ : Costs) (controller : Controller config dimension actions) :
    (clear κ controller).work ≤ clearBound κ actions dimension.capacity := Nat.le_refl _

theorem clear_costed (κ : Costs) (controller : Controller config dimension actions) :
    controller.clearCosted.Within κ (clear κ controller).work := clearCosted_within κ controller

/-- Bound of a shared-error update of `rows` rows over `width` features: the taken row's credit
and second loop, then the indexed map at a credit for each row. -/
abbrev creditStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  creditBound κ capacity + (secondLoopBound κ width +
    (Library.mapFinIdx.work (κ .visit) rows (creditBound κ capacity) + κ .creditClose))

/-- A detached update is within the bound of its update at the element it takes. -/
theorem detachedUpdateCosted_within {α β : Type} {size : Nat} {items : Vector α size}
    {index : Fin size} {update : α → Acorn.Costed (α × β)} {κ : Costs} {bound : Nat}
    (fits : (update (items.get index)).Within κ bound) :
    (detachedUpdateCosted items index update).Within κ bound := by
  unfold detachedUpdateCosted takeOut
  dsimp only
  refine (Acorn.Costed.bind_within_all (b := 0) fits fun result => ?_).mono
    (Nat.le_of_eq (Nat.add_zero _))
  obtain ⟨_, _⟩ := result
  exact Acorn.Costed.pure_within _ κ

theorem creditStepCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (controller.creditStepCosted features action lag delta decay).Within κ
      (creditStepBound κ actions dimension.capacity features.indices.length) := by
  cases controller with
  | mk learners vOld vDelta restart =>
  unfold Controller.creditStepCosted creditStepBound
  refine Acorn.Costed.Within.mono
    (a := (creditBound κ dimension.capacity + (secondLoopBound κ features.indices.length + 0)) +
      (Library.mapFinIdx.work (κ .visit) actions (creditBound κ dimension.capacity) +
        κ .creditClose)) ?_ (by omega)
  refine Acorn.Costed.bind_within (detachedUpdateCosted_within ?_) ?_
  · refine Acorn.Costed.bind_within
      (Acorn.Costed.attach_within (creditCosted_within κ _ delta vDelta decay restart)) ?_
    exact Acorn.Costed.bind_within (Acorn.Costed.attach_within
      (learnSecondLoopCosted_within κ config _ features .zero)) (Acorn.Costed.pure_within _ κ)
  · refine Acorn.Costed.bind_within (Acorn.Costed.mapFinIdx_within fun index =>
      Acorn.Costed.ite_within (fun _ => (Acorn.Costed.pure_within _ κ).mono (Nat.zero_le _))
        fun _ => (Acorn.Costed.bind_within (b := 0)
          (creditCosted_within κ _ delta vDelta decay restart)
          (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _)))
      (Acorn.Costed.op_within _ _ κ)

/-- `Controller.creditStep` with its bound. -/
def creditStep (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) : Costed (Controller config dimension actions) :=
  ⟨controller.creditStep features action lag delta decay,
    creditStepBound κ actions dimension.capacity features.indices.length⟩

theorem creditStep_val (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (creditStep κ controller features action lag delta decay).val =
      controller.creditStep features action lag delta decay := rfl

theorem creditStep_work (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (creditStep κ controller features action lag delta decay).work ≤
      creditStepBound κ actions dimension.capacity features.indices.length := Nat.le_refl _

theorem creditStep_costed (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (controller.creditStepCosted features action lag delta decay).Within κ
      (creditStep κ controller features action lag delta decay).work :=
  creditStepCosted_within κ controller features action lag delta decay

theorem valuesStepCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (controller.valuesStepCosted features values action reward bootstrap decay).Within κ
      (κ .valuesOpen + creditStepBound κ actions dimension.capacity features.indices.length) :=
  Acorn.Costed.charge_within (creditStepCosted_within κ controller features action _ _ decay)

/-- `Controller.valuesStep` with its bound. -/
def valuesStep (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    Costed (Controller config dimension actions) :=
  ⟨controller.valuesStep features values action reward bootstrap decay,
    κ .valuesOpen + creditStepBound κ actions dimension.capacity features.indices.length⟩

theorem valuesStep_val (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (valuesStep κ controller features values action reward bootstrap decay).val =
      controller.valuesStep features values action reward bootstrap decay := rfl

theorem valuesStep_work (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (valuesStep κ controller features values action reward bootstrap decay).work ≤
      κ .valuesOpen + creditStepBound κ actions dimension.capacity features.indices.length :=
  Nat.le_refl _

theorem valuesStep_costed (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (controller.valuesStepCosted features values action reward bootstrap decay).Within κ
      (valuesStep κ controller features values action reward bootstrap decay).work :=
  valuesStepCosted_within κ controller features values action reward bootstrap decay

/-- Bound of the release of one row at a capacity. -/
abbrev releaseBound (κ : Costs) (capacity : Nat) : Nat :=
  Library.foldlArray.work (κ .visit) capacity (κ .clearRegisters) + κ .releaseClose

theorem releaseCosted_within (κ : Costs) (controller : Controller config dimension actions) :
    controller.releaseCosted.Within κ
      (Library.vectorMap.work (κ .visit) actions
        (κ .managedEntry + releaseBound κ dimension.capacity) + κ .controllerClose) := by
  unfold Controller.releaseCosted
  exact Acorn.Costed.bind_within (Acorn.Costed.mapVector_within fun learner _ =>
    (managedApply_costed κ learner .release trivial).mono
      (managedApply_work κ learner .release trivial))
    (Acorn.Costed.op_within _ _ κ)

/-- `Controller.release` with its bound. -/
def release (κ : Costs) (controller : Controller config dimension actions) :
    Costed (Controller config dimension actions) :=
  ⟨controller.release, Library.vectorMap.work (κ .visit) actions
    (κ .managedEntry + releaseBound κ dimension.capacity) + κ .controllerClose⟩

theorem release_val (κ : Costs) (controller : Controller config dimension actions) :
    (release κ controller).val = controller.release := rfl

theorem release_work (κ : Costs) (controller : Controller config dimension actions) :
    (release κ controller).work ≤
      Library.vectorMap.work (κ .visit) actions
        (κ .managedEntry + releaseBound κ dimension.capacity) + κ .controllerClose :=
  Nat.le_refl _

theorem release_costed (κ : Costs) (controller : Controller config dimension actions) :
    controller.releaseCosted.Within κ (release κ controller).work :=
  releaseCosted_within κ controller

/-- Bound of a stopping credit of `rows` rows. -/
abbrev stopBound (κ : Costs) (rows capacity : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows
    (creditBound κ capacity + (κ .managedEntry + releaseBound κ capacity)) + κ .controllerClose

theorem stopStepCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (delta : Binary32) :
    (controller.stopStepCosted delta).Within κ (stopBound κ actions dimension.capacity) := by
  cases controller with
  | mk learners vOld vDelta restart =>
  unfold Controller.stopStepCosted stopBound
  exact Acorn.Costed.bind_within (Acorn.Costed.mapVector_within fun learner _ =>
      Acorn.Costed.bind_within (creditCosted_within κ learner delta vDelta .zero restart)
        ((managedApply_costed κ _ .release trivial).mono (managedApply_work κ _ .release trivial)))
    (Acorn.Costed.op_within _ _ κ)

/-- `Controller.stopStep` with its bound. -/
def stopStep (κ : Costs) (controller : Controller config dimension actions) (delta : Binary32) :
    Costed (Controller config dimension actions) :=
  ⟨controller.stopStep delta, stopBound κ actions dimension.capacity⟩

theorem stopStep_val (κ : Costs) (controller : Controller config dimension actions)
    (delta : Binary32) : (stopStep κ controller delta).val = controller.stopStep delta := rfl

theorem stopStep_work (κ : Costs) (controller : Controller config dimension actions)
    (delta : Binary32) :
    (stopStep κ controller delta).work ≤ stopBound κ actions dimension.capacity := Nat.le_refl _

theorem stopStep_costed (κ : Costs) (controller : Controller config dimension actions)
    (delta : Binary32) :
    (controller.stopStepCosted delta).Within κ (stopStep κ controller delta).work :=
  stopStepCosted_within κ controller delta

/-- Bound of a terminal credit of `rows` rows. -/
abbrev terminalCreditBound (κ : Costs) (rows capacity : Nat) : Nat :=
  κ .learnerError + (Library.vectorMap.work (κ .visit) rows
    (κ .managedEntry + firstLoopBound κ capacity) + clearBound κ rows capacity)

theorem terminalCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) :
    (controller.terminalCosted reward).Within κ
      (terminalCreditBound κ actions dimension.capacity) := by
  cases controller with
  | mk learners vOld vDelta restart =>
  unfold Controller.terminalCosted terminalCreditBound
  exact Acorn.Costed.charge_within (Acorn.Costed.bind_within (Acorn.Costed.mapVector_within
    fun learner _ => (managedApply_costed κ learner _ trivial).mono
      (managedApply_work κ learner _ trivial)) (clearCosted_within κ _))

/-- `Controller.terminal` with its bound. -/
def terminal (κ : Costs) (controller : Controller config dimension actions) (reward : Binary32) :
    Costed (Controller config dimension actions) :=
  ⟨controller.terminal reward, terminalCreditBound κ actions dimension.capacity⟩

theorem terminal_val (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) : (terminal κ controller reward).val = controller.terminal reward := rfl

theorem terminal_work (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) :
    (terminal κ controller reward).work ≤ terminalCreditBound κ actions dimension.capacity :=
  Nat.le_refl _

theorem terminal_costed (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) :
    (controller.terminalCosted reward).Within κ (terminal κ controller reward).work :=
  terminalCosted_within κ controller reward

theorem retireCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) :
    (controller.retireCosted feature).Within κ
      (Library.vectorMap.work (κ .visit) actions (κ .managedEntry +
        (κ .retire + Library.findIdx.work (κ .visit) dimension.capacity (κ .compare))) +
        κ .controllerClose) := by
  cases controller with
  | mk learners vOld vDelta restart =>
  unfold Controller.retireCosted
  exact Acorn.Costed.bind_within (Acorn.Costed.mapVector_within fun learner _ =>
      (managedApply_costed κ learner (.retire feature) trivial).mono
        (managedApply_work κ learner (.retire feature) trivial))
    (Acorn.Costed.op_within _ _ κ)

/-- `Controller.retire` with its bound. -/
def retire (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) : Costed (Controller config dimension actions) :=
  ⟨controller.retire feature,
    Library.vectorMap.work (κ .visit) actions (κ .managedEntry +
      (κ .retire + Library.findIdx.work (κ .visit) dimension.capacity (κ .compare))) +
      κ .controllerClose⟩

theorem retire_val (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) :
    (retire κ controller feature).val = controller.retire feature := rfl

theorem retire_work (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) :
    (retire κ controller feature).work ≤
      Library.vectorMap.work (κ .visit) actions (κ .managedEntry +
        (κ .retire + Library.findIdx.work (κ .visit) dimension.capacity (κ .compare))) +
        κ .controllerClose := Nat.le_refl _

theorem retire_costed (κ : Costs) (controller : Controller config dimension actions)
    (feature : FeatIdx dimension) :
    (controller.retireCosted feature).Within κ (retire κ controller feature).work :=
  retireCosted_within κ controller feature

theorem planCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (action : Action actions) (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    (controller.planCosted action features target).Within κ
      (planBound κ features.indices.length + κ .planClose) := by
  unfold Controller.planCosted
  exact Acorn.Costed.bind_within (Acorn.Costed.attach_within
    (planStepCosted_within κ config _ features target)) (Acorn.Costed.op_within _ _ κ)

/-- `Controller.plan` with its bound. -/
def plan (κ : Costs) (controller : Controller config dimension actions) (action : Action actions)
    (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    Costed (Controller config dimension actions × Binary32) :=
  ⟨controller.plan action features target, planBound κ features.indices.length + κ .planClose⟩

theorem plan_val (κ : Costs) (controller : Controller config dimension actions)
    (action : Action actions) (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    (plan κ controller action features target).val = controller.plan action features target := rfl

theorem plan_work (κ : Costs) (controller : Controller config dimension actions)
    (action : Action actions) (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    (plan κ controller action features target).work ≤
      planBound κ features.indices.length + κ .planClose := Nat.le_refl _

theorem plan_costed (κ : Costs) (controller : Controller config dimension actions)
    (action : Action actions) (features : SwiftTd.ActiveSet dimension) (target : Binary32) :
    (controller.planCosted action features target).Within κ
      (plan κ controller action features target).work :=
  planCosted_within κ controller action features target

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

Each definition below is the executed function with the bound proved of its costed definition as
its work, and its `_costed` theorem checks that the costed definition is within it. -/

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

theorem snapshotCosted_within (κ : Costs)
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    (controller.snapshotCosted features epsilon).Within κ
      (predictAllBound κ count.word.toNat features.indices.length + κ .snapshot) := by
  unfold Controller.snapshotCosted
  exact Acorn.Costed.bind_within (predictAllCosted_within κ controller features)
    (Acorn.Costed.op_within _ _ κ)

/-- `Controller.snapshot` with its bound. -/
def snapshot (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    Costed (PolicySnapshot count) :=
  ⟨controller.snapshot features epsilon,
    predictAllBound κ count.word.toNat features.indices.length + κ .snapshot⟩

theorem snapshot_val (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    (snapshot κ controller features epsilon).val = controller.snapshot features epsilon := rfl

theorem snapshot_work (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    (snapshot κ controller features epsilon).work ≤
      predictAllBound κ count.word.toNat features.indices.length + κ .snapshot := Nat.le_refl _

theorem snapshot_costed (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    (controller.snapshotCosted features epsilon).Within κ
      (snapshot κ controller features epsilon).work :=
  snapshotCosted_within κ controller features epsilon

/-- Bound of a frozen-decision credit of `rows` rows over `width` features. -/
abbrev policyStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  κ .policyOpen + (κ .valuesOpen + creditStepBound κ rows capacity width)

theorem policyStepCosted_within (κ : Costs)
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    (controller.policyStepCosted features decision reward duration).Within κ
      (policyStepBound κ count.word.toNat dimension.capacity features.indices.length) :=
  Acorn.Costed.charge_within (valuesStepCosted_within κ controller features _ _ reward _ _)

/-- `Controller.policyStep` with its bound. -/
def policyStep (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    Costed (Controller config dimension count.word.toNat) :=
  ⟨controller.policyStep features decision reward duration,
    policyStepBound κ count.word.toNat dimension.capacity features.indices.length⟩

theorem policyStep_val (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    (policyStep κ controller features decision reward duration).val =
      controller.policyStep features decision reward duration := rfl

theorem policyStep_work (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    (policyStep κ controller features decision reward duration).work ≤
      policyStepBound κ count.word.toNat dimension.capacity features.indices.length :=
  Nat.le_refl _

theorem policyStep_costed (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    (controller.policyStepCosted features decision reward duration).Within κ
      (policyStep κ controller features decision reward duration).work :=
  policyStepCosted_within κ controller features decision reward duration

theorem persistentStepCosted_within (κ : Costs)
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    (controller.persistentStepCosted features snapshot drawn reward duration).Within κ
      (policyStepBound κ count.word.toNat dimension.capacity features.indices.length) :=
  Acorn.Costed.charge_within (valuesStepCosted_within κ controller features _ _ reward _ _)

/-- `Controller.persistentStep` with its bound. -/
def persistentStep (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    Costed (Controller config dimension count.word.toNat) :=
  ⟨controller.persistentStep features snapshot drawn reward duration,
    policyStepBound κ count.word.toNat dimension.capacity features.indices.length⟩

theorem persistentStep_val (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    (persistentStep κ controller features snapshot drawn reward duration).val =
      controller.persistentStep features snapshot drawn reward duration := rfl

theorem persistentStep_work (κ : Costs) (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    (persistentStep κ controller features snapshot drawn reward duration).work ≤
      policyStepBound κ count.word.toNat dimension.capacity features.indices.length :=
  Nat.le_refl _

theorem persistentStep_costed (κ : Costs)
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    (controller.persistentStepCosted features snapshot drawn reward duration).Within κ
      (persistentStep κ controller features snapshot drawn reward duration).work :=
  persistentStepCosted_within κ controller features snapshot drawn reward duration

/-- Bound of a normalized step-size sum over `size` eligible entries. -/
abbrev normalizedBound (κ : Costs) (size : Nat) : Nat :=
  Library.toList.control (κ .visit) size +
    (Library.map.work (κ .visit) size (κ .normalizedTerm)) +
    Library.foldl.work (κ .visit) size (κ .sumTerm) + κ .normalizedOpen

theorem normalizedStepSizeSumCosted_within (κ : Costs) (state : NumericState config dimension) :
    state.normalizedStepSizeSumCosted.Within κ
      (normalizedBound κ state.transient.eligible.size) := by
  unfold NumericState.normalizedStepSizeSumCosted normalizedBound
  split
  · exact (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _)
  · refine Acorn.Costed.Within.mono
      (a := Library.toList.control (κ .visit) state.transient.eligible.size +
        (Library.map.work (κ .visit) state.transient.eligible.size (κ .normalizedTerm) +
          (Library.foldl.work (κ .visit) state.transient.eligible.size (κ .sumTerm) +
            κ .normalizedOpen))) ?_ (by omega)
    refine Acorn.Costed.bind_within (Acorn.Costed.arrayToList_within _ κ) ?_
    refine Acorn.Costed.bind_within
      ((Acorn.Costed.map_within fun _ _ => Acorn.Costed.op_within _ _ κ).mono ?_) ?_
    · simp [Acorn.Costed.arrayToList_val]
    refine Acorn.Costed.bind_within ((sumFromCosted_within κ _ _).mono ?_)
      (Acorn.Costed.op_within _ _ κ)
    simp [Acorn.Costed.map_val, Acorn.Costed.arrayToList_val]

/-- `NumericState.normalizedStepSizeSum` with its bound. -/
def normalizedStepSizeSum (κ : Costs) (state : NumericState config dimension) :
    Costed (Binary32 × Nat) :=
  ⟨state.normalizedStepSizeSum, normalizedBound κ state.transient.eligible.size⟩

theorem normalizedStepSizeSum_val (κ : Costs) (state : NumericState config dimension) :
    (normalizedStepSizeSum κ state).val = state.normalizedStepSizeSum := rfl

theorem normalizedStepSizeSum_work (κ : Costs) (state : NumericState config dimension) :
    (normalizedStepSizeSum κ state).work ≤ normalizedBound κ state.transient.eligible.size :=
  Nat.le_refl _

theorem normalizedStepSizeSum_costed (κ : Costs) (state : NumericState config dimension) :
    state.normalizedStepSizeSumCosted.Within κ (normalizedStepSizeSum κ state).work :=
  normalizedStepSizeSumCosted_within κ state

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

theorem exploreRateCosted_within (κ : Costs)
    (controller : Controller config dimension count.word.toNat) :
    controller.exploreRateCosted.Within κ (rateBound κ count.word.toNat dimension.capacity) := by
  unfold Controller.exploreRateCosted rateBound
  refine Acorn.Costed.Within.mono
    (a := Library.toList.control (κ .visit) count.word.toNat +
      (Library.foldl.work (κ .visit) count.word.toNat (normalizedBound κ dimension.capacity +
        κ .rateTerm) + κ .rateClose)) ?_ (by omega)
  refine Acorn.Costed.bind_within (Acorn.Costed.toList_within _ κ) ?_
  refine Acorn.Costed.bind_within ((Acorn.Costed.foldl_within
    (bound := normalizedBound κ dimension.capacity + κ .rateTerm) fun acc learner _ => ?_).mono ?_)
    (Acorn.Costed.op_within _ _ κ)
  · obtain ⟨_, _⟩ := acc
    exact Acorn.Costed.bind_within ((normalizedStepSizeSumCosted_within κ learner.state).mono
      (normalizedBound_mono κ (CurrentFeatureConsumers.managed_capacity learner)))
      (Acorn.Costed.op_within _ _ κ)
  · simp [Acorn.Costed.toList_val]

/-- `Controller.exploreRate` with its bound. -/
def exploreRate (κ : Costs) (controller : Controller config dimension count.word.toNat) :
    Costed SwiftTd.ExploreRate :=
  ⟨controller.exploreRate, rateBound κ count.word.toNat dimension.capacity⟩

theorem exploreRate_val (κ : Costs) (controller : Controller config dimension count.word.toNat) :
    (exploreRate κ controller).val = controller.exploreRate := rfl

theorem exploreRate_work (κ : Costs) (controller : Controller config dimension count.word.toNat) :
    (exploreRate κ controller).work ≤ rateBound κ count.word.toNat dimension.capacity :=
  Nat.le_refl _

theorem exploreRate_costed (κ : Costs) (controller : Controller config dimension count.word.toNat) :
    controller.exploreRateCosted.Within κ (exploreRate κ controller).work :=
  exploreRateCosted_within κ controller

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

/-! ## The controllers' remaining updates -/

/-- Bound of a trajectory's start at `rows` rows, a capacity and `width` features. -/
abbrev startStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  (Library.vectorMap.work (κ .visit) rows (κ .managedEntry + releaseBound κ capacity) +
    κ .controllerClose) + creditStepBound κ rows capacity width

theorem startStepCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (lag : Binary32) :
    (controller.startStepCosted features action lag).Within κ
      (startStepBound κ actions dimension.capacity features.indices.length) :=
  Acorn.Costed.bind_within (releaseCosted_within κ controller)
    (creditStepCosted_within κ _ features action lag .zero .zero)

/-- Bound of a primitive continuing update or a duration credit at `rows` rows, a capacity and
`width` features. -/
abbrev controllerStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  predictAllBound κ rows width + ((κ .valuesOpen + creditStepBound κ rows capacity width) + 0)

theorem controllerStepCosted_within (κ : Costs)
    (controller : Controller config dimension actions) (features : SwiftTd.ActiveSet dimension)
    (action : Action actions) (reward : Binary32) :
    (controller.stepCosted features action reward).Within κ
      (controllerStepBound κ actions dimension.capacity features.indices.length) :=
  Acorn.Costed.bind_within (predictAllCosted_within κ controller features)
    (Acorn.Costed.bind_within (valuesStepCosted_within κ controller features _ action reward _ _)
      (Acorn.Costed.pure_within _ κ))

theorem smdpStepCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (reward : Binary32)
    (duration : UInt32) :
    (controller.smdpStepCosted features action reward duration).Within κ
      (controllerStepBound κ actions dimension.capacity features.indices.length) :=
  Acorn.Costed.bind_within (predictAllCosted_within κ controller features)
    (Acorn.Costed.bind_within (valuesStepCosted_within κ controller features _ action reward _ _)
      (Acorn.Costed.pure_within _ κ))

theorem closeStepCosted_within (κ : Costs) (controller : Controller config dimension actions)
    (reward continuation : Binary32) (duration : UInt32) :
    (controller.closeStepCosted reward continuation duration).Within κ
      (κ .learnerError + stopBound κ actions dimension.capacity) :=
  Acorn.Costed.charge_within (stopStepCosted_within κ controller _)

/-- Bound of a tree-backup error over `size` values. -/
abbrev backupErrorBound (κ : Costs) (size : Nat) : Nat :=
  expectedBound κ size + κ .learnerError

theorem backupErrorCosted_within (κ : Costs)
    (controller : Controller config dimension count.word.toNat) (snapshot : PolicySnapshot count)
    (reward : Binary32) :
    (controller.backupErrorCosted snapshot reward).Within κ
      (backupErrorBound κ count.word.toNat) :=
  Acorn.Costed.bind_within (expectedCosted_within κ snapshot) (Acorn.Costed.op_within _ _ κ)

/-- Bound of one action's nominal mass over `size` values. -/
abbrev massBound (κ : Costs) (size : Nat) : Nat :=
  probabilitiesBound κ size + κ .probability

theorem massCosted_within (κ : Costs) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) :
    (snapshot.massCosted action).Within κ (massBound κ count.word.toNat) :=
  Acorn.Costed.bind_within (probabilitiesCosted_within κ snapshot) (Acorn.Costed.op_within _ _ κ)

/-- Bound of a tree-backup credit over `size` values, at `rows` rows, a capacity and `width`
features. -/
abbrev backupStepBound (κ : Costs) (size rows capacity width : Nat) : Nat :=
  backupErrorBound κ size + (massBound κ size + creditStepBound κ rows capacity width)

theorem backupStepCosted_within (κ : Costs)
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) (reward : Binary32) :
    (controller.backupStepCosted features snapshot action reward).Within κ
      (backupStepBound κ count.word.toNat count.word.toNat dimension.capacity
        features.indices.length) :=
  Acorn.Costed.bind_within (backupErrorCosted_within κ controller snapshot reward)
    (Acorn.Costed.bind_within (massCosted_within κ snapshot action)
      (creditStepCosted_within κ controller features action _ _ _))

end AcornVerif.Resource.Twin
