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

Twins of `Managed.apply`, the shared-error controller of `Acorn.Sarsa` and the policies of
`Acorn.Policy` and `Acorn.Exploration`. A learner entry's bound reads the learner's
eligible entries, and every admitted learner has at most the capacity of its dimension
(`AcornVerif.CurrentFeatureConsumers.managed_capacity`), so the bound of an admitted entry
is a function of the capacity and the length of the feature list it reads. A
controller's update visits each of its rows, and a policy's loops visit its actions.

Where an executed definition takes a row out of its table so that the runtime can reuse
the row's storage (`detachedUpdate`), the twin follows the listed composition the
repository proves equal to it (`Controller.creditStep_eq`, `Controller.stopStep_eq`,
`Controller.terminal_eq`): both compositions make the same learner entries on the same
rows. Calls of the scalar operations that the native resource audit admits, including
the bounded halving loop of `Portable.pow`, are stretches of constant work here.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat} {count : Word.Count}

/-! ## Learner entries -/

/-- Twin of `Managed.apply`: the executed learner, with the work of its entry. -/
def managedApply (κ : Costs) (learner : Managed config dimension) (entry : SwiftTd.Entry dimension)
    (permitted : SwiftTd.Permitted entry learner.phase) : Costed (Managed config dimension) :=
  Costed.via (learner.apply entry permitted) (entryApply κ entry learner.state)

/-- The entry's twin computes the learner's executed state. -/
theorem managedApply_run (κ : Costs) (learner : Managed config dimension)
    (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry learner.phase) :
    (entryApply κ entry learner.state).val = (learner.apply entry permitted).state :=
  entryApply_val κ entry learner.state

/-- An admitted learner's entry is bounded at the capacity of its dimension. -/
theorem managedApply_work (κ : Costs) (learner : Managed config dimension)
    (entry : SwiftTd.Entry dimension) (permitted : SwiftTd.Permitted entry learner.phase) :
    (managedApply κ learner entry permitted).work ≤
      entryBound κ dimension.capacity dimension.capacity entry :=
  Nat.le_trans (entryApply_work κ entry learner.state)
    (entryBound_mono κ _ (CurrentFeatureConsumers.managed_capacity learner) entry)

/-- The costed composition of `Managed.credit`: a first loop, then a clear on a pending
restart. -/
def creditRun (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : Costed (Managed config dimension) := do
  let credited ← managedApply κ learner (.first delta vd decay) trivial
  Costed.ite (restart = true) (managedApply κ credited .clear trivial) (Costed.pure credited)

theorem creditRun_val (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    (creditRun κ learner delta vd decay restart).val =
      (learner.credit delta vd decay restart).val := by
  cases restart <;> rfl

/-- Twin of `Managed.credit`. -/
def credit (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : Costed { result : Managed config dimension // result.phase = true } :=
  Costed.via (learner.credit delta vd decay restart) (creditRun κ learner delta vd decay restart)

/-- Bound of a row's credit: its first loop and a possible clear. -/
abbrev creditBound (κ : Costs) (capacity : Nat) : Nat :=
  firstLoopBound κ capacity + zeroBound κ capacity

theorem credit_work (κ : Costs) (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    (credit κ learner delta vd decay restart).work ≤ creditBound κ dimension.capacity :=
  Costed.bind_work_le (managedApply_work κ learner (.first delta vd decay) trivial) fun credited =>
    Nat.le_trans (Costed.ite_work_le _ _ _)
      (Nat.max_le.mpr ⟨managedApply_work κ credited .clear trivial, Nat.zero_le _⟩)

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
  Library.vectorMap.work (κ .visit) rows (zeroBound κ capacity) + κ .controllerClose

theorem clear_work (κ : Costs) (controller : Controller config dimension actions) :
    (clear κ controller).work ≤ clearBound κ actions dimension.capacity :=
  Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ => managedApply_work κ learner .clear trivial)
    fun _ => Nat.le_refl _

/-- Twin of `Controller.creditStep`, in the listed composition of `Controller.creditStep_eq`:
every row's credit, then the taken row's second loop. -/
def creditStep (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) : Costed (Controller config dimension actions) := do
  let rows ← Costed.mapVector (κ .visit)
    (fun learner => credit κ learner delta controller.vDelta decay controller.restartPending)
    controller.learners
  let chosen := rows.get action
  Costed.bind (secondLoop κ config chosen.val.state features .zero) fun _ =>
    let second := chosen.val.state.learnSecondLoop config features .zero
    Costed.op (κ .creditClose)
      ⟨(rows.map Subtype.val).set action.val
          ⟨second.1, false,
            .transition (.second features .zero) chosen.property chosen.val.admitted⟩
          action.isLt, lag, second.2, false⟩

theorem creditStep_val (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (creditStep κ controller features action lag delta decay).val =
      controller.creditStep features action lag delta decay := by
  rw [Controller.creditStep_eq]
  rfl

/-- Bound of a shared-error update of `rows` rows over `width` features. -/
abbrev creditStepBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows (creditBound κ capacity) +
    (secondLoopBound κ width + κ .creditClose)

theorem creditStep_work (κ : Costs) (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    (creditStep κ controller features action lag delta decay).work ≤
      creditStepBound κ actions dimension.capacity features.indices.length :=
  Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ =>
      credit_work κ learner delta controller.vDelta decay controller.restartPending)
    fun _ => Costed.bind_work_le (secondLoop_work κ config _ features .zero) fun _ =>
      Nat.le_refl _

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
      Library.vectorMap.work (κ .visit) actions (releaseBound κ dimension.capacity) +
        κ .controllerClose :=
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
  Library.vectorMap.work (κ .visit) rows (creditBound κ capacity + releaseBound κ capacity) +
    κ .controllerClose

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
each row's first loop, then the controller's clear. -/
def terminal (κ : Costs) (controller : Controller config dimension actions) (reward : Binary32) :
    Costed (Controller config dimension actions) := do
  let credited ← Costed.mapVector (κ .visit)
    (fun learner => managedApply κ learner
      (.first (reward.sub controller.vOld) controller.vDelta controller.traceDecay) trivial)
    controller.learners
  clear κ (Controller.mk credited controller.vOld controller.vDelta controller.restartPending)

theorem terminal_val (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) : (terminal κ controller reward).val = controller.terminal reward := by
  rw [Controller.terminal_eq]
  rfl

/-- Bound of a terminal credit of `rows` rows. -/
abbrev terminalCreditBound (κ : Costs) (rows capacity : Nat) : Nat :=
  Library.vectorMap.work (κ .visit) rows (firstLoopBound κ capacity) + clearBound κ rows capacity

theorem terminal_work (κ : Costs) (controller : Controller config dimension actions)
    (reward : Binary32) :
    (terminal κ controller reward).work ≤ terminalCreditBound κ actions dimension.capacity :=
  Costed.bind_work_le
    (Costed.mapVector_work_le _ _ _ _ fun learner _ => managedApply_work κ learner
      (.first (reward.sub controller.vOld) controller.vDelta controller.traceDecay) trivial)
    fun _ => clear_work κ _

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
      Library.vectorMap.work (κ .visit) actions
        (κ .retire + Library.findIdx.work (κ .visit) dimension.capacity (κ .compare)) +
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

/-- Twin of `PolicySnapshot.best`: the values listed, then one comparison for each. -/
def best (κ : Costs) (snapshot : PolicySnapshot count) : Costed Binary32 := do
  let values ← Costed.scanVector .toList (κ .visit) snapshot.values snapshot.values.toList
  Costed.foldl (κ .visit)
    (fun best value => Costed.op (κ .compare) (if best.Less value then value else best))
    (snapshot.values.get (firstAction count)) (values.drop 1)

theorem best_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (best κ snapshot).val = snapshot.best := rfl

/-- Bound of an ordered maximum over `size` values. -/
abbrev bestBound (κ : Costs) (size : Nat) : Nat :=
  Library.toList.control (κ .visit) size + Library.foldl.work (κ .visit) size (κ .compare)

theorem best_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (best κ snapshot).work ≤ bestBound κ count.word.toNat := by
  unfold best
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _)
    (Costed.foldl_work_le (κ .visit) (κ .compare) _ _ _ fun _ _ _ => Nat.le_refl _)) ?_
  have shorter := Library.foldl.work_mono (visit := κ .visit) (Nat.sub_le count.word.toNat 1)
    (Nat.le_refl (κ .compare))
  simp only [List.length_drop, Vector.length_toList, bestBound]
  omega

/-- Twin of `PolicySnapshot.candidates`: the maximum, the action list, then one test for
each action. -/
def candidates (κ : Costs) (snapshot : PolicySnapshot count) :
    Costed (List (Action count.word.toNat)) := do
  let top ← best κ snapshot
  let threshold := top.sub tieWindow
  let range ← Costed.scanList .finRange (κ .visit) (List.finRange count.word.toNat)
    (List.finRange count.word.toNat)
  Costed.scanList .filter (κ .visit + κ .candidate) range
    (range.filter fun action => decide (threshold.LessOrEqual (snapshot.values.get action)))

theorem candidates_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (candidates κ snapshot).val = snapshot.candidates := rfl

/-- Bound of the near-maximum candidates over `size` values. -/
abbrev candidatesBound (κ : Costs) (size : Nat) : Nat :=
  bestBound κ size + (Library.finRange.control (κ .visit) size +
    Library.filter.control (κ .visit + κ .candidate) size)

theorem candidates_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (candidates κ snapshot).work ≤ candidatesBound κ count.word.toNat := by
  have top := best_work κ snapshot
  simp only [candidates, Costed.bind_work, List.length_finRange, candidatesBound]
  omega

theorem candidates_length (snapshot : PolicySnapshot count) :
    snapshot.candidates.length ≤ count.word.toNat := by
  have filtered := List.length_filter_le
    (fun action => decide ((snapshot.best.sub tieWindow).LessOrEqual (snapshot.values.get action)))
    (List.finRange count.word.toNat)
  simpa only [PolicySnapshot.candidates, List.length_finRange] using filtered

/-- The costed recursion of `reservoir`, by the same recursion: one draw for each pending
candidate, and a visit for its end. -/
def reservoirRun (κ : Costs) : List (Action actions) → UInt64 → Action actions →
    Rng.Xoshiro256 → Costed (Action actions × Rng.Xoshiro256)
  | [], _, pick, rng => Costed.op (κ .visit) (pick, rng)
  | action :: rest, seen, pick, rng =>
    let seen := seen + 1
    let draw := rng.nextBelow (Word.Count.ofWord seen)
    Costed.charge (κ .visit + κ .reservoirDraw)
      (reservoirRun κ rest seen (if draw.1.val == 0 then action else pick) draw.2)

theorem reservoirRun_val (κ : Costs) (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoirRun κ pending seen pick rng).val = reservoir pending seen pick rng := by
  induction pending generalizing seen pick rng with
  | nil => rfl
  | cons action rest ih =>
    rw [reservoirRun, reservoir]
    exact ih _ _ _

theorem reservoirRun_work (κ : Costs) (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoirRun κ pending seen pick rng).work ≤
      pass (κ .visit) pending.length (κ .reservoirDraw) := by
  induction pending generalizing seen pick rng with
  | nil => simp [reservoirRun]
  | cons action rest ih =>
    have restBound := ih (seen + 1)
      (if (rng.nextBelow (Word.Count.ofWord (seen + 1))).1.val == 0 then action else pick)
      (rng.nextBelow (Word.Count.ofWord (seen + 1))).2
    simp only [reservoirRun, Costed.charge, pass, List.length_cons, Nat.succ_mul] at restBound ⊢
    omega

/-- Twin of `PolicySnapshot.greedy`. -/
def greedy (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (Action count.word.toNat × Rng.Xoshiro256) := do
  let pending ← candidates κ snapshot
  Costed.via (reservoir pending 0 (firstAction count) rng)
    (reservoirRun κ pending 0 (firstAction count) rng)

theorem greedy_val (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (greedy κ snapshot rng).val = snapshot.greedy rng := rfl

/-- Bound of a greedy draw over `size` values. -/
abbrev greedyBound (κ : Costs) (size : Nat) : Nat :=
  candidatesBound κ size + pass (κ .visit) size (κ .reservoirDraw)

theorem greedy_work (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (greedy κ snapshot rng).work ≤ greedyBound κ count.word.toNat :=
  Costed.bind_work_le_at (candidates_work κ snapshot)
    (Nat.le_trans (reservoirRun_work κ _ 0 _ rng)
      (pass_mono (candidates_length snapshot) (Nat.le_refl _)))

/-- Twin of `PolicySnapshot.probabilities`: the candidates and their count, the maximum,
then one mass for each action. -/
def probabilities (κ : Costs) (snapshot : PolicySnapshot count) :
    Costed (Vector Binary32 count.word.toNat) := do
  let pending ← candidates κ snapshot
  let size ← Costed.scanList .length (κ .visit) pending pending.length
  let top ← best κ snapshot
  let explore := snapshot.epsilon.value.div (Binary32.ofUInt64 count.word)
  let greedy := (Binary32.one.sub snapshot.epsilon.value).div (Binary32.ofUInt64 size.toUInt64)
  let threshold := top.sub tieWindow
  Costed.charge (κ .probabilitiesOpen)
    (Costed.mapVector (κ .visit)
      (fun value => Costed.op (κ .probability)
        (explore.add (if threshold.LessOrEqual value then greedy else .zero)))
      snapshot.values)

theorem probabilities_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (probabilities κ snapshot).val = snapshot.probabilities := rfl

/-- Bound of the nominal masses over `size` values. -/
abbrev probabilitiesBound (κ : Costs) (size : Nat) : Nat :=
  candidatesBound κ size + Library.length.control (κ .visit) size + bestBound κ size +
    κ .probabilitiesOpen +
    Library.vectorMap.work (κ .visit) size (κ .probability)

theorem probabilities_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (probabilities κ snapshot).work ≤ probabilitiesBound κ count.word.toNat := by
  have size := Library.length.control_mono (visit := κ .visit) (candidates_length snapshot)
  unfold probabilities
  refine Nat.le_trans (Costed.bind_work_le_at (candidates_work κ snapshot)
    (Costed.bind_work_le_at (Nat.le_refl _)
      (Costed.bind_work_le (best_work κ snapshot) fun _ =>
        Nat.add_le_add_left (Costed.mapVector_work_le (κ .visit) (κ .probability) _
          snapshot.values fun _ _ => Nat.le_refl _) (κ .probabilitiesOpen)))) ?_
  simp only [candidates_val, probabilitiesBound]
  omega

/-- The costed composition of `PolicySnapshot.draw`: the branch draw, then the uniform or
the greedy draw. -/
def drawRun (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (Action count.word.toNat × Rng.Xoshiro256) :=
  let branch := rng.nextF64
  let explored := branch.1.less (Conversion.widen snapshot.epsilon.value)
  Costed.charge (κ .drawClose)
    (Costed.ite (explored = true) (Costed.op (κ .uniform) (uniformAction count branch.2))
      (greedy κ snapshot branch.2))

theorem drawRun_val (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (drawRun κ snapshot rng).val = ((snapshot.draw rng).1.action, (snapshot.draw rng).2) := by
  simp only [drawRun, Costed.charge, PolicySnapshot.draw]
  split <;> rfl

/-- Twin of `PolicySnapshot.draw`. -/
def draw (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (PolicyDecision count × Rng.Xoshiro256) :=
  Costed.via (snapshot.draw rng) (drawRun κ snapshot rng)

theorem draw_work (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (draw κ snapshot rng).work ≤
      κ .drawClose + max (κ .uniform) (greedyBound κ count.word.toNat) :=
  Nat.add_le_add_left (Nat.le_trans (Costed.ite_work_le _ _ _)
    (Costed.max_le_max (Nat.le_refl _) (greedy_work κ snapshot _))) _

/-- Twin of `PolicySnapshot.drawPersistent`: a run begun, or the greedy draw, and the
nominal masses. -/
def drawPersistent (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (PersistentDecision count × Rng.Xoshiro256) :=
  let begun := beginExploration count snapshot.epsilon rng
  Costed.charge (κ .explorationBegin) <|
  match begun.1 with
  | some run => do
    let masses ← probabilities κ snapshot
    Costed.pure (⟨run.action, true, some run, masses⟩, begun.2)
  | none => do
    let chosen ← greedy κ snapshot begun.2
    let masses ← probabilities κ snapshot
    Costed.pure (⟨chosen.1, false, none, masses⟩, chosen.2)

theorem drawPersistent_val (κ : Costs) (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (drawPersistent κ snapshot rng).val = snapshot.drawPersistent rng := by
  cases begun : (beginExploration count snapshot.epsilon rng).1 <;>
    simp only [drawPersistent, PolicySnapshot.drawPersistent, Costed.charge, begun] <;> rfl

/-- Bound of a persistent draw over `size` values. -/
abbrev persistentBound (κ : Costs) (size : Nat) : Nat :=
  κ .explorationBegin + (greedyBound κ size + probabilitiesBound κ size)

theorem drawPersistent_work (κ : Costs) (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    (drawPersistent κ snapshot rng).work ≤ persistentBound κ count.word.toNat := by
  have masses := probabilities_work κ snapshot
  have chosen := greedy_work κ snapshot (beginExploration count snapshot.epsilon rng).2
  cases begun : (beginExploration count snapshot.epsilon rng).1 <;>
    simp only [drawPersistent, Costed.charge, begun, Costed.bind_work, Costed.pure,
      persistentBound] <;> omega

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

/-- Twin of `PolicySnapshot.expected`: the lower bound, the maximum and the totals, each a
pass over the values. -/
def expected (κ : Costs) (snapshot : PolicySnapshot count) : Costed Binary32 := do
  let first := snapshot.values.get (firstAction count)
  let lows ← Costed.scanVector .toList (κ .visit) snapshot.values snapshot.values.toList
  let lower ← Costed.foldl (κ .visit)
    (fun lo value => Costed.op (κ .compare) (if value.less lo then value else lo)) first lows
  let upper ← best κ snapshot
  let threshold := upper.sub tieWindow
  let values ← Costed.scanVector .toList (κ .visit) snapshot.values snapshot.values.toList
  let totals ← Costed.foldl (κ .visit)
    (fun (all, tied, n) value => Costed.op (κ .expectedTerm)
      (all.add (Conversion.widen value),
        if threshold.lessOrEqual value then tied.add (Conversion.widen value) else tied,
        if threshold.lessOrEqual value then n + 1 else n))
    (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0) values
  let eps := Conversion.widen snapshot.epsilon.value
  let value := ((Binary64.ofUInt64 1).sub eps).mul
    (totals.2.1.div (Binary64.ofUInt64 totals.2.2.toUInt64))
  let value := value.add (eps.mul (totals.1.div (Binary64.ofUInt64 count.word)))
  Costed.op (κ .expectedClose) ((Conversion.narrow value).saturate lower upper)

theorem expected_val (κ : Costs) (snapshot : PolicySnapshot count) :
    (expected κ snapshot).val = snapshot.expected := rfl

/-- Bound of a policy mean over `size` values. -/
abbrev expectedBound (κ : Costs) (size : Nat) : Nat :=
  Library.toList.control (κ .visit) size + Library.foldl.work (κ .visit) size (κ .compare) +
    bestBound κ size + Library.toList.control (κ .visit) size +
    Library.foldl.work (κ .visit) size (κ .expectedTerm) + κ .expectedClose

theorem expected_work (κ : Costs) (snapshot : PolicySnapshot count) :
    (expected κ snapshot).work ≤ expectedBound κ count.word.toNat := by
  unfold expected
  refine Nat.le_trans (Costed.bind_work_le_at (Nat.le_refl _) (Costed.bind_work_le_at
    (Costed.foldl_work_le (κ .visit) (κ .compare) _ _ _ fun _ _ _ => Nat.le_refl _)
    (Costed.bind_work_le_at (best_work κ snapshot) (Costed.bind_work_le_at (Nat.le_refl _)
      (Costed.bind_work_le_at (Costed.foldl_work_le (κ .visit) (κ .expectedTerm) _ _ _
        fun acc _ _ => ?_) (Nat.le_refl _)))))) ?_
  · obtain ⟨all, tied, n⟩ := acc
    exact Nat.le_refl _
  · simp only [Vector.length_toList, expectedBound]
    omega

/-- Twin of `servedProbabilities`: one mass for each action. -/
def servedProbabilities (κ : Costs) (action : Action count.word.toNat) :
    Costed (Vector Binary32 count.word.toNat) :=
  Costed.ofFn (κ .visit) fun query => Costed.op (κ .read) (if query = action then .one else .zero)

theorem servedProbabilities_val (κ : Costs) (action : Action count.word.toNat) :
    (servedProbabilities κ action).val = Features.servedProbabilities action := rfl

theorem servedProbabilities_work (κ : Costs) (action : Action count.word.toNat) :
    (servedProbabilities κ action).work ≤ Library.ofFn.work (κ .visit) count.word.toNat (κ .read) :=
  Costed.ofFn_work_le _ _ _ fun _ => Nat.le_refl _

end AcornVerif.Resource.Twin
