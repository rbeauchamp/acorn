/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.SwiftTd
import AcornVerif.Resource.Work
import AcornVerif.Resource.Sites

/-!
# Work of the SwiftTD learner

Twins of the executed learner operations of `Acorn.SwiftTd`. Each twin's value is the
executed operation's (`_val`), and its work is bounded by the number of eligible
entries of the learner it receives and the length of the feature list it reads
(`_work`). No bound here depends on the learner's values: the first loop visits each
eligible entry once whether it prunes it or not, and a release and a retirement scan
the eligible list once.

The second loop pushes at most one index for each feature it visits, so a learner's
eligible list can grow during a step; the bounds of a step read the sizes of the state
each loop receives, and a caller bounds those by the learner's admission
(`AcornVerif.managed_capacity`).
-/

namespace AcornVerif.Resource.Twin

open Acorn
open Acorn.SwiftTd (ActiveSet swapRemove TdStep)

variable {config : Acorn.Config} {dimension : Dimension} {α : Type}

/-! ## Ordered sums -/

/-- Twin of `Binary32.sumMap`: one visit and one term for each value. -/
def sumMap (κ : Costs) (term : Site) (initial : Binary32) (values : List α)
    (read : α → Binary32) : Costed Binary32 :=
  Costed.foldl (κ .visit) (fun total value => Costed.op (κ term) (total.add (read value)))
    initial values

theorem sumMap_val (κ : Costs) (term : Site) (initial : Binary32) (values : List α)
    (read : α → Binary32) :
    (sumMap κ term initial values read).val = Binary32.sumMap initial values read := rfl

theorem sumMap_work (κ : Costs) (term : Site) (initial : Binary32) (values : List α)
    (read : α → Binary32) :
    (sumMap κ term initial values read).work ≤ values.length * (κ .visit + κ term) :=
  Costed.foldl_work_le _ _ _ _ _ fun _ _ _ => Nat.le_refl _

/-- Twin of `Binary32.sumFrom`. -/
def sumFrom (κ : Costs) (initial : Binary32) (values : List Binary32) : Costed Binary32 :=
  Costed.foldl (κ .visit) (fun total value => Costed.op (κ .sumTerm) (total.add value))
    initial values

theorem sumFrom_val (κ : Costs) (initial : Binary32) (values : List Binary32) :
    (sumFrom κ initial values).val = Binary32.sumFrom initial values := rfl

theorem sumFrom_work (κ : Costs) (initial : Binary32) (values : List Binary32) :
    (sumFrom κ initial values).work ≤ values.length * (κ .visit + κ .sumTerm) :=
  Costed.foldl_work_le _ _ _ _ _ fun _ _ _ => Nat.le_refl _

/-- Twin of the stored step sizes of a feature list. -/
def stepSizes (κ : Costs) (state : NumericState config dimension)
    (indices : List (FeatIdx dimension)) : Costed (List Binary32) :=
  Costed.map (κ .visit) (fun idx => Costed.op (κ .read) (state.stepSize idx)) indices

theorem stepSizes_work (κ : Costs) (state : NumericState config dimension)
    (indices : List (FeatIdx dimension)) :
    (stepSizes κ state indices).work ≤ indices.length * (κ .visit + κ .read) :=
  Costed.mapWork_le _ _ _ _ fun _ _ => Nat.le_refl _

/-! ## Prediction -/

/-- Twin of `NumericState.linearPrediction`: one term for each active feature. -/
def linearPrediction (κ : Costs) (state : NumericState config dimension)
    (features : ActiveSet dimension) : Costed Binary32 :=
  sumMap κ .sumTerm .zero features.indices fun idx => (state.weights.get idx).value

theorem linearPrediction_val (κ : Costs) (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    (linearPrediction κ state features).val = state.linearPrediction features := rfl

theorem linearPrediction_work (κ : Costs) (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    (linearPrediction κ state features).work ≤
      features.indices.length * (κ .visit + κ .sumTerm) :=
  sumMap_work _ _ _ _ _

/-! ## The first loop -/

/-- The costed recursion of `NumericState.learnFirstLoopGo`, by the same recursion: each
visit is one element, and a pruned visit also clears the index and swap-removes it. -/
def firstLoopRun (κ : Costs) (config : Acorn.Config) (delta vDelta traceDecay : Binary32) :
    NumericState config dimension → Array (FeatIdx dimension) → Nat →
      Costed (NumericState config dimension)
  | state, work, pos =>
    if inRange : pos < work.size then
      let idx := work[pos]
      let (state, prune) := state.firstLoopElement idx delta vDelta traceDecay
      if prune then
        Costed.charge (κ .visit + κ .firstElement + κ .prune)
          (firstLoopRun κ config delta vDelta traceDecay (state.clearFeatureRegisters idx)
            (swapRemove work pos inRange) pos)
      else
        Costed.charge (κ .visit + κ .firstElement)
          (firstLoopRun κ config delta vDelta traceDecay state work (pos + 1))
    else
      Costed.op (κ .firstClose)
        { state with transient := { state.transient with eligible := work } }
  termination_by _state work pos => work.size - pos
  decreasing_by
    · simp only [swapRemove, Array.size_pop, Array.size_set]
      omega
    · omega

/-- The costed recursion computes the executed first loop. -/
theorem firstLoopRun_val (κ : Costs) (config : Acorn.Config) (delta vDelta traceDecay : Binary32)
    (state : NumericState config dimension) (work : Array (FeatIdx dimension)) (pos : Nat) :
    (firstLoopRun κ config delta vDelta traceDecay state work pos).val =
      NumericState.learnFirstLoopGo config delta vDelta traceDecay state work pos := by
  fun_induction NumericState.learnFirstLoopGo config delta vDelta traceDecay state work pos with
  | case1 state work pos inRange idx next element ih =>
    rw [firstLoopRun]
    have element' : state.firstLoopElement work[pos] delta vDelta traceDecay = (next, true) :=
      element
    simp only [inRange, ↓reduceDIte, element', ite_true]
    exact ih
  | case2 state work pos inRange idx next prune element kept ih =>
    rw [firstLoopRun]
    have element' : state.firstLoopElement work[pos] delta vDelta traceDecay = (next, prune) :=
      element
    simp only [inRange, ↓reduceDIte, element', kept]
    exact ih
  | case3 state work pos outside =>
    rw [firstLoopRun]
    simp only [outside, ↓reduceDIte]

/-- The most work of one first-loop visit. -/
abbrev firstVisit (κ : Costs) : Nat := κ .visit + κ .firstElement + κ .prune

theorem firstLoopRun_work (κ : Costs) (config : Acorn.Config) (delta vDelta traceDecay : Binary32)
    (state : NumericState config dimension) (work : Array (FeatIdx dimension)) (pos : Nat) :
    (firstLoopRun κ config delta vDelta traceDecay state work pos).work ≤
      (work.size - pos) * firstVisit κ + κ .firstClose := by
  fun_induction firstLoopRun κ config delta vDelta traceDecay state work pos with
  | case1 state work pos inRange idx next element ih =>
    have shrinks : (swapRemove work pos inRange).size - pos + 1 = work.size - pos := by
      simp only [swapRemove, Array.size_pop, Array.size_set]
      omega
    rw [← shrinks]
    exact Costed.visit_le (Nat.le_refl _) ih
  | case2 state work pos inRange idx next prune element kept ih =>
    have advances : work.size - (pos + 1) + 1 = work.size - pos := by omega
    rw [← advances]
    exact Costed.visit_le (by simp only [firstVisit]; omega) ih
  | case3 state work pos outside => exact Nat.le_add_left _ _

/-- Twin of `NumericState.learnFirstLoop`: the executed loop's value with the work of
its costed recursion (`firstLoopRun_val`). -/
def firstLoop (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) : Costed (NumericState config dimension) :=
  ⟨state.learnFirstLoop config delta vDelta traceDecay,
    κ .firstOpen + (firstLoopRun κ config delta vDelta traceDecay
      { state with transient := { state.transient with eligible := #[] } }
      state.transient.eligible 0).work⟩

theorem firstLoop_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) :
    (firstLoop κ config state delta vDelta traceDecay).val =
      state.learnFirstLoop config delta vDelta traceDecay := rfl

/-- Bound of the first loop over `count` eligible entries. -/
abbrev firstLoopBound (κ : Costs) (count : Nat) : Nat :=
  κ .firstOpen + count * firstVisit κ + κ .firstClose

theorem firstLoop_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) :
    (firstLoop κ config state delta vDelta traceDecay).work ≤
      firstLoopBound κ state.transient.eligible.size := by
  have go := firstLoopRun_work κ config delta vDelta traceDecay
    { state with transient := { state.transient with eligible := #[] } }
    state.transient.eligible 0
  simp only [Nat.sub_zero] at go
  simp only [firstLoop, firstLoopBound]
  omega

/-! ## The second loop -/

/-- The costed recursion of `NumericState.learnSecondLoopGo`, by the same recursion. -/
def secondLoopRun (κ : Costs) (overshoot : Bool) (scale oneSubT : Binary32) :
    List (FeatIdx dimension) → List Binary32 → NumericState config dimension → Binary32 →
      Costed (NumericState config dimension × Binary32)
  | idx :: indices, alpha :: alphas, state, vDelta =>
    let next := NumericState.secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx
    Costed.charge (κ .visit + κ .secondElement)
      (secondLoopRun κ overshoot scale oneSubT indices alphas next.1 next.2)
  | _, _, state, vDelta => Costed.pure (state, vDelta)

/-- Twin of `NumericState.learnSecondLoopGo`: the executed traversal's value with the work
of its costed recursion (`secondLoopRun_val`). -/
def secondLoopGo (κ : Costs) (overshoot : Bool) (scale oneSubT : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) :
    Costed (NumericState config dimension × Binary32) :=
  ⟨NumericState.learnSecondLoopGo overshoot scale oneSubT indices alphas state vDelta,
    (secondLoopRun κ overshoot scale oneSubT indices alphas state vDelta).work⟩

/-- The costed recursion computes the executed second loop. -/
theorem secondLoopRun_val (κ : Costs) (overshoot : Bool) (scale oneSubT : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) :
    (secondLoopRun κ overshoot scale oneSubT indices alphas state vDelta).val =
      NumericState.learnSecondLoopGo overshoot scale oneSubT indices alphas state vDelta := by
  induction indices generalizing alphas state vDelta with
  | nil => cases alphas <;> rfl
  | cons idx rest ih =>
    cases alphas with
    | nil => rfl
    | cons alpha alphas =>
      rw [secondLoopRun, NumericState.learnSecondLoopGo]
      exact ih _ _ _

theorem secondLoopGo_work (κ : Costs) (overshoot : Bool) (scale oneSubT : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) :
    (secondLoopGo κ overshoot scale oneSubT indices alphas state vDelta).work ≤
      indices.length * (κ .visit + κ .secondElement) := by
  induction indices generalizing alphas state vDelta with
  | nil => cases alphas <;> exact Nat.zero_le _
  | cons idx rest ih =>
    cases alphas with
    | nil => exact Nat.zero_le _
    | cons alpha alphas =>
      have rest := ih alphas
        (NumericState.secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).1
        (NumericState.secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).2
      simp only [secondLoopGo, secondLoopRun, Costed.charge, List.length_cons,
        Nat.succ_mul] at rest ⊢
      omega

/-- Twin of `NumericState.learnSecondLoop`: the step sizes and the two sums read once,
then one element for each feature. -/
def secondLoop (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    Costed (NumericState config dimension × Binary32) := do
  let alphas ← stepSizes κ state features.indices
  let rate ← sumFrom κ .zero alphas
  let t ← sumMap κ .sumTerm .zero features.indices fun idx => (state.transient.z.get idx).value
  let overshoot := config.eta.less rate
  let e := if overshoot then rate else config.eta
  Costed.charge (κ .secondOpen)
    (secondLoopGo κ overshoot (config.eta.div e) (Binary32.one.sub t) features.indices alphas
      state vDelta)

theorem secondLoop_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    (secondLoop κ config state features vDelta).val =
      state.learnSecondLoop config features vDelta := rfl

/-- Bound of the second loop over `width` features. -/
abbrev secondLoopBound (κ : Costs) (width : Nat) : Nat :=
  width * (κ .visit + κ .read) + width * (κ .visit + κ .sumTerm) +
    width * (κ .visit + κ .sumTerm) + κ .secondOpen + width * (κ .visit + κ .secondElement)

theorem secondLoop_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    (secondLoop κ config state features vDelta).work ≤
      secondLoopBound κ features.indices.length := by
  have length : (stepSizes κ state features.indices).val.length = features.indices.length :=
    List.length_map ..
  unfold secondLoop
  refine Nat.le_trans (Costed.bind_work_le_at (stepSizes_work κ state features.indices)
    (Costed.bind_work_le_at (sumFrom_work κ .zero _)
      (Costed.bind_work_le_at (sumMap_work κ .sumTerm .zero _ _)
        (Nat.add_le_add_left (secondLoopGo_work κ _ _ _ _ _ state vDelta) _)))) ?_
  rw [length]
  simp only [secondLoopBound]
  omega

/-! ## Updates -/

/-- Twin of `NumericState.step`: the prediction, the first loop over the eligible
entries, the second loop over the features, and the store of the results. -/
def step (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    Costed (NumericState config dimension × TdStep) := do
  let v ← linearPrediction κ state features
  let delta := (reward.add (config.rule.gamma.mul v)).sub state.transient.vOld
  let first ← firstLoop κ config state delta state.transient.vDelta
    (config.rule.gamma.mul config.lambda)
  let second ← secondLoop κ config first features .zero
  Costed.op (κ .stepClose)
    ({ second.1 with transient := { second.1.transient with vDelta := second.2, vOld := v } },
      (⟨v, delta⟩ : TdStep))

theorem step_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    (step κ config state features reward).val = state.step config features reward := rfl

/-- Bound of a SwiftTD step at `count` eligible entries and `width` features. -/
abbrev stepBound (κ : Costs) (count width : Nat) : Nat :=
  width * (κ .visit + κ .sumTerm) + firstLoopBound κ count + secondLoopBound κ width +
    κ .stepClose

theorem step_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    (step κ config state features reward).work ≤
      stepBound κ state.transient.eligible.size features.indices.length := by
  have bound : (step κ config state features reward).work ≤
      features.indices.length * (κ .visit + κ .sumTerm) +
        (firstLoopBound κ state.transient.eligible.size +
          (secondLoopBound κ features.indices.length + κ .stepClose)) :=
    Costed.bind_work_le (linearPrediction_work κ state features) fun _ =>
      Costed.bind_work_le (firstLoop_work κ config state _ _ _) fun first =>
        Costed.bind_work_le (secondLoop_work κ config first features .zero) fun _ =>
          Nat.le_refl _
  simp only [stepBound]
  omega

/-- Twin of `TransientState.zero`: nine register vectors written in full. -/
def zeroTransient (κ : Costs) (dimension : Dimension) : Costed (TransientState dimension) := do
  let z ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : TraceRegister)
  let zDelta ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : TraceRegister)
  let zBar ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : TraceRegister)
  let lastAlpha ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : TraceRegister)
  let deltaWeight ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : MetaRegister)
  let h ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : MetaRegister)
  let hOld ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : MetaRegister)
  let hTemp ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : MetaRegister)
  let p ← Costed.replicate (κ .visit) dimension.capacity (⟨.zero⟩ : MetaRegister)
  Costed.op (κ .zeroTransient)
    { z, zDelta, zBar, lastAlpha, deltaWeight, h, hOld, hTemp, p, eligible := #[],
      vDelta := .zero, vOld := .zero }

theorem zeroTransient_val (κ : Costs) (dimension : Dimension) :
    (zeroTransient κ dimension).val = TransientState.zero dimension := rfl

/-- Bound of a fresh transient record at a capacity. -/
abbrev zeroBound (κ : Costs) (capacity : Nat) : Nat := 9 * (capacity * κ .visit) + κ .zeroTransient

theorem zeroTransient_work (κ : Costs) (dimension : Dimension) :
    (zeroTransient κ dimension).work ≤ zeroBound κ dimension.capacity := by
  simp only [zeroTransient, Costed.bind_work, zeroBound]
  omega

/-- Twin of `NumericState.clearTransient`. -/
def clearTransient (κ : Costs) (state : NumericState config dimension) :
    Costed (NumericState config dimension) := do
  let zero ← zeroTransient κ dimension
  Costed.pure { state with transient := zero }

theorem clearTransient_val (κ : Costs) (state : NumericState config dimension) :
    (clearTransient κ state).val = state.clearTransient := rfl

theorem clearTransient_work (κ : Costs) (state : NumericState config dimension) :
    (clearTransient κ state).work ≤ zeroBound κ dimension.capacity := by
  have zero := zeroTransient_work κ dimension
  simp only [clearTransient, Costed.bind_work, Costed.pure]
  omega

/-- Twin of `NumericState.beginTrajectory`. -/
def beginTrajectory (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) : Costed (NumericState config dimension) := do
  let cleared ← clearTransient κ state
  let v ← linearPrediction κ cleared features
  let second ← secondLoop κ config cleared features .zero
  Costed.op (κ .beginClose)
    { second.1 with transient := { second.1.transient with vOld := v, vDelta := second.2 } }

theorem beginTrajectory_val (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) :
    (beginTrajectory κ config state features).val = state.beginTrajectory config features := rfl

/-- Bound of a trajectory start at a capacity and `width` features. -/
abbrev beginBound (κ : Costs) (capacity width : Nat) : Nat :=
  zeroBound κ capacity + width * (κ .visit + κ .sumTerm) + secondLoopBound κ width + κ .beginClose

theorem beginTrajectory_work (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) :
    (beginTrajectory κ config state features).work ≤
      beginBound κ dimension.capacity features.indices.length := by
  have bound : (beginTrajectory κ config state features).work ≤
      zeroBound κ dimension.capacity + (features.indices.length * (κ .visit + κ .sumTerm) +
        (secondLoopBound κ features.indices.length + κ .beginClose)) :=
    Costed.bind_work_le (clearTransient_work κ state) fun cleared =>
      Costed.bind_work_le (linearPrediction_work κ cleared features) fun _ =>
        Costed.bind_work_le (secondLoop_work κ config cleared features .zero) fun _ =>
          Nat.le_refl _
  simp only [beginBound]
  omega

/-- Twin of `NumericState.terminalStep`. -/
def terminalStep (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (target : Binary32) : Costed (NumericState config dimension × Binary32) := do
  let delta := target.sub state.transient.vOld
  let first ← firstLoop κ config state delta state.transient.vDelta
    (config.rule.gamma.mul config.lambda)
  let cleared ← clearTransient κ first
  Costed.op (κ .terminalClose) (cleared, delta)

theorem terminalStep_val (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (target : Binary32) :
    (terminalStep κ config state target).val = state.terminalStep config target := rfl

/-- Bound of a terminal step at a capacity and `count` eligible entries. -/
abbrev terminalBound (κ : Costs) (capacity count : Nat) : Nat :=
  firstLoopBound κ count + zeroBound κ capacity + κ .terminalClose

theorem terminalStep_work (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (target : Binary32) :
    (terminalStep κ config state target).work ≤
      terminalBound κ dimension.capacity state.transient.eligible.size := by
  have bound : (terminalStep κ config state target).work ≤
      firstLoopBound κ state.transient.eligible.size +
        (zeroBound κ dimension.capacity + κ .terminalClose) :=
    Costed.bind_work_le (firstLoop_work κ config state _ _ _) fun first =>
      Costed.bind_work_le (clearTransient_work κ first) fun _ => Nat.le_refl _
  simp only [terminalBound]
  omega

/-- The costed recursion of `NumericState.planWeightsGo`, by the same recursion. -/
def planWeightsRun (κ : Costs) (scale delta : Binary32) :
    List (FeatIdx dimension) → List Binary32 → NumericState config dimension →
      Costed (NumericState config dimension)
  | idx :: indices, alpha :: alphas, state =>
    Costed.charge (κ .visit + κ .planElement)
      (planWeightsRun κ scale delta indices alphas
        (state.writeWeight idx ((state.weights.get idx).value.add ((scale.mul alpha).mul delta))))
  | _, _, state => Costed.pure state

/-- Twin of `NumericState.planWeightsGo`: the executed traversal's value with the work of
its costed recursion (`planWeightsRun_val`). -/
def planWeightsGo (κ : Costs) (scale delta : Binary32) (indices : List (FeatIdx dimension))
    (alphas : List Binary32) (state : NumericState config dimension) :
    Costed (NumericState config dimension) :=
  ⟨NumericState.planWeightsGo scale delta indices alphas state,
    (planWeightsRun κ scale delta indices alphas state).work⟩

/-- The costed recursion computes the executed planning traversal. -/
theorem planWeightsRun_val (κ : Costs) (scale delta : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) :
    (planWeightsRun κ scale delta indices alphas state).val =
      NumericState.planWeightsGo scale delta indices alphas state := by
  induction indices generalizing alphas state with
  | nil => cases alphas <;> rfl
  | cons idx rest ih =>
    cases alphas with
    | nil => rfl
    | cons alpha alphas =>
      rw [planWeightsRun, NumericState.planWeightsGo]
      exact ih _ _

theorem planWeightsGo_work (κ : Costs) (scale delta : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) :
    (planWeightsGo κ scale delta indices alphas state).work ≤
      indices.length * (κ .visit + κ .planElement) := by
  induction indices generalizing alphas state with
  | nil => cases alphas <;> exact Nat.zero_le _
  | cons idx rest ih =>
    cases alphas with
    | nil => exact Nat.zero_le _
    | cons alpha alphas =>
      have rest := ih alphas
        (state.writeWeight idx ((state.weights.get idx).value.add ((scale.mul alpha).mul delta)))
      simp only [planWeightsGo, planWeightsRun, Costed.charge, List.length_cons,
        Nat.succ_mul] at rest ⊢
      omega

/-- Twin of `NumericState.planStep`. -/
def planStep (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    Costed (NumericState config dimension × Binary32) := do
  let v ← linearPrediction κ state features
  let delta := target.sub v
  Costed.ite ((!decide delta.Finite || delta.numericallyEqual .zero) = true)
    (Costed.op (κ .planOpen) (state, .zero))
    (do
      let alphas ← stepSizes κ state features.indices
      let rate ← sumFrom κ .zero alphas
      let e := if config.eta.less rate then rate else config.eta
      let next ← planWeightsGo κ (config.eta.div e) delta features.indices alphas state
      Costed.op (κ .planOpen) (next, delta))

theorem planStep_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    (planStep κ config state features target).val = state.planStep config features target := rfl

/-- Bound of a planning step over `width` features. -/
abbrev planBound (κ : Costs) (width : Nat) : Nat :=
  width * (κ .visit + κ .sumTerm) + width * (κ .visit + κ .read) +
    width * (κ .visit + κ .sumTerm) + width * (κ .visit + κ .planElement) + κ .planOpen

theorem planStep_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    (planStep κ config state features target).work ≤ planBound κ features.indices.length := by
  have length : (stepSizes κ state features.indices).val.length = features.indices.length :=
    List.length_map ..
  have rate := sumFrom_work κ .zero (stepSizes κ state features.indices).val
  rw [length] at rate
  have bound : (planStep κ config state features target).work ≤
      features.indices.length * (κ .visit + κ .sumTerm) +
        max (κ .planOpen) (features.indices.length * (κ .visit + κ .read) +
          (features.indices.length * (κ .visit + κ .sumTerm) +
            (features.indices.length * (κ .visit + κ .planElement) + κ .planOpen))) :=
    Costed.bind_work_le (linearPrediction_work κ state features) fun v =>
      Nat.le_trans (Costed.ite_work_le _ _ _) (Costed.max_le_max (Nat.le_refl _)
        (Costed.bind_work_le_at (stepSizes_work κ state features.indices)
          (Costed.bind_work_le_at rate
            (Costed.bind_work_le (planWeightsGo_work κ _ _ features.indices _ state) fun _ =>
              Nat.le_refl _))))
  simp only [planBound]
  omega

/-- Twin of `NumericState.releaseEligible`: one clear for each eligible entry. -/
def releaseEligible (κ : Costs) (state : NumericState config dimension) :
    Costed (NumericState config dimension) := do
  let cleared ← Costed.foldlArray (κ .visit)
    (fun next idx => Costed.op (κ .clearRegisters) (next.clearFeatureRegisters idx)) state
    state.transient.eligible
  Costed.op (κ .releaseClose)
    { cleared with transient := { cleared.transient with eligible := #[] } }

theorem releaseEligible_val (κ : Costs) (state : NumericState config dimension) :
    (releaseEligible κ state).val = state.releaseEligible := rfl

theorem releaseEligible_work (κ : Costs) (state : NumericState config dimension) :
    (releaseEligible κ state).work ≤
      state.transient.eligible.size * (κ .visit + κ .clearRegisters) + κ .releaseClose := by
  have loop := Costed.foldlArray_work_le (κ .visit) (κ .clearRegisters)
    (fun (next : NumericState config dimension) idx =>
      Costed.op (κ .clearRegisters) (next.clearFeatureRegisters idx)) state
    state.transient.eligible (fun _ _ _ => Nat.le_refl _)
  exact Nat.add_le_add_right loop _

/-- Twin of `NumericState.retireIndex`: its one loop is the search of the eligible list
for the retired index; the removal, the clear and the two writes are loop-free. -/
def retireIndex (κ : Costs) (state : NumericState config dimension) (idx : FeatIdx dimension) :
    Costed (NumericState config dimension) :=
  Costed.charge (κ .retire)
    (Costed.scanArray (κ .visit) state.transient.eligible (state.retireIndex idx))

theorem retireIndex_val (κ : Costs) (state : NumericState config dimension)
    (idx : FeatIdx dimension) : (retireIndex κ state idx).val = state.retireIndex idx := rfl

theorem retireIndex_work (κ : Costs) (state : NumericState config dimension)
    (idx : FeatIdx dimension) :
    (retireIndex κ state idx).work = κ .retire + state.transient.eligible.size * κ .visit := rfl

end AcornVerif.Resource.Twin
