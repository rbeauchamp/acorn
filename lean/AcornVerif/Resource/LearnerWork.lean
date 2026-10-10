/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.SwiftTd
import AcornVerif.Resource.Work

/-!
# Work of the SwiftTD learner

The learner's executed definitions in `Acorn.SwiftTd`, and the ordered sums and the fresh
transient record they use, are the values of their costed definitions (`Acorn.Costed`), so the
loops a bound proved here counts are the loops of the code that runs. A bound counts the work of
that code under the cost discipline of `Acorn.Cost`: every function a combinator takes is
costed, and every value a costed definition passes in, the uncosted entry points that
`Acorn.Cost` lists, is computed without a loop and without a costed definition. The combinators
cannot enforce the second, since `Costed.pure` accepts any value; it is checked by reading until
the cost-closed rule of rbeauchamp/regula#333 checks it.

Each bound is a function of the number of eligible entries of the learner the definition receives
and of the length of the feature list it reads. No bound depends on the learner's values: the
first loop visits each eligible entry once whether it prunes it or not, and a release and a
retirement pass over the eligible list once. Each loop is also charged one visit for its end.

The second loop pushes at most one index for each feature it visits, so a learner's eligible
list can grow during a step; the bounds of a step read the sizes of the state each loop
receives, and a caller bounds those by the learner's admission
(`AcornVerif.CurrentFeatureConsumers.managed_capacity`).

The twins of the definitions that are not yet costed (`AcornVerif.Resource.Work`) read the
learner through the last section: each is the executed value with the bound proved here as
its work.
-/

namespace AcornVerif.Resource.Twin

open Acorn
open Acorn.SwiftTd (ActiveSet swapRemove TdStep)

variable {config : Acorn.Config} {dimension : Dimension} {α : Type}

/-! ## Ordered sums -/

theorem sumFromCosted_within (κ : Costs) (initial : Binary32) (values : List Binary32) :
    (Binary32.sumFromCosted initial values).Within κ (pass (κ .visit) values.length (κ .sumTerm)) :=
  Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ

theorem sumMapCosted_within (κ : Costs) (site : Site) (initial : Binary32) (values : List α)
    (read : α → Binary32) :
    (Binary32.sumMapCosted site initial values read).Within κ
      (pass (κ .visit) values.length (κ site)) :=
  Acorn.Costed.foldl_within fun _ _ _ => Acorn.Costed.op_within _ _ κ

/-- The step sizes of a feature list, read one by one, and the further passes of the map. -/
theorem stepSizes_within (κ : Costs) (state : NumericState config dimension)
    (indices : List (FeatIdx dimension)) :
    (Acorn.Costed.map (fun idx => Acorn.Costed.op .read (state.stepSize idx)) indices).Within κ
      (pass (κ .visit) indices.length (κ .read) +
        (Library.map.passes - 1) * bare (κ .visit) indices.length) :=
  Acorn.Costed.map_within fun _ _ => Acorn.Costed.op_within _ _ κ

/-! ## Prediction -/

theorem linearPredictionCosted_within (κ : Costs) (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    (state.linearPredictionCosted features).Within κ
      (pass (κ .visit) features.indices.length (κ .sumTerm)) :=
  sumMapCosted_within κ .sumTerm _ _ _

/-! ## The first loop -/

/-- The most work of one first-loop visit. -/
abbrev firstVisit (κ : Costs) : Nat := κ .visit + κ .firstElement + κ .prune

theorem learnFirstLoopGoCosted_within (κ : Costs) (config : Acorn.Config)
    (delta vDelta traceDecay : Binary32) (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) :
    (NumericState.learnFirstLoopGoCosted config delta vDelta traceDecay state work pos).Within κ
      ((work.size - pos) * firstVisit κ + (κ .visit + κ .firstClose)) := by
  fun_induction NumericState.learnFirstLoopGoCosted config delta vDelta traceDecay state work pos
    with
  | case1 state work pos inRange idx next element ih =>
    have shrinks : (swapRemove work pos inRange).size - pos + 1 = work.size - pos := by
      simp only [swapRemove, Array.size_pop, Array.size_set]
      omega
    refine (Acorn.Costed.charge_within (Acorn.Costed.charge_within
      (Acorn.Costed.charge_within ih))).mono ?_
    rw [← shrinks, Nat.succ_mul]
    simp only [firstVisit]
    omega
  | case2 state work pos inRange idx next prune element kept ih =>
    refine (Acorn.Costed.charge_within (Acorn.Costed.charge_within ih)).mono ?_
    have advances : work.size - (pos + 1) + 1 = work.size - pos := by omega
    rw [← advances, Nat.succ_mul]
    simp only [firstVisit]
    omega
  | case3 state work pos outside =>
    exact (Acorn.Costed.charge_within (Acorn.Costed.op_within _ _ κ)).mono (by omega)

/-- Bound of the first loop over `count` eligible entries. -/
abbrev firstLoopBound (κ : Costs) (count : Nat) : Nat :=
  κ .firstOpen + count * firstVisit κ + (κ .visit + κ .firstClose)

theorem learnFirstLoopCosted_within (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (delta vDelta traceDecay : Binary32) :
    (state.learnFirstLoopCosted config delta vDelta traceDecay).Within κ
      (firstLoopBound κ state.transient.eligible.size) := by
  have go := learnFirstLoopGoCosted_within κ config delta vDelta traceDecay
    { state with transient := { state.transient with eligible := #[] } }
    state.transient.eligible 0
  rw [Nat.sub_zero] at go
  refine (Acorn.Costed.charge_within go).mono ?_
  simp only [firstLoopBound]
  omega

/-! ## The second loop -/

theorem learnSecondLoopGoCosted_within (κ : Costs) (overshoot : Bool) (scale oneSubT : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) (vDelta : Binary32) :
    (NumericState.learnSecondLoopGoCosted overshoot scale oneSubT indices alphas state
      vDelta).Within κ (pass (κ .visit) indices.length (κ .secondElement)) := by
  induction indices generalizing alphas state vDelta with
  | nil =>
    cases alphas <;>
      exact (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _)
  | cons idx rest ih =>
    cases alphas with
    | nil => exact (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _)
    | cons alpha alphas =>
      refine (Acorn.Costed.charge_within (Acorn.Costed.charge_within (ih alphas _ _))).mono ?_
      simp only [pass, List.length_cons, Nat.succ_mul]
      omega

/-- Bound of the second loop over `width` features. -/
abbrev secondLoopBound (κ : Costs) (width : Nat) : Nat :=
  (pass (κ .visit) width (κ .read) + (Library.map.passes - 1) * bare (κ .visit) width) +
    pass (κ .visit) width (κ .sumTerm) + pass (κ .visit) width (κ .sumTerm) + κ .secondOpen +
    pass (κ .visit) width (κ .secondElement)

theorem learnSecondLoopCosted_within (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) (vDelta : Binary32) :
    (state.learnSecondLoopCosted config features vDelta).Within κ
      (secondLoopBound κ features.indices.length) := by
  have length : (Acorn.Costed.map (fun idx => Acorn.Costed.op .read (state.stepSize idx))
      features.indices).val.length = features.indices.length :=
    List.length_map ..
  have rate := sumFromCosted_within κ .zero
    (Acorn.Costed.map (fun idx => Acorn.Costed.op .read (state.stepSize idx))
      features.indices).val
  rw [length] at rate
  refine (Acorn.Costed.bind_within (stepSizes_within κ state features.indices)
    (Acorn.Costed.bind_within rate
      (Acorn.Costed.bind_within (sumMapCosted_within κ .sumTerm _ _ _)
        (Acorn.Costed.charge_within
          (learnSecondLoopGoCosted_within κ _ _ _ _ _ state vDelta))))).mono ?_
  simp only [secondLoopBound]
  omega

/-! ## Updates -/

/-- Bound of a SwiftTD step at `count` eligible entries and `width` features. -/
abbrev stepBound (κ : Costs) (count width : Nat) : Nat :=
  pass (κ .visit) width (κ .sumTerm) + firstLoopBound κ count + secondLoopBound κ width +
    κ .stepClose

theorem stepCosted_within (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) (reward : Binary32) :
    (state.stepCosted config features reward).Within κ
      (stepBound κ state.transient.eligible.size features.indices.length) := by
  refine (Acorn.Costed.bind_within_all (linearPredictionCosted_within κ state features) fun _ =>
    Acorn.Costed.bind_within_all (learnFirstLoopCosted_within κ config state _ _ _) fun first =>
      Acorn.Costed.bind_within_all (learnSecondLoopCosted_within κ config first features .zero)
        fun _ => Acorn.Costed.op_within _ _ κ).mono ?_
  simp only [stepBound]
  omega

/-- Bound of a fresh transient record at a capacity. -/
abbrev zeroBound (κ : Costs) (capacity : Nat) : Nat :=
  9 * bare (κ .visit) capacity + κ .zeroTransient

theorem zeroCosted_within (κ : Costs) (dimension : Dimension) :
    (TransientState.zeroCosted dimension).Within κ (zeroBound κ dimension.capacity) := by
  have each := fun {β : Type} (value : β) =>
    Acorn.Costed.replicate_within dimension.capacity value κ
  refine (Acorn.Costed.bind_within (each _) <| Acorn.Costed.bind_within (each _) <|
    Acorn.Costed.bind_within (each _) <| Acorn.Costed.bind_within (each _) <|
    Acorn.Costed.bind_within (each _) <| Acorn.Costed.bind_within (each _) <|
    Acorn.Costed.bind_within (each _) <| Acorn.Costed.bind_within (each _) <|
    Acorn.Costed.bind_within (each _) <| Acorn.Costed.op_within _ _ κ).mono ?_
  simp only [zeroBound, bare]
  omega

theorem clearTransientCosted_within (κ : Costs) (state : NumericState config dimension) :
    state.clearTransientCosted.Within κ (zeroBound κ dimension.capacity) :=
  (Acorn.Costed.bind_within (zeroCosted_within κ dimension)
    (Acorn.Costed.pure_within _ κ)).mono (Nat.le_of_eq (Nat.add_zero _))

/-- Bound of a trajectory start at a capacity and `width` features. -/
abbrev beginBound (κ : Costs) (capacity width : Nat) : Nat :=
  zeroBound κ capacity + pass (κ .visit) width (κ .sumTerm) + secondLoopBound κ width +
    κ .beginClose

theorem beginTrajectoryCosted_within (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) :
    (state.beginTrajectoryCosted config features).Within κ
      (beginBound κ dimension.capacity features.indices.length) := by
  refine (Acorn.Costed.bind_within_all (clearTransientCosted_within κ state) fun cleared =>
    Acorn.Costed.bind_within_all (linearPredictionCosted_within κ cleared features) fun _ =>
      Acorn.Costed.bind_within_all (learnSecondLoopCosted_within κ config cleared features .zero)
        fun _ => Acorn.Costed.op_within _ _ κ).mono ?_
  simp only [beginBound]
  omega

/-- Bound of a terminal step at a capacity and `count` eligible entries. -/
abbrev terminalBound (κ : Costs) (capacity count : Nat) : Nat :=
  firstLoopBound κ count + zeroBound κ capacity + κ .terminalClose

theorem terminalStepCosted_within (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (target : Binary32) :
    (state.terminalStepCosted config target).Within κ
      (terminalBound κ dimension.capacity state.transient.eligible.size) := by
  refine (Acorn.Costed.bind_within_all (learnFirstLoopCosted_within κ config state _ _ _)
    fun first => Acorn.Costed.bind_within_all (clearTransientCosted_within κ first)
      fun _ => Acorn.Costed.op_within _ _ κ).mono ?_
  simp only [terminalBound]
  omega

theorem planWeightsGoCosted_within (κ : Costs) (scale delta : Binary32)
    (indices : List (FeatIdx dimension)) (alphas : List Binary32)
    (state : NumericState config dimension) :
    (NumericState.planWeightsGoCosted scale delta indices alphas state).Within κ
      (pass (κ .visit) indices.length (κ .planElement)) := by
  induction indices generalizing alphas state with
  | nil => cases alphas <;> exact (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _)
  | cons idx rest ih =>
    cases alphas with
    | nil => exact (Acorn.Costed.op_within _ _ κ).mono (Nat.le_add_left _ _)
    | cons alpha alphas =>
      refine (Acorn.Costed.charge_within (Acorn.Costed.charge_within (ih alphas _))).mono ?_
      simp only [pass, List.length_cons, Nat.succ_mul]
      omega

/-- Bound of a planning step over `width` features. -/
abbrev planBound (κ : Costs) (width : Nat) : Nat :=
  pass (κ .visit) width (κ .sumTerm) +
    (pass (κ .visit) width (κ .read) + (Library.map.passes - 1) * bare (κ .visit) width) +
    pass (κ .visit) width (κ .sumTerm) + pass (κ .visit) width (κ .planElement) + κ .planOpen

theorem planStepCosted_within (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) (target : Binary32) :
    (state.planStepCosted config features target).Within κ
      (planBound κ features.indices.length) := by
  have length : (Acorn.Costed.map (fun idx => Acorn.Costed.op .read (state.stepSize idx))
      features.indices).val.length = features.indices.length :=
    List.length_map ..
  have rate := sumFromCosted_within κ .zero
    (Acorn.Costed.map (fun idx => Acorn.Costed.op .read (state.stepSize idx))
      features.indices).val
  rw [length] at rate
  refine (Acorn.Costed.bind_within_all (linearPredictionCosted_within κ state features) fun _ =>
    Acorn.Costed.within_ite (bound := (pass (κ .visit) features.indices.length (κ .read) +
        (Library.map.passes - 1) * bare (κ .visit) features.indices.length) +
        (pass (κ .visit) features.indices.length (κ .sumTerm) +
          (pass (κ .visit) features.indices.length (κ .planElement) + κ .planOpen)))
      ((Acorn.Costed.op_within _ _ κ).mono (by omega))
      (Acorn.Costed.bind_within (stepSizes_within κ state features.indices)
        (Acorn.Costed.bind_within rate
          (Acorn.Costed.bind_within_all (planWeightsGoCosted_within κ _ _ features.indices _ state)
            fun _ => Acorn.Costed.op_within _ _ κ)))).mono ?_
  simp only [planBound]
  omega

theorem releaseEligibleCosted_within (κ : Costs) (state : NumericState config dimension) :
    state.releaseEligibleCosted.Within κ
      (pass (κ .visit) state.transient.eligible.size (κ .clearRegisters) + κ .releaseClose) :=
  Acorn.Costed.bind_within
    (Acorn.Costed.foldlArray_within fun _ _ _ => Acorn.Costed.op_within _ _ κ)
    (Acorn.Costed.op_within _ _ κ)

theorem retireIndexCosted_within (κ : Costs) (state : NumericState config dimension)
    (idx : FeatIdx dimension) :
    (state.retireIndexCosted idx).Within κ
      (κ .retire + pass (κ .visit) state.transient.eligible.size (κ .compare)) :=
  (Acorn.Costed.bind_within (Acorn.Costed.findIdx?_within fun _ _ => Acorn.Costed.op_within _ _ κ)
    (Acorn.Costed.op_within _ _ κ)).mono (Nat.le_of_eq (Nat.add_comm _ _))

/-- Bound of one learner entry at a capacity and `count` eligible entries. -/
def entryBound (κ : Costs) (capacity count : Nat) : SwiftTd.Entry dimension → Nat
  | .first .. => firstLoopBound κ count
  | .second features _ => secondLoopBound κ features.indices.length
  | .step features _ => stepBound κ count features.indices.length
  | .beginTrajectory features => beginBound κ capacity features.indices.length
  | .terminal _ => terminalBound κ capacity count
  | .plan features _ => planBound κ features.indices.length
  | .retire _ => κ .retire + pass (κ .visit) count (κ .compare)
  | .clear => zeroBound κ capacity
  | .release => pass (κ .visit) count (κ .clearRegisters) + κ .releaseClose

theorem applyCosted_within (κ : Costs) (entry : SwiftTd.Entry dimension)
    (state : NumericState config dimension) :
    (entry.applyCosted state).Within κ
      (entryBound κ dimension.capacity state.transient.eligible.size entry) := by
  cases entry with
  | first delta vDelta decay => exact learnFirstLoopCosted_within κ config state delta vDelta decay
  | second features vDelta =>
    exact (Acorn.Costed.bind_within_all (learnSecondLoopCosted_within κ config state features
      vDelta) fun _ => Acorn.Costed.pure_within _ κ).mono (Nat.le_of_eq (Nat.add_zero _))
  | step features reward =>
    exact (Acorn.Costed.bind_within_all (stepCosted_within κ config state features reward)
      fun _ => Acorn.Costed.pure_within _ κ).mono (Nat.le_of_eq (Nat.add_zero _))
  | beginTrajectory features => exact beginTrajectoryCosted_within κ config state features
  | terminal target =>
    exact (Acorn.Costed.bind_within_all (terminalStepCosted_within κ config state target)
      fun _ => Acorn.Costed.pure_within _ κ).mono (Nat.le_of_eq (Nat.add_zero _))
  | plan features target =>
    exact (Acorn.Costed.bind_within_all (planStepCosted_within κ config state features target)
      fun _ => Acorn.Costed.pure_within _ κ).mono (Nat.le_of_eq (Nat.add_zero _))
  | retire idx => exact retireIndexCosted_within κ state idx
  | clear => exact clearTransientCosted_within κ state
  | release => exact releaseEligibleCosted_within κ state

/-- An entry's bound grows with the number of eligible entries. -/
theorem entryBound_mono (κ : Costs) (capacity : Nat) {count limit : Nat} (fits : count ≤ limit)
    (entry : SwiftTd.Entry dimension) :
    entryBound κ capacity count entry ≤ entryBound κ capacity limit entry := by
  have first := Nat.mul_le_mul_right (firstVisit κ) fits
  have visit := pass_mono (visit := κ .visit) fits (Nat.le_refl (κ .compare))
  have clear := pass_mono (visit := κ .visit) fits (Nat.le_refl (κ .clearRegisters))
  cases entry <;> simp only [entryBound, stepBound, terminalBound, firstLoopBound] <;> omega

/-! ## The learner in the twins' accounting

Each twin below is an executed learner definition's value with, as its work, the bound that
the section above proves of its costed definition. -/

/-- `Binary32.sumMap` with terms at `term`. -/
def sumMap (κ : Costs) (term : Site) (initial : Binary32) (values : List α)
    (read : α → Binary32) : Costed Binary32 :=
  ⟨Binary32.sumMap initial values read, pass (κ .visit) values.length (κ term)⟩

theorem sumMap_val (κ : Costs) (term : Site) (initial : Binary32) (values : List α)
    (read : α → Binary32) :
    (sumMap κ term initial values read).val = Binary32.sumMap initial values read := rfl

theorem sumMap_work (κ : Costs) (term : Site) (initial : Binary32) (values : List α)
    (read : α → Binary32) :
    (sumMap κ term initial values read).work ≤ pass (κ .visit) values.length (κ term) :=
  Nat.le_refl _

/-- `Binary32.sumFrom`. -/
def sumFrom (κ : Costs) (initial : Binary32) (values : List Binary32) : Costed Binary32 :=
  ⟨Binary32.sumFrom initial values, pass (κ .visit) values.length (κ .sumTerm)⟩

theorem sumFrom_val (κ : Costs) (initial : Binary32) (values : List Binary32) :
    (sumFrom κ initial values).val = Binary32.sumFrom initial values := rfl

theorem sumFrom_work (κ : Costs) (initial : Binary32) (values : List Binary32) :
    (sumFrom κ initial values).work ≤ pass (κ .visit) values.length (κ .sumTerm) :=
  Nat.le_refl _

/-- `NumericState.linearPrediction`. -/
def linearPrediction (κ : Costs) (state : NumericState config dimension)
    (features : ActiveSet dimension) : Costed Binary32 :=
  ⟨state.linearPrediction features, pass (κ .visit) features.indices.length (κ .sumTerm)⟩

theorem linearPrediction_val (κ : Costs) (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    (linearPrediction κ state features).val = state.linearPrediction features := rfl

theorem linearPrediction_work (κ : Costs) (state : NumericState config dimension)
    (features : ActiveSet dimension) :
    (linearPrediction κ state features).work ≤
      pass (κ .visit) features.indices.length (κ .sumTerm) :=
  Nat.le_refl _

/-- `NumericState.learnFirstLoop`. -/
def firstLoop (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) : Costed (NumericState config dimension) :=
  ⟨state.learnFirstLoop config delta vDelta traceDecay,
    firstLoopBound κ state.transient.eligible.size⟩

theorem firstLoop_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) :
    (firstLoop κ config state delta vDelta traceDecay).val =
      state.learnFirstLoop config delta vDelta traceDecay := rfl

theorem firstLoop_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (delta vDelta traceDecay : Binary32) :
    (firstLoop κ config state delta vDelta traceDecay).work ≤
      firstLoopBound κ state.transient.eligible.size :=
  Nat.le_refl _

/-- `NumericState.learnSecondLoop`. -/
def secondLoop (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    Costed (NumericState config dimension × Binary32) :=
  ⟨state.learnSecondLoop config features vDelta, secondLoopBound κ features.indices.length⟩

theorem secondLoop_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    (secondLoop κ config state features vDelta).val =
      state.learnSecondLoop config features vDelta := rfl

theorem secondLoop_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    (secondLoop κ config state features vDelta).work ≤
      secondLoopBound κ features.indices.length :=
  Nat.le_refl _

/-- `NumericState.step`. -/
def step (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    Costed (NumericState config dimension × TdStep) :=
  ⟨state.step config features reward,
    stepBound κ state.transient.eligible.size features.indices.length⟩

theorem step_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    (step κ config state features reward).val = state.step config features reward := rfl

theorem step_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (reward : Binary32) :
    (step κ config state features reward).work ≤
      stepBound κ state.transient.eligible.size features.indices.length :=
  Nat.le_refl _

/-- `TransientState.zero`. -/
def zeroTransient (κ : Costs) (dimension : Dimension) : Costed (TransientState dimension) :=
  ⟨TransientState.zero dimension, zeroBound κ dimension.capacity⟩

theorem zeroTransient_val (κ : Costs) (dimension : Dimension) :
    (zeroTransient κ dimension).val = TransientState.zero dimension := rfl

theorem zeroTransient_work (κ : Costs) (dimension : Dimension) :
    (zeroTransient κ dimension).work ≤ zeroBound κ dimension.capacity :=
  Nat.le_refl _

/-- `NumericState.clearTransient`. -/
def clearTransient (κ : Costs) (state : NumericState config dimension) :
    Costed (NumericState config dimension) :=
  ⟨state.clearTransient, zeroBound κ dimension.capacity⟩

theorem clearTransient_val (κ : Costs) (state : NumericState config dimension) :
    (clearTransient κ state).val = state.clearTransient := rfl

theorem clearTransient_work (κ : Costs) (state : NumericState config dimension) :
    (clearTransient κ state).work ≤ zeroBound κ dimension.capacity :=
  Nat.le_refl _

/-- `NumericState.beginTrajectory`. -/
def beginTrajectory (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) : Costed (NumericState config dimension) :=
  ⟨state.beginTrajectory config features, beginBound κ dimension.capacity features.indices.length⟩

theorem beginTrajectory_val (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) :
    (beginTrajectory κ config state features).val = state.beginTrajectory config features := rfl

theorem beginTrajectory_work (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (features : ActiveSet dimension) :
    (beginTrajectory κ config state features).work ≤
      beginBound κ dimension.capacity features.indices.length :=
  Nat.le_refl _

/-- `NumericState.terminalStep`. -/
def terminalStep (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (target : Binary32) : Costed (NumericState config dimension × Binary32) :=
  ⟨state.terminalStep config target,
    terminalBound κ dimension.capacity state.transient.eligible.size⟩

theorem terminalStep_val (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (target : Binary32) :
    (terminalStep κ config state target).val = state.terminalStep config target := rfl

theorem terminalStep_work (κ : Costs) (config : Acorn.Config)
    (state : NumericState config dimension) (target : Binary32) :
    (terminalStep κ config state target).work ≤
      terminalBound κ dimension.capacity state.transient.eligible.size :=
  Nat.le_refl _

/-- `NumericState.planStep`. -/
def planStep (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    Costed (NumericState config dimension × Binary32) :=
  ⟨state.planStep config features target, planBound κ features.indices.length⟩

theorem planStep_val (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    (planStep κ config state features target).val = state.planStep config features target := rfl

theorem planStep_work (κ : Costs) (config : Acorn.Config) (state : NumericState config dimension)
    (features : ActiveSet dimension) (target : Binary32) :
    (planStep κ config state features target).work ≤ planBound κ features.indices.length :=
  Nat.le_refl _

/-- `NumericState.releaseEligible`. -/
def releaseEligible (κ : Costs) (state : NumericState config dimension) :
    Costed (NumericState config dimension) :=
  ⟨state.releaseEligible,
    pass (κ .visit) state.transient.eligible.size (κ .clearRegisters) + κ .releaseClose⟩

theorem releaseEligible_val (κ : Costs) (state : NumericState config dimension) :
    (releaseEligible κ state).val = state.releaseEligible := rfl

theorem releaseEligible_work (κ : Costs) (state : NumericState config dimension) :
    (releaseEligible κ state).work ≤
      pass (κ .visit) state.transient.eligible.size (κ .clearRegisters) + κ .releaseClose :=
  Nat.le_refl _

/-- `NumericState.retireIndex`. -/
def retireIndex (κ : Costs) (state : NumericState config dimension) (idx : FeatIdx dimension) :
    Costed (NumericState config dimension) :=
  ⟨state.retireIndex idx, κ .retire + pass (κ .visit) state.transient.eligible.size (κ .compare)⟩

theorem retireIndex_val (κ : Costs) (state : NumericState config dimension)
    (idx : FeatIdx dimension) : (retireIndex κ state idx).val = state.retireIndex idx := rfl

theorem retireIndex_work (κ : Costs) (state : NumericState config dimension)
    (idx : FeatIdx dimension) :
    (retireIndex κ state idx).work =
      κ .retire + pass (κ .visit) state.transient.eligible.size (κ .compare) :=
  rfl

/-- `SwiftTd.Entry.apply`. -/
def entryApply (κ : Costs) (entry : SwiftTd.Entry dimension)
    (state : NumericState config dimension) : Costed (NumericState config dimension) :=
  ⟨entry.apply state, entryBound κ dimension.capacity state.transient.eligible.size entry⟩

theorem entryApply_val (κ : Costs) (entry : SwiftTd.Entry dimension)
    (state : NumericState config dimension) :
    (entryApply κ entry state).val = entry.apply state := rfl

theorem entryApply_work (κ : Costs) (entry : SwiftTd.Entry dimension)
    (state : NumericState config dimension) :
    (entryApply κ entry state).work ≤
      entryBound κ dimension.capacity state.transient.eligible.size entry :=
  Nat.le_refl _

end AcornVerif.Resource.Twin
