/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.SwiftTd
import AcornVerif.CurrentPrediction
import AcornVerif.CurrentState
import AcornVerif.CurrentLearnerArithmetic
import Mathlib.Data.Fintype.Card
/-!
# Contracts of the executing current learner

These statements refer directly to `Acorn.NumericState` transitions. Knowledge
legality and dimension preservation follow from the result types, including
exceptional raw inputs. Process-local registers have a separate support
invariant; no bound on their numerical magnitude follows from projection.

Ordered machine operations remain ordered in every identity. The real-valued
SwiftTD identities in `MetaGradient` apply to their mathematical domains, not
to reassociated machine expressions here.

The recurrence source is Javed, Sharifnassab & Sutton, *SwiftTD: A Fast and
Robust Algorithm for Temporal Difference Learning*, Reinforcement Learning
Journal 2 (2024), Algorithm 1 (p. 848) and equation (32) (printed p. 18).
Native arithmetic, compiler/runtime,
and ownership implementation are the declared execution trust boundaries.
-/

open Acorn Acorn.SwiftTd
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder
open AcornVerif.CurrentPrediction
open AcornVerif.CurrentLearnerArithmetic

namespace AcornVerif.CurrentLearner

variable {config : Config} {dimension : Dimension}

/-- Fin-indexed vector reads have the same elements as bounded Nat reads. -/
theorem vector_get {α : Type} {capacity : Nat} (values : Vector α capacity) (idx : Fin capacity) :
    values.get idx = values[idx.val] := by
  simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray]

/-- Finite numeric equality identifies precisely equal order keys, including
the two encodings of zero. -/
theorem finite_equal (left right : Binary32) (hl : left.Finite) (hr : right.Finite) :
    left.numericallyEqual right = decide (left.key = right.key) := by
  simp [Binary32.numericallyEqual_eq_key, Binary32.finite_not_nan left hl,
    Binary32.finite_not_nan right hr]

/-- The stored comparison has the exact rational ordering on finite inputs. -/
theorem finite_lessOrEqual (left right : Binary32) (hl : left.Finite) (hr : right.Finite) :
    left.lessOrEqual right = decide (numerical32 left ≤ numerical32 right) := by
  simp [Binary32.lessOrEqual_eq_key, Binary32.finite_not_nan left hl,
    Binary32.finite_not_nan right hr, numerical32_order left right hl hr]

/-- A zero encoding has zero order key; no finiteness premise is assumed. -/
theorem zero_key (word : Binary32) (zero : word.isZero = true) : word.key = 0 := by
  rw [Binary32.isZero_eq_key] at zero
  exact of_decide_eq_true zero

/-- A nonnegative non-NaN pruning threshold removes either zero encoding. -/
theorem zero_pruned (word threshold : Binary32) (zero : word.isZero = true)
    (ordered : threshold.isNaN = false) (nonnegative : 0 ≤ threshold.key) :
    word.lessOrEqual threshold = true := by
  have hn : word.isNaN = false := by
    have hz := zero_key word zero
    have hm : word.magnitude = 0 := by
      unfold Binary32.key at hz
      split at hz <;> omega
    simp [Binary32.isNaN_eq_magnitude, hm]
  simp [Binary32.lessOrEqual_eq_key, hn, ordered, zero_key word zero, nonnegative]

/-- Every unique active-feature set fits the admitted dimension. -/
theorem active_cardinality (features : ActiveSet dimension) :
    features.indices.length ≤ dimension.capacity := by
  simpa using features.nodup.length_le_card

/-- A unique eligible sequence fits the dimension; uniqueness is an explicit
premise because standalone second-loop calls may append existing members. -/
theorem eligible_cardinality (state : NumericState config dimension)
    (unique : state.transient.eligible.toList.Nodup) :
    state.eligibleCount ≤ dimension.capacity := by
  simpa [NumericState.eligibleCount] using unique.length_le_card

/-- Every stored knowledge word is legal at every slot, for every state of
the result type of every learner entry and restore boundary. -/
theorem knowledge_legal (state : NumericState config dimension) (idx : FeatIdx dimension) :
    config.rule.domain.range.Contains (state.weights.get idx).value ∧
      state.rails.range.Contains (state.beta.get idx).value :=
  ⟨weight_legal (state.weights.get idx), (state.beta.get idx).legal⟩

/-- The actual public prediction obeys the existing ordered-machine-sum
envelope on all admitted configurations, dimensions, states and active sets. -/
theorem prediction_bound (state : NumericState config dimension) (features : ActiveSet dimension) :
    (state.predict features).Finite ∧
      |numerical32 (state.predict features)| ≤ predictionRadius features.indices.length := by
  have bound := legal_weight_sum_bound config.rule
    (features.indices.map fun idx => state.weights.get idx)
  simpa [NumericState.predict, NumericState.linearPrediction_eq_sumFrom,
    List.map_map, Function.comp_def] using bound

/-- Clearing installs exact zero registers and an empty eligible sequence. -/
theorem clear_transient (state : NumericState config dimension) :
    state.clearTransient.transient = TransientState.zero dimension := rfl

/-- Clearing preserves all learned words and the receiver's derived rails. -/
theorem clear_knowledge (state : NumericState config dimension) :
    state.clearTransient.weights = state.weights ∧
      state.clearTransient.rails = state.rails ∧
      state.clearTransient.beta = state.beta := ⟨rfl, rfl, rfl⟩

/-- Initialization has no process-local selective-credit state. -/
theorem initial_transient :
    (NumericState.initial config dimension).transient = TransientState.zero dimension := rfl

/-- The full learner step returns the entry prediction and its ordered error,
before the loops write the next knowledge state. -/
theorem step_observation (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) :
    (state.step config features reward).2 =
      ⟨state.predict features,
        (reward.add (config.rule.gamma.mul (state.predict features))).sub
          state.transient.vOld⟩ := by
  rfl

/-- A terminal update clears every transient even when the raw target or
error is nonfinite. -/
theorem terminal_transient (state : NumericState config dimension) (target : Binary32) :
    (state.terminalStep config target).1.transient = TransientState.zero dimension := rfl

/-- Restore installation ends with the exact same clear boundary, independent
of either untrusted prefix length or any raw input encoding. -/
theorem install_transient (state : NumericState config dimension) (weights beta : List Binary32) :
    (state.installRestored weights beta).transient = TransientState.zero dimension := rfl

/-- Swap-remove decrements the eligible size by one for every valid position. -/
theorem swap_remove_size {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size) :
    (swapRemove items pos valid).size = items.size - 1 := by
  simp [swapRemove]

/-- Array uniqueness is exactly injectivity of valid indexed reads. -/
theorem array_nodup_iff {α : Type} (items : Array α) :
    items.toList.Nodup ↔
      ∀ (i j : Nat) (hi : i < items.size) (hj : j < items.size),
        items[i] = items[j] → i = j := by
  constructor
  · intro unique i j hi hj equality
    have equation : items.toList[i] = items.toList[j] := by
      simpa only [Array.getElem_toList] using equality
    exact unique.getElem_inj_iff.mp equation
  · intro injective
    apply List.nodup_iff_injective_getElem.mpr
    intro i j equality
    apply Fin.ext
    exact injective i.val j.val (by simp) (by simp)
      (by simpa using equality)

/-- Every surviving array position reads either its original element or the
original last element moved into the removed position. -/
theorem swap_remove_get {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size)
    (idx : Nat) (inside : idx < (swapRemove items pos valid).size) :
    (swapRemove items pos valid)[idx] =
      if pos = idx then items[items.size - 1] else items[idx]'(by
        rw [swap_remove_size] at inside; omega) := by
  simp [swapRemove, Array.getElem_set]

/-- Swap-remove cannot introduce an index that was absent from its input. -/
theorem swap_remove_subset {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size)
    (value : α) (member : value ∈ swapRemove items pos valid) : value ∈ items := by
  obtain ⟨idx, inside, equality⟩ := Array.mem_iff_getElem.mp member
  rw [swap_remove_get] at equality
  split at equality
  · exact equality ▸ Array.getElem_mem _
  · exact equality ▸ Array.getElem_mem _

/-- Every value other than the removed value survives swap-remove, even when
the input is a sequence with repeated members. -/
theorem swap_remove_preserves_other {α : Type} (items : Array α) (pos : Nat)
    (valid : pos < items.size) (value : α) (different : value ≠ items[pos])
    (member : value ∈ items) : value ∈ swapRemove items pos valid := by
  obtain ⟨idx, inside, equality⟩ := Array.mem_iff_getElem.mp member
  have notPos : pos ≠ idx := by intro same; subst idx; exact different equality.symm
  by_cases last : idx = items.size - 1
  · have remains : pos < (swapRemove items pos valid).size := by
      rw [swap_remove_size]; omega
    apply Array.mem_iff_getElem.mpr
    refine ⟨pos, remains, ?_⟩
    rw [swap_remove_get]
    simpa only [ite_true, ← last] using equality
  · have remains : idx < (swapRemove items pos valid).size := by
      rw [swap_remove_size]; omega
    apply Array.mem_iff_getElem.mpr
    refine ⟨idx, remains, ?_⟩
    rw [swap_remove_get, if_neg notPos]
    exact equality

/-- Unique eligible sequences stay unique through swap-remove. -/
theorem swap_remove_nodup {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size)
    (unique : items.toList.Nodup) : (swapRemove items pos valid).toList.Nodup := by
  apply (array_nodup_iff _).mpr
  intro i j hi hj equality
  have ib : i < items.size - 1 := by simpa [swap_remove_size] using hi
  have jb : j < items.size - 1 := by simpa [swap_remove_size] using hj
  rw [swap_remove_get, swap_remove_get] at equality
  split_ifs at equality with ip jp jp
  · omega
  · have same := (array_nodup_iff items).mp unique _ _ _ _ equality
    omega
  · have same := (array_nodup_iff items).mp unique _ _ _ _ equality
    omega
  · exact (array_nodup_iff items).mp unique _ _ _ _ equality

/-- Exact prefix/suffix semantics of the shared executing restoration loop. -/
theorem restore_prefix_get {α : Type} {capacity : Nat} (project : Binary32 → α)
    (values : Vector α capacity) (raw : List Binary32) (pos idx : Nat) (valid : idx < capacity) :
    (restorePrefix project values raw pos)[idx] =
      if inside : pos ≤ idx ∧ idx - pos < raw.length then
        project raw[idx - pos] else values[idx] := by
  induction raw generalizing values pos with
  | nil => simp [restorePrefix]
  | cons word rest ih =>
    rw [restorePrefix]
    split
    · rename_i inRange
      rw [ih]
      by_cases before : idx < pos
      · simp [show ¬pos ≤ idx by omega, show ¬pos + 1 ≤ idx by omega,
          show pos ≠ idx by omega]
      · by_cases same : pos = idx
        · subst pos
          simp [show ¬idx + 1 ≤ idx by omega]
        · have past : pos + 1 ≤ idx := by omega
          have successor : idx - pos = (idx - (pos + 1)) + 1 := by omega
          simp [past, show pos ≤ idx by omega, successor, same]
    · rename_i pastEnd
      simp [show ¬pos ≤ idx by omega]

/-- Restoring weights changes exactly the zipped prefix through the
receiver's immutable projection, preserving every original suffix word. -/
theorem restore_weights_get (state : NumericState config dimension) (raw : List Binary32)
    (idx : FeatIdx dimension) :
    ((state.restoreWeights raw).weights.get idx) =
      if inside : idx.val < raw.length then Weight.project config.rule raw[idx.val]
      else state.weights.get idx := by
  simpa [NumericState.restoreWeights, vector_get] using
    restore_prefix_get (Weight.project config.rule) state.weights raw 0 idx.val idx.isLt

/-- Restoring beta uses precisely the same zipped-prefix law with the
receiver's existing rails; there is no replacement learner or widened range. -/
theorem restore_beta_get (state : NumericState config dimension) (raw : List Binary32)
    (idx : FeatIdx dimension) :
    ((state.restoreLogStepSizes raw).beta.get idx).value =
      if inside : idx.val < raw.length then
        (LogStepSize.project state.rails raw[idx.val]).value
      else (state.beta.get idx).value := by
  have equation := restore_prefix_get (LogStepSize.project state.rails) state.beta raw
    0 idx.val idx.isLt
  simpa [NumericState.restoreLogStepSizes, vector_get, apply_dite] using
    congrArg (fun beta => beta.value) equation

/-- All nine per-index raw transient words, in their declared storage order. -/
def registers (state : NumericState config dimension) (idx : FeatIdx dimension) :
    Vector Binary32 9 :=
  #v[(state.transient.z.get idx).value, (state.transient.zDelta.get idx).value,
    (state.transient.zBar.get idx).value, (state.transient.lastAlpha.get idx).value,
    (state.transient.deltaWeight.get idx).value, (state.transient.h.get idx).value,
    (state.transient.hOld.get idx).value, (state.transient.hTemp.get idx).value,
    (state.transient.p.get idx).value]

/-- The selective-credit support contract, separate from numerical bounds. -/
def Supported (state : NumericState config dimension)
    (eligible : Array (FeatIdx dimension)) : Prop :=
  ∀ idx, idx ∉ eligible → registers state idx = Vector.replicate 9 Binary32.zero

/-- The reference alone has a finite nonnegative numerical bound; other
transient registers deliberately do not inherit it. -/
def ReferenceLegal (word : Binary32) : Prop :=
  word.Finite ∧ 0 ≤ numerical32 word ∧ numerical32 word ≤ 5

/-- Every pruning reference is legal, including dormant zero references. -/
def ReferencesLegal (state : NumericState config dimension) : Prop :=
  ∀ idx, ReferenceLegal (state.transient.lastAlpha.get idx).value

/-- The process-local invariant preserved without a caller scheduling premise. -/
def CoreInv (state : NumericState config dimension) : Prop :=
  Supported state state.transient.eligible ∧ ReferencesLegal state

/-- The condition needed immediately before an active-set admission: no
duplicate eligible index and no eligible zero trace. -/
def Ready (state : NumericState config dimension) : Prop :=
  state.transient.eligible.toList.Nodup ∧
    ∀ idx ∈ state.transient.eligible, (state.transient.z.get idx).value.isZero = false

/-- Reset establishes the complete support and reference invariants. -/
theorem clear_core (state : NumericState config dimension) : CoreInv state.clearTransient := by
  constructor
  · intro idx _
    simp only [registers, NumericState.clearTransient, TransientState.zero,
      vector_get, Vector.getElem_replicate]
    rfl
  · intro idx
    simp only [ReferenceLegal, NumericState.clearTransient, TransientState.zero,
      vector_get, Vector.getElem_replicate]
    exact ⟨by decide, le_refl 0, by change (0:ℚ) ≤ 5; norm_num⟩

/-- Reset also establishes the next admission's uniqueness and nonzero-trace
premises by its empty eligible sequence. -/
theorem clear_ready (state : NumericState config dimension) : Ready state.clearTransient := by
  simp [Ready, NumericState.clearTransient, TransientState.zero]

/-- Initialization establishes the same invariants through its actual storage constructor. -/
theorem initial_core : CoreInv (NumericState.initial config dimension) :=
  clear_core (NumericState.initial config dimension)

/-- Initialization establishes the same admission readiness as reset. -/
theorem initial_ready : Ready (NumericState.initial config dimension) :=
  clear_ready (NumericState.initial config dimension)

/-- Clearing one feature zeros all nine of its own raw registers. -/
theorem clear_feature_self (state : NumericState config dimension) (idx : FeatIdx dimension) :
    registers (state.clearFeatureRegisters idx) idx = Vector.replicate 9 Binary32.zero := by
  simp only [registers, NumericState.clearFeatureRegisters,
      NumericState.writeZ,
      NumericState.writeZDelta,
      NumericState.writeZBar,
      NumericState.writeLastAlpha,
      NumericState.writeDeltaWeight,
      NumericState.writeH,
      NumericState.writeHOld,
      NumericState.writeHTemp,
      NumericState.writeP,
      vector_get, Vector.getElem_set_self]
  rfl

/-- Clearing one feature leaves every other feature's registers unchanged. -/
theorem clear_feature_other (state : NumericState config dimension) (idx other : FeatIdx dimension)
    (different : idx ≠ other) :
    registers (state.clearFeatureRegisters idx) other = registers state other := by
  have distinct : idx.val ≠ other.val := fun same => different (Fin.ext same)
  simp only [registers, NumericState.clearFeatureRegisters,
      NumericState.writeZ,
      NumericState.writeZDelta,
      NumericState.writeZBar,
      NumericState.writeLastAlpha,
      NumericState.writeDeltaWeight,
      NumericState.writeH,
      NumericState.writeHOld,
      NumericState.writeHTemp,
      NumericState.writeP,
      vector_get, Vector.getElem_set, distinct, if_false]

/-- One first-loop visit cannot change another feature's knowledge or any of
its nine registers, regardless of projection, exceptional inputs or pruning. -/
theorem first_element_frame (state : NumericState config dimension) (idx other : FeatIdx dimension)
    (different : idx ≠ other) (delta vDelta decay : Binary32) :
    let next := (state.firstLoopElement idx delta vDelta decay).1
    next.weights.get other = state.weights.get other ∧
      (next.beta.get other).value = (state.beta.get other).value ∧
      registers next other = registers state other := by
  have distinct : idx.val ≠ other.val := fun same => different (Fin.ext same)
  simp only [NumericState.firstLoopElement, registers, vector_get,
    Vector.getElem_set, distinct, if_false, and_self]

/-- A first-loop visit preserves the complete pruning-reference array. -/
theorem first_element_reference (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).1.transient.lastAlpha =
      state.transient.lastAlpha := rfl

/-- A first-loop visit preserves the eligible sequence until its enclosing
traversal performs swap-remove. -/
theorem first_element_eligible (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).1.transient.eligible =
      state.transient.eligible := rfl

/-- The pruning decision reads the updated trace and its unchanged reference. -/
theorem first_element_prune (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    let result := state.firstLoopElement idx delta vDelta decay
    result.2 = (result.1.transient.z.get idx).value.lessOrEqual
      ((result.1.transient.lastAlpha.get idx).value.mul config.epsilon) := by
  simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self]

/-- Projection binding re-anchors the actual first-loop registers before
ordered adaptation and decay. Zero times a raw nonfinite decay is deliberately
left as a machine expression, not incorrectly simplified to zero. -/
theorem first_element_reanchor (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32)
    (clipped : ((Weight.project config.rule
      ((state.weights.get idx).value.add
        ((delta.mul (state.transient.z.get idx).value).sub
          ((state.transient.zDelta.get idx).value.mul vDelta)))).value.numericallyEqual
      ((state.weights.get idx).value.add
        ((delta.mul (state.transient.z.get idx).value).sub
          ((state.transient.zDelta.get idx).value.mul vDelta)))) = false) :
    let next := (state.firstLoopElement idx delta vDelta decay).1
    (next.transient.deltaWeight.get idx).value = Binary32.zero ∧
    (next.transient.hOld.get idx).value = Binary32.zero ∧
    (next.transient.h.get idx).value = Binary32.zero ∧
    (next.transient.p.get idx).value = Binary32.zero.mul decay ∧
    (next.transient.zBar.get idx).value = Binary32.zero.mul decay ∧
    (next.beta.get idx).value =
      (LogStepSize.project state.rails (state.rails.initial.value.add
        (((config.metaStep.div state.rails.initial.alpha).mul (delta.sub vDelta)).mul
          Binary32.zero))).value := by
  simp only [vector_get] at clipped
  simp [NumericState.firstLoopElement, vector_get, clipped]

/-- Overshoot clears the three adaptation registers only after the trace
increment reads the entry beta. The reference is that exact computed increment. -/
theorem second_element_overshoot (state : NumericState config dimension) (idx : FeatIdx dimension)
    (denominator total vDelta : Binary32) :
    let next := (NumericState.secondLoopElement config true denominator total state vDelta idx).1
    (next.transient.h.get idx).value = Binary32.zero ∧
    (next.transient.hTemp.get idx).value = Binary32.zero ∧
    (next.transient.zBar.get idx).value = Binary32.zero ∧
    (next.transient.lastAlpha.get idx).value =
      (config.eta.div denominator).mul (state.beta.get idx).alpha ∧
    (next.beta.get idx).value =
      (LogStepSize.project state.rails
        ((state.beta.get idx).value.add state.rails.decay)).value := by
  simp [NumericState.secondLoopElement, vector_get]

/-- One active visit cannot change another feature's knowledge or registers. -/
theorem second_element_frame (state : NumericState config dimension)
    (idx other : FeatIdx dimension) (different : idx ≠ other)
    (overshoot : Bool) (denominator total vDelta : Binary32) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    next.weights.get other = state.weights.get other ∧
      (next.beta.get other).value = (state.beta.get other).value ∧
      registers next other = registers state other := by
  have distinct : idx.val ≠ other.val := fun same => different (Fin.ext same)
  cases overshoot <;>
    simp only [NumericState.secondLoopElement, registers, vector_get,
      Vector.getElem_set, distinct, if_false, if_true, Bool.false_eq_true, and_self]

/-- The only eligible admission of an active visit reads the entry trace. -/
theorem second_element_eligible (state : NumericState config dimension) (idx : FeatIdx dimension)
    (overshoot : Bool) (denominator total vDelta : Binary32) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    next.transient.eligible = if (state.transient.z.get idx).value.isZero then
        state.transient.eligible.push idx else state.transient.eligible := rfl

/-- The zero-vector support equation includes the actual trace read by admission. -/
theorem registers_zero_trace (state : NumericState config dimension) (idx : FeatIdx dimension)
    (zero : registers state idx = Vector.replicate 9 Binary32.zero) :
    (state.transient.z.get idx).value = .zero := by
  have equation := congrArg (fun (words : Vector Binary32 9) => words[0]) zero
  simpa [registers] using equation

/-- Equality of register snapshots includes the actual admission trace. -/
theorem registers_trace_eq (left right : NumericState config dimension) (idx : FeatIdx dimension)
    (same : registers left idx = registers right idx) :
    (left.transient.z.get idx).value = (right.transient.z.get idx).value := by
  exact congrArg (fun (words : Vector Binary32 9) => words[0]) same

/-- Equality of register snapshots includes the pruning reference. -/
theorem registers_reference_eq (left right : NumericState config dimension)
    (idx : FeatIdx dimension) (same : registers left idx = registers right idx) :
    (left.transient.lastAlpha.get idx).value = (right.transient.lastAlpha.get idx).value := by
  exact congrArg (fun (words : Vector Binary32 9) => words[3]) same

/-- Clearing preserves reference legality at the modified and untouched slots. -/
theorem clear_feature_references (state : NumericState config dimension) (idx : FeatIdx dimension)
    (legal : ReferencesLegal state) : ReferencesLegal (state.clearFeatureRegisters idx) := by
  intro other
  by_cases same : idx = other
  · subst other
    have equation := congrArg (fun (words : Vector Binary32 9) => words[3])
      (clear_feature_self state idx)
    have zero : ((state.clearFeatureRegisters idx).transient.lastAlpha.get idx).value = .zero :=
      equation
    rw [zero]
    exact ⟨by decide, le_refl 0, by change (0:ℚ) ≤ 5; norm_num⟩
  · rw [registers_reference_eq _ _ other (clear_feature_other state idx other same)]
    exact legal other

/-- A visit inside a work sequence leaves its off-sequence support invariant. -/
theorem first_element_supported (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (idx : FeatIdx dimension) (member : idx ∈ work)
    (delta vDelta decay : Binary32) (support : Supported state work) :
    Supported (state.firstLoopElement idx delta vDelta decay).1 work := by
  intro other absent
  have different : idx ≠ other := by intro same; exact absent (same ▸ member)
  rw [(first_element_frame state idx other different delta vDelta decay).2.2]
  exact support other absent

/-- A pruned feature's complete clear closes the support contract for the
shortened work sequence; unrelated members survive the actual swap-remove. -/
theorem prune_supported (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (valid : pos < work.size)
    (support : Supported state work) :
    Supported (state.clearFeatureRegisters work[pos]) (swapRemove work pos valid) := by
  intro other absent
  by_cases same : work[pos] = other
  · subst other
    exact clear_feature_self state work[pos]
  · rw [clear_feature_other state work[pos] other same]
    apply support other
    intro member
    exact absent (swap_remove_preserves_other work pos valid other (Ne.symm same) member)

/-- Every first-loop traversal preserves support and reference legality over
all raw arguments and arbitrary eligible sequences, including duplicates. -/
theorem first_loop_go_core (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32)
    (support : Supported state work) (references : ReferencesLegal state) :
    CoreInv (NumericState.learnFirstLoopGo config delta vDelta decay state work pos) := by
  induction state, work, pos using
      NumericState.learnFirstLoopGo.induct config delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    have nextSupport : Supported next work := by
      simpa only [equation] using first_element_supported state work work[pos]
        (Array.getElem_mem valid) delta vDelta decay support
    have nextReferences : ReferencesLegal next := by
      have unchanged := first_element_reference state work[pos] delta vDelta decay
      rw [equation] at unchanged
      intro idx
      simpa only [← unchanged] using references idx
    have result := ih (prune_supported next work pos valid nextSupport)
      (clear_feature_references next work[pos] nextReferences)
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, ite_true] using result
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    have nextSupport : Supported next work := by
      simpa only [equation] using first_element_supported state work work[pos]
        (Array.getElem_mem valid) delta vDelta decay support
    have nextReferences : ReferencesLegal next := by
      have unchanged := first_element_reference state work[pos] delta vDelta decay
      rw [equation] at unchanged
      intro idx
      simpa only [← unchanged] using references idx
    have result := ih nextSupport nextReferences
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, if_neg noPrune] using result
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo, dif_neg finished]
    exact ⟨support, references⟩

/-- The public first loop preserves the core invariant with no scheduling or
normal-stream restriction on its raw delta, shared accumulator or decay. -/
theorem first_loop_core (state : NumericState config dimension) (delta vDelta decay : Binary32)
    (core : CoreInv state) : CoreInv (state.learnFirstLoop config delta vDelta decay) := by
  exact first_loop_go_core _ _ _ _ _ _ core.1 core.2

/-- Every active visit records exactly its normalized increment as its
pruning reference, before any overshoot beta decay. -/
theorem second_element_reference (state : NumericState config dimension) (idx : FeatIdx dimension)
    (overshoot : Bool) (denominator total vDelta : Binary32) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    (next.transient.lastAlpha.get idx).value =
      (config.eta.div denominator).mul (state.beta.get idx).alpha := by
  simp only [NumericState.secondLoopElement, vector_get, Vector.getElem_set_self]

/-- Existing eligible members survive an active visit in their existing order. -/
theorem second_element_contains (state : NumericState config dimension)
    (idx other : FeatIdx dimension) (overshoot : Bool) (denominator total vDelta : Binary32)
    (member : other ∈ state.transient.eligible) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    other ∈ next.transient.eligible := by
  dsimp only
  rw [second_element_eligible]
  split
  · exact Array.mem_push.mpr (Or.inl member)
  · exact member

/-- Support makes the active slot eligible after its visit: either it was
already eligible, or its dormant zero trace causes admission. -/
theorem second_element_self (state : NumericState config dimension) (idx : FeatIdx dimension)
    (overshoot : Bool) (denominator total vDelta : Binary32)
    (support : Supported state state.transient.eligible) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    idx ∈ next.transient.eligible := by
  dsimp only
  rw [second_element_eligible]
  split
  · exact Array.mem_push.mpr (Or.inr rfl)
  · rename_i nonzero
    by_contra absent
    have zero := registers_zero_trace state idx (support idx absent)
    rw [zero] at nonzero
    exact nonzero rfl

/-- An active visit preserves all dormant-zero support, even if the eligible
sequence already has duplicates or the newly written trace becomes zero. -/
theorem second_element_supported (state : NumericState config dimension) (idx : FeatIdx dimension)
    (overshoot : Bool) (denominator total vDelta : Binary32)
    (support : Supported state state.transient.eligible) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    Supported next next.transient.eligible := by
  dsimp only
  intro other absent
  have different : idx ≠ other := by
    intro same
    exact absent (same ▸ second_element_self state idx overshoot denominator total vDelta support)
  rw [(second_element_frame state idx other different overshoot denominator total vDelta).2.2]
  apply support other
  intro member
  exact absent (second_element_contains state idx other overshoot denominator total vDelta member)

/-- A normalized active visit preserves the core invariant, over all raw
total-trace and shared-accumulator words. -/
theorem second_element_core (state : NumericState config dimension) (idx : FeatIdx dimension)
    (rate total vDelta : Binary32) (finite : rate.Finite) (core : CoreInv state) :
    let overshoot := config.eta.less rate
    let denominator := if overshoot then rate else config.eta
    CoreInv
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1 := by
  refine ⟨second_element_supported state idx _ _ _ _ core.1, ?_⟩
  intro other
  by_cases same : idx = other
  · subst other
    rw [second_element_reference]
    exact trace_increment_numeric (state.beta.get idx) rate finite
  · rw [registers_reference_eq _ _ other
      (second_element_frame state idx other same _ _ _ _).2.2]
    exact core.2 other

/-- Finite-prefix composition of the actual active traversal preserves the
core invariant. No uniqueness premise is needed for this weaker guarantee. -/
theorem second_fold_core (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) (rate total vDelta : Binary32)
    (finite : rate.Finite) (core : CoreInv state) :
    let overshoot := config.eta.less rate
    let denominator := if overshoot then rate else config.eta
    CoreInv (indices.foldl (fun (s, vd) idx =>
      NumericState.secondLoopElement config overshoot denominator total s vd idx)
        (state, vDelta)).1 := by
  induction indices generalizing state vDelta with
  | nil => exact core
  | cons idx rest ih =>
    exact ih _ _ (second_element_core state idx rate total vDelta finite core)

/-- The public second loop preserves the core invariant on every call,
including consecutive standalone calls with arbitrary shared accumulators. -/
theorem second_loop_core (state : NumericState config dimension) (features : ActiveSet dimension)
    (vDelta : Binary32) (core : CoreInv state) :
    CoreInv (state.learnSecondLoop config features vDelta).1 := by
  have finite := alpha_sum_finite (features.indices.map fun idx => state.beta.get idx)
  simp only [List.map_map, Function.comp_def] at finite
  rw [NumericState.learnSecondLoop_eq_sumFrom]
  exact second_fold_core features.indices state _ _ vDelta finite core

/-- Exact eligible-sequence change of the actual fold over unique active
indices. The filter reads the entry state because earlier distinct visits
cannot alter a later feature's trace. -/
theorem second_fold_eligible (indices : List (FeatIdx dimension)) (unique : indices.Nodup)
    (state : NumericState config dimension) (overshoot : Bool)
    (denominator total vDelta : Binary32) :
    (indices.foldl (fun (s, vd) idx =>
      NumericState.secondLoopElement config overshoot denominator total s vd idx)
        (state, vDelta)).1.transient.eligible.toList =
      state.transient.eligible.toList ++
        indices.filter (fun idx => (state.transient.z.get idx).value.isZero) := by
  induction indices generalizing state vDelta with
  | nil => simp
  | cons idx rest ih =>
    rw [List.foldl_cons]
    have notRest := (List.nodup_cons.mp unique).1
    have restUnique := (List.nodup_cons.mp unique).2
    rw [ih restUnique]
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    have unchanged : rest.filter (fun other => (next.transient.z.get other).value.isZero) =
        rest.filter (fun other => (state.transient.z.get other).value.isZero) := by
      apply List.filter_congr
      intro other member
      have different : idx ≠ other := by intro same; exact notRest (same ▸ member)
      rw [registers_trace_eq _ _ other
        (second_element_frame state idx other different overshoot denominator total vDelta).2.2]
    dsimp only [next] at unchanged
    rw [unchanged, second_element_eligible]
    split <;> simp_all [List.append_assoc]

/-- The public second loop appends exactly the active indices whose entry
trace is zero. This identity covers every state, including arbitrary existing
duplicates, signed zero and exceptional transient encodings. -/
theorem second_loop_eligible (state : NumericState config dimension)
    (features : ActiveSet dimension)
    (vDelta : Binary32) :
    (state.learnSecondLoop config features vDelta).1.transient.eligible.toList =
      state.transient.eligible.toList ++
        features.indices.filter (fun idx => (state.transient.z.get idx).value.isZero) :=
  second_fold_eligible features.indices features.nodup state _ _ _ vDelta

/-- The actual eligible count grows by precisely the number of zero-trace
active admissions; repeated calls have no unconditional capacity bound. -/
theorem second_loop_count (state : NumericState config dimension) (features : ActiveSet dimension)
    (vDelta : Binary32) :
    (state.learnSecondLoop config features vDelta).1.eligibleCount = state.eligibleCount +
      (features.indices.filter (fun idx => (state.transient.z.get idx).value.isZero)).length := by
  have equation := congrArg List.length (second_loop_eligible state features vDelta)
  simpa [NumericState.eligibleCount] using equation

/-- One second loop adds at most the active-set cardinality, even for an
undisciplined caller whose existing eligible sequence has duplicates. -/
theorem second_loop_count_le (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    (state.learnSecondLoop config features vDelta).1.eligibleCount ≤
      state.eligibleCount + features.indices.length := by
  rw [second_loop_count]
  exact Nat.add_le_add_left (List.length_filter_le _ _) _

/-- A ready state admits no existing eligible member; active-set uniqueness
then suffices for the resulting eligible sequence to remain unique. -/
theorem second_loop_unique (state : NumericState config dimension) (features : ActiveSet dimension)
    (vDelta : Binary32) (ready : Ready state) :
    (state.learnSecondLoop config features vDelta).1.transient.eligible.toList.Nodup := by
  rw [second_loop_eligible]
  apply List.nodup_append.mpr
  refine ⟨ready.1, features.nodup.filter _, ?_⟩
  intro old oldMember fresh freshMember same
  have zero := (List.mem_filter.mp freshMember).2
  have nonzero := ready.2 old (by simpa using oldMember)
  rw [← same, nonzero] at zero
  contradiction

/-- A retained first-loop visit cannot leave a zero trace: its legal
reference makes either zero encoding satisfy the actual pruning comparison. -/
theorem first_element_retained_nonzero (state : NumericState config dimension)
    (idx : FeatIdx dimension) (delta vDelta decay : Binary32)
    (references : ReferencesLegal state)
    (retained : (state.firstLoopElement idx delta vDelta decay).2 = false) :
    ((state.firstLoopElement idx delta vDelta decay).1.transient.z.get idx).value.isZero
      = false := by
  apply Bool.eq_false_iff.mpr
  intro zero
  have reference := references idx
  have threshold := pruning_threshold_numeric config (state.transient.lastAlpha.get idx).value
    reference.1 reference.2.1 reference.2.2
  have prunes := zero_pruned _ _ zero (Binary32.finite_not_nan _ threshold.1) threshold.2
  have decision := first_element_prune state idx delta vDelta decay
  dsimp only at decision
  rw [first_element_reference] at decision
  rw [← decision, retained] at prunes
  contradiction

/-- Every processed position has a nonzero trace; the unprocessed suffix has
no such premise. This follows the actual swap-remove cursor. -/
def Processed (state : NumericState config dimension) (work : Array (FeatIdx dimension))
    (pos : Nat) : Prop :=
  ∀ (idx : Nat) (valid : idx < work.size), idx < pos →
    (state.transient.z.get work[idx]).value.isZero = false

/-- Processing a distinct position leaves every earlier processed trace alone. -/
theorem first_element_processed (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (valid : pos < work.size)
    (delta vDelta decay : Binary32) (unique : work.toList.Nodup)
    (processed : Processed state work pos) :
    Processed (state.firstLoopElement work[pos] delta vDelta decay).1 work pos := by
  intro idx inside before
  have different : work[pos] ≠ work[idx] := by
    intro same
    have := (array_nodup_iff work).mp unique pos idx valid inside same
    omega
  rw [registers_trace_eq _ _ work[idx]
    (first_element_frame state work[pos] work[idx] different delta vDelta decay).2.2]
  exact processed idx inside before

/-- Pruning does not move or clear an earlier processed feature in a unique
work sequence. The moved tail occupies the current unprocessed position. -/
theorem prune_processed (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (valid : pos < work.size)
    (unique : work.toList.Nodup) (processed : Processed state work pos) :
    Processed (state.clearFeatureRegisters work[pos]) (swapRemove work pos valid) pos := by
  intro idx inside before
  have original : idx < work.size := by rw [swap_remove_size] at inside; omega
  have different : work[pos] ≠ work[idx] := by
    intro same
    have := (array_nodup_iff work).mp unique pos idx valid original same
    omega
  have untouched : (swapRemove work pos valid)[idx] = work[idx] := by
    rw [swap_remove_get, if_neg (show pos ≠ idx by omega)]
  rw [untouched, registers_trace_eq _ _ work[idx]
    (clear_feature_other state work[pos] work[idx] different)]
  exact processed idx original before

/-- From unique entry eligibility, the first loop re-establishes admission
readiness. Raw deltas and decays remain unrestricted; reference legality is
the numerical premise that justifies the zero-pruning step. -/
theorem first_loop_go_ready (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32)
    (unique : work.toList.Nodup) (references : ReferencesLegal state)
    (processed : Processed state work pos) :
    Ready (NumericState.learnFirstLoopGo config delta vDelta decay state work pos) := by
  induction state, work, pos using
      NumericState.learnFirstLoopGo.induct config delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    have nextReferences : ReferencesLegal next := by
      have unchanged := first_element_reference state work[pos] delta vDelta decay
      rw [equation] at unchanged
      intro idx
      simpa only [← unchanged] using references idx
    have nextProcessed : Processed next work pos := by
      simpa only [equation] using
        first_element_processed state work pos valid delta vDelta decay unique processed
    have result := ih (swap_remove_nodup work pos valid unique)
      (clear_feature_references next work[pos] nextReferences)
      (prune_processed next work pos valid unique nextProcessed)
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, ite_true] using result
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    have nextReferences : ReferencesLegal next := by
      have unchanged := first_element_reference state work[pos] delta vDelta decay
      rw [equation] at unchanged
      intro idx
      simpa only [← unchanged] using references idx
    have earlier : Processed next work pos := by
      simpa only [equation] using
        first_element_processed state work pos valid delta vDelta decay unique processed
    have here : (next.transient.z.get work[pos]).value.isZero = false := by
      have retained : (state.firstLoopElement work[pos] delta vDelta decay).2 = false := by
        rw [equation]
        exact Bool.eq_false_iff.mpr noPrune
      simpa only [equation] using
        first_element_retained_nonzero state work[pos] delta vDelta decay references retained
    have nextProcessed : Processed next work (pos + 1) := by
      intro j inside before
      by_cases same : j = pos
      · subst j
        exact here
      · exact earlier j inside (by omega)
    have result := ih unique nextReferences nextProcessed
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, if_neg noPrune] using result
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo, dif_neg finished]
    refine ⟨unique, ?_⟩
    intro idx member
    obtain ⟨j, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    change j < work.size at inside
    exact processed j inside (by omega)

/-- The public first loop makes a unique eligible state ready for the next
second-loop admission. It does not manufacture uniqueness from a duplicate input. -/
theorem first_loop_ready (state : NumericState config dimension) (delta vDelta decay : Binary32)
    (unique : state.transient.eligible.toList.Nodup) (references : ReferencesLegal state) :
    Ready (state.learnFirstLoop config delta vDelta decay) := by
  unfold NumericState.learnFirstLoop
  apply first_loop_go_ready
  · exact unique
  · exact references
  · intro idx valid before
    omega

/-- Equal complete transient storage carries the same core invariant,
independently of any legal weight or beta changes. -/
theorem core_of_transient_eq (before after : NumericState config dimension)
    (same : after.transient = before.transient) (core : CoreInv before) : CoreInv after := by
  simpa only [CoreInv, Supported, ReferencesLegal, registers, same] using core

/-- Equal complete transient storage carries the same admission readiness. -/
theorem ready_of_transient_eq (before after : NumericState config dimension)
    (same : after.transient = before.transient) (ready : Ready before) : Ready after := by
  simpa only [Ready, same] using ready

/-- The actual background weight traversal leaves every transient array,
eligible element and aggregate word exactly unchanged. -/
theorem plan_fold_transient (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) (scale delta : Binary32) :
    (indices.foldl (fun s idx =>
      let stepSize := (scale.mul (s.beta.get idx).alpha).mul delta
      s.writeWeight idx ((s.weights.get idx).value.add stepSize)) state).transient =
      state.transient := by
  induction indices generalizing state with
  | nil => rfl
  | cons idx rest ih => exact ih _

/-- Planning preserves exact process-local storage on both the no-update and
update branches, for every raw target. -/
theorem plan_transient (state : NumericState config dimension) (features : ActiveSet dimension)
    (target : Binary32) :
    (state.planStep config features target).1.transient = state.transient := by
  dsimp only [NumericState.planStep]
  split
  · rfl
  · exact plan_fold_transient features.indices state _ _

/-- Every complete TD step preserves the core invariant, including its two
aggregate writes after the actual loops. -/
theorem step_core (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) (core : CoreInv state) :
    CoreInv (state.step config features reward).1 := by
  exact second_loop_core _ features .zero (first_loop_core state _ _ _ core)

/-- Beginning a trajectory establishes the core invariant from any raw
numeric state because it first clears every process-local register. -/
theorem begin_core (state : NumericState config dimension) (features : ActiveSet dimension) :
    CoreInv (state.beginTrajectory config features) := by
  exact second_loop_core state.clearTransient features .zero (clear_core state)

/-- Terminal update clears establish the core invariant independently of
the entry transients and the raw target. -/
theorem terminal_core (state : NumericState config dimension) (target : Binary32) :
    CoreInv (state.terminalStep config target).1 := clear_core _

/-- Exclusive restoration establishes the core invariant from any entry state. -/
theorem install_core (state : NumericState config dimension) (weights beta : List Binary32) :
    CoreInv (state.installRestored weights beta) := clear_core _

/-- Clearing one slot without removing eligibility preserves dormant support. -/
theorem clear_feature_supported (state : NumericState config dimension) (idx : FeatIdx dimension)
    (support : Supported state state.transient.eligible) :
    Supported (state.clearFeatureRegisters idx) state.transient.eligible := by
  intro other absent
  by_cases same : idx = other
  · subst other
    exact clear_feature_self state idx
  · rw [clear_feature_other state idx other same]
    exact support other absent

/-- Retirement preserves the core invariant, removing precisely the first
matching eligible occurrence and zeroing the retired slot and aggregates. -/
theorem retire_core (state : NumericState config dimension) (idx : FeatIdx dimension)
    (core : CoreInv state) : CoreInv (state.retireIndex idx) := by
  unfold NumericState.retireIndex
  split
  · rename_i pos found
    obtain ⟨valid, same, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have equality : state.transient.eligible[pos] = idx := by simpa using same
    have support := prune_supported state state.transient.eligible pos valid core.1
    rw [equality] at support
    exact ⟨support, clear_feature_references state idx core.2⟩
  · exact ⟨clear_feature_supported state idx core.1, clear_feature_references state idx core.2⟩

/-- Every constructor of the complete public interface preserves the core
invariant. The closed operation domain makes omissions a compiler error. -/
theorem entry_core (entry : Entry dimension) (state : NumericState config dimension)
    (core : CoreInv state) : CoreInv (entry.apply state) := by
  cases entry with
  | first delta vDelta decay => exact first_loop_core state delta vDelta decay core
  | second features vDelta => exact second_loop_core state features vDelta core
  | step features reward => exact step_core state features reward core
  | beginTrajectory features => exact begin_core state features
  | terminal target => exact terminal_core state target
  | plan features target =>
    exact core_of_transient_eq state _ (plan_transient state features target) core
  | retire idx => exact retire_core state idx core
  | restoreWeights raw => exact core
  | restoreBeta raw => exact core
  | install weights beta => exact install_core state weights beta
  | clear => exact clear_core state

/-- All finite interface histories from a valid state preserve the core
invariant, without a normal-stream or loop-scheduling restriction. -/
theorem entries_core (entries : List (Entry dimension)) (state : NumericState config dimension)
    (core : CoreInv state) : CoreInv (entries.foldl (fun s entry => entry.apply s) state) := by
  induction entries generalizing state with
  | nil => exact core
  | cons entry rest ih => exact ih _ (entry_core entry state core)

/-- Admission provenance proves the core invariant for every inhabitant of
the executing learner type. No client-supplied invariant assumption is needed. -/
theorem admitted_core (state : NumericState config dimension)
    (admitted : Admitted config dimension state) :
    CoreInv state := by
  induction admitted with
  | initial => exact initial_core
  | transition entry _ ih => exact entry_core entry _ ih

/-- Every admitted learner has legal knowledge, dormant-zero support and
legal pruning references through its actual construction/write boundary. -/
theorem learner_invariant (learner : Learner config dimension) (idx : FeatIdx dimension) :
    config.rule.domain.range.Contains (learner.val.weights.get idx).value ∧
      learner.val.rails.range.Contains (learner.val.beta.get idx).value ∧ CoreInv learner.val :=
  ⟨(knowledge_legal learner.val idx).1, (knowledge_legal learner.val idx).2,
    admitted_core learner.val learner.property⟩

/-- Removing a position from a unique sequence removes its value entirely. -/
theorem swap_remove_absent {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size)
    (unique : items.toList.Nodup) : items[pos] ∉ swapRemove items pos valid := by
  intro member
  obtain ⟨j, inside, equality⟩ := Array.mem_iff_getElem.mp member
  have bound : j < items.size - 1 := by simpa [swap_remove_size] using inside
  rw [swap_remove_get] at equality
  split at equality
  · rename_i same
    have last := (array_nodup_iff items).mp unique _ _ _ _ equality
    omega
  · rename_i different
    have same := (array_nodup_iff items).mp unique _ _ _ _ equality
    omega

/-- Retirement preserves eligible uniqueness when it holds at entry. -/
theorem retire_unique (state : NumericState config dimension) (idx : FeatIdx dimension)
    (unique : state.transient.eligible.toList.Nodup) :
    (state.retireIndex idx).transient.eligible.toList.Nodup := by
  unfold NumericState.retireIndex
  split
  · exact swap_remove_nodup _ _ _ unique
  · exact unique

/-- Retirement preserves admission readiness: its cleared slot is absent
from the unique surviving sequence and every other trace is unchanged. -/
theorem retire_ready (state : NumericState config dimension) (idx : FeatIdx dimension)
    (ready : Ready state) : Ready (state.retireIndex idx) := by
  refine ⟨retire_unique state idx ready.1, ?_⟩
  unfold NumericState.retireIndex
  split
  · rename_i pos found
    obtain ⟨valid, same, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have equality : state.transient.eligible[pos] = idx := by simpa using same
    have removed := swap_remove_absent state.transient.eligible pos valid ready.1
    rw [equality] at removed
    intro other member
    have different : idx ≠ other := by intro same; exact removed (same ▸ member)
    have frame := registers_trace_eq _ _ other (clear_feature_other state idx other different)
    change ((state.clearFeatureRegisters idx).transient.z.get other).value.isZero = false
    rw [frame]
    exact ready.2 other (swap_remove_subset state.transient.eligible pos valid other member)
  · rename_i found
    have absent : idx ∉ state.transient.eligible := by
      intro member
      have noMatch := Array.findIdx?_eq_none_iff.mp found idx member
      simp at noMatch
    intro other member
    have different : idx ≠ other := by intro same; exact absent (same ▸ member)
    have frame := registers_trace_eq _ _ other (clear_feature_other state idx other different)
    change ((state.clearFeatureRegisters idx).transient.z.get other).value.isZero = false
    rw [frame]
    exact ready.2 other member

/-- The caller's phase after one operation. `true` means an immediately
following standalone second loop has the required admission premises. -/
abbrev nextReady (entry : Entry dimension) (before : Bool) : Bool :=
  SwiftTd.nextReady entry before

/-- The sole scheduling restriction for the capacity bound. It is a premise
of the stronger theorem, not a restriction on the public executing interface. -/
abbrev Permitted (entry : Entry dimension) (ready : Bool) : Prop :=
  SwiftTd.Permitted entry ready

/-- Phase-indexed resource invariant, separate from unrestricted core safety. -/
def ScheduleInv (state : NumericState config dimension) (phase : Bool) : Prop :=
  CoreInv state ∧ state.transient.eligible.toList.Nodup ∧ (phase = true → Ready state)

/-- Each permitted public operation preserves the stronger resource
invariant under its derived next phase. -/
theorem entry_schedule (entry : Entry dimension) (state : NumericState config dimension)
    (phase : Bool) (permitted : Permitted entry phase) (invariant : ScheduleInv state phase) :
    ScheduleInv (entry.apply state) (nextReady entry phase) := by
  refine ⟨entry_core entry state invariant.1, ?_⟩
  cases entry with
  | first delta vDelta decay =>
    have ready := first_loop_ready state delta vDelta decay invariant.2.1 invariant.1.2
    exact ⟨ready.1, fun _ => ready⟩
  | second features vDelta =>
    exact ⟨second_loop_unique state features vDelta (invariant.2.2 permitted),
      fun impossible => Bool.noConfusion impossible⟩
  | step features reward =>
    exact ⟨second_loop_unique _ features .zero
      (first_loop_ready state _ _ _ invariant.2.1 invariant.1.2),
      fun impossible => Bool.noConfusion impossible⟩
  | beginTrajectory features =>
    exact ⟨second_loop_unique _ features .zero (clear_ready state),
      fun impossible => Bool.noConfusion impossible⟩
  | terminal target =>
    have ready : Ready (state.terminalStep config target).1 := clear_ready _
    exact ⟨ready.1, fun _ => ready⟩
  | install weights beta =>
    have ready : Ready (state.installRestored weights beta) := clear_ready _
    exact ⟨ready.1, fun _ => ready⟩
  | clear => exact ⟨(clear_ready state).1, fun _ => clear_ready state⟩
  | restoreWeights raw => exact invariant.2
  | restoreBeta raw => exact invariant.2
  | plan features target =>
    have same := plan_transient state features target
    exact ⟨by simpa only [Entry.apply, same] using invariant.2.1,
      fun hp => ready_of_transient_eq state _ same (invariant.2.2 hp)⟩
  | retire idx =>
    exact ⟨retire_unique state idx invariant.2.1,
      fun hp => retire_ready state idx (invariant.2.2 hp)⟩

/-- All finite histories obeying the phase discipline, including exposed
loop, restore, planning and retirement calls. -/
def Scheduled : List (Entry dimension) → Bool → Prop
  | [], _ => True
  | entry :: rest, phase => Permitted entry phase ∧ Scheduled rest (nextReady entry phase)

/-- Final scheduling phase, derived by folding the same closed operation domain. -/
def finalPhase (entries : List (Entry dimension)) (phase : Bool) : Bool :=
  entries.foldl (fun before entry => nextReady entry before) phase

/-- Universal finite-prefix resource preservation under the explicit phase
discipline; the executing state fold is the same interface fold as core safety. -/
theorem entries_schedule (entries : List (Entry dimension)) (state : NumericState config dimension)
    (phase : Bool) (scheduled : Scheduled entries phase) (invariant : ScheduleInv state phase) :
    ScheduleInv (entries.foldl (fun s entry => entry.apply s) state)
      (finalPhase entries phase) := by
  induction entries generalizing state phase with
  | nil => exact invariant
  | cons entry rest ih =>
    exact ih _ _ scheduled.2 (entry_schedule entry state phase scheduled.1 invariant)

/-- Every disciplined finite history from initialization retains at most N
eligible indices. The proof covers all admitted dimensions and configurations. -/
theorem scheduled_capacity (entries : List (Entry dimension)) (scheduled : Scheduled entries true) :
    (entries.foldl (fun s entry => entry.apply s)
      (NumericState.initial config dimension)).eligibleCount ≤ dimension.capacity := by
  apply eligible_cardinality
  exact (entries_schedule entries _ true scheduled
    ⟨initial_core, initial_ready.1, fun _ => initial_ready⟩).2.1

/-- Each pruned recursive branch consumes exactly one position of remaining
work, including removal of the final position. -/
theorem prune_work_decreases {α : Type} (work : Array α) (pos : Nat) (valid : pos < work.size) :
    (swapRemove work pos valid).size - pos + 1 = work.size - pos := by
  rw [swap_remove_size]
  omega

/-- Each retained recursive branch consumes exactly one position of remaining work. -/
theorem retain_work_decreases {α : Type} (work : Array α) (pos : Nat) (valid : pos < work.size) :
    work.size - (pos + 1) + 1 = work.size - pos := by omega

/-- First-loop traversal never increases eligible length, for any raw state
or cursor and without a uniqueness premise. -/
theorem first_loop_go_size (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32) :
    (NumericState.learnFirstLoopGo config delta vDelta decay state work pos).eligibleCount ≤
      work.size := by
  induction state, work, pos using
      NumericState.learnFirstLoopGo.induct config delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simp only [equation, ite_true]
    exact le_trans ih (by rw [swap_remove_size]; omega)
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, if_neg noPrune] using ih
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo, dif_neg finished]
    exact le_refl _

/-- Logical retained slots are counted from every executing state vector,
the eligible array and both scalar aggregate registers. Object headers, boxed
word representation, allocator capacity and sharing are separate native costs. -/
def retainedSlots (state : NumericState config dimension) : Nat :=
  state.weights.toArray.size + state.beta.toArray.size +
    state.transient.z.toArray.size + state.transient.zDelta.toArray.size +
    state.transient.zBar.toArray.size + state.transient.lastAlpha.toArray.size +
    state.transient.deltaWeight.toArray.size + state.transient.h.toArray.size +
    state.transient.hOld.toArray.size + state.transient.hTemp.toArray.size +
    state.transient.p.toArray.size + state.transient.eligible.size + 2

/-- The storage representation derives eleven dimension-sized arrays plus
the current eligible sequence and two aggregates, for every raw state. -/
theorem retained_slots_exact (state : NumericState config dimension) :
    retainedSlots state = 11 * dimension.capacity + state.eligibleCount + 2 := by
  simp only [retainedSlots, Vector.size_toArray, NumericState.eligibleCount]
  omega

/-- Under eligible uniqueness the logical retained storage is at most
`12N+2` slots, independently of the duration of the stream. -/
theorem retained_slots_unique (state : NumericState config dimension)
    (unique : state.transient.eligible.toList.Nodup) :
    retainedSlots state ≤ 12 * dimension.capacity + 2 := by
  rw [retained_slots_exact]
  have bound := eligible_cardinality state unique
  omega

/-- Every disciplined finite prefix from initialization has the same linear
retained-storage bound; no operation log is part of the executing state. -/
theorem scheduled_storage (entries : List (Entry dimension)) (scheduled : Scheduled entries true) :
    retainedSlots (entries.foldl (fun s entry => entry.apply s)
      (NumericState.initial config dimension)) ≤ 12 * dimension.capacity + 2 := by
  rw [retained_slots_exact]
  have bound : (entries.foldl (fun s entry => entry.apply s)
      (NumericState.initial config dimension)).eligibleCount ≤ dimension.capacity :=
    scheduled_capacity entries scheduled
  omega

/-- Retirement clears every register and both aggregate words, and restores
fresh knowledge at the retired slot even for arbitrary raw pre-state. -/
theorem retire_registers (state : NumericState config dimension) (idx : FeatIdx dimension) :
    registers (state.retireIndex idx) idx = Vector.replicate 9 Binary32.zero ∧
    ((state.retireIndex idx).weights.get idx).value = Binary32.zero ∧
    ((state.retireIndex idx).beta.get idx).value = state.rails.initial.value ∧
    (state.retireIndex idx).transient.vOld = Binary32.zero ∧
    (state.retireIndex idx).transient.vDelta = Binary32.zero := by
  unfold NumericState.retireIndex
  have zero := config.rule.domain.symmetric_project_identity
    Binary32.zero config.rule.domain.zeroLegal
  split <;> simp [registers, NumericState.removeEligibleAt,
    NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha, NumericState.writeWeight, NumericState.writeBetaValue,
    vector_get, Weight.project, Bounded32.projectSymmetric, zero, Weight.value,
    show Array.replicate 9 Binary32.zero =
      #[Binary32.zero, Binary32.zero, Binary32.zero, Binary32.zero, Binary32.zero,
        Binary32.zero, Binary32.zero, Binary32.zero, Binary32.zero] from rfl]

/-- The normalized observer's count is the actual eligible length, including
repeated members admitted by unrestricted standalone second loops. -/
theorem normalized_count (state : NumericState config dimension) :
    state.normalizedStepSizeSum.2 = state.eligibleCount := by
  simp only [NumericState.normalizedStepSizeSum, NumericState.eligibleCount]
  split
  · rename_i empty
    simp_all
  · rfl

/-- Clearing also resets the two eligible-set observers to their empty values. -/
theorem clear_observers (state : NumericState config dimension) :
    state.clearTransient.activeAlpha = Binary32.zero ∧
    state.clearTransient.normalizedStepSizeSum = (Binary32.zero, 0) := ⟨rfl, rfl⟩

/-- Exploration-rate legality is carried at storage for every raw producer,
including NaN and either infinity. -/
theorem exploration_legal (raw : Binary32) :
    exploreRange.Contains (ExploreRate.project raw).value :=
  (ExploreRate.project raw).legal

/-- A reader built from one learner uses precisely its own retirement predicate. -/
theorem consumer_own (state : NumericState config dimension) (idx : FeatIdx dimension) :
    (Consumer.of state).negligible idx = state.unitIsNegligible idx := rfl

/-- Every-consumer retirement is exactly conjunction over the supplied nonempty
reader vector; no consumer can be skipped. -/
theorem every_consumer {rails : StepSizeRails config} {count : Nat}
    (consumers : Vector (Consumer (dimension := dimension) rails) (count + 1))
    (idx : FeatIdx dimension) :
    unitNegligibleInEvery consumers idx = true ↔
      ∀ reader ∈ consumers.toList, reader.negligible idx = true := by
  exact List.all_eq_true

end AcornVerif.CurrentLearner
