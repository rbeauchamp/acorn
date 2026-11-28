import Acorn.SwiftTd
import AcornVerif.CurrentPrediction
import AcornVerif.CurrentState
import AcornVerif.CurrentLearnerArithmetic
import Mathlib.Data.Fintype.Card

open Acorn Acorn.SwiftTd
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder
open AcornVerif.CurrentPrediction
open AcornVerif.CurrentLearnerArithmetic

namespace AcornVerif.CurrentLearner

variable {config : Config} {dimension : Dimension}

theorem vector_get {α : Type} {capacity : Nat} (values : Vector α capacity) (idx : Fin capacity) :
    values.get idx = values[idx.val] := by
  simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray]

theorem finite_equal (left right : Binary32) (hl : left.Finite) (hr : right.Finite) :
    left.numericallyEqual right = decide (left.key = right.key) := by
  simp [Binary32.numericallyEqual_eq_key, Binary32.finite_not_nan left hl,
    Binary32.finite_not_nan right hr]

theorem finite_lessOrEqual (left right : Binary32) (hl : left.Finite) (hr : right.Finite) :
    left.lessOrEqual right = decide (numerical32 left ≤ numerical32 right) := by
  simp [Binary32.lessOrEqual_eq_key, Binary32.finite_not_nan left hl,
    Binary32.finite_not_nan right hr, numerical32_order left right hl hr]

theorem zero_key (word : Binary32) (zero : word.isZero = true) : word.key = 0 := by
  rw [Binary32.isZero_eq_key] at zero
  exact of_decide_eq_true zero

theorem zero_pruned (word threshold : Binary32) (zero : word.isZero = true)
    (ordered : threshold.isNaN = false) (nonnegative : 0 ≤ threshold.key) :
    word.lessOrEqual threshold = true := by
  have hn : word.isNaN = false := by
    have hz := zero_key word zero
    have hm : word.magnitude = 0 := by
      simp only [Binary32.key_eq_negative] at hz
      split at hz <;> omega
    simp [Binary32.isNaN_eq_magnitude, hm]
  simp [Binary32.lessOrEqual_eq_key, hn, ordered, zero_key word zero, nonnegative]

theorem active_cardinality (features : ActiveSet dimension) :
    features.indices.length ≤ dimension.capacity := by
  simpa using features.nodup.length_le_card

theorem active_cardinality_attained (dimension : Dimension) :
    ∃ features : ActiveSet dimension, features.indices.length = dimension.capacity :=
  ⟨⟨List.finRange dimension.capacity, List.nodup_finRange _⟩, List.length_finRange⟩

theorem eligible_cardinality (state : NumericState config dimension)
    (unique : state.transient.eligible.toList.Nodup) :
    state.eligibleCount ≤ dimension.capacity := by
  simpa [NumericState.eligibleCount] using unique.length_le_card

theorem knowledge_legal (state : NumericState config dimension) (idx : FeatIdx dimension) :
    config.rule.domain.range.Contains (state.weights.get idx).value ∧
      state.rails.range.Contains (state.beta.get idx).value :=
  ⟨weight_legal (state.weights.get idx), (state.beta.get idx).legal⟩

theorem prediction_bound (state : NumericState config dimension) (features : ActiveSet dimension) :
    (state.predict features).Finite ∧
      |numerical32 (state.predict features)| ≤ predictionRadius features.indices.length := by
  have bound := legal_weight_sum_bound config.rule
    (features.indices.map fun idx => state.weights.get idx)
  simpa [NumericState.predict_def, NumericState.linearPrediction_eq_sumFrom,
    List.map_map, Function.comp_def] using bound

theorem clear_transient (state : NumericState config dimension) :
    state.clearTransient.transient = TransientState.zero dimension := rfl

theorem clear_knowledge (state : NumericState config dimension) :
    state.clearTransient.weights = state.weights ∧
      state.clearTransient.rails = state.rails ∧
      state.clearTransient.beta = state.beta := ⟨rfl, rfl, rfl⟩

theorem initial_transient :
    (NumericState.initial config dimension).transient = TransientState.zero dimension := rfl

theorem step_observation (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) :
    (state.step config features reward).2 =
      ⟨state.predict features,
        (reward.add (config.rule.gamma.mul (state.predict features))).sub
          state.transient.vOld⟩ := by
  rfl

theorem terminal_transient (state : NumericState config dimension) (target : Binary32) :
    (state.terminalStep config target).1.transient = TransientState.zero dimension := rfl

theorem swap_remove_size {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size) :
    (swapRemove items pos valid).size = items.size - 1 := by
  simp [swapRemove]

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

theorem swap_remove_get {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size)
    (idx : Nat) (inside : idx < (swapRemove items pos valid).size) :
    (swapRemove items pos valid)[idx] =
      if pos = idx then items[items.size - 1] else items[idx]'(by
        rw [swap_remove_size] at inside; omega) := by
  simp [swapRemove, Array.getElem_set]

theorem swap_remove_subset {α : Type} (items : Array α) (pos : Nat) (valid : pos < items.size)
    (value : α) (member : value ∈ swapRemove items pos valid) : value ∈ items := by
  obtain ⟨idx, inside, equality⟩ := Array.mem_iff_getElem.mp member
  rw [swap_remove_get] at equality
  split at equality
  · exact equality ▸ Array.getElem_mem _
  · exact equality ▸ Array.getElem_mem _

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
    rw [swap_remove_get, ite_eq_right notPos]
    exact equality

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

def registers (state : NumericState config dimension) (idx : FeatIdx dimension) :
    Vector Binary32 9 :=
  #v[(state.transient.z.get idx).value, (state.transient.zDelta.get idx).value,
    (state.transient.zBar.get idx).value, (state.transient.lastAlpha.get idx).value,
    (state.transient.deltaWeight.get idx).value, (state.transient.h.get idx).value,
    (state.transient.hOld.get idx).value, (state.transient.hTemp.get idx).value,
    (state.transient.p.get idx).value]

def Supported (state : NumericState config dimension)
    (eligible : Array (FeatIdx dimension)) : Prop :=
  ∀ idx, idx ∉ eligible → registers state idx = Vector.replicate 9 Binary32.zero

def ReferenceLegal (word : Binary32) : Prop :=
  word.Finite ∧ 0 ≤ numerical32 word ∧ numerical32 word ≤ 5

def ReferencesLegal (state : NumericState config dimension) : Prop :=
  ∀ idx, ReferenceLegal (state.transient.lastAlpha.get idx).value

def CoreInv (state : NumericState config dimension) : Prop :=
  Supported state state.transient.eligible ∧ ReferencesLegal state

def Ready (state : NumericState config dimension) : Prop :=
  state.transient.eligible.toList.Nodup ∧
    ∀ idx ∈ state.transient.eligible, (state.transient.z.get idx).value.isZero = false

theorem clear_core (state : NumericState config dimension) : CoreInv state.clearTransient := by
  constructor
  · intro idx _
    simp only [registers, NumericState.clearTransient_def, TransientState.zero_def,
      vector_get, Vector.getElem_replicate]
    rfl
  · intro idx
    simp only [ReferenceLegal, NumericState.clearTransient_def, TransientState.zero_def,
      vector_get, Vector.getElem_replicate]
    exact ⟨by decide, le_refl 0, by change (0:ℚ) ≤ 5; norm_num⟩

theorem clear_ready (state : NumericState config dimension) : Ready state.clearTransient := by
  simp [Ready, NumericState.clearTransient_def, TransientState.zero_def]

theorem initial_core : CoreInv (NumericState.initial config dimension) :=
  clear_core (NumericState.initial config dimension)

theorem initial_ready : Ready (NumericState.initial config dimension) :=
  clear_ready (NumericState.initial config dimension)

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
      vector_get, Vector.getElem_set, distinct, ite_false]

theorem first_element_frame (state : NumericState config dimension) (idx other : FeatIdx dimension)
    (different : idx ≠ other) (delta vDelta decay : Binary32) :
    let next := (state.firstLoopElement idx delta vDelta decay).1
    next.weights.get other = state.weights.get other ∧
      (next.beta.get other).value = (state.beta.get other).value ∧
      registers next other = registers state other := by
  have distinct : idx.val ≠ other.val := fun same => different (Fin.ext same)
  simp only [NumericState.firstLoopElement, registers, vector_get,
    Vector.getElem_set, distinct, ite_false, and_self]

theorem first_element_reference (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).1.transient.lastAlpha =
      state.transient.lastAlpha := rfl

theorem first_element_eligible (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).1.transient.eligible =
      state.transient.eligible := rfl

theorem first_element_prune (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    let result := state.firstLoopElement idx delta vDelta decay
    result.2 = (result.1.transient.z.get idx).value.lessOrEqual
      ((result.1.transient.lastAlpha.get idx).value.mul config.epsilon) := by
  simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self]

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
    (next.transient.hTemp.get idx).value = Binary32.zero ∧
    (next.transient.p.get idx).value = Binary32.zero.mul decay ∧
    (next.transient.zBar.get idx).value = Binary32.zero.mul decay ∧
    (next.beta.get idx).value = state.rails.initial.value ∧
    next.alpha.get idx = state.rails.initial.alpha := by
  simp only [vector_get] at clipped
  simp [NumericState.firstLoopElement, vector_get, clipped, LogStepSize.alphaAfter]

theorem weight_project_nonfinite_clipped (rule : ValueRule) (raw : Binary32)
    (nonfinite : ¬raw.Finite) :
    (Weight.project rule raw).value.numericallyEqual raw = false := by
  rw [Binary32.numericallyEqual_eq_key]
  by_cases hnan : raw.isNaN = true
  · simp [hnan]
  · have hproj : (Weight.project rule raw).value.Finite := (weight_legal _).1
    have hneq : (Weight.project rule raw).value.key ≠ raw.key := by
      intro hkey
      have hmag : (Weight.project rule raw).value.magnitude = raw.magnitude := by
        simp only [Binary32.key_eq_negative] at hkey
        split at hkey <;> split at hkey <;> omega
      exact nonfinite (by unfold Binary32.Finite at hproj ⊢; omega)
    simp [hneq]

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
  simp [NumericState.secondLoopElement, NumericState.secondLoopElementAt,
    NumericState.writeBetaValue, vector_get]

theorem second_element_overshoot_p (state : NumericState config dimension) (idx : FeatIdx dimension)
    (denominator total vDelta : Binary32) :
    let next := (NumericState.secondLoopElement config true denominator total state vDelta idx).1
    (next.transient.p.get idx).value = (state.transient.p.get idx).value := by
  simp [NumericState.secondLoopElement, NumericState.secondLoopElementAt,
    NumericState.writeBetaValue, vector_get]

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
    simp only [NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      NumericState.writeBetaValue, registers,
      vector_get, Vector.getElem_set, distinct, ite_false, ite_true, Bool.false_eq_true, and_self]

theorem second_element_eligible (state : NumericState config dimension) (idx : FeatIdx dimension)
    (overshoot : Bool) (denominator total vDelta : Binary32) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    next.transient.eligible = if (state.transient.z.get idx).value.isZero then
        state.transient.eligible.push idx else state.transient.eligible := by
  cases overshoot <;> rfl

theorem registers_zero_trace (state : NumericState config dimension) (idx : FeatIdx dimension)
    (zero : registers state idx = Vector.replicate 9 Binary32.zero) :
    (state.transient.z.get idx).value = .zero := by
  have equation := congrArg (fun (words : Vector Binary32 9) => words[0]) zero
  simpa [registers] using equation

theorem registers_trace_eq (left right : NumericState config dimension) (idx : FeatIdx dimension)
    (same : registers left idx = registers right idx) :
    (left.transient.z.get idx).value = (right.transient.z.get idx).value := by
  exact congrArg (fun (words : Vector Binary32 9) => words[0]) same

theorem registers_reference_eq (left right : NumericState config dimension)
    (idx : FeatIdx dimension) (same : registers left idx = registers right idx) :
    (left.transient.lastAlpha.get idx).value = (right.transient.lastAlpha.get idx).value := by
  exact congrArg (fun (words : Vector Binary32 9) => words[3]) same

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

theorem first_element_supported (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (idx : FeatIdx dimension) (member : idx ∈ work)
    (delta vDelta decay : Binary32) (support : Supported state work) :
    Supported (state.firstLoopElement idx delta vDelta decay).1 work := by
  intro other absent
  have different : idx ≠ other := by intro same; exact absent (same ▸ member)
  rw [(first_element_frame state idx other different delta vDelta decay).2.2]
  exact support other absent

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

theorem first_loop_go_core (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32)
    (support : Supported state work) (references : ReferencesLegal state) :
    CoreInv (NumericState.learnFirstLoopGo config delta vDelta decay state work pos) := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct config delta vDelta decay with
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
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
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
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simpa only [equation, ite_eq_right noPrune] using result
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    exact ⟨support, references⟩

theorem first_loop_core (state : NumericState config dimension) (delta vDelta decay : Binary32)
    (core : CoreInv state) : CoreInv (state.learnFirstLoop config delta vDelta decay) := by
  exact first_loop_go_core _ _ _ _ _ _ core.1 core.2

theorem second_element_reference (state : NumericState config dimension) (idx : FeatIdx dimension)
    (overshoot : Bool) (denominator total vDelta : Binary32) :
    let next :=
      (NumericState.secondLoopElement config overshoot denominator total state vDelta idx).1
    (next.transient.lastAlpha.get idx).value =
      (config.eta.div denominator).mul (state.beta.get idx).alpha := by
  cases overshoot <;>
    simp only [NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      NumericState.writeBetaValue, vector_get,
      Vector.getElem_set_self, ite_false, ite_true, Bool.false_eq_true]

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

theorem second_loop_core (state : NumericState config dimension) (features : ActiveSet dimension)
    (vDelta : Binary32) (core : CoreInv state) :
    CoreInv (state.learnSecondLoop config features vDelta).1 := by
  have finite := alpha_sum_finite (features.indices.map fun idx => state.beta.get idx)
  simp only [List.map_map, Function.comp_def] at finite
  rw [NumericState.learnSecondLoop_eq_sumFrom]
  exact second_fold_core features.indices state _ _ vDelta finite core

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

theorem second_loop_eligible (state : NumericState config dimension)
    (features : ActiveSet dimension)
    (vDelta : Binary32) :
    (state.learnSecondLoop config features vDelta).1.transient.eligible.toList =
      state.transient.eligible.toList ++
        features.indices.filter (fun idx => (state.transient.z.get idx).value.isZero) := by
  rw [NumericState.learnSecondLoop_eq_sumFrom]
  exact second_fold_eligible features.indices features.nodup state _ _ _ vDelta

theorem second_loop_count (state : NumericState config dimension) (features : ActiveSet dimension)
    (vDelta : Binary32) :
    (state.learnSecondLoop config features vDelta).1.eligibleCount = state.eligibleCount +
      (features.indices.filter (fun idx => (state.transient.z.get idx).value.isZero)).length := by
  have equation := congrArg List.length (second_loop_eligible state features vDelta)
  simpa [NumericState.eligibleCount] using equation

theorem second_loop_count_le (state : NumericState config dimension)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    (state.learnSecondLoop config features vDelta).1.eligibleCount ≤
      state.eligibleCount + features.indices.length := by
  rw [second_loop_count]
  exact Nat.add_le_add_left (List.length_filter_le _ _) _

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

def Processed (state : NumericState config dimension) (work : Array (FeatIdx dimension))
    (pos : Nat) : Prop :=
  ∀ (idx : Nat) (valid : idx < work.size), idx < pos →
    (state.transient.z.get work[idx]).value.isZero = false

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
    rw [swap_remove_get, ite_eq_right (show pos ≠ idx by omega)]
  rw [untouched, registers_trace_eq _ _ work[idx]
    (clear_feature_other state work[pos] work[idx] different)]
  exact processed idx original before

theorem first_loop_go_ready (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32)
    (unique : work.toList.Nodup) (references : ReferencesLegal state)
    (processed : Processed state work pos) :
    Ready (NumericState.learnFirstLoopGo config delta vDelta decay state work pos) := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct config delta vDelta decay with
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
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
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
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simpa only [equation, ite_eq_right noPrune] using result
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    refine ⟨unique, ?_⟩
    intro idx member
    obtain ⟨j, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    change j < work.size at inside
    exact processed j inside (by omega)

theorem first_loop_ready (state : NumericState config dimension) (delta vDelta decay : Binary32)
    (unique : state.transient.eligible.toList.Nodup) (references : ReferencesLegal state) :
    Ready (state.learnFirstLoop config delta vDelta decay) := by
  rw [NumericState.learnFirstLoop_def]
  apply first_loop_go_ready
  · exact unique
  · exact references
  · intro idx valid before
    omega

theorem zero_decay_trace (word : Binary32) (finite : word.Finite) :
    (word.mul .zero).isZero = true := by
  rw [Binary32.isZero_eq_key, mul32_zero word finite]
  rfl

theorem first_loop_go_empty (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32)
    (start : pos = 0) (unique : work.toList.Nodup) (references : ReferencesLegal state)
    (absorbed : ∀ (j : Nat) (valid : j < work.size),
      ((state.transient.z.get work[j]).value.mul decay).isZero = true) :
    (NumericState.learnFirstLoopGo config delta vDelta decay state work pos).transient.eligible =
      #[] := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct config delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    have nextReferences : ReferencesLegal next := by
      have unchanged := first_element_reference state work[pos] delta vDelta decay
      rw [equation] at unchanged
      intro idx
      simpa only [← unchanged] using references idx
    have frame : ∀ other, work[pos] ≠ other →
        ((next.clearFeatureRegisters work[pos]).transient.z.get other).value =
          (state.transient.z.get other).value := by
      intro other different
      rw [registers_trace_eq _ _ other (clear_feature_other next work[pos] other different)]
      have kept := registers_trace_eq _ _ other
        (first_element_frame state work[pos] other different delta vDelta decay).2.2
      rw [equation] at kept
      exact kept
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simp only [equation, ite_true]
    refine ih start (swap_remove_nodup work pos valid unique)
      (clear_feature_references next work[pos] nextReferences) ?_
    intro j inside
    have original : j < work.size := by rw [swap_remove_size] at inside; omega
    have last : work.size - 1 < work.size := by omega
    have element := swap_remove_get work pos valid j inside
    by_cases here : pos = j
    · have distinct : work[pos] ≠ work[work.size - 1] := by
        intro same
        have := (array_nodup_iff work).mp unique pos (work.size - 1) valid last same
        rw [swap_remove_size] at inside
        omega
      rw [ite_eq_left here] at element
      rw [element, frame _ distinct]
      exact absorbed _ last
    · have distinct : work[pos] ≠ work[j] := fun same =>
        here ((array_nodup_iff work).mp unique pos j valid original same)
      rw [ite_eq_right here] at element
      rw [element, frame _ distinct]
      exact absorbed j original
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation
    exfalso
    have retained : (state.firstLoopElement work[pos] delta vDelta decay).2 = false := by
      rw [equation]
      exact Bool.eq_false_iff.mpr noPrune
    have nonzero :=
      first_element_retained_nonzero state work[pos] delta vDelta decay references retained
    have trace : ((state.firstLoopElement work[pos] delta vDelta decay).1.transient.z.get
        work[pos]).value = (state.transient.z.get work[pos]).value.mul decay := by
      simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self]
    rw [trace, absorbed pos valid] at nonzero
    contradiction
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    subst start
    have empty : work.size = 0 := by omega
    exact Array.eq_empty_of_size_eq_zero empty

theorem first_loop_empty (state : NumericState config dimension) (delta vDelta decay : Binary32)
    (unique : state.transient.eligible.toList.Nodup) (references : ReferencesLegal state)
    (absorbed : ∀ idx ∈ state.transient.eligible,
      ((state.transient.z.get idx).value.mul decay).isZero = true) :
    (state.learnFirstLoop config delta vDelta decay).transient.eligible = #[] := by
  rw [NumericState.learnFirstLoop_def]
  apply first_loop_go_empty
  · rfl
  · exact unique
  · exact references
  · intro j valid
    exact absorbed _ (Array.getElem_mem valid)

theorem first_loop_stop (state : NumericState config dimension) (delta vDelta : Binary32)
    (unique : state.transient.eligible.toList.Nodup) (references : ReferencesLegal state)
    (finite : ∀ idx ∈ state.transient.eligible, (state.transient.z.get idx).value.Finite) :
    (state.learnFirstLoop config delta vDelta .zero).transient.eligible = #[] :=
  first_loop_empty state delta vDelta .zero unique references fun idx member =>
    zero_decay_trace _ (finite idx member)

theorem core_of_transient_eq (before after : NumericState config dimension)
    (same : after.transient = before.transient) (core : CoreInv before) : CoreInv after := by
  simpa only [CoreInv, Supported, ReferencesLegal, registers, same] using core

theorem ready_of_transient_eq (before after : NumericState config dimension)
    (same : after.transient = before.transient) (ready : Ready before) : Ready after := by
  simpa only [Ready, same] using ready

theorem plan_fold_transient (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) (scale delta : Binary32) :
    (indices.foldl (fun s idx =>
      let stepSize := (scale.mul (s.beta.get idx).alpha).mul delta
      s.writeWeight idx ((s.weights.get idx).value.add stepSize)) state).transient =
      state.transient := by
  induction indices generalizing state with
  | nil => rfl
  | cons idx rest ih => exact ih _

theorem plan_transient (state : NumericState config dimension) (features : ActiveSet dimension)
    (target : Binary32) :
    (state.planStep config features target).1.transient = state.transient := by
  rw [NumericState.planStep_eq_foldl]
  dsimp only
  split
  · rfl
  · exact plan_fold_transient features.indices state _ _

theorem step_core (state : NumericState config dimension) (features : ActiveSet dimension)
    (reward : Binary32) (core : CoreInv state) :
    CoreInv (state.step config features reward).1 := by
  exact second_loop_core _ features .zero (first_loop_core state _ _ _ core)

theorem begin_core (state : NumericState config dimension) (features : ActiveSet dimension) :
    CoreInv (state.beginTrajectory config features) := by
  exact second_loop_core state.clearTransient features .zero (clear_core state)

theorem terminal_core (state : NumericState config dimension) (target : Binary32) :
    CoreInv (state.terminalStep config target).1 := clear_core _

theorem clear_feature_supported (state : NumericState config dimension) (idx : FeatIdx dimension)
    (support : Supported state state.transient.eligible) :
    Supported (state.clearFeatureRegisters idx) state.transient.eligible := by
  intro other absent
  by_cases same : idx = other
  · subst other
    exact clear_feature_self state idx
  · rw [clear_feature_other state idx other same]
    exact support other absent

theorem retire_core (state : NumericState config dimension) (idx : FeatIdx dimension)
    (core : CoreInv state) : CoreInv (state.retireIndex idx) := by
  rw [NumericState.retireIndex_def]
  split
  · rename_i pos found
    obtain ⟨valid, same, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have equality : state.transient.eligible[pos] = idx := by simpa using same
    have support := prune_supported state state.transient.eligible pos valid core.1
    rw [equality] at support
    exact ⟨support, clear_feature_references state idx core.2⟩
  · exact ⟨clear_feature_supported state idx core.1, clear_feature_references state idx core.2⟩

theorem clear_fold_registers (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) (idx : FeatIdx dimension) :
    registers (indices.foldl (fun next i => next.clearFeatureRegisters i) state) idx =
      if idx ∈ indices then Vector.replicate 9 Binary32.zero else registers state idx := by
  induction indices generalizing state with
  | nil => simp
  | cons head rest ih =>
    rw [List.foldl_cons, ih]
    by_cases same : head = idx
    · subst same
      simp [clear_feature_self]
    · have other : idx ≠ head := fun equal => same equal.symm
      simp [other, clear_feature_other state head idx same]

theorem clear_fold_references (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) (legal : ReferencesLegal state) :
    ReferencesLegal (indices.foldl (fun next i => next.clearFeatureRegisters i) state) := by
  induction indices generalizing state with
  | nil => exact legal
  | cons head rest ih =>
    rw [List.foldl_cons]
    exact ih (state.clearFeatureRegisters head) (clear_feature_references state head legal)

theorem clear_feature_knowledge (state : NumericState config dimension)
    (idx other : FeatIdx dimension) :
    (state.clearFeatureRegisters idx).weights.get other = state.weights.get other ∧
      ((state.clearFeatureRegisters idx).beta.get other).value =
        (state.beta.get other).value := by
  simp only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha, and_self]

theorem clear_fold_knowledge (indices : List (FeatIdx dimension))
    (state : NumericState config dimension) (other : FeatIdx dimension) :
    (indices.foldl (fun next i => next.clearFeatureRegisters i) state).weights.get other =
        state.weights.get other ∧
      ((indices.foldl (fun next i => next.clearFeatureRegisters i) state).beta.get other).value =
        (state.beta.get other).value := by
  induction indices generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons head rest ih =>
    rw [List.foldl_cons]
    have step := ih (state.clearFeatureRegisters head)
    have one := clear_feature_knowledge state head other
    exact ⟨step.1.trans one.1, step.2.trans one.2⟩

theorem release_empty (state : NumericState config dimension) :
    state.releaseEligible.eligibleCount = 0 := rfl

theorem release_knowledge (state : NumericState config dimension) (idx : FeatIdx dimension) :
    state.releaseEligible.weights.get idx = state.weights.get idx ∧
      (state.releaseEligible.beta.get idx).value = (state.beta.get idx).value := by
  have fold := clear_fold_knowledge state.transient.eligible.toList state idx
  rw [Array.foldl_toList] at fold
  exact fold

theorem release_core (state : NumericState config dimension) (core : CoreInv state) :
    CoreInv state.releaseEligible := by
  constructor
  · intro idx _
    have value := clear_fold_registers state.transient.eligible.toList state idx
    rw [Array.foldl_toList] at value
    have same : registers state.releaseEligible idx = registers
        (state.transient.eligible.foldl (fun next i => next.clearFeatureRegisters i) state) idx :=
      rfl
    rw [same, value]
    split
    · rfl
    · rename_i absent
      exact core.1 idx (by simpa using absent)
  · have legal := clear_fold_references state.transient.eligible.toList state core.2
    rw [Array.foldl_toList] at legal
    exact legal

theorem release_ready (state : NumericState config dimension) : Ready state.releaseEligible := by
  simp [Ready, NumericState.releaseEligible_def]

theorem first_loop_idle (state : NumericState config dimension) (delta vDelta decay : Binary32)
    (empty : state.transient.eligible = #[]) :
    state.learnFirstLoop config delta vDelta decay = state := by
  rw [NumericState.learnFirstLoop_def]
  dsimp only
  rw [empty, NumericState.learnFirstLoopGo_def, dite_eq_right (by simp)]
  cases state with
  | mk rails weights beta alpha evaluated transient =>
    cases transient
    simp_all

theorem release_idle (state : NumericState config dimension) (delta vDelta decay : Binary32) :
    state.releaseEligible.learnFirstLoop config delta vDelta decay = state.releaseEligible :=
  first_loop_idle _ delta vDelta decay rfl

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
  | clear => exact clear_core state
  | release => exact release_core state core

theorem entries_core (entries : List (Entry dimension)) (state : NumericState config dimension)
    (core : CoreInv state) : CoreInv (entries.foldl (fun s entry => entry.apply s) state) := by
  induction entries generalizing state with
  | nil => exact core
  | cons entry rest ih => exact ih _ (entry_core entry state core)

theorem admitted_core (state : NumericState config dimension)
    (admitted : Admitted config dimension state) :
    CoreInv state := by
  induction admitted with
  | initial => exact initial_core
  | transition entry _ ih => exact entry_core entry _ ih

theorem learner_invariant (learner : Learner config dimension) (idx : FeatIdx dimension) :
    config.rule.domain.range.Contains (learner.val.weights.get idx).value ∧
      learner.val.rails.range.Contains (learner.val.beta.get idx).value ∧ CoreInv learner.val :=
  ⟨(knowledge_legal learner.val idx).1, (knowledge_legal learner.val idx).2,
    admitted_core learner.val learner.property⟩

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

theorem retire_unique (state : NumericState config dimension) (idx : FeatIdx dimension)
    (unique : state.transient.eligible.toList.Nodup) :
    (state.retireIndex idx).transient.eligible.toList.Nodup := by
  rw [NumericState.retireIndex_def]
  split
  · exact swap_remove_nodup _ _ _ unique
  · exact unique

theorem retire_ready (state : NumericState config dimension) (idx : FeatIdx dimension)
    (ready : Ready state) : Ready (state.retireIndex idx) := by
  refine ⟨retire_unique state idx ready.1, ?_⟩
  rw [NumericState.retireIndex_def]
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

abbrev nextReady (entry : Entry dimension) (before : Bool) : Bool :=
  SwiftTd.nextReady entry before

abbrev Permitted (entry : Entry dimension) (ready : Bool) : Prop :=
  SwiftTd.Permitted entry ready

def ScheduleInv (state : NumericState config dimension) (phase : Bool) : Prop :=
  CoreInv state ∧ state.transient.eligible.toList.Nodup ∧ (phase = true → Ready state)

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
  | clear => exact ⟨(clear_ready state).1, fun _ => clear_ready state⟩
  | release => exact ⟨(release_ready state).1, fun _ => release_ready state⟩
  | plan features target =>
    have same := plan_transient state features target
    exact ⟨by simpa only [Entry.apply_def, same] using invariant.2.1,
      fun hp => ready_of_transient_eq state _ same (invariant.2.2 hp)⟩
  | retire idx =>
    exact ⟨retire_unique state idx invariant.2.1,
      fun hp => retire_ready state idx (invariant.2.2 hp)⟩

def Scheduled : List (Entry dimension) → Bool → Prop
  | [], _ => True
  | entry :: rest, phase => Permitted entry phase ∧ Scheduled rest (nextReady entry phase)

def finalPhase (entries : List (Entry dimension)) (phase : Bool) : Bool :=
  entries.foldl (fun before entry => nextReady entry before) phase

theorem entries_schedule (entries : List (Entry dimension)) (state : NumericState config dimension)
    (phase : Bool) (scheduled : Scheduled entries phase) (invariant : ScheduleInv state phase) :
    ScheduleInv (entries.foldl (fun s entry => entry.apply s) state)
      (finalPhase entries phase) := by
  induction entries generalizing state phase with
  | nil => exact invariant
  | cons entry rest ih =>
    exact ih _ _ scheduled.2 (entry_schedule entry state phase scheduled.1 invariant)

theorem scheduled_capacity (entries : List (Entry dimension)) (scheduled : Scheduled entries true) :
    (entries.foldl (fun s entry => entry.apply s)
      (NumericState.initial config dimension)).eligibleCount ≤ dimension.capacity := by
  apply eligible_cardinality
  exact (entries_schedule entries _ true scheduled
    ⟨initial_core, initial_ready.1, fun _ => initial_ready⟩).2.1

theorem prune_work_decreases {α : Type} (work : Array α) (pos : Nat) (valid : pos < work.size) :
    (swapRemove work pos valid).size - pos + 1 = work.size - pos := by
  rw [swap_remove_size]
  omega

theorem retain_work_decreases {α : Type} (work : Array α) (pos : Nat) (valid : pos < work.size) :
    work.size - (pos + 1) + 1 = work.size - pos := by omega

theorem first_loop_go_size (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32) :
    (NumericState.learnFirstLoopGo config delta vDelta decay state work pos).eligibleCount ≤
      work.size := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct config delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simp only [equation, ite_true]
    exact le_trans ih (by rw [swap_remove_size]; omega)
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simpa only [equation, ite_eq_right noPrune] using ih
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    exact le_refl _

def retainedSlots (state : NumericState config dimension) : Nat :=
  state.weights.toArray.size + state.beta.toArray.size + state.alpha.toArray.size +
    state.transient.z.toArray.size + state.transient.zDelta.toArray.size +
    state.transient.zBar.toArray.size + state.transient.lastAlpha.toArray.size +
    state.transient.deltaWeight.toArray.size + state.transient.h.toArray.size +
    state.transient.hOld.toArray.size + state.transient.hTemp.toArray.size +
    state.transient.p.toArray.size + state.transient.eligible.size + 2

theorem retained_slots_exact (state : NumericState config dimension) :
    retainedSlots state = 12 * dimension.capacity + state.eligibleCount + 2 := by
  simp only [retainedSlots, Vector.size_toArray, NumericState.eligibleCount]
  omega

theorem retained_slots_unique (state : NumericState config dimension)
    (unique : state.transient.eligible.toList.Nodup) :
    retainedSlots state ≤ 13 * dimension.capacity + 2 := by
  rw [retained_slots_exact]
  have bound := eligible_cardinality state unique
  omega

theorem scheduled_storage (entries : List (Entry dimension)) (scheduled : Scheduled entries true) :
    retainedSlots (entries.foldl (fun s entry => entry.apply s)
      (NumericState.initial config dimension)) ≤ 13 * dimension.capacity + 2 := by
  rw [retained_slots_exact]
  have bound : (entries.foldl (fun s entry => entry.apply s)
      (NumericState.initial config dimension)).eligibleCount ≤ dimension.capacity :=
    scheduled_capacity entries scheduled
  omega

theorem retire_registers (state : NumericState config dimension) (idx : FeatIdx dimension) :
    registers (state.retireIndex idx) idx = Vector.replicate 9 Binary32.zero ∧
    ((state.retireIndex idx).weights.get idx).value = Binary32.zero ∧
    ((state.retireIndex idx).beta.get idx).value = state.rails.initial.value ∧
    (state.retireIndex idx).transient.vOld = state.transient.vOld ∧
    (state.retireIndex idx).transient.vDelta = state.transient.vDelta := by
  rw [NumericState.retireIndex_def]
  have zero := config.rule.domain.symmetric_project_identity
    Binary32.zero config.rule.domain.zeroLegal
  split <;> simp [registers, NumericState.removeEligibleAt,
    NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha, NumericState.writeWeight, NumericState.writeBetaValue,
    vector_get, Weight.project_eq, Bounded32.projectSymmetric, zero, Weight.value,
    show Array.replicate 9 Binary32.zero =
      #[Binary32.zero, Binary32.zero, Binary32.zero, Binary32.zero, Binary32.zero,
        Binary32.zero, Binary32.zero, Binary32.zero, Binary32.zero] from rfl]

theorem normalized_count (state : NumericState config dimension) :
    state.normalizedStepSizeSum.2 = state.eligibleCount := by
  simp only [NumericState.normalizedStepSizeSum_def, NumericState.eligibleCount]
  split
  · rename_i empty
    simp_all
  · rfl

theorem clear_observers (state : NumericState config dimension) :
    state.clearTransient.activeAlpha = Binary32.zero ∧
    state.clearTransient.normalizedStepSizeSum = (Binary32.zero, 0) := ⟨rfl, rfl⟩

theorem exploration_legal (raw : Binary32) :
    exploreRange.Contains (ExploreRate.project raw).value :=
  (ExploreRate.project raw).legal

end AcornVerif.CurrentLearner
