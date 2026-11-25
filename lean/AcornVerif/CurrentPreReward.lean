import AcornVerif.CurrentAccounting
import AcornVerif.CurrentArithmetic

namespace AcornVerif.CurrentPreReward
open Acorn Acorn.Features Acorn.Handcrafted

def Resting {config : Acorn.Config} {dimension : Dimension} {actions : Nat}
    (controller : Controller config dimension actions) : Prop :=
  ∀ (row : Fin actions) (slot : FeatIdx dimension),
    ((controller.learners.get row).state.weights.get slot).value.isZero = true

section Zero

open Acorn
open Float.Model (Format UnpackedFloat)

def Inert (value : UnpackedFloat) : Prop :=
  value = .notANumber ∨ ∃ sign, value = .zero sign

def Inert32 (word : Binary32) : Prop := word.isZero = true ∨ word.isNaN = true

theorem Inert32.ofZero {word : Binary32} (zero : word.isZero = true) : Inert32 word := Or.inl zero

theorem Inert32.zero : Inert32 Binary32.zero := Or.inl (by decide)

theorem isZero_bits (word : Binary32) (zero : word.isZero = true) :
    word.bits = 0 ∨ word.bits = 0x80000000 := by
  have bound := word.bits.toNat_lt
  simp only [Binary32.isZero, beq_iff_eq, ← UInt32.toNat_inj, UInt32.toNat_and] at zero
  change word.bits.toNat &&& (2 ^ 31 - 1) = 0 at zero
  rw [Nat.and_two_pow_sub_one_eq_mod] at zero
  simp only [← UInt32.toNat_inj]
  change word.bits.toNat = 0 ∨ word.bits.toNat = 2 ^ 31
  omega

theorem nan_unpack (word : Binary32) (nan : word.isNaN = true) :
    UnpackedFloat.unpack Format.binary32 word.bits.toBitVec = .notANumber := by
  have fields := (Binary32.isNaN_iff word).mp nan
  have bound := word.bits.toNat_lt
  unfold Binary32.IsNaN at fields
  have magnitude : word.magnitude = word.bits.toNat % 2 ^ 31 := by
    simp only [Binary32.magnitude, UInt32.toNat_and]
    change word.bits.toNat &&& (2 ^ 31 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [magnitude] at fields
  have exponent : UnpackedFloat.unpackExponent (spec := Format.binary32) word.bits.toBitVec =
      -1#8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [UnpackedFloat.unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    change word.bits.toNat / 2 ^ 23 % 2 ^ 8 = 255
    omega
  have mantissa : UnpackedFloat.unpackMantissa (spec := Format.binary32) word.bits.toBitVec ≠
      0#23 := by
    intro same
    have value := congrArg BitVec.toNat same
    simp only [UnpackedFloat.unpackMantissa, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow] at value
    change word.bits.toNat / 2 ^ 0 % 2 ^ 23 = 0 at value
    omega
  unfold UnpackedFloat.unpack
  simp only [exponent, mantissa, ite_true, ite_false]

theorem Inert32.model {word : Binary32} (inert : Inert32 word) :
    Inert (Float32.ofBits word.bits).toModel.unpack := by
  rcases inert with zero | nan
  · rcases isZero_bits word zero with bits | bits
    · exact Or.inr ⟨.positive, by rw [bits]; rfl⟩
    · exact Or.inr ⟨.negative, by rw [bits]; rfl⟩
  · left
    change UnpackedFloat.unpack Format.binary32
      (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.unpack Format.binary32 word.bits.toBitVec)) = _
    rw [nan_unpack word nan]
    rfl

theorem Inert.word {value : UnpackedFloat} (inert : Inert value) :
    Inert32 ⟨(Float32.Model.pack value).toBits⟩ := by
  rcases inert with rfl | ⟨sign, rfl⟩
  · exact Or.inr (by decide)
  · cases sign
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)

theorem Inert.add {left right : UnpackedFloat} (hl : Inert left) (hr : Inert right) :
    Inert (UnpackedFloat.add Format.binary32 left right) := by
  rcases hl with rfl | ⟨sl, rfl⟩ <;> rcases hr with rfl | ⟨sr, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · cases sl <;> cases sr <;> exact Or.inr ⟨_, rfl⟩

theorem Inert.sub {left right : UnpackedFloat} (hl : Inert left) (hr : Inert right) :
    Inert (UnpackedFloat.sub Format.binary32 left right) := by
  rcases hl with rfl | ⟨sl, rfl⟩ <;> rcases hr with rfl | ⟨sr, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · cases sl <;> cases sr <;> exact Or.inr ⟨_, rfl⟩

theorem Inert.mulLeft {left : UnpackedFloat} (hl : Inert left) (right : UnpackedFloat) :
    Inert (UnpackedFloat.mul Format.binary32 left right) := by
  rcases hl with rfl | ⟨sl, rfl⟩
  · exact Or.inl rfl
  · cases right with
    | notANumber => exact Or.inl rfl
    | infinity _ => exact Or.inl rfl
    | zero _ => exact Or.inr ⟨_, rfl⟩
    | finite _ _ _ _ => exact Or.inr ⟨_, rfl⟩

theorem Inert.mulRight (left : UnpackedFloat) {right : UnpackedFloat} (hr : Inert right) :
    Inert (UnpackedFloat.mul Format.binary32 left right) := by
  rcases hr with rfl | ⟨sr, rfl⟩
  · cases left <;> exact Or.inl rfl
  · cases left with
    | notANumber => exact Or.inl rfl
    | infinity _ => exact Or.inl rfl
    | zero _ => exact Or.inr ⟨_, rfl⟩
    | finite _ _ _ _ => exact Or.inr ⟨_, rfl⟩

theorem Inert.divLeft {left : UnpackedFloat} (hl : Inert left) (right : UnpackedFloat) :
    Inert (UnpackedFloat.div Format.binary32 left right) := by
  rcases hl with rfl | ⟨sl, rfl⟩
  · exact Or.inl rfl
  · cases right with
    | notANumber => exact Or.inl rfl
    | infinity _ => exact Or.inr ⟨_, rfl⟩
    | zero _ => exact Or.inl rfl
    | finite _ _ _ _ => exact Or.inr ⟨_, rfl⟩

theorem Inert32.add {left right : Binary32} (hl : Inert32 left) (hr : Inert32 right) :
    Inert32 (left.add right) :=
  (Inert.add hl.model hr.model).word

theorem Inert32.sub {left right : Binary32} (hl : Inert32 left) (hr : Inert32 right) :
    Inert32 (left.sub right) :=
  (Inert.sub hl.model hr.model).word

theorem Inert32.mulLeft {left : Binary32} (hl : Inert32 left) (right : Binary32) :
    Inert32 (left.mul right) :=
  (Inert.mulLeft hl.model _).word

theorem Inert32.mulRight (left : Binary32) {right : Binary32} (hr : Inert32 right) :
    Inert32 (left.mul right) :=
  (Inert.mulRight _ hr.model).word

theorem Inert32.divLeft {left : Binary32} (hl : Inert32 left) (right : Binary32) :
    Inert32 (left.div right) :=
  (Inert.divLeft hl.model _).word

theorem Inert32.foldlAdd (values : List Binary32) (initial : Binary32) (start : Inert32 initial)
    (terms : ∀ value ∈ values, Inert32 value) : Inert32 (values.foldl Binary32.add initial) := by
  induction values generalizing initial with
  | nil => exact start
  | cons value rest ih =>
    exact ih _ (start.add (terms value (List.mem_cons_self ..)))
      (fun other held => terms other (List.mem_cons_of_mem _ held))

theorem Inert32.sumFrom (values : List Binary32) (initial : Binary32) (start : Inert32 initial)
    (terms : ∀ value ∈ values, Inert32 value) : Inert32 (Binary32.sumFrom initial values) := by
  rw [Binary32.sumFrom_def]
  exact Inert32.foldlAdd values initial start terms

theorem Inert32.project {word : Binary32} (inert : Inert32 word) (rule : ValueRule) :
    (Weight.project rule word).value.isZero = true := by
  rw [Weight.project_eq]
  change (word.project rule.domain.range.upper).isZero = true
  unfold Binary32.project
  rcases inert with zero | nan
  · rcases isZero_bits word zero with bits | bits <;>
    · obtain ⟨raw⟩ := word
      simp only at bits
      subst bits
      cases rule with
      | discounted discount => cases discount <;> decide
      | differential => decide
  · simp only [nan, ite_true]
    decide

theorem zeroWord_model {word : Binary32} (zero : word.isZero = true) :
    ∃ sign, (Float32.ofBits word.bits).toModel.unpack = .zero sign := by
  rcases isZero_bits word zero with bits | bits
  · exact ⟨.positive, by rw [bits]; rfl⟩
  · exact ⟨.negative, by rw [bits]; rfl⟩

theorem zeroWord_pack (sign : UnpackedFloat.Sign) :
    (⟨(Float32.Model.pack (.zero sign)).toBits⟩ : Binary32).isZero = true := by
  cases sign <;> decide

theorem zeroWord_add {left right : Binary32} (hl : left.isZero = true) (hr : right.isZero = true) :
    (left.add right).isZero = true := by
  obtain ⟨sl, el⟩ := zeroWord_model hl
  obtain ⟨sr, er⟩ := zeroWord_model hr
  change (⟨(Float32.Model.pack (UnpackedFloat.add Format.binary32
    (Float32.ofBits left.bits).toModel.unpack (Float32.ofBits right.bits).toModel.unpack)).toBits⟩ :
      Binary32).isZero = true
  rw [el, er]
  cases sl <;> cases sr <;> exact zeroWord_pack _

theorem zeroWord_sub {left right : Binary32} (hl : left.isZero = true) (hr : right.isZero = true) :
    (left.sub right).isZero = true := by
  obtain ⟨sl, el⟩ := zeroWord_model hl
  obtain ⟨sr, er⟩ := zeroWord_model hr
  change (⟨(Float32.Model.pack (UnpackedFloat.sub Format.binary32
    (Float32.ofBits left.bits).toModel.unpack (Float32.ofBits right.bits).toModel.unpack)).toBits⟩ :
      Binary32).isZero = true
  rw [el, er]
  cases sl <;> cases sr <;> exact zeroWord_pack _

theorem zeroWord_foldlAdd (values : List Binary32) (initial : Binary32) (start : initial.isZero =
    true)
    (terms : ∀ value ∈ values, value.isZero = true) :
    (values.foldl Binary32.add initial).isZero = true := by
  induction values generalizing initial with
  | nil => exact start
  | cons value rest ih =>
    exact ih _ (zeroWord_add start (terms value (List.mem_cons_self ..)))
      (fun other held => terms other (List.mem_cons_of_mem _ held))

theorem sumFrom_zeros (values : List Binary32) (zeros : ∀ value ∈ values, value = Binary32.zero) :
    Binary32.sumFrom .zero values = .zero := by
  rw [Binary32.sumFrom_def]
  induction values with
  | nil => rfl
  | cons head rest ih =>
    rw [List.foldl_cons, zeros head (List.mem_cons_self ..)]
    exact ih fun value member => zeros value (List.mem_cons_of_mem _ member)

theorem zeroWord_saturate (value : Binary32) {lower upper : Binary32}
    (hl : lower.isZero = true) (hu : upper.isZero = true) :
    (value.saturate lower upper).isZero = true := by
  rw [Binary32.saturate_eq_less]
  have lowerNan : lower.isNaN = false := by
    rcases isZero_bits lower hl with bits | bits <;>
    · obtain ⟨raw⟩ := lower
      simp only at bits
      subst bits
      decide
  have upperNan : upper.isNaN = false := by
    rcases isZero_bits upper hu with bits | bits <;>
    · obtain ⟨raw⟩ := upper
      simp only at bits
      subst bits
      decide
  have lowerKey : lower.key = 0 := by
    have := Binary32.isZero_eq_key lower
    rw [hl] at this
    exact (of_decide_eq_true this.symm)
  have upperKey : upper.key = 0 := by
    have := Binary32.isZero_eq_key upper
    rw [hu] at this
    exact (of_decide_eq_true this.symm)
  split
  · exact hl
  · split
    · exact hu
    · rename_i below above
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at below above
      rw [Binary32.less_eq_key] at below above
      rw [Binary32.isZero_eq_key]
      simp only [below.1, upperNan, lowerNan, Bool.not_false, Bool.true_and, Bool.and_true,
        decide_eq_false_iff_not, lowerKey, upperKey] at below above
      simp only [decide_eq_true_eq]
      omega

end Zero

section Learner

open Acorn
open Acorn.SwiftTd (ActiveSet Entry)

variable {config : Acorn.Config} {dimension : Dimension}

structure Calm (state : NumericState config dimension) : Prop where
  weights : ∀ idx : FeatIdx dimension, (state.weights.get idx).value.isZero = true
  deltaWeight : ∀ idx : FeatIdx dimension, Inert32 (state.transient.deltaWeight.get idx).value
  vOld : Inert32 state.transient.vOld
  vDelta : Inert32 state.transient.vDelta

theorem vec_get {α : Type} {capacity : Nat} (values : Vector α capacity) (idx : Fin capacity) :
    values.get idx = values[idx.val] := by
  simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray]

theorem get_set_vec {α : Type} {capacity : Nat} (values : Vector α capacity) (idx other : Fin
    capacity)
    (value : α) :
    (values.set idx.val value idx.isLt).get other = if idx = other then value else values.get other
      := by
  simp only [vec_get]
  rw [Vector.getElem_set]
  by_cases same : idx = other
  · subst same
    simp
  · have distinct : idx.val ≠ other.val := fun equal => same (Fin.ext equal)
    simp [same, distinct]

theorem get_replicate_vec {α : Type} {capacity : Nat} (value : α) (idx : Fin capacity) :
    (Vector.replicate capacity value).get idx = value := by
  rw [vec_get, Vector.getElem_replicate]

theorem Inert32.sumMap {α : Type} (values : List α) (read : α → Binary32)
    (terms : ∀ value ∈ values, Inert32 (read value)) :
    Inert32 (Binary32.sumMap .zero values read) := by
  rw [Binary32.sumMap_eq]
  apply Inert32.sumFrom _ _ Inert32.zero
  intro value held
  obtain ⟨source, member, rfl⟩ := List.mem_map.mp held
  exact terms source member

theorem Calm.predict {state : NumericState config dimension} (calm : Calm state)
    (features : ActiveSet dimension) : Inert32 (state.linearPrediction features) := by
  rw [NumericState.linearPrediction_def]
  exact Inert32.sumMap _ _ fun idx _ => Inert32.ofZero (calm.weights idx)

theorem Calm.initial : Calm (NumericState.initial config dimension) where
  weights idx := by
    change ((Vector.replicate _ (Weight.project config.rule .zero)).get idx).value.isZero = true
    rw [get_replicate_vec, Weight.project_zero]
    decide
  deltaWeight idx := by
    change Inert32 ((TransientState.zero dimension).deltaWeight.get idx).value
    rw [TransientState.zero_def, get_replicate_vec]
    exact Inert32.zero
  vOld := Inert32.zero
  vDelta := Inert32.zero

theorem Calm.writeWeight {state : NumericState config dimension} (calm : Calm state)
    (idx : FeatIdx dimension) {raw : Binary32} (inert : Inert32 raw) :
    Calm (state.writeWeight idx raw) where
  weights other := by
    simp only [NumericState.writeWeight, get_set_vec]
    split
    · exact inert.project _
    · exact calm.weights other
  deltaWeight := calm.deltaWeight
  vOld := calm.vOld
  vDelta := calm.vDelta

theorem Calm.writeBetaValue {state : NumericState config dimension} (calm : Calm state)
    (idx : FeatIdx dimension) (value : LogStepSize state.rails) :
    Calm (state.writeBetaValue idx value) :=
  ⟨calm.weights, calm.deltaWeight, calm.vOld, calm.vDelta⟩

theorem Calm.ofTransient {state next : NumericState config dimension} (calm : Calm state)
    (weights : next.weights = state.weights)
    (deltaWeight : next.transient.deltaWeight = state.transient.deltaWeight)
    (vOld : next.transient.vOld = state.transient.vOld)
    (vDelta : next.transient.vDelta = state.transient.vDelta) : Calm next where
  weights idx := weights ▸ calm.weights idx
  deltaWeight idx := deltaWeight ▸ calm.deltaWeight idx
  vOld := vOld ▸ calm.vOld
  vDelta := vDelta ▸ calm.vDelta

theorem Calm.writeDeltaWeight {state : NumericState config dimension} (calm : Calm state)
    (idx : FeatIdx dimension) {word : Binary32} (inert : Inert32 word) :
    Calm (state.writeDeltaWeight idx word) where
  weights := calm.weights
  deltaWeight other := by
    simp only [NumericState.writeDeltaWeight, get_set_vec]
    split
    · exact inert
    · exact calm.deltaWeight other
  vOld := calm.vOld
  vDelta := calm.vDelta

theorem Calm.clearFeatureRegisters {state : NumericState config dimension} (calm : Calm state)
    (idx : FeatIdx dimension) : Calm (state.clearFeatureRegisters idx) := by
  unfold NumericState.clearFeatureRegisters
  dsimp only
  have written : Calm (((state.writeZ idx .zero).writeP idx .zero).writeZBar idx .zero) :=
    calm.ofTransient rfl rfl rfl rfl
  exact (written.writeDeltaWeight idx Inert32.zero).ofTransient rfl rfl rfl rfl

theorem Calm.clearTransient {state : NumericState config dimension} (calm : Calm state) :
    Calm state.clearTransient where
  weights := calm.weights
  deltaWeight idx := by
    change Inert32 ((TransientState.zero dimension).deltaWeight.get idx).value
    rw [TransientState.zero_def, get_replicate_vec]
    exact Inert32.zero
  vOld := Inert32.zero
  vDelta := Inert32.zero

theorem Calm.firstLoopElement {state : NumericState config dimension} (calm : Calm state)
    (idx : FeatIdx dimension) {delta vDelta : Binary32} (hd : Inert32 delta)
    (hv : Inert32 vDelta) (decay : Binary32) :
    Calm (state.firstLoopElement idx delta vDelta decay).1 := by
  have dw : Inert32 ((delta.mul (state.transient.z.get idx).value).sub
      ((state.transient.zDelta.get idx).value.mul vDelta)) :=
    (hd.mulLeft _).sub (Inert32.mulRight _ hv)
  have raw := (Inert32.ofZero (calm.weights idx)).add dw
  refine ⟨?_, ?_, calm.vOld, calm.vDelta⟩
  · intro other
    simp only [NumericState.firstLoopElement, get_set_vec]
    split
    · exact raw.project _
    · exact calm.weights other
  · intro other
    simp only [NumericState.firstLoopElement, get_set_vec]
    split
    · split
      · exact Inert32.zero
      · exact dw
    · exact calm.deltaWeight other

theorem Calm.learnFirstLoopGo {delta vDelta : Binary32} (hd : Inert32 delta)
    (hv : Inert32 vDelta) (decay : Binary32) (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (calm : Calm state) :
    Calm (NumericState.learnFirstLoopGo config delta vDelta decay state work pos) := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct config delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    have nextCalm : Calm next := by
      simpa only [equation] using calm.firstLoopElement work[pos] hd hv decay
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simpa only [equation, ite_true] using ih (nextCalm.clearFeatureRegisters work[pos])
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    have nextCalm : Calm next := by
      simpa only [equation] using calm.firstLoopElement work[pos] hd hv decay
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simpa only [equation, ite_eq_right noPrune] using ih nextCalm
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    exact ⟨calm.weights, calm.deltaWeight, calm.vOld, calm.vDelta⟩

theorem Calm.learnFirstLoop {state : NumericState config dimension} (calm : Calm state)
    {delta vDelta : Binary32} (hd : Inert32 delta) (hv : Inert32 vDelta) (decay : Binary32) :
    Calm (state.learnFirstLoop config delta vDelta decay) := by
  rw [NumericState.learnFirstLoop_def]
  exact Calm.learnFirstLoopGo hd hv decay _ _ _ ⟨calm.weights, calm.deltaWeight, calm.vOld,
    calm.vDelta⟩

theorem Calm.secondLoopElementAt {state : NumericState config dimension} (calm : Calm state)
    (overshoot : Bool) (scale oneSubT alpha vDelta : Binary32) (idx : FeatIdx dimension) :
    Calm (NumericState.secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).1 ∧
      (Inert32 vDelta → Inert32
        (NumericState.secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).2) := by
  refine ⟨?_, fun hv => hv.add (calm.deltaWeight idx)⟩
  unfold NumericState.secondLoopElementAt
  cases overshoot <;> dsimp only
  · exact calm.ofTransient rfl rfl rfl rfl
  · refine Calm.writeBetaValue ?_ _ _
    exact calm.ofTransient rfl rfl rfl rfl

theorem Calm.learnSecondLoopGo (overshoot : Bool) (scale oneSubT : Binary32) :
    ∀ (indices : List (FeatIdx dimension)) (alphas : List Binary32)
      (state : NumericState config dimension) (vDelta : Binary32), Calm state →
      Calm (NumericState.learnSecondLoopGo overshoot scale oneSubT indices alphas state vDelta).1 ∧
        (Inert32 vDelta → Inert32 (NumericState.learnSecondLoopGo overshoot scale oneSubT indices
          alphas state vDelta).2)
  | idx :: indices, alpha :: alphas, state, vDelta, calm => by
    rw [NumericState.learnSecondLoopGo_def]
    dsimp only
    have next := calm.secondLoopElementAt overshoot scale oneSubT alpha vDelta idx
    have rest := Calm.learnSecondLoopGo overshoot scale oneSubT indices alphas
      (NumericState.secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).1
      (NumericState.secondLoopElementAt overshoot scale oneSubT alpha state vDelta idx).2 next.1
    exact ⟨rest.1, fun hv => rest.2 (next.2 hv)⟩
  | [], _, state, vDelta, calm => by
    rw [NumericState.learnSecondLoopGo_def]
    exact ⟨calm, id⟩
  | _ :: _, [], state, vDelta, calm => by
    rw [NumericState.learnSecondLoopGo_def]
    exact ⟨calm, id⟩

theorem Calm.learnSecondLoop {state : NumericState config dimension} (calm : Calm state)
    (features : ActiveSet dimension) (vDelta : Binary32) :
    Calm (state.learnSecondLoop config features vDelta).1 ∧
      (Inert32 vDelta → Inert32 (state.learnSecondLoop config features vDelta).2) := by
  rw [NumericState.learnSecondLoop_def]
  exact Calm.learnSecondLoopGo _ _ _ _ _ _ _ calm

theorem Calm.step {state : NumericState config dimension} (calm : Calm state)
    (features : ActiveSet dimension) {reward : Binary32} (hr : Inert32 reward) :
    Calm (state.step config features reward).1 := by
  rw [NumericState.step_def]
  have v := calm.predict features
  have delta : Inert32 ((reward.add (config.rule.gamma.mul (state.linearPrediction features))).sub
      state.transient.vOld) := (hr.add (Inert32.mulRight _ v)).sub calm.vOld
  have first := calm.learnFirstLoop delta calm.vDelta (config.rule.gamma.mul config.lambda)
  have second := first.learnSecondLoop features .zero
  exact ⟨second.1.weights, second.1.deltaWeight, v, second.2 Inert32.zero⟩

theorem Calm.beginTrajectory {state : NumericState config dimension} (calm : Calm state)
    (features : ActiveSet dimension) : Calm (state.beginTrajectory config features) := by
  rw [NumericState.beginTrajectory_def]
  have cleared := calm.clearTransient
  have second := cleared.learnSecondLoop features .zero
  exact ⟨second.1.weights, second.1.deltaWeight, cleared.predict features, second.2 Inert32.zero⟩

theorem Calm.terminalStep {state : NumericState config dimension} (calm : Calm state)
    {target : Binary32} (ht : Inert32 target) : Calm (state.terminalStep config target).1 := by
  rw [NumericState.terminalStep_def]
  exact (calm.learnFirstLoop (ht.sub calm.vOld) calm.vDelta _).clearTransient

theorem Calm.planWeightsGo (scale : Binary32) {delta : Binary32} (hd : Inert32 delta) :
    ∀ (indices : List (FeatIdx dimension)) (alphas : List Binary32)
      (state : NumericState config dimension), Calm state →
      Calm (NumericState.planWeightsGo scale delta indices alphas state)
  | idx :: indices, alpha :: alphas, state, calm => by
    rw [NumericState.planWeightsGo_def]
    exact Calm.planWeightsGo scale hd indices alphas _
      (calm.writeWeight idx ((Inert32.ofZero (calm.weights idx)).add
        (Inert32.mulRight _ hd)))
  | [], _, state, calm => by
    rw [NumericState.planWeightsGo_def]
    exact calm
  | _ :: _, [], state, calm => by
    rw [NumericState.planWeightsGo_def]
    exact calm

theorem Calm.planStep {state : NumericState config dimension} (calm : Calm state)
    (features : ActiveSet dimension) {target : Binary32} (ht : Inert32 target) :
    Calm (state.planStep config features target).1 := by
  rw [NumericState.planStep_def]
  dsimp only
  split
  · exact calm
  · exact Calm.planWeightsGo _ (ht.sub (calm.predict features)) _ _ _ calm

theorem Calm.retireIndex {state : NumericState config dimension} (calm : Calm state)
    (idx : FeatIdx dimension) : Calm (state.retireIndex idx) := by
  rw [NumericState.retireIndex_def]
  dsimp only
  have removed : Calm (match found : state.transient.eligible.findIdx? (· == idx) with
      | some pos => state.removeEligibleAt pos (Array.findIdx?_eq_some_iff_getElem.mp found).1
      | none => state) := by
    split
    · exact calm.ofTransient rfl rfl rfl rfl
    · exact calm
  exact ((removed.clearFeatureRegisters idx).writeWeight idx Inert32.zero).writeBetaValue _ _

theorem Calm.releaseEligible {state : NumericState config dimension} (calm : Calm state) :
    Calm state.releaseEligible := by
  rw [NumericState.releaseEligible_def]
  dsimp only
  have folded : ∀ (items : List (FeatIdx dimension)) (start : NumericState config dimension),
      Calm start → Calm (items.foldl (fun next idx => next.clearFeatureRegisters idx) start) := by
    intro items
    induction items with
    | nil => intro start held; exact held
    | cons idx rest ih =>
      intro start held
      rw [List.foldl_cons]
      exact ih (start.clearFeatureRegisters idx) (Calm.clearFeatureRegisters held idx)
  have cleared := folded state.transient.eligible.toList state calm
  rw [Array.foldl_toList] at cleared
  exact cleared.ofTransient rfl rfl rfl rfl

def Entry.Quiet : Entry dimension → Prop
  | .first delta vDelta _ => Inert32 delta ∧ Inert32 vDelta
  | .second _ _ => True
  | .step _ reward => Inert32 reward
  | .beginTrajectory _ => True
  | .terminal target => Inert32 target
  | .plan _ target => Inert32 target
  | .retire _ => True
  | .clear => True
  | .release => True

theorem Calm.apply {state : NumericState config dimension} (calm : Calm state)
    (entry : Entry dimension) (quiet : Entry.Quiet entry) : Calm (entry.apply state) := by
  cases entry with
  | first delta vDelta decay =>
    exact (Entry.apply_def (.first delta vDelta decay) state) ▸
      calm.learnFirstLoop quiet.1 quiet.2 decay
  | second features vDelta =>
    exact (Entry.apply_def (.second features vDelta) state) ▸
      (calm.learnSecondLoop features vDelta).1
  | step features reward =>
    exact (Entry.apply_def (.step features reward) state) ▸ calm.step features quiet
  | beginTrajectory features =>
    exact (Entry.apply_def (.beginTrajectory features) state) ▸ calm.beginTrajectory features
  | terminal target =>
    exact (Entry.apply_def (.terminal target) state) ▸ calm.terminalStep quiet
  | plan features target =>
    exact (Entry.apply_def (.plan features target) state) ▸ calm.planStep features quiet
  | retire idx => exact (Entry.apply_def (.retire idx) state) ▸ calm.retireIndex idx
  | clear => exact (Entry.apply_def .clear state) ▸ calm.clearTransient
  | release => exact (Entry.apply_def .release state) ▸ calm.releaseEligible

end Learner

section Control

open Acorn Acorn.Features
open Acorn.SwiftTd (ActiveSet Entry)

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat}

theorem Calm.predict_zero {state : NumericState config dimension} (calm : Calm state)
    (features : ActiveSet dimension) : (state.linearPrediction features).isZero = true := by
  rw [NumericState.linearPrediction_eq_sumFrom, Binary32.sumFrom_def]
  apply zeroWord_foldlAdd _ _ (by decide)
  intro value held
  obtain ⟨idx, _, rfl⟩ := List.mem_map.mp held
  exact calm.weights idx

theorem initial_prediction (features : ActiveSet dimension) :
    (NumericState.initial config dimension).linearPrediction features = .zero := by
  rw [NumericState.linearPrediction_eq_sumFrom]
  apply sumFrom_zeros
  intro value member
  obtain ⟨idx, _, rfl⟩ := List.mem_map.mp member
  change ((Vector.replicate _ (Weight.project config.rule .zero)).get idx).value = .zero
  rw [get_replicate_vec, Weight.project_zero]

theorem Calm.managed {learner : Managed config dimension} (calm : Calm learner.state)
    (entry : Entry dimension) (permitted : SwiftTd.Permitted entry learner.phase)
    (quiet : Entry.Quiet entry) : Calm (learner.apply entry permitted).state :=
  (Managed.apply_state learner entry permitted) ▸ calm.apply entry quiet

structure Still (controller : Controller config dimension actions) : Prop where
  rows : ∀ row : Fin actions, Calm (controller.learners.get row).state
  vOld : Inert32 controller.vOld
  vDelta : Inert32 controller.vDelta

theorem Still.resting {controller : Controller config dimension actions} (still : Still controller)
    :
    Resting controller := fun row slot => (still.rows row).weights slot

def Settled {count : Word.Count} (snapshot : PolicySnapshot count) : Prop :=
  ∀ action : Action count.word.toNat, (snapshot.values.get action).isZero = true

theorem Still.initial : Still (Controller.initial config dimension actions) where
  rows row := by
    change Calm ((Vector.ofFn fun _ => Managed.initial config dimension).get row).state
    rw [vec_get, Vector.getElem_ofFn]
    exact Calm.initial
  vOld := Inert32.zero
  vDelta := Inert32.zero

theorem Still.predictAll {controller : Controller config dimension actions} (still : Still
    controller)
    (features : ActiveSet dimension) (action : Fin actions) :
    ((controller.predictAll features).get action).isZero = true := by
  rw [Controller.predictAll_def, vec_get, Vector.getElem_map]
  exact (still.rows action).predict_zero features

theorem Still.snapshot {count : Word.Count} {controller : Controller config dimension
    count.word.toNat}
    (still : Still controller) (features : ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    Settled (controller.snapshot features epsilon) := by
  intro action
  rw [Controller.snapshot_def]
  exact still.predictAll features action

theorem get_map_vec {α β : Type} {size : Nat} (values : Vector α size) (f : α → β) (idx : Fin size)
    :
    (values.map f).get idx = f (values.get idx) := by
  rw [vec_get, vec_get, Vector.getElem_map]

theorem Still.clear {controller : Controller config dimension actions} (still : Still controller) :
    Still controller.clear where
  rows row := by
    rw [Controller.clear_def]
    dsimp only
    rw [get_map_vec]
    exact (still.rows row).managed .clear trivial trivial
  vOld := Inert32.zero
  vDelta := Inert32.zero

theorem Calm.credit {learner : Managed config dimension} (calm : Calm learner.state)
    {delta vd : Binary32} (hd : Inert32 delta) (hv : Inert32 vd) (decay : Binary32)
    (restart : Bool) : Calm (learner.credit delta vd decay restart).val.state := by
  rw [Managed.credit_def]
  have first := calm.managed (.first delta vd decay) trivial ⟨hd, hv⟩
  cases restart
  · exact first
  · exact first.managed .clear trivial trivial

theorem Still.creditStep {controller : Controller config dimension actions} (still : Still
    controller)
    (features : ActiveSet dimension) (action : Action actions) {lag delta : Binary32}
    (hl : Inert32 lag) (hd : Inert32 delta) (decay : Binary32) :
    Still (controller.creditStep features action lag delta decay) := by
  rw [Controller.creditStep_eq]
  dsimp only
  have rows : ∀ row : Fin actions,
      Calm ((controller.learners.get row).credit delta controller.vDelta decay
        controller.restartPending).val.state :=
    fun row => (still.rows row).credit hd still.vDelta decay controller.restartPending
  have second := (rows action).learnSecondLoop features .zero
  simp only [get_map_vec]
  refine ⟨fun row => ?_, hl, second.2 Inert32.zero⟩
  rw [get_set_vec]
  split
  · exact second.1
  · rw [get_map_vec, get_map_vec]
    exact rows row

theorem Still.valuesStep {controller : Controller config dimension actions} (still : Still
    controller)
    (features : ActiveSet dimension) (values : Vector Binary32 actions) (action : Action actions)
    {reward : Binary32} (hv : Inert32 (values.get action)) (hr : Inert32 reward)
    (bootstrap decay : Binary32) :
    Still (controller.valuesStep features values action reward bootstrap decay) := by
  rw [Controller.valuesStep_def]
  exact still.creditStep features action hv ((hr.add (Inert32.mulRight _ hv)).sub still.vOld) decay

theorem Still.release {controller : Controller config dimension actions} (still : Still controller)
    :
    Still controller.release where
  rows row := by
    rw [Controller.release_def]
    dsimp only
    rw [get_map_vec]
    exact (still.rows row).managed .release trivial trivial
  vOld := still.vOld
  vDelta := Inert32.zero

theorem Still.startStep {controller : Controller config dimension actions} (still : Still
    controller)
    (features : ActiveSet dimension) (action : Action actions) {lag : Binary32} (hl : Inert32 lag) :
    Still (controller.startStep features action lag) := by
  rw [Controller.startStep_def]
  exact still.release.creditStep features action hl Inert32.zero .zero

theorem Still.stopStep {controller : Controller config dimension actions} (still : Still controller)
    {delta : Binary32} (hd : Inert32 delta) : Still (controller.stopStep delta) where
  rows row := by
    rw [Controller.stopStep_eq]
    dsimp only
    rw [get_map_vec]
    exact ((still.rows row).credit hd still.vDelta .zero controller.restartPending).managed
      .release trivial trivial
  vOld := by rw [Controller.stopStep_eq]; exact Inert32.zero
  vDelta := by rw [Controller.stopStep_eq]; exact Inert32.zero

theorem Still.step {controller : Controller config dimension actions} (still : Still controller)
    (features : ActiveSet dimension) (action : Action actions) {reward : Binary32}
    (hr : Inert32 reward) : Still (controller.step features action reward).1 := by
  rw [Controller.step_def]
  exact still.valuesStep features _ action (Inert32.ofZero (still.predictAll features action)) hr _
    _

theorem Still.smdpStep {controller : Controller config dimension actions} (still : Still controller)
    (features : ActiveSet dimension) (action : Action actions) {reward : Binary32}
    (hr : Inert32 reward) (duration : UInt32) :
    Still (controller.smdpStep features action reward duration).1 := by
  rw [Controller.smdpStep_def]
  exact still.valuesStep features _ action (Inert32.ofZero (still.predictAll features action)) hr _
    _

theorem Still.closeStep {controller : Controller config dimension actions} (still : Still
    controller)
    {reward continuation : Binary32} (hr : Inert32 reward) (hc : Inert32 continuation)
    (duration : UInt32) : Still (controller.closeStep reward continuation duration) := by
  rw [Controller.closeStep_def]
  exact still.stopStep ((hr.add (Inert32.mulRight _ hc)).sub still.vOld)

theorem Still.terminal {controller : Controller config dimension actions} (still : Still controller)
    {reward : Binary32} (hr : Inert32 reward) : Still (controller.terminal reward) := by
  rw [Controller.terminal_eq]
  refine Still.clear ⟨fun row => ?_, still.vOld, still.vDelta⟩
  dsimp only
  rw [get_map_vec]
  exact (still.rows row).managed _ trivial ⟨hr.sub still.vOld, still.vDelta⟩

theorem Still.retire {controller : Controller config dimension actions} (still : Still controller)
    (feature : FeatIdx dimension) : Still (controller.retire feature) := by
  rw [Controller.retire_def]
  refine ⟨fun row => ?_, still.vOld, still.vDelta⟩
  dsimp only
  rw [get_map_vec, Managed.retire_def]
  exact (still.rows row).managed _ trivial trivial

theorem Still.resetAction {controller : Controller config dimension actions} (still : Still
    controller)
    (action : Fin actions) : Still (controller.resetAction action) where
  rows row := by
    change Calm ((controller.learners.set action.val (Managed.initial config dimension)
      action.isLt).get row).state
    rw [get_set_vec]
    split
    · exact Calm.initial
    · exact still.rows row
  vOld := still.vOld
  vDelta := still.vDelta

theorem Still.policyStep {count : Word.Count} {controller : Controller config dimension
    count.word.toNat}
    (still : Still controller) (features : ActiveSet dimension) (decision : PolicyDecision count)
    (settled : Settled decision.snapshot) {reward : Binary32} (hr : Inert32 reward)
    (duration : UInt32) : Still (controller.policyStep features decision reward duration) := by
  rw [Controller.policyStep_def]
  exact still.valuesStep features _ _ (Inert32.ofZero (settled _)) hr _ _

theorem Still.persistentStep {count : Word.Count}
    {controller : Controller config dimension count.word.toNat} (still : Still controller)
    (features : ActiveSet dimension) (snapshot : PolicySnapshot count) (settled : Settled snapshot)
    (drawn : PersistentDecision count) {reward : Binary32} (hr : Inert32 reward)
    (duration : UInt32) :
    Still (controller.persistentStep features snapshot drawn reward duration) := by
  rw [Controller.persistentStep_def]
  exact still.valuesStep features _ _ (Inert32.ofZero (settled _)) hr _ _

theorem Still.plan {controller : Controller config dimension actions} (still : Still controller)
    (action : Action actions) (features : ActiveSet dimension) {target : Binary32}
    (ht : Inert32 target) : Still (controller.plan action features target).1 := by
  rw [Controller.plan_def]
  refine ⟨fun row => ?_, still.vOld, still.vDelta⟩
  dsimp only
  rw [get_set_vec]
  split
  · exact (still.rows action).planStep features ht
  · exact still.rows row

theorem Settled.best {count : Word.Count} {snapshot : PolicySnapshot count} (settled : Settled
    snapshot) :
    snapshot.best.isZero = true := by
  rw [PolicySnapshot.best_def]
  have each : ∀ value ∈ snapshot.values.toList, value.isZero = true := by
    intro value held
    obtain ⟨idx, bound, same⟩ := List.getElem_of_mem held
    rw [← same, Vector.getElem_toList]
    have := settled ⟨idx, by simpa using bound⟩
    rwa [vec_get] at this
  have folded : ∀ (items : List Binary32) (start : Binary32), start.isZero = true →
      (∀ value ∈ items, value.isZero = true) →
      (items.foldl (fun best value => if best.Less value then value else best) start).isZero = true
        := by
    intro items
    induction items with
    | nil => intro start held _; exact held
    | cons head rest ih =>
      intro start held terms
      rw [List.foldl_cons]
      apply ih _ _ (fun value member => terms value (List.mem_cons_of_mem _ member))
      split
      · exact terms head (List.mem_cons_self ..)
      · exact held
  exact folded _ _ (settled _) (fun value held => each value (List.mem_of_mem_drop held))

theorem Settled.expected {count : Word.Count} {snapshot : PolicySnapshot count} (settled : Settled
    snapshot) :
    snapshot.expected.isZero = true := by
  rw [PolicySnapshot.expected_def]
  dsimp only
  apply zeroWord_saturate
  · have each : ∀ value ∈ snapshot.values.toList, value.isZero = true := by
      intro value held
      obtain ⟨idx, bound, same⟩ := List.getElem_of_mem held
      rw [← same, Vector.getElem_toList]
      have := settled ⟨idx, by simpa using bound⟩
      rwa [vec_get] at this
    have folded : ∀ (items : List Binary32) (start : Binary32), start.isZero = true →
        (∀ value ∈ items, value.isZero = true) →
        (items.foldl (fun lo v => if v.less lo then v else lo) start).isZero = true := by
      intro items
      induction items with
      | nil => intro start held _; exact held
      | cons head rest ih =>
        intro start held terms
        rw [List.foldl_cons]
        apply ih _ _ (fun value member => terms value (List.mem_cons_of_mem _ member))
        split
        · exact terms head (List.mem_cons_self ..)
        · exact held
    exact folded _ _ (settled _) each
  · exact settled.best

theorem Settled.comparison {count : Word.Count} {snapshot : PolicySnapshot count}
    (settled : Settled snapshot) (criterion : Criterion) :
    (comparisonValue criterion snapshot).isZero = true := by
  rw [comparisonValue_def]
  cases criterion
  · exact settled.best
  · exact settled.expected

theorem Still.backupStep {count : Word.Count} {controller : Controller config dimension
    count.word.toNat}
    (still : Still controller) (features : ActiveSet dimension) (snapshot : PolicySnapshot count)
    (settled : Settled snapshot) (action : Action count.word.toNat) {reward : Binary32}
    (hr : Inert32 reward) : Still (controller.backupStep features snapshot action reward) := by
  rw [Controller.backupStep_def, Controller.backupError_def]
  exact still.creditStep features action (Inert32.ofZero (settled action))
    ((hr.add (Inert32.mulRight _ (Inert32.ofZero settled.expected))).sub still.vOld) _

end Control

section Model

open Acorn Acorn.Features
open Acorn.SwiftTd (ActiveSet Entry)
open Float.Model (Format UnpackedFloat)

theorem zeroWord_mul_finite {left right : Binary32} (hl : left.isZero = true) (hr : right.Finite) :
    (left.mul right).isZero = true := by
  obtain ⟨sl, el⟩ := zeroWord_model hl
  have decoded := AcornVerif.CurrentArithmetic.model_ofBits32_decoded right hr
  have finiteModel := (AcornVerif.CurrentArithmetic.model_decoded32_finite right).mpr hr
  change (⟨(Float32.Model.pack (UnpackedFloat.mul Format.binary32
    (Float32.ofBits left.bits).toModel.unpack (Float32.ofBits right.bits).toModel.unpack)).toBits⟩ :
      Binary32).isZero = true
  rw [el]
  change (⟨(Float32.Model.pack (UnpackedFloat.mul Format.binary32 (.zero sl)
    (Float32.Model.ofBits right.bits).unpack)).toBits⟩ : Binary32).isZero = true
  rw [decoded]
  cases hd : AcornVerif.CurrentArithmetic.decoded32 right with
  | notANumber => rw [hd] at finiteModel; contradiction
  | infinity sign => rw [hd] at finiteModel; contradiction
  | zero sign => exact zeroWord_pack _
  | finite sign mantissa exponent positive => exact zeroWord_pack _

theorem Inert32.saturate {word : Binary32} (inert : Inert32 word) (range : Interval32)
    (lower : range.lower = .zero) (upper : 0 ≤ range.upper.key) :
    (range.saturate word).isZero = true := by
  rcases inert with zero | nan
  · have key : word.key = 0 := by
      have := Binary32.isZero_eq_key word
      rw [zero] at this
      exact of_decide_eq_true this.symm
    have finite : word.Finite := by
      rcases isZero_bits word zero with bits | bits <;>
      · obtain ⟨raw⟩ := word
        simp only at bits
        subst bits
        decide
    have lowerKey : range.lower.key = 0 := by rw [lower]; decide
    rw [range.saturate_identity word ⟨finite, by omega, by omega⟩]
    exact zero
  · unfold Interval32.saturate
    rw [Binary32.saturate_eq_less]
    simp only [nan, Bool.true_or, ite_true, lower]
    decide

theorem zeroWord_outcome {first second third : Binary32} (h1 : first.isZero = true)
    (h2 : second.isZero = true) (h3 : third.isZero = true) :
    (Conversion.narrow (((Conversion.widen first).add (Conversion.widen second)).add
      (Conversion.widen third))).isZero = true := by
  rcases isZero_bits first h1 with b1 | b1 <;> rcases isZero_bits second h2 with b2 | b2 <;>
    rcases isZero_bits third h3 with b3 | b3 <;>
  · obtain ⟨r1⟩ := first
    obtain ⟨r2⟩ := second
    obtain ⟨r3⟩ := third
    simp only at b1 b2 b3
    subst b1 b2 b3
    decide

variable {dimension : Dimension} {criterion : Criterion}

def Deviations (transition : Transition dimension criterion) : Prop :=
  ∀ action : Fin Acorn.FeatureConstants.metaActionCount, AcornVerif.CurrentPreReward.Calm
    (transition.deviations.get action).state

def ModelCalm : Model dimension criterion → Prop
  | .discounted reward continuation transition =>
    AcornVerif.CurrentPreReward.Calm reward.state ∧
      AcornVerif.CurrentPreReward.Calm continuation.state ∧ Deviations transition
  | .differential reward continuation _ transition =>
    AcornVerif.CurrentPreReward.Calm reward.state ∧
      AcornVerif.CurrentPreReward.Calm continuation.state ∧ Deviations transition

theorem Deviations.updateRows {transition : Transition dimension criterion}
    (calm : Deviations transition)
    (update : RankIdx dimension → Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension))
    (deviate : Action metaCount.word.toNat →
      Managed (criterion.config .demon) (rankDimension dimension) →
      Managed (criterion.config .demon) (rankDimension dimension))
    (kept : ∀ action learner, AcornVerif.CurrentPreReward.Calm learner.state →
      AcornVerif.CurrentPreReward.Calm (deviate action learner).state) :
    Deviations (transition.updateRows update deviate) := by
  intro action
  obtain ⟨ranked, rows, deviations⟩ := transition
  have held := calm action
  simp only [Transition.updateRows, Vector.get, Vector.getElem_toArray] at held ⊢
  simp only [Vector.getElem_mapFinIdx]
  exact kept _ _ held

theorem Deviations.initial : Deviations (Transition.initial dimension criterion) := by
  intro action
  change AcornVerif.CurrentPreReward.Calm
    ((Vector.replicate _ (Managed.initial _ _)).get action).state
  rw [get_replicate_vec]
  exact AcornVerif.CurrentPreReward.Calm.initial

theorem Calm.retireAll {config : Acorn.Config} {rank : Dimension} (positions : List (FeatIdx rank))
    :
    ∀ learner : Managed config rank, AcornVerif.CurrentPreReward.Calm learner.state →
      AcornVerif.CurrentPreReward.Calm
        (positions.foldl (fun current position => current.retire position) learner).state := by
  induction positions with
  | nil => intro learner calm; exact calm
  | cons position rest ih =>
    intro learner calm
    rw [List.foldl_cons]
    apply ih
    rw [Managed.retire_def]
    exact calm.managed _ trivial trivial

theorem Deviations.forgetColumns {count : Nat}
    {learners : Vector (Managed (criterion.config .demon) (rankDimension dimension)) count}
    (calm : ∀ index, AcornVerif.CurrentPreReward.Calm (learners.get index).state)
    (positions : List (RankIdx dimension)) (index : Fin count) :
    AcornVerif.CurrentPreReward.Calm
      ((Transition.forgetColumns learners positions).get index).state := by
  unfold Transition.forgetColumns
  rw [get_map_vec]
  exact Calm.retireAll positions _ (calm index)

theorem Deviations.rerank {transition : Transition dimension criterion} (calm : Deviations
    transition)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) : Deviations (transition.rerank order
      fresh) :=
  fun action => Deviations.forgetColumns calm _ action

theorem Deviations.retire {transition : Transition dimension criterion} (calm : Deviations
    transition)
    (feature : FeatIdx dimension) : Deviations (transition.retire feature) := by
  unfold Transition.retire
  split
  · exact calm
  · exact fun action => Deviations.forgetColumns calm _ action

theorem Deviations.begin {transition : Transition dimension criterion} (calm : Deviations
    transition)
    (features : ActiveSet dimension) : Deviations (transition.begin features) := by
  rw [Transition.begin_def]
  exact calm.updateRows _ _ fun _ learner held => held.managed _ trivial trivial

theorem Deviations.step {transition : Transition dimension criterion} (calm : Deviations transition)
    (features : ActiveSet dimension) : Deviations (transition.step features) := by
  rw [Transition.step_def]
  exact calm.updateRows _ _ fun _ learner held => held.managed _ trivial Inert32.zero

theorem Deviations.restart {transition : Transition dimension criterion} (calm : Deviations
    transition)
    (features : ActiveSet dimension) : Deviations (transition.restart features) := by
  rw [Transition.restart_def]
  refine calm.updateRows _ _ fun _ learner held => ?_
  rw [Managed.restartTrajectory_def]
  exact (held.managed .release trivial trivial).managed (.step _ .zero) trivial Inert32.zero

def OutcomeQuiet (outcome : Outcome dimension) : Prop :=
  ∀ action : Action metaCount.word.toNat, Inert32 (outcome.deviations.get action)

theorem Deviations.terminal {transition : Transition dimension criterion} (calm : Deviations
    transition)
    {outcome : Outcome dimension} (quiet : OutcomeQuiet outcome) : Deviations (transition.terminal
      outcome) := by
  rw [Transition.terminal_def]
  exact calm.updateRows _ _ fun action learner held => held.managed _ trivial (quiet action)

theorem Deviations.stop {transition : Transition dimension criterion} (calm : Deviations transition)
    {outcome : Outcome dimension} (quiet : OutcomeQuiet outcome) : Deviations (transition.stop
      outcome) := by
  rw [Transition.stop_def]
  refine calm.updateRows _ _ fun action learner held => ?_
  rw [Managed.stopTrajectory_def]
  exact (held.managed (.first _ _ .zero) trivial ⟨(quiet action).sub held.vOld,
    held.vDelta⟩).managed .release trivial trivial

abbrev ValueStill (value : ValueFunction criterion dimension) : Prop := Still value.controller

theorem expectation_finite (word : Expectation) : word.value.Finite := word.legal.1

theorem ranked_zero {value : ValueFunction criterion dimension} (still : ValueStill value)
    (ranked : RankedFeatures dimension)
    (expected : Vector Expectation (rankDimension dimension).capacity) :
    Settled (⟨value.rankedValues ranked expected, value.epsilon⟩ : PolicySnapshot metaCount) := by
  intro action
  change ((value.rankedValues ranked expected).get action).isZero = true
  rw [ValueFunction.rankedValues_def, get_map_vec, Binary32.sumMap_eq, Binary32.sumFrom_def]
  apply zeroWord_foldlAdd _ _ (by decide)
  intro term held
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp held
  exact zeroWord_mul_finite ((still.rows action).weights entry.2) (expectation_finite _)

theorem lookahead_zero {transition : Transition dimension criterion} (calm : Deviations transition)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {shared : Binary32} (zero : shared.isZero = true) :
    (transition.lookahead value features shared).isZero = true := by
  rw [Transition.lookahead_def]
  apply Settled.comparison
  intro action
  change ((transition.outcomeValues value features shared).get action).isZero = true
  rw [Transition.outcomeValues_def]
  dsimp only
  rw [vec_get, Vector.getElem_ofFn]
  have rankedZero := ranked_zero still transition.ranked
    (transition.expectedAt (transition.ranked.input features)) action
  exact zeroWord_outcome rankedZero zero ((calm action).predict_zero _)

theorem outcome_quiet (transition : Transition dimension criterion)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) :
    OutcomeQuiet (transition.outcome value features) ∧
      Inert32 (transition.outcome value features).shared := by
  rw [Transition.outcome_def]
  dsimp only
  have complete : Settled (⟨value.controller.predictAll features, value.epsilon⟩ :
      PolicySnapshot metaCount) := fun action => still.predictAll features action
  have rankedZero := ranked_zero still transition.ranked (transition.ranked.indicator features)
  have residual := zeroWord_sub (complete.comparison criterion) (rankedZero.comparison criterion)
  refine ⟨fun action => ?_, Inert32.mulRight _ (Inert32.ofZero residual)⟩
  change Inert32 ((Vector.ofFn fun action : Fin metaCount.word.toNat =>
    criterion.rule.gamma.mul ((((value.controller.predictAll features).get action).sub
      ((value.rankedValues transition.ranked (transition.ranked.indicator features)).get
        action)).sub _)).get action)
  rw [vec_get, Vector.getElem_ofFn]
  exact Inert32.mulRight _ (Inert32.ofZero (zeroWord_sub (zeroWord_sub (complete action)
    (rankedZero action)) residual))

theorem ModelCalm.initial : ModelCalm (Model.initial dimension criterion) := by
  cases criterion
  · exact ⟨Calm.initial, Calm.initial, Deviations.initial⟩
  · exact ⟨Calm.initial, Calm.initial, Deviations.initial⟩

theorem ModelCalm.retire {model : Model dimension criterion} (calm : ModelCalm model)
    (feature : FeatIdx dimension) : ModelCalm (model.retire feature) := by
  cases model with
  | discounted r c t =>
    obtain ⟨hr, hc, ht⟩ := calm
    refine ⟨?_, ?_, ht.retire feature⟩
    · rw [Managed.retire_def]; exact hr.managed _ trivial trivial
    · rw [Managed.retire_def]; exact hc.managed _ trivial trivial
  | differential r c d t =>
    obtain ⟨hr, hc, ht⟩ := calm
    refine ⟨?_, ?_, ht.retire feature⟩
    · rw [Managed.retire_def]; exact hr.managed _ trivial trivial
    · rw [Managed.retire_def]; exact hc.managed _ trivial trivial

theorem ModelCalm.rerank {model : Model dimension criterion} (calm : ModelCalm model)
    (order : List (FeatIdx dimension)) (fresh : order.Nodup) :
    ModelCalm (model.rerank order fresh) := by
  cases model with
  | discounted r c t => exact ⟨calm.1, calm.2.1, calm.2.2.rerank order fresh⟩
  | differential r c d t => exact ⟨calm.1, calm.2.1, calm.2.2.rerank order fresh⟩

theorem ModelCalm.begin {model : Model dimension criterion} (calm : ModelCalm model)
    (base : ActiveSet dimension) : ModelCalm (model.begin base) := by
  rw [Model.begin_def]
  cases model with
  | discounted r c t =>
    exact ⟨calm.1.managed _ trivial trivial, calm.2.1.managed _ trivial trivial, calm.2.2.begin
      base⟩
  | differential r c d t =>
    exact ⟨calm.1.managed _ trivial trivial, calm.2.1.managed _ trivial trivial, calm.2.2.begin
      base⟩

theorem ModelCalm.step {model : Model dimension criterion} (calm : ModelCalm model)
    (base : ActiveSet dimension) (age : ModelAge) {reward : Binary32} (hr : Inert32 reward) :
    ModelCalm (model.step base age reward) := by
  rw [Model.step_def]
  cases model with
  | discounted r c t =>
    exact ⟨calm.1.managed _ trivial hr, calm.2.1.managed _ trivial Inert32.zero, calm.2.2.step base⟩
  | differential r c d t =>
    exact ⟨calm.1.managed _ trivial hr, calm.2.1.managed _ trivial Inert32.zero, calm.2.2.step base⟩

theorem ModelCalm.terminal {model : Model dimension criterion} (calm : ModelCalm model)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {reward : Binary32} (hr : Inert32 reward) :
    ModelCalm (model.terminal value features reward) := by
  rw [Model.terminal_def]
  cases model with
  | discounted r c t =>
    have outcome := outcome_quiet t still features
    exact ⟨calm.1.managed _ trivial hr, calm.2.1.managed _ trivial outcome.2,
      calm.2.2.terminal outcome.1⟩
  | differential r c d t =>
    have outcome := outcome_quiet t still features
    exact ⟨calm.1.managed _ trivial hr, calm.2.1.managed _ trivial outcome.2,
      calm.2.2.terminal outcome.1⟩

theorem Calm.restartTrajectory {config : Acorn.Config} {rank : Dimension}
    {learner : Managed config rank} (calm : AcornVerif.CurrentPreReward.Calm learner.state)
    (features : ActiveSet rank) :
    AcornVerif.CurrentPreReward.Calm (learner.restartTrajectory features).state := by
  rw [Managed.restartTrajectory_def]
  exact (calm.managed .release trivial trivial).managed (.step _ .zero) trivial Inert32.zero

theorem Calm.stopTrajectory {config : Acorn.Config} {rank : Dimension}
    {learner : Managed config rank} (calm : AcornVerif.CurrentPreReward.Calm learner.state)
    {target : Binary32} (ht : Inert32 target) :
    AcornVerif.CurrentPreReward.Calm (learner.stopTrajectory target).state := by
  rw [Managed.stopTrajectory_def]
  exact (calm.managed (.first _ _ .zero) trivial ⟨ht.sub calm.vOld, calm.vDelta⟩).managed .release
    trivial trivial

theorem ModelCalm.restart {model : Model dimension criterion} (calm : ModelCalm model)
    (base : ActiveSet dimension) (age : ModelAge) : ModelCalm (model.restart base age) := by
  rw [Model.restart_def]
  cases model with
  | discounted r c t =>
    exact ⟨calm.1.restartTrajectory _, calm.2.1.restartTrajectory _, calm.2.2.restart base⟩
  | differential r c d t =>
    exact ⟨calm.1.restartTrajectory _, calm.2.1.restartTrajectory _, calm.2.2.restart base⟩

theorem ModelCalm.stop {model : Model dimension criterion} (calm : ModelCalm model)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {reward : Binary32} (hr : Inert32 reward) :
    ModelCalm (model.stop value features reward) := by
  rw [Model.stop_def]
  cases model with
  | discounted r c t =>
    have outcome := outcome_quiet t still features
    exact ⟨calm.1.stopTrajectory hr, calm.2.1.stopTrajectory outcome.2, calm.2.2.stop outcome.1⟩
  | differential r c d t =>
    have outcome := outcome_quiet t still features
    exact ⟨calm.1.stopTrajectory hr, calm.2.1.stopTrajectory outcome.2, calm.2.2.stop outcome.1⟩

theorem ModelCalm.target {model : Model dimension criterion} (calm : ModelCalm model)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (base : ActiveSet dimension) (age : ModelAge) {gain : RewardRate} (hg : Inert32 gain.value) :
    Inert32 ((model.predict value base age).target gain) := by
  rw [Model.predict_def]
  cases model with
  | discounted r c t =>
    dsimp only
    have rewardZero := (Inert32.ofZero (calm.1.predict_zero (modelInput .discounted base
      age))).saturate
      Criterion.discounted.modelRewardRange rfl (by decide)
    have look := lookahead_zero calm.2.2 still base
      (calm.2.1.predict_zero (modelInput .discounted base age))
    have continuation := (Inert32.ofZero look).saturate (Discount.predictionRange .g99) rfl
      (by decide)
    exact Inert32.ofZero ((Inert32.ofZero (zeroWord_add rewardZero continuation)).saturate
      (Discount.predictionRange .g99) rfl (by decide))
  | differential r c d t =>
    dsimp only
    have rewardZero := (Inert32.ofZero (calm.1.predict_zero (modelInput .differential base
      age))).saturate
      Criterion.differential.modelRewardRange rfl (by decide)
    have look := lookahead_zero calm.2.2 still base
      (calm.2.1.predict_zero (modelInput .differential base age))
    exact ((Inert32.ofZero rewardZero).sub (hg.mulLeft _)).add (Inert32.ofZero look)

end Model

section Skill

open Acorn Acorn.Features
open Acorn.SwiftTd (ActiveSet Entry)

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {discounts : List Discount} {mode : Bool}

structure OpsQuiet (models : OptionModelOps criterion dimension) : Prop where
  begin : ∀ model features, ModelCalm model → ModelCalm (models.begin model features).val
  step : ∀ model features age reward, ModelCalm model → Inert32 reward →
    ModelCalm (models.step model features age reward).val
  terminal : ∀ model (value : ValueFunction criterion dimension) features reward,
    ModelCalm model → ValueStill value → Inert32 reward →
      ModelCalm (models.terminal model value features reward).val
  restart : ∀ model features age, ModelCalm model →
    ModelCalm (models.restart model features age).val
  stop : ∀ model (value : ValueFunction criterion dimension) features reward, ModelCalm model →
    ValueStill value → Inert32 reward → ModelCalm (models.stop model value features reward).val

theorem modelOperations_quiet : OpsQuiet (modelOperations criterion dimension) where
  begin _ features calm := calm.begin features
  step _ features age _ calm hr := calm.step features age hr
  terminal _ _ features _ calm still hr := calm.terminal still features hr
  restart _ features age calm := calm.restart features age
  stop _ _ features _ calm still hr := calm.stop still features hr

theorem center_inert {reward : Binary32} (hr : Inert32 reward) (duration : UInt32) {rate :
    RewardRate}
    (hg : Inert32 rate.value) : Inert32 (criterion.center reward duration rate) := by
  cases criterion
  · exact hr
  · exact hr.sub (Inert32.mulRight _ hg)

theorem shaped_inert {reward : Binary32} (hr : Inert32 reward) (gamma : Binary32) :
    Inert32 (shapedCumulant reward gamma false false) :=
  (hr.add (Inert32.mulRight _ (by exact Inert32.zero))).sub (by exact Inert32.zero)

theorem terminal_inert {reward stopping : Binary32} (hr : Inert32 reward) (hs : Inert32 stopping) :
    Inert32 (terminalCumulant reward stopping false) :=
  (hr.add hs).sub (by exact Inert32.zero)

theorem stopping_inert {estimate : Binary32} (he : Inert32 estimate) (potential : Potential) :
    Inert32 ((Interest.learned (.neutral : Assignment config)).stoppingValue estimate potential) :=
      by
  change Inert32 (Assignment.stoppingValue .neutral estimate potential)
  unfold Assignment.stoppingValue
  split
  · exact he.add (by exact Inert32.zero)
  · exact he

theorem neutral_potential (features : ActiveSet dimension) (declared : DeclaredPotentials) :
    (Interest.learned (.neutral : Assignment config)).potential features declared = some false := by
  rw [Interest.potential_def]
  rfl

structure SkillCalm (learned : Bool)
    (skill : Skill actions config criterion dimension discounts) : Prop where
  model : ModelCalm skill.model
  policy : learned = true → Still skill.policy
  interest : learned = true → skill.interest = .learned .neutral
  following : learned = true → ∀ following, skill.following = some following →
    following.previous = false

def ActivationQuiet (learned : Bool) (activation : OptionActivation mode) : Prop :=
  learned = true → activation.previous = false

def ContinuationQuiet (learned : Bool) {activation : OptionActivation mode}
    (next : OptionContinuation actions dimension activation) : Prop :=
  learned = true → next.potential = false ∧ Settled next.policy

theorem SkillCalm.initial (learned : Bool) :
    SkillCalm learned (Skill.initial (actions := actions) (discounts := discounts) config criterion
      dimension (.learned .neutral)) where
  model := ModelCalm.initial
  policy _ := Still.initial
  interest _ := rfl
  following _ following held := by cases held

theorem SkillCalm.initialDeclared (interest : Interest config) :
    SkillCalm false (Skill.initial (actions := actions) (discounts := discounts) config criterion
      dimension interest) where
  model := ModelCalm.initial
  policy := by intro h; cases h
  interest := by intro h; cases h
  following := by intro h; cases h

theorem SkillCalm.retire {learned : Bool} {skill : Skill actions config criterion dimension
    discounts}
    (calm : SkillCalm learned skill) (feature : FeatIdx dimension) :
    SkillCalm learned (skill.retire feature) where
  model := calm.model.retire feature
  policy held := (calm.policy held).retire feature
  interest := calm.interest
  following := calm.following

section Operations

variable {learned : Bool} {skill : Skill actions config criterion dimension discounts}
  {models : OptionModelOps criterion dimension}

theorem SkillCalm.snapshot (calm : SkillCalm learned skill) (held : learned = true)
    (features : ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    Settled (skill.policy.snapshot (count := actions) features epsilon) :=
  (calm.policy held).snapshot features epsilon

theorem SkillCalm.beginOption (calm : SkillCalm learned skill) (features : ActiveSet dimension)
    {potential : Potential} (unattained : learned = true → potential = false) (learning : Bool)
    (rate : ConsumerRate) :
    SkillCalm learned (skill.beginOption features potential learning rate).1 ∧
      ActivationQuiet learned (skill.beginOption features potential learning rate).2.1 ∧
      ContinuationQuiet learned (skill.beginOption features potential learning rate).2.2 := by
  have cleared : SkillCalm learned
      (if learning then { skill with policy := skill.policy.clear } else skill) := by
    split
    · exact ⟨calm.model, fun held => (calm.policy held).clear, calm.interest, calm.following⟩
    · exact calm
  rw [Skill.beginOption_def]
  exact ⟨cleared, unattained, fun held => ⟨unattained held, cleared.snapshot held features _⟩⟩

theorem SkillCalm.beginTemporal (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    (features : ActiveSet dimension) {potential : Potential}
    (unattained : learned = true → potential = false) (learning : Bool) (rate : ConsumerRate) :
    SkillCalm learned (skill.beginTemporal models features potential learning rate).1 ∧
      ActivationQuiet learned (skill.beginTemporal models features potential learning rate).2.1 ∧
      ContinuationQuiet learned (skill.beginTemporal models features potential learning rate).2.2 :=
        by
  have begun := calm.beginOption features unattained learning rate
  rw [Skill.beginTemporal_def]
  refine ⟨?_, begun.2.1, begun.2.2⟩
  dsimp only
  split
  · exact ⟨ops.begin _ _ begun.1.model, begun.1.policy, begun.1.interest, begun.1.following⟩
  · exact begun.1

theorem SkillCalm.decide (calm : SkillCalm learned skill) {activation : OptionActivation mode}
    (features : ActiveSet dimension) {potential : Potential}
    (unattained : learned = true → potential = false) (goal : Bool) (estimate : Binary32)
    (rate : ConsumerRate) (next : OptionContinuation actions dimension activation)
    (continuing : skill.decideOption activation features potential goal estimate rate =
      .continuing next) : ContinuationQuiet learned next := by
  intro held
  have frame := skill.decide_frame activation features potential goal estimate rate next continuing
  have policy := skill.decide_policy activation features potential goal estimate rate next
    continuing
  rw [frame.2, policy]
  exact ⟨unattained held, calm.snapshot held features _⟩

theorem SkillCalm.optionCredit (calm : SkillCalm learned skill) {activation : OptionActivation mode}
    (quietActivation : ActivationQuiet learned activation)
    {next : OptionContinuation actions dimension activation} (quietNext : ContinuationQuiet learned
      next)
    (drawn : PersistentDecision actions) {reward : Binary32} (hr : Inert32 reward)
    {gain : RewardRate} (hg : Inert32 gain.value) :
    SkillCalm learned (skill.optionCredit activation next drawn reward gain) := by
  rw [Skill.optionCredit_def]
  split
  · refine ⟨calm.model, fun held => ?_, calm.interest, calm.following⟩
    obtain ⟨unattained, settled⟩ := quietNext held
    have shaped : Inert32 (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma
        next.potential activation.previous) := by
      rw [unattained, quietActivation held]
      exact shaped_inert (center_inert hr 1 hg) _
    exact (calm.policy held).persistentStep _ _ settled drawn shaped 1
  · exact calm

theorem SkillCalm.creditTemporal (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {activation : OptionActivation mode} (quietActivation : ActivationQuiet learned activation)
    {next : OptionContinuation actions dimension activation} (quietNext : ContinuationQuiet learned
      next)
    (drawn : PersistentDecision actions) {reward : Binary32} (hr : Inert32 reward)
    {gain : RewardRate} (hg : Inert32 gain.value) :
    SkillCalm learned (skill.creditTemporal models activation next drawn reward gain) := by
  have credited := calm.optionCredit quietActivation quietNext drawn hr hg
  rw [Skill.creditTemporal_def]
  dsimp only
  split
  · exact ⟨ops.step _ _ _ _ credited.model hr, credited.policy, credited.interest,
      credited.following⟩
  · exact credited

theorem SkillCalm.stepTemporal (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {activation : OptionActivation mode} (quietActivation : ActivationQuiet learned activation)
    {next : OptionContinuation actions dimension activation} (quietNext : ContinuationQuiet learned
      next)
    {reward : Binary32} (hr : Inert32 reward) {gain : RewardRate} (hg : Inert32 gain.value)
    (rng : Rng.Xoshiro256) :
    SkillCalm learned (skill.stepTemporal models activation next reward gain rng).1 ∧
      ActivationQuiet learned (skill.stepTemporal models activation next reward gain rng).2.1 := by
  rw [Skill.stepTemporal_credit]
  exact ⟨calm.creditTemporal ops quietActivation quietNext _ hr hg,
    fun held => (quietNext held).1⟩

theorem SkillCalm.terminateOption (calm : SkillCalm learned skill)
    {activation : OptionActivation mode} (quietActivation : ActivationQuiet learned activation)
    (potential : Potential) {reward terminal : Binary32} (hr : Inert32 reward)
    (ht : Inert32 terminal) {gain : RewardRate} (hg : Inert32 gain.value) :
    SkillCalm learned (skill.terminateOption activation potential reward terminal gain) := by
  rw [Skill.terminateOption_def]
  split
  · refine ⟨calm.model, fun held => ?_, calm.interest, calm.following⟩
    have cumulant : Inert32 (terminalCumulant (criterion.center reward 1 gain)
        (skill.interest.stoppingValue terminal potential) activation.previous) := by
      rw [quietActivation held, calm.interest held]
      exact terminal_inert (center_inert hr 1 hg) (stopping_inert ht potential)
    exact (calm.policy held).terminal cumulant
  · exact calm

theorem SkillCalm.endTemporal (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {ending : EndingPayload mode}
    (quietActivation : ActivationQuiet learned ending.activation) {reward terminal : Binary32}
    (hr : Inert32 reward) (ht : Inert32 terminal) {gain : RewardRate} (hg : Inert32 gain.value) :
    SkillCalm learned (skill.endTemporal models value features ending reward terminal gain) := by
  have ended := calm.terminateOption quietActivation ending.potential hr ht hg
  rw [Skill.endTemporal_def]
  dsimp only
  split
  · exact ⟨ops.terminal _ _ _ _ ended.model still hr, ended.policy, ended.interest, ended.following⟩
  · exact ended

end Operations

section Following

variable {learned : Bool} {skill : Skill actions config criterion dimension discounts}
  {models : OptionModelOps criterion dimension}

theorem SkillCalm.startFollowing (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    (features : ActiveSet dimension) {potential : Potential}
    (unattained : learned = true → potential = false) (rate : ConsumerRate)
    (action : Action actions.word.toNat) (behaviour : Vector Binary32 actions.word.toNat) :
    SkillCalm learned (skill.startFollowing models features potential rate action behaviour) := by
  rw [Skill.startFollowing_def]
  obtain ⟨interest, policy, model, following⟩ := skill
  dsimp only
  refine ⟨?_, fun held => ?_, calm.interest, fun held stored same => ?_⟩
  · split
    · exact ops.restart _ _ _ calm.model
    · exact calm.model
  · exact (calm.policy held).startStep features action
      (Inert32.ofZero (calm.snapshot held features _ action))
  · cases same
    exact unattained held

theorem SkillCalm.stopFollowing (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {following : Following}
    (stored : skill.following = some following) (potential : Potential)
    {estimate reward : Binary32} (he : Inert32 estimate) (hr : Inert32 reward)
    {gain : RewardRate} (hg : Inert32 gain.value) :
    SkillCalm learned (skill.stopFollowing models value features following potential estimate
      reward gain) := by
  have previous := calm.following
  rw [Skill.stopFollowing_def]
  obtain ⟨interest, policy, model, linked⟩ := skill
  dsimp only
  refine ⟨?_, fun held => ?_, calm.interest, fun _ _ same => by cases same⟩
  · split
    · exact ops.stop _ _ _ _ calm.model still hr
    · exact calm.model
  · have unattained := previous held following stored
    have neutral := calm.interest held
    dsimp only at neutral unattained
    rw [unattained, neutral]
    exact (calm.policy held).stopStep ((terminal_inert (center_inert hr 1 hg)
      (stopping_inert he potential)).sub (calm.policy held).vOld)

theorem SkillCalm.followTemporal (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {potential : Potential}
    (unattained : learned = true → potential = false) (goal : Bool) {estimate : Binary32}
    (he : Inert32 estimate) (rate : ConsumerRate) (action : Action actions.word.toNat)
    (behaviour : Vector Binary32 actions.word.toNat) {reward : Binary32} (hr : Inert32 reward)
    {gain : RewardRate} (hg : Inert32 gain.value) :
    SkillCalm learned (skill.followTemporal models value features potential goal estimate rate
      action behaviour reward gain) := by
  rw [Skill.followTemporal_def]
  split
  · exact calm.startFollowing ops features unattained rate action behaviour
  · rename_i following stored
    split
    · rename_i next decided
      have quietNext := calm.decide features unattained goal estimate rate next decided
      have previous := calm.following
      obtain ⟨interest, policy, model, linked⟩ := skill
      dsimp only at stored ⊢
      refine ⟨?_, fun held => ?_, calm.interest, fun held stored' same => ?_⟩
      · have credited : ModelCalm (if following.live then
            (models.step model features following.age reward).val else model) := by
          split
          · exact ops.step _ _ _ _ calm.model hr
          · exact calm.model
        split
        · exact ops.restart _ _ _ credited
        · exact credited
      · obtain ⟨unattainedNext, settled⟩ := quietNext held
        have shaped : Inert32 (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma
            potential following.previous) := by
          rw [unattained held, previous held following stored]
          exact shaped_inert (center_inert hr 1 hg) _
        exact (calm.policy held).backupStep features next.policy settled action shaped
      · cases same
        exact unattained held
    · rename_i reason decided
      exact (calm.stopFollowing ops still features stored potential he hr hg).startFollowing ops
        features unattained rate action behaviour

theorem SkillCalm.settleFollowing (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {potential : Potential}
    (unattained : learned = true → potential = false) (goal : Bool) {estimate : Binary32}
    (he : Inert32 estimate) (rate : ConsumerRate) {reward : Binary32} (hr : Inert32 reward)
    {gain : RewardRate} (hg : Inert32 gain.value) :
    SkillCalm learned (skill.settleFollowing models value features potential goal estimate rate
      reward gain) := by
  rw [Skill.settleFollowing_def]
  split
  · exact calm
  · rename_i following stored
    split
    · rename_i next decided
      have quietNext := calm.decide features unattained goal estimate rate next decided
      have previous := calm.following
      obtain ⟨interest, policy, model, linked⟩ := skill
      dsimp only at stored ⊢
      refine ⟨?_, fun held => ?_, calm.interest, fun _ _ same => by cases same⟩
      · split
        · exact ops.step _ _ _ _ calm.model hr
        · exact calm.model
      · obtain ⟨_, settled⟩ := quietNext held
        have shaped : Inert32 (shapedCumulant (criterion.center reward 1 gain) criterion.rule.gamma
            potential following.previous) := by
          rw [unattained held, previous held following stored]
          exact shaped_inert (center_inert hr 1 hg) _
        rw [Controller.backupError_def]
        exact (calm.policy held).stopStep ((shaped.add (Inert32.mulRight _
          (Inert32.ofZero settled.expected))).sub (calm.policy held).vOld)
    · exact calm.stopFollowing ops still features ‹_› potential he hr hg

theorem SkillCalm.settleTemporal (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {potential : Potential}
    (unattained : learned = true → potential = false) (goal : Bool) {estimate : Binary32}
    (he : Inert32 estimate) (rate : ConsumerRate) {reward : Binary32} (hr : Inert32 reward)
    {gain : RewardRate} (hg : Inert32 gain.value) (learning : Bool) :
    SkillCalm learned (skill.settleTemporal models value features potential goal estimate rate
      reward gain learning) := by
  rw [Skill.settleTemporal_def]
  split
  · exact calm.settleFollowing ops still features unattained goal he rate hr hg
  · exact calm

theorem SkillCalm.startTemporal (calm : SkillCalm learned skill) (ops : OpsQuiet models)
    {value : ValueFunction criterion dimension} (still : ValueStill value)
    (features : ActiveSet dimension) {potential : Potential}
    (unattained : learned = true → potential = false) (goal : Bool) {estimate : Binary32}
    (he : Inert32 estimate) (rate : ConsumerRate) {reward : Binary32} (hr : Inert32 reward)
    {gain : RewardRate} (hg : Inert32 gain.value) (learning : Bool)
    (drawn : PersistentDecision actions) :
    SkillCalm learned (skill.startTemporal models value features potential goal estimate rate
      reward gain learning drawn) := by
  rw [Skill.startTemporal_def]
  have settled := calm.settleTemporal ops still features unattained goal he rate hr hg learning
  have begun := settled.beginTemporal ops features unattained learning rate
  exact begun.1.creditTemporal ops begun.2.1 begun.2.2 drawn hr hg

end Following

end Skill

section State

open Acorn Acorn.Features Acorn.Handcrafted
open Acorn.SwiftTd (ActiveSet Entry)

def DemonRest {dimension : Dimension} {rest : List Discount} :
    DemonBank dimension (.g99 :: rest) → Prop
  | .cons learner _ => Calm learner.state

def PhaseQuiet {actions : Word.Count} {mode : Bool} (learned : Bool) :
    Occupancy (OptionActivation mode) (CommittedRun actions mode) → Prop
  | .idle => True
  | .exploring committed => ∀ slot activation, committed.origin = some (slot, activation) →
      ActivationQuiet learned activation
  | .option _ activation => ActivationQuiet learned activation

def CreditQuiet : PrimitiveCredit → Prop
  | .perStep => True
  | .catchUp gap => Inert32 gap.reward
  | .noSpan => True

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}

structure Quiet (state : TemporalControl interface profile config criterion dimension) :
    Prop where
  control : Still state.runtime.lifecycle.consumers.control
  metaController : Still state.runtime.lifecycle.consumers.metaController
  skills : ∀ slot,
    SkillCalm profile.ranksSubtasks (state.runtime.lifecycle.consumers.skills.get slot)
  demon : profile.ranksSubtasks = true → DemonRest state.runtime.lifecycle.consumers.demons
  gap : Inert32 state.runtime.references.gapReward
  credit : CreditQuiet state.credit
  rate : Inert32 state.average.rate.value
  phase : PhaseQuiet profile.ranksSubtasks state.runtime.references.phase

structure DecisionQuiet {actions : Word.Count} (decision : TemporalDecision actions) :
    Prop where
  metaValues : ∀ action, (decision.metaValues.get action).isZero = true
  metaDecision : ∀ drawn, decision.metaDecision = some drawn → Settled drawn.snapshot

def ResultQuiet (result : TemporalControl interface profile config criterion dimension ×
    TemporalDecision interface.actions) : Prop :=
  Quiet result.1 ∧ DecisionQuiet result.2

theorem Quiet.value {state : TemporalControl interface profile config criterion dimension}
    (quiet : Quiet state) : ValueStill state.valueFunction := quiet.metaController

theorem DemonRest.initial (rest : List Discount) :
    DemonRest (DemonBank.initial dimension (.g99 :: rest)) := Calm.initial

theorem Quiet.initial :
    Quiet (TemporalControl.initial interface profile config criterion dimension) where
  control := Still.initial
  metaController := Still.initial
  skills slot := by
    change SkillCalm profile.ranksSubtasks (((profile.interests config).map
      (Skill.initial config criterion dimension)).get slot)
    rw [get_map_vec]
    cases learned : profile.subtasks
    · have ranks : profile.ranksSubtasks = true := by
        simp [FeatureProfile.ranksSubtasks, learned]
      rw [ranks]
      have interest : (profile.interests config).get slot = .learned .neutral := by
        simp only [FeatureProfile.interests, vec_get, Vector.getElem_ofFn, learned]
      rw [interest]
      exact SkillCalm.initial true
    · have ranks : profile.ranksSubtasks = false := by
        simp [FeatureProfile.ranksSubtasks, learned]
      rw [ranks]
      exact SkillCalm.initialDeclared _
  demon _ := DemonRest.initial interface.signals
  gap := Inert32.zero
  credit := by
    change CreditQuiet profile.credit.initial
    cases profile.credit
    · trivial
    · exact Inert32.zero
    · trivial
  rate := by
    change Inert32 (RewardRate.project .zero).value
    exact Inert32.ofZero (by decide)
  phase := trivial

end State

section Ops

open Acorn Acorn.Features Acorn.Handcrafted
open Acorn.SwiftTd (ActiveSet Entry)

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}

section Writes

variable {state : TemporalControl interface profile config criterion dimension}

theorem Quiet.withSkill (quiet : Quiet state) (slot : Fin Acorn.FeatureConstants.skillCount)
    {skill : Skill interface.actions config criterion dimension interface.layout}
    (calm : SkillCalm profile.ranksSubtasks skill) : Quiet (state.withSkill slot skill) where
  control := quiet.control
  metaController := quiet.metaController
  skills other := by
    change SkillCalm profile.ranksSubtasks
      ((state.runtime.lifecycle.consumers.skills.set slot.val skill slot.isLt).get other)
    rw [get_set_vec]
    split
    · exact calm
    · exact quiet.skills other
  demon := quiet.demon
  gap := quiet.gap
  credit := quiet.credit
  rate := quiet.rate
  phase := quiet.phase

theorem Quiet.withPhase (quiet : Quiet state)
    {phase : Occupancy (OptionActivation (profile.mode != .frozen))
      (CommittedRun interface.actions (profile.mode != .frozen))}
    (quietPhase : PhaseQuiet profile.ranksSubtasks phase) : Quiet (state.withPhase phase) :=
  ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, quiet.gap, quiet.credit,
    quiet.rate, quietPhase⟩

theorem Quiet.withoutPlanning (quiet : Quiet state) : Quiet state.withoutPlanning :=
  ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, quiet.gap, quiet.credit,
    quiet.rate, quiet.phase⟩

theorem Quiet.withGap (quiet : Quiet state) {gap : CreditGap} (inert : Inert32 gap.reward) :
    Quiet (state.withGap gap) :=
  ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, inert, quiet.credit,
    quiet.rate, quiet.phase⟩

theorem Quiet.skipMeta (quiet : Quiet state) : Quiet state.skipMeta := by
  unfold TemporalControl.skipMeta
  split
  · exact quiet.withGap quiet.gap
  · exact quiet

theorem Quiet.withRng (quiet : Quiet state) (rng : Rng.Xoshiro256) :
    Quiet { state with runtime := { state.runtime with references :=
      { state.runtime.references with rng := rng } } } :=
  ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, quiet.gap, quiet.credit,
    quiet.rate, quiet.phase⟩

theorem Quiet.interrupt (quiet : Quiet state)
    (origin : Option (Fin Acorn.FeatureConstants.skillCount ×
      OptionActivation (profile.mode != .frozen)))
    (quietOrigin : ∀ slot activation, origin = some (slot, activation) →
      ActivationQuiet profile.ranksSubtasks activation) : Quiet (state.interrupt origin).1 := by
  cases origin with
  | none => exact quiet
  | some held =>
    obtain ⟨slot, activation⟩ := held
    unfold TemporalControl.interrupt
    dsimp only
    split
    · have calm := quiet.skills slot
      refine quiet.withSkill slot ⟨calm.model, calm.policy, calm.interest, ?_⟩
      intro learned following same
      cases same
      exact quietOrigin slot activation rfl learned
    · exact quiet

theorem PhaseQuiet.afterOption {mode : Bool} {learned : Bool}
    (slot : Fin Acorn.FeatureConstants.skillCount) {activation : OptionActivation mode}
    (quiet : ActivationQuiet learned activation) (run : Option (ExploratoryRun interface.actions)) :
    PhaseQuiet learned (Occupancy.afterOption slot activation run) := by
  unfold Occupancy.afterOption
  split
  · split
    · intro other held same
      cases same
      exact quiet
    · exact quiet
  · exact quiet

theorem PhaseQuiet.afterPrimitive {mode : Bool} {learned : Bool}
    (run : Option (ExploratoryRun interface.actions)) :
    PhaseQuiet (mode := mode) learned (Occupancy.afterPrimitive run) := by
  unfold Occupancy.afterPrimitive
  split
  · split
    · intro slot activation same
      cases same
    · trivial
  · trivial

end Writes

section Dispatch

variable {state : TemporalControl interface profile config criterion dimension}

theorem Quiet.choosePrimitive (quiet : Quiet state) (features : ActiveSet dimension)
    {metaValues : Vector Binary32 metaCount.word.toNat}
    (zero : ∀ action, (metaValues.get action).isZero = true)
    {metaDecision : Option (PolicyDecision metaCount)}
    (settled : ∀ drawn, metaDecision = some drawn → Settled drawn.snapshot)
    (ended : Option EndEvent) :
    ResultQuiet (state.choosePrimitive features metaValues metaDecision ended) :=
  ⟨(quiet.withPhase (PhaseQuiet.afterPrimitive _)).withRng _, ⟨zero, settled⟩⟩

theorem Quiet.serve (quiet : Quiet state) (features : ActiveSet dimension)
    {next : TemporalControl interface profile config criterion dimension}
    {decision : TemporalDecision interface.actions}
    (served : state.serve features = some (next, decision)) : ResultQuiet (next, decision) := by
  unfold TemporalControl.serve at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      obtain ⟨rfl, rfl⟩ := served
      have origin : ∀ slot activation, committed.origin = some (slot, activation) →
          ActivationQuiet profile.ranksSubtasks activation := by
        have := quiet.phase
        rw [phase] at this
        exact this
      have interrupted := (quiet.interrupt committed.origin origin).withPhase
        (phase := .exploring (.bare pair.2)) (fun slot activation same => by cases same)
      have skipped : Quiet (if committed.origin.isSome = true then
          (state.interrupt committed.origin).1.withPhase (.exploring (.bare pair.2))
          else ((state.interrupt committed.origin).1.withPhase
            (.exploring (.bare pair.2))).skipMeta) := by
        split
        · exact interrupted
        · exact interrupted.skipMeta
      generalize (if committed.origin.isSome = true then
          (state.interrupt committed.origin).1.withPhase (.exploring (.bare pair.2))
          else ((state.interrupt committed.origin).1.withPhase
            (.exploring (.bare pair.2))).skipMeta) = chosen at skipped ⊢
      refine ⟨?_, ⟨?_, fun drawn same => by cases same⟩⟩
      · dsimp only
        split
        · exact skipped.withoutPlanning
        · exact skipped
      · intro action
        dsimp only
        split
        · exact skipped.withoutPlanning.metaController.predictAll features action
        · simp only [Vector.get, Vector.getElem_toArray, Vector.getElem_replicate]
          decide
  · contradiction
  · contradiction

theorem Quiet.stepOption (quiet : Quiet state) {models : OptionModelOps criterion dimension}
    (ops : OpsQuiet models) (slot : Fin Acorn.FeatureConstants.skillCount)
    {activation : OptionActivation (profile.mode != .frozen)}
    (quietActivation : ActivationQuiet profile.ranksSubtasks activation)
    {next : OptionContinuation interface.actions dimension activation}
    (quietNext : ContinuationQuiet profile.ranksSubtasks next) {reward : Binary32}
    (hr : Inert32 reward) {metaValues : Vector Binary32 metaCount.word.toNat}
    (zero : ∀ action, (metaValues.get action).isZero = true)
    {metaDecision : Option (PolicyDecision metaCount)}
    (settled : ∀ drawn, metaDecision = some drawn → Settled drawn.snapshot)
    (started : Bool) (ended : Option EndEvent) :
    ResultQuiet (state.stepOption models slot activation next reward metaValues metaDecision
      started ended) := by
  rw [TemporalControl.stepOption_eq]
  have stepped := (quiet.skills slot).stepTemporal ops quietActivation quietNext hr quiet.rate
    state.runtime.references.rng
  exact ⟨((quiet.withSkill slot stepped.1).withPhase
    (PhaseQuiet.afterOption slot stepped.2 _)).withRng _, ⟨zero, settled⟩⟩

def ClosingQuiet (learned : Bool)
    (closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))) : Prop :=
  ActivationQuiet learned closing.activation.activation

theorem Quiet.closeOption (quiet : Quiet state) {models : OptionModelOps criterion dimension}
    (ops : OpsQuiet models) (features : ActiveSet dimension)
    {closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen))}
    (quietClosing : ClosingQuiet profile.ranksSubtasks closing) {reward terminal : Binary32}
    (hr : Inert32 reward) (ht : Inert32 terminal) :
    Quiet (state.closeOption models features closing reward terminal).1 := by
  rw [TemporalControl.closeOption_eq]
  dsimp only
  split
  · rename_i none
    rw [none]
    exact quiet.withSkill closing.slot ((quiet.skills closing.slot).endTemporal ops quiet.value
      features quietClosing hr ht quiet.rate)
  · exact quiet

theorem Quiet.learnMeta (quiet : Quiet state) (features : ActiveSet dimension)
    {decision : PolicyDecision metaCount} (settled : Settled decision.snapshot) :
    Quiet (state.learnMeta features decision) := by
  rw [TemporalControl.learnMeta_eq]
  split
  · exact quiet
  · have closed := quiet.withGap (gap := .closed) Inert32.zero
    refine ⟨closed.control, ?_, closed.skills, closed.demon, closed.gap, closed.credit,
      closed.rate, closed.phase⟩
    exact quiet.metaController.policyStep features decision settled
      (center_inert quiet.gap _ quiet.rate) _

theorem Quiet.drawMeta (quiet : Quiet state) (features : ActiveSet dimension) :
    Quiet (state.drawMeta features).1 ∧ Settled (state.drawMeta features).2.snapshot := by
  unfold TemporalControl.drawMeta
  refine ⟨quiet.withRng _, ?_⟩
  dsimp only
  rw [PolicySnapshot.draw_snapshot]
  exact quiet.metaController.snapshot features _

end Dispatch

end Ops

section Refresh

open Acorn Acorn.Features Acorn.Handcrafted
open Acorn.SwiftTd (ActiveSet Entry)

section Ranking

variable {config : Features.Config} {dimension : Dimension}

theorem rankedCandidates_rest (weights : WeightArray (.discounted .g99) dimension)
    (zero : ∀ idx, (weights.get idx).value.isZero = true) :
    rankedCandidates dimension config weights = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro candidate member
  have source := ranked_subset _ _ candidate member
  obtain ⟨unit, _, found⟩ := List.mem_filterMap.mp source
  unfold candidateOfWeight at found
  dsimp only at found
  split at found
  · rename_i positive
    have key := Binary32.isZero_eq_key (weights.get (unitFeature dimension config unit)).value
    rw [zero (unitFeature dimension config unit)] at key
    have same := of_decide_eq_true key.symm
    omega
  · contradiction

theorem rankAssignments_rest (weights : WeightArray (.discounted .g99) dimension)
    (zero : ∀ idx, (weights.get idx).value.isZero = true)
    (held : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    (rankAssignments dimension config weights held)[slot.val] = .neutral := by
  unfold rankAssignments
  rw [rankedCandidates_rest weights zero]
  simp only [Vector.getElem_ofFn]
  have none : kept held [] slot = none := by
    unfold kept
    split
    · rfl
    · cases held[slot.val] <;> rfl
  rw [none]
  simp [entrants]

end Ranking

section Free

variable {shape : PatchShape} {actions : Word.Count} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {discounts : List Discount} {payload : Type}

structure FreeQuiet (learned : Bool)
    (free : FreeDispatch shape actions config criterion dimension discounts payload) : Prop where
  control : Still free.lifecycle.consumers.control
  metaController : Still free.lifecycle.consumers.metaController
  skills : ∀ slot, SkillCalm learned (free.lifecycle.consumers.skills.get slot)
  demon : learned = true → DemonRest free.lifecycle.consumers.demons

def closingPayload (free : FreeDispatch shape actions config criterion dimension discounts payload)
    :
    Option (Fin Acorn.FeatureConstants.skillCount × payload) :=
  free.closing.map fun ending => (ending.slot, ending.activation)

theorem FreeQuiet.install {learned : Bool}
    {free : FreeDispatch shape actions config criterion dimension discounts payload}
    (quiet : FreeQuiet learned free) (slot : Fin Acorn.FeatureConstants.skillCount)
    {target : Assignment config} (neutral : learned = true → target = .neutral) :
    FreeQuiet learned (free.install slot target) ∧
      closingPayload (free.install slot target) = closingPayload free := by
  unfold FreeDispatch.install
  dsimp only
  split
  · refine ⟨⟨quiet.control, quiet.metaController, fun other => ?_, quiet.demon⟩, rfl⟩
    change SkillCalm learned ((free.lifecycle.consumers.skills.set slot.val _ slot.isLt).get other)
    rw [get_set_vec]
    split
    · rename_i same
      subst same
      have calm := quiet.skills slot
      rw [vec_get] at calm
      refine ⟨calm.model, calm.policy, fun held => ?_, calm.following⟩
      rw [neutral held]
    · exact quiet.skills other
  · refine ⟨⟨quiet.control, quiet.metaController.resetAction _, fun other => ?_, quiet.demon⟩, ?_⟩
    · change SkillCalm learned ((free.lifecycle.consumers.skills.set slot.val _ slot.isLt).get
      other)
      rw [get_set_vec]
      split
      · cases learned
        · exact SkillCalm.initialDeclared _
        · rw [neutral rfl]
          exact SkillCalm.initial true
      · exact quiet.skills other
    · unfold closingPayload
      dsimp only
      cases free.closing with
      | none => rfl
      | some ending =>
        simp only [Option.map_some]
        split <;> rfl

theorem FreeQuiet.installAll {learned : Bool}
    (targets : Vector (Assignment config) Acorn.FeatureConstants.skillCount)
    (neutral : learned = true → ∀ slot : Fin Acorn.FeatureConstants.skillCount,
      targets[slot.val] = .neutral) :
    ∀ (slots : List (Fin Acorn.FeatureConstants.skillCount))
      (free : FreeDispatch shape actions config criterion dimension discounts payload),
      FreeQuiet learned free →
      FreeQuiet learned (slots.foldl (fun current slot => current.install slot targets[slot.val])
          free) ∧
        closingPayload (slots.foldl (fun current slot => current.install slot targets[slot.val])
          free) = closingPayload free := by
  intro slots
  induction slots with
  | nil => intro free quiet; exact ⟨quiet, rfl⟩
  | cons slot rest ih =>
    intro free quiet
    rw [List.foldl_cons]
    have installed := quiet.install slot (fun held => neutral held slot)
    have later := ih _ installed.1
    exact ⟨later.1, later.2.trans installed.2⟩

theorem DemonRest.weights {rest : List Discount} {bank : DemonBank dimension (.g99 :: rest)}
    (calm : DemonRest bank) : ∀ idx, (bank.rankingWeights.get idx).value.isZero = true := by
  cases bank with
  | cons learner tail => exact Calm.weights (show Calm learner.state from calm)

theorem FreeQuiet.rerankModels {learned : Bool}
    {free : FreeDispatch shape actions config criterion dimension discounts payload}
    (quiet : FreeQuiet learned free) :
    FreeQuiet learned free.rerankModels ∧ closingPayload free.rerankModels = closingPayload free :=
      by
  refine ⟨⟨quiet.control, quiet.metaController, fun slot => ?_, quiet.demon⟩, rfl⟩
  change SkillCalm learned ((free.lifecycle.consumers.skills.map _).get slot)
  rw [get_map_vec]
  have calm := quiet.skills slot
  exact ⟨calm.model.rerank _ _, calm.policy, calm.interest, calm.following⟩

theorem FreeQuiet.refreshModels {learned : Bool}
    {free : FreeDispatch shape actions config criterion dimension discounts payload}
    (quiet : FreeQuiet learned free) :
    FreeQuiet learned (free.refreshModels learned) ∧
      closingPayload (free.refreshModels learned) = closingPayload free := by
  cases learned with
  | false =>
    rw [FreeDispatch.refreshModels_keep]
    exact quiet.rerankModels
  | true =>
    rw [FreeDispatch.refreshModels_assign]
    unfold FreeDispatch.refreshRanked
    have targets := fun (_ : true = true) (slot : Fin Acorn.FeatureConstants.skillCount) =>
      rankAssignments_rest free.lifecycle.consumers.demons.rankingWeights
        (DemonRest.weights (quiet.demon rfl))
        (free.lifecycle.consumers.skills.map (·.interest.held)) slot
    have installed := FreeQuiet.installAll _ targets (List.finRange _) free quiet
    have reranked := installed.1.rerankModels
    exact ⟨reranked.1, reranked.2.trans installed.2⟩

end Free

section State

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}
  {state : TemporalControl interface profile config criterion dimension}

def payloads (closing : Option (Closing interface.actions config criterion dimension
    interface.layout
    (EndingPayload (profile.mode != .frozen)))) :
    Option (Fin Acorn.FeatureConstants.skillCount × EndingPayload (profile.mode != .frozen)) :=
  closing.map fun ending => (ending.slot, ending.activation)

theorem Quiet.refreshFree (quiet : Quiet state)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) :
    Quiet (state.refreshFree closing).1 ∧ payloads (state.refreshFree closing).2 = payloads closing
      := by
  have free : FreeQuiet profile.ranksSubtasks
      (⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩ :
        FreeDispatch interface.symbols interface.actions config criterion dimension
          interface.signals
          (EndingPayload (profile.mode != .frozen))) :=
    ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon⟩
  have refreshed := free.refreshModels
  exact ⟨⟨refreshed.1.control, refreshed.1.metaController, refreshed.1.skills, refreshed.1.demon,
    quiet.gap, quiet.credit, quiet.rate, quiet.phase⟩, refreshed.2⟩

end State

section Planning

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {discounts : List Discount}
  {skills : Vector (Skill actions config criterion dimension discounts)
    Acorn.FeatureConstants.skillCount}

theorem lookAhead_still {result : PlanningResult criterion dimension} (still : Still
    result.controller)
    (calm : ∀ slot, ModelCalm (skills.get slot).model) (features : ActiveSet dimension)
    {gain : RewardRate} (hg : Inert32 gain.value) (rate : SwiftTd.ExploreRate)
    (slot : Fin Acorn.FeatureConstants.skillCount) :
    Still (result.lookAhead skills features gain rate slot).1.controller := by
  unfold PlanningResult.lookAhead
  exact still.plan _ features ((calm slot).target (value := ⟨result.controller, rate⟩) still
    features _ hg)

theorem backupAll_still (calm : ∀ slot, ModelCalm (skills.get slot).model)
    (features : ActiveSet dimension) {gain : RewardRate} (hg : Inert32 gain.value)
    (rate : SwiftTd.ExploreRate) :
    ∀ (slots : List (Fin Acorn.FeatureConstants.skillCount)) (result : PlanningResult criterion
      dimension),
      Still result.controller →
      Still (slots.foldl (fun state slot => state.backup skills features gain rate slot)
        result).controller := by
  intro slots
  induction slots with
  | nil => intro result still; exact still
  | cons slot rest ih =>
    intro result still
    rw [List.foldl_cons]
    exact ih _ (lookAhead_still still calm features hg rate slot)

theorem sweepAll_still (calm : ∀ slot, ModelCalm (skills.get slot).model)
    (features : ActiveSet dimension) {gain : RewardRate} (hg : Inert32 gain.value)
    (rate : SwiftTd.ExploreRate) :
    ∀ (slots : List (Fin Acorn.FeatureConstants.skillCount)) (result : PlanningResult criterion
      dimension),
      Still result.controller →
      Still (slots.foldl (fun state slot => state.sweep skills features gain rate slot)
        result).controller := by
  intro slots
  induction slots with
  | nil => intro result still; exact still
  | cons slot rest ih =>
    intro result still
    rw [List.foldl_cons]
    exact ih _ (lookAhead_still still calm features hg rate slot)

theorem planning_still (selection : PlanningSelection) {result : PlanningResult criterion dimension}
    (still : Still result.controller) (calm : ∀ slot, ModelCalm (skills.get slot).model)
    (features : ActiveSet dimension) {gain : RewardRate} (hg : Inert32 gain.value)
    (rate : SwiftTd.ExploreRate) :
    Still (planningBoundary selection result skills features gain rate).controller := by
  cases selection with
  | none => exact still
  | expectation =>
    rw [planning_expectation]
    exact sweepAll_still calm _ hg rate _ _ (backupAll_still calm features hg rate _ _ still)

end Planning

section PlanState

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}
  {state : TemporalControl interface profile config criterion dimension}

theorem Quiet.planFree (quiet : Quiet state) (selection : PlanningSelection)
    (features : ActiveSet dimension) : Quiet (state.planFree (planningBoundary selection) features)
      := by
  unfold TemporalControl.planFree
  dsimp only
  have planned : Still (if profile.mode == .frozen then
      ({ (⟨state.runtime.lifecycle.consumers.metaController,
        state.runtime.references.modelPredictions, state.runtime.references.planningSteps,
        state.runtime.references.planningErrors, state.runtime.references.recent⟩ :
          PlanningResult criterion dimension) with errors := Vector.replicate _ .zero } :
        PlanningResult criterion dimension)
      else planningBoundary selection ⟨state.runtime.lifecycle.consumers.metaController,
        state.runtime.references.modelPredictions, state.runtime.references.planningSteps,
        state.runtime.references.planningErrors, state.runtime.references.recent⟩
        state.runtime.lifecycle.consumers.skills features state.average.rate
        state.metaRate).controller := by
    split
    · exact quiet.metaController
    · exact planning_still selection quiet.metaController (fun slot => (quiet.skills slot).model)
        features quiet.rate _
  exact ⟨quiet.control, planned, quiet.skills, quiet.demon, quiet.gap, quiet.credit, quiet.rate,
    quiet.phase⟩

theorem Quiet.prepareSelection (quiet : Quiet state) (models : OptionModelOps criterion dimension)
    (features : ActiveSet dimension) {reward : Binary32} (hr : Inert32 reward) :
    Quiet (state.prepareSelection models features reward) := by
  unfold TemporalControl.prepareSelection
  dsimp only
  have advanced : Quiet { state with rate := state.rate.advance } :=
    ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, quiet.gap, quiet.credit,
      quiet.rate, quiet.phase⟩
  have owed : Quiet (if profile.usesHierarchy && profile.mode != .frozen then
      ({ state with rate := state.rate.advance } : TemporalControl interface profile config
        criterion
        dimension).withGap ((({ state with rate := state.rate.advance } :
          TemporalControl interface profile config criterion dimension)).gap.accumulate reward
            criterion.rule.gamma)
      else { state with rate := state.rate.advance }) := by
    split
    · exact advanced.withGap (quiet.gap.add (hr.mulLeft _))
    · exact advanced
  generalize (if profile.usesHierarchy && profile.mode != .frozen then
      ({ state with rate := state.rate.advance } : TemporalControl interface profile config
        criterion
        dimension).withGap ((({ state with rate := state.rate.advance } :
          TemporalControl interface profile config criterion dimension)).gap.accumulate reward
            criterion.rule.gamma)
      else { state with rate := state.rate.advance }) = owedState at owed ⊢
  split
  · exact ⟨owed.control, owed.metaController, owed.skills, owed.demon, owed.gap, owed.credit,
      owed.rate, owed.phase⟩
  · exact owed

end PlanState

end Refresh

section Select

open Acorn Acorn.Features Acorn.Handcrafted
open Acorn.SwiftTd (ActiveSet Entry)

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}
  {state : TemporalControl interface profile config criterion dimension}

theorem SkillCalm.unattained {learned : Bool} {actions : Word.Count} {discounts : List Discount}
    {skill : Skill actions config criterion dimension discounts} (calm : SkillCalm learned skill)
    {features : ActiveSet dimension} {declared : DeclaredPotentials} {potential : Potential}
    (reported : skill.interest.potential features declared = some potential) :
    learned = true → potential = false := by
  intro held
  rw [calm.interest held, neutral_potential] at reported
  cases reported
  rfl

theorem Quiet.dispatchMeta (quiet : Quiet state) {models : OptionModelOps criterion dimension}
    (ops : OpsQuiet models) (features : ActiveSet dimension) (declared : DeclaredPotentials)
    {reward : Binary32} (hr : Inert32 reward) (goal : Bool) {decision : PolicyDecision metaCount}
    (settled : Settled decision.snapshot) (ended : Option EndEvent)
    {next : TemporalControl interface profile config criterion dimension}
    {selected : TemporalDecision interface.actions}
    (executed : state.dispatchMeta models features declared reward goal decision ended =
      some (next, selected)) : ResultQuiet (next, selected) := by
  rw [TemporalControl.dispatchMeta_eq] at executed
  have learnt := quiet.learnMeta features settled
  generalize state.learnMeta features decision = credited at executed learnt
  dsimp only at executed
  have drawnSettled : ∀ drawn, some decision = some drawn → Settled drawn.snapshot := by
    intro drawn same
    cases same
    exact settled
  split at executed
  · obtain ⟨rfl, rfl⟩ := selected_eq executed
    exact learnt.choosePrimitive features settled drawnSettled ended
  · rename_i slot _
    cases potential : (credited.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure] at executed
      obtain ⟨rfl, rfl⟩ := selected_eq executed
      have unattained := (learnt.skills slot).unattained potential
      have settledSkill := (learnt.skills slot).settleTemporal ops learnt.value features unattained
        goal (Inert32.ofZero (settled.comparison criterion)) credited.skillRate hr learnt.rate
        (profile.mode != .frozen)
      have begun := settledSkill.beginTemporal ops features unattained (profile.mode != .frozen)
        credited.skillRate
      exact (learnt.withSkill slot begun.1).stepOption ops slot begun.2.1 begun.2.2 hr settled
        drawnSettled true ended

def ClosingsQuiet (learned : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) : Prop :=
  ∀ ending, closing = some ending → ClosingQuiet learned ending

theorem ClosingsQuiet.ofPayloads {learned : Bool}
    {closing other : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))}
    (quiet : ClosingsQuiet learned closing) (same : payloads other = payloads closing) :
    ClosingsQuiet learned other := by
  intro ending held
  rw [held] at same
  cases closing with
  | none => cases same
  | some original =>
    simp only [payloads, Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
    have quietOriginal := quiet original rfl
    unfold ClosingQuiet at quietOriginal ⊢
    rw [same.2]
    exact quietOriginal

theorem Quiet.atBoundary (quiet : Quiet state) {models : OptionModelOps criterion dimension}
    (ops : OpsQuiet models) (selection : PlanningSelection) (features : ActiveSet dimension)
    (declared : DeclaredPotentials) {reward : Binary32} (hr : Inert32 reward) (goal : Bool)
    {closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))}
    (quietClosing : ClosingsQuiet profile.ranksSubtasks closing) (ended : Option EndEvent)
    {next : TemporalControl interface profile config criterion dimension}
    {selected : TemporalDecision interface.actions}
    (executed : state.atBoundary models (planningBoundary selection) features declared reward goal
      closing ended = some (next, selected)) : ResultQuiet (next, selected) := by
  unfold TemporalControl.atBoundary at executed
  have refreshedQuiet := quiet.refreshFree closing
  have refreshedClosing := quietClosing.ofPayloads refreshedQuiet.2
  generalize state.refreshFree closing = refreshed at executed refreshedQuiet refreshedClosing
  dsimp only at executed
  have drawnQuiet := (refreshedQuiet.1.planFree selection features).drawMeta features
  generalize (refreshed.1.planFree (planningBoundary selection) features).drawMeta features = drawn
    at executed drawnQuiet
  revert executed refreshedClosing
  cases refreshed.2 with
  | none =>
    intro _ executed
    exact drawnQuiet.1.dispatchMeta ops features declared hr goal drawnQuiet.2 ended executed
  | some owner =>
    intro quietOwner executed
    have closed := drawnQuiet.1.closeOption ops features (quietOwner owner rfl) hr
      (Inert32.ofZero (drawnQuiet.2 drawn.2.action))
    exact closed.dispatchMeta ops features declared hr goal drawnQuiet.2 _ executed

theorem Quiet.selectWithOperations (quiet : Quiet state) {models : OptionModelOps criterion
    dimension}
    (ops : OpsQuiet models) (selection : PlanningSelection) (features : ActiveSet dimension)
    (declared : DeclaredPotentials) {reward : Binary32} (hr : Inert32 reward) (goal : Bool)
    {next : TemporalControl interface profile config criterion dimension}
    {selected : TemporalDecision interface.actions}
    (executed : state.selectWithOperations models (planningBoundary selection) features declared
      reward goal = some (next, selected)) : ResultQuiet (next, selected) := by
  unfold TemporalControl.selectWithOperations at executed
  have preparedQuiet := quiet.prepareSelection models features hr
  generalize state.prepareSelection models features reward = prepared at executed preparedQuiet
  dsimp only at executed
  revert executed
  cases served : prepared.serve features with
  | some result =>
    intro executed
    obtain ⟨rfl, rfl⟩ := selected_eq executed
    exact preparedQuiet.serve features served
  | none =>
    intro executed
    simp only at executed
    have idle := preparedQuiet.withPhase (phase := .idle) trivial
    have zero : ∀ action, ((Vector.replicate metaCount.word.toNat Binary32.zero).get
        action).isZero = true := by
      intro action
      simp only [Vector.get, Vector.getElem_toArray, Vector.getElem_replicate]
      decide
    have phaseQuiet := preparedQuiet.phase
    split at executed
    · obtain ⟨rfl, rfl⟩ := selected_eq executed
      exact idle.choosePrimitive features zero (fun drawn same => by cases same) none
    · split at executed
      · exact idle.atBoundary ops selection features declared hr goal
          (fun ending same => by cases same) none executed
      · exact idle.atBoundary ops selection features declared hr goal
          (fun ending same => by cases same) none executed
      · rename_i slot activation phase
        rw [phase] at phaseQuiet
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          have unattained := (idle.skills slot).unattained potential
          have metaSettled := idle.metaController.snapshot (count := metaCount) features
            (prepared.withPhase .idle).metaRate
          have estimate := Inert32.ofZero (metaSettled.comparison criterion)
          split at executed
          · rename_i next decided
            obtain ⟨rfl, rfl⟩ := selected_eq executed
            have quietNext := (idle.skills slot).decide features unattained goal _ _ next decided
            have stepped := idle.withoutPlanning.stepOption ops slot phaseQuiet quietNext hr
              metaSettled (metaDecision := none) (fun drawn same => by cases same) false none
            exact ⟨stepped.1.skipMeta, stepped.2⟩
          · rename_i reason decided
            have closingQuiet : ClosingsQuiet profile.ranksSubtasks
                (some ⟨slot, ⟨activation, value, reason⟩, none⟩ :
                  Option (Closing interface.actions config criterion dimension interface.layout
                    (EndingPayload (profile.mode != .frozen)))) := by
              intro ending same
              cases same
              exact phaseQuiet
            split at executed
            · exact idle.atBoundary ops selection features declared hr goal closingQuiet none
                executed
            · have closed := idle.closeOption ops features (closingQuiet _ rfl) hr estimate
              exact closed.atBoundary ops selection features declared hr goal
                (fun ending same => by cases same) _ executed

end Select

section Learn

open Acorn Acorn.Features Acorn.Handcrafted
open Acorn.SwiftTd (ActiveSet Entry)

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}
  {state : TemporalControl interface profile config criterion dimension}

theorem Quiet.stoppingEstimate {decision : TemporalDecision interface.actions}
    (quiet : DecisionQuiet decision) : (state.stoppingEstimate decision).isZero = true := by
  rw [TemporalControl.stoppingEstimate_def]
  split
  · rename_i drawn same
    exact (quiet.metaDecision drawn same).comparison criterion
  · exact Settled.comparison (snapshot := ⟨decision.metaValues, state.metaRate⟩)
      quiet.metaValues criterion

theorem Quiet.takeoverValue (features : ActiveSet dimension) (declared : DeclaredPotentials)
    (goal : Bool) {decision : TemporalDecision interface.actions} (quiet : DecisionQuiet decision) :
    ∀ value, state.takeoverValue features declared goal decision = some value → Inert32 value := by
  intro value held
  unfold TemporalControl.takeoverValue at held
  split at held
  · cases ended : decision.ended with
    | none => rw [ended] at held; cases held
    | some event =>
      rw [ended] at held
      simp only [Option.map_some, Option.some.injEq] at held
      subst held
      split
      · split
        · exact Inert32.ofZero (quiet.metaValues _)
        · exact Inert32.ofZero (Quiet.stoppingEstimate quiet)
      · exact Inert32.ofZero (Quiet.stoppingEstimate quiet)
  · cases held

theorem Quiet.closeSpan (quiet : Quiet state) {continuation : Option Binary32}
    (inert : ∀ value, continuation = some value → Inert32 value) :
    Quiet (state.closeSpan continuation) := by
  cases continuation with
  | none => exact quiet
  | some value =>
    rw [TemporalControl.closeSpan_eq]
    have closed := quiet.withGap (gap := .closed) Inert32.zero
    exact ⟨closed.control, quiet.metaController.closeStep (center_inert quiet.gap _ quiet.rate)
      (inert value rfl) _, closed.skills, closed.demon, closed.gap, closed.credit, closed.rate,
      closed.phase⟩

theorem Quiet.followOptions (quiet : Quiet state) (features : ActiveSet dimension)
    (declared : DeclaredPotentials) {reward : Binary32} (hr : Inert32 reward) (goal : Bool)
    {decision : TemporalDecision interface.actions} (quietDecision : DecisionQuiet decision) :
    Quiet (state.followOptions (modelOperations criterion dimension) features declared reward goal
      decision) := by
  rw [TemporalControl.followOptions_eq]
  split
  · refine ⟨quiet.control, quiet.metaController, fun slot => ?_, quiet.demon, quiet.gap,
      quiet.credit, quiet.rate, quiet.phase⟩
    change SkillCalm profile.ranksSubtasks
      ((state.runtime.lifecycle.consumers.skills.mapFinIdx _).get slot)
    rw [vec_get, Vector.getElem_mapFinIdx]
    have calm := quiet.skills slot
    rw [vec_get] at calm
    rw [followSlot_def]
    split
    · exact ⟨calm.model, calm.policy, calm.interest, fun _ _ same => by cases same⟩
    · split
      · rename_i potential reported
        exact calm.followTemporal modelOperations_quiet quiet.value features
          (calm.unattained reported) goal (Inert32.ofZero (Quiet.stoppingEstimate quietDecision))
          _ _ _ hr quiet.rate
      · exact ⟨calm.model, calm.policy, calm.interest, fun _ _ same => by cases same⟩
  · exact quiet

theorem rewardSignal_zero {reward : Binary32} (hr : Inert32 reward) :
    (rewardSignal reward).isZero = true := by
  unfold rewardSignal indicator
  have below : Binary32.zero.less reward = false := by
    rw [Binary32.less_eq_key]
    rcases hr with zero | nan
    · have key : reward.key = 0 := by
        have := Binary32.isZero_eq_key reward
        rw [zero] at this
        exact of_decide_eq_true this.symm
      have zeroKey : (Binary32.zero).key = 0 := by decide
      simp [key, zeroKey]
    · simp [nan]
  rw [below]
  decide

theorem DemonRest.step {rest : List Discount} {bank : DemonBank dimension (.g99 :: rest)}
    (calm : DemonRest bank) (features : ActiveSet dimension) {origin : Option Departure}
    {reward : Binary32} (hr : Inert32 reward) (tail : Cumulants rest) :
    DemonRest (bank.step features (.cons origin reward tail)).bank := by
  cases bank with
  | cons learner others =>
    rw [DemonBank.step_def]
    exact Calm.step (show Calm learner.state from calm) features hr

theorem observe_inert (tracker : AverageRewardTracker) (pending learning : Bool)
    {reward : Binary32} (hr : Inert32 reward) (hg : Inert32 tracker.rate.value) :
    Inert32 (criterion.observe tracker pending learning reward).rate.value := by
  unfold Criterion.observe
  split
  · unfold AverageRewardTracker.observe
    dsimp only
    have projected : (RewardRate.project reward).value.isZero = true :=
      hr.saturate rewardRange rfl (by decide)
    have delta := Inert32.mulRight gainTrackingStep
      ((Inert32.ofZero projected).sub hg)
    exact Inert32.ofZero ((hg.add delta).saturate rewardRange rfl (by decide))
  · exact hg

theorem PrimitiveControl.creditQuiet {actions : Nat} {control : PrimitiveControl criterion dimension
    actions}
    (still : Still control.controller) (credit : CreditQuiet control.credit)
    (hg : Inert32 control.average.rate.value) (features : ActiveSet dimension)
    (action : Action actions) (own : Bool) {reward : Binary32} (hr : Inert32 reward) :
    Still (control.creditStep features action own reward).controller ∧
      CreditQuiet (control.creditStep features action own reward).credit := by
  unfold PrimitiveControl.creditStep
  split
  · exact ⟨still.step features action (center_inert hr 1 hg), credit⟩
  · split
    · exact ⟨still.step features action (center_inert hr 1 hg), credit⟩
    · exact ⟨still, credit⟩
  · rename_i gap same
    rw [same] at credit
    have accumulated : Inert32 (gap.accumulate reward criterion.rule.gamma).reward :=
      (show Inert32 gap.reward from credit).add (hr.mulLeft _)
    dsimp only
    split
    · exact ⟨still.smdpStep features action (center_inert accumulated _ hg) _, Inert32.zero⟩
    · exact ⟨still, accumulated⟩

theorem Quiet.finish (quiet : Quiet state) (features : ActiveSet dimension) (obs : Frame interface)
    {reward : Binary32} (hr : Inert32 reward) (decision : TemporalDecision interface.actions) :
    Quiet (state.finish features obs reward decision) := by
  rw [TemporalControl.finish_eq]
  dsimp only
  unfold PredictionControl.advanceWith
  dsimp only [TemporalControl.predictionView, TemporalControl.recordEpisodes]
  have skills : ∀ slot, SkillCalm profile.ranksSubtasks
      (state.runtime.lifecycle.consumers.skills.get slot) := quiet.skills
  split
  · exact ⟨quiet.control, quiet.metaController, skills, quiet.demon, quiet.gap, quiet.credit,
      observe_inert _ _ _ hr quiet.rate, quiet.phase⟩
  · have credited := PrimitiveControl.creditQuiet (control :=
    ⟨state.runtime.lifecycle.consumers.control,
      state.credit, state.average, state.runtime.references.pendingAction⟩) quiet.control
      quiet.credit quiet.rate features decision.action decision.own hr
    refine ⟨credited.1, quiet.metaController, skills, fun held => ?_, quiet.gap, credited.2,
      observe_inert _ _ _ hr ?_, quiet.phase⟩
    · exact DemonRest.step (quiet.demon held) features (Inert32.ofZero (rewardSignal_zero hr))
        obs.signals
    · rw [(PrimitiveControl.credit_preserves_clock _ features decision.action decision.own
        reward).1]
      exact quiet.rate

theorem Quiet.learn (quiet : Quiet state) (features : ActiveSet dimension) (obs : Frame interface)
    {reward : Binary32} (hr : Inert32 reward) (goal : Bool)
    {decision : TemporalDecision interface.actions} (quietDecision : DecisionQuiet decision) :
    Quiet (state.learn features obs reward goal decision) := by
  unfold TemporalControl.learn
  dsimp only
  exact ((quiet.followOptions features obs.declared hr goal quietDecision).closeSpan
    (Quiet.takeoverValue features obs.declared goal quietDecision)).finish features obs hr decision

end Learn

section Draw

open Acorn Acorn.Features Acorn.Handcrafted
open Acorn.SwiftTd (ActiveSet Entry)

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension}
  {state : TemporalControl interface profile config criterion dimension}

def OwedQuiet (learned : Bool) : Owed interface profile config criterion dimension → Prop
  | .settled => True
  | .served _ => True
  | .continuing _ activation next _ =>
    ActivationQuiet learned activation ∧ ContinuationQuiet learned next
  | .boundary closing decision start =>
    (∀ ending, closing = some ending → ClosingQuiet learned ending.1 ∧ Inert32 ending.2) ∧
      Settled decision.snapshot ∧ (∀ drawn, start = some drawn → learned = true →
        drawn.potential = false)

def DrawQuiet (result : TemporalControl interface profile config criterion dimension ×
    Owed interface profile config criterion dimension × TemporalDecision interface.actions) : Prop
      :=
  Quiet result.1 ∧ OwedQuiet profile.ranksSubtasks result.2.1 ∧ DecisionQuiet result.2.2

theorem Quiet.prepareDraw (quiet : Quiet state) (models : OptionModelOps criterion dimension)
    (features : ActiveSet dimension) : Quiet (state.prepareDraw models features) := by
  unfold TemporalControl.prepareDraw
  dsimp only
  split
  · exact ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, quiet.gap, quiet.credit,
      quiet.rate, quiet.phase⟩
  · exact ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, quiet.gap, quiet.credit,
      quiet.rate, quiet.phase⟩

theorem Quiet.oweReward (quiet : Quiet state) {reward : Binary32} (hr : Inert32 reward) :
    Quiet (state.oweReward reward) := by
  unfold TemporalControl.oweReward
  split
  · exact quiet.withGap (quiet.gap.add (hr.mulLeft _))
  · exact quiet

theorem Quiet.serveDraw (quiet : Quiet state) (features : ActiveSet dimension)
    {next : TemporalControl interface profile config criterion dimension} {skip : Bool}
    {decision : TemporalDecision interface.actions}
    (served : state.serveDraw features = some (next, skip, decision)) :
    Quiet next ∧ DecisionQuiet decision := by
  unfold TemporalControl.serveDraw at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      obtain ⟨rfl, _, rfl⟩ := served
      have origin : ∀ slot activation, committed.origin = some (slot, activation) →
          ActivationQuiet profile.ranksSubtasks activation := by
        have := quiet.phase
        rw [phase] at this
        exact this
      have interrupted := (quiet.interrupt committed.origin origin).withPhase
        (phase := .exploring (.bare pair.2)) (fun slot activation same => by cases same)
      refine ⟨?_, ⟨?_, fun drawn same => by cases same⟩⟩
      · split
        · exact interrupted.withoutPlanning
        · exact interrupted
      · intro action
        dsimp only
        split
        · exact interrupted.withoutPlanning.metaController.predictAll features action
        · simp only [Vector.get, Vector.getElem_toArray, Vector.getElem_replicate]
          decide
  · contradiction
  · contradiction

theorem terminalValue_inert {decision : PolicyDecision metaCount} (settled : Settled
    decision.snapshot)
    {estimate : Binary32} (he : Inert32 estimate) :
    Inert32 (terminalValue criterion decision estimate) := by
  unfold terminalValue
  cases criterion
  · exact he
  · exact Inert32.ofZero (settled decision.action)

theorem Quiet.drawBoundary (quiet : Quiet state) (selection : PlanningSelection)
    (features : ActiveSet dimension) (declared : DeclaredPotentials)
    {closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))}
    (quietClosing : ClosingsQuiet profile.ranksSubtasks closing) {estimate : Binary32}
    (he : Inert32 estimate)
    {result : TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions}
    (executed : state.drawBoundary (planningBoundary selection) features declared closing estimate =
      some result) : DrawQuiet result := by
  unfold TemporalControl.drawBoundary at executed
  have refreshedQuiet := quiet.refreshFree closing
  have refreshedClosing := quietClosing.ofPayloads refreshedQuiet.2
  generalize state.refreshFree closing = refreshed at executed refreshedQuiet refreshedClosing
  dsimp only at executed
  have drawnQuiet := (refreshedQuiet.1.planFree selection features).drawMeta features
  generalize (refreshed.1.planFree (planningBoundary selection) features).drawMeta features = drawn
    at executed drawnQuiet
  have terminal := terminalValue_inert (criterion := criterion) drawnQuiet.2 he
  have owedClosing : ∀ ending, refreshed.2.map (fun closing =>
      (closing, terminalValue criterion drawn.2 estimate)) = some ending →
      ClosingQuiet profile.ranksSubtasks ending.1 ∧ Inert32 ending.2 := by
    intro ending held
    cases hc : refreshed.2 with
    | none => rw [hc] at held; cases held
    | some original =>
      rw [hc] at held
      cases held
      exact ⟨refreshedClosing original hc, terminal⟩
  have drawnSettled : ∀ chosen, some drawn.2 = some chosen → Settled chosen.snapshot := by
    intro chosen same
    cases same
    exact drawnQuiet.2
  split at executed
  · cases executed
    have chosen := drawnQuiet.1.choosePrimitive features drawnQuiet.2 drawnSettled
      (refreshed.2.map closingEvent)
    exact ⟨chosen.1, ⟨owedClosing, drawnQuiet.2, fun _ same => by cases same⟩, chosen.2⟩
  · rename_i slot _
    cases potential : (drawn.1.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at executed
      subst executed
      have unattained := (drawnQuiet.1.skills slot).unattained potential
      refine ⟨(drawnQuiet.1.withPhase (PhaseQuiet.afterOption slot (activation :=
        OptionActivation.first _ value) unattained _)).withRng _, ⟨owedClosing, drawnQuiet.2, ?_⟩,
        ⟨drawnQuiet.2, drawnSettled⟩⟩
      intro start same
      cases same
      exact unattained

theorem Quiet.drawFirst (quiet : Quiet state) {models : OptionModelOps criterion dimension}
    (selection : PlanningSelection) (features : ActiveSet dimension)
    (declared : DeclaredPotentials) (goal : Bool)
    {result : TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions}
    (executed : state.drawFirst models (planningBoundary selection) features declared goal =
      some result) : DrawQuiet result := by
  unfold TemporalControl.drawFirst at executed
  have preparedQuiet := quiet.prepareDraw models features
  generalize state.prepareDraw models features = prepared at executed preparedQuiet
  dsimp only at executed
  revert executed
  cases served : prepared.serveDraw features with
  | some drawn =>
    intro executed
    simp only [pure, Option.some.injEq] at executed
    subst executed
    have servedQuiet := preparedQuiet.serveDraw features served
    exact ⟨servedQuiet.1, trivial, servedQuiet.2⟩
  | none =>
    intro executed
    simp only at executed
    have idle := preparedQuiet.withPhase (phase := .idle) trivial
    have zero : ∀ action, ((Vector.replicate metaCount.word.toNat Binary32.zero).get
        action).isZero = true := by
      intro action
      simp only [Vector.get, Vector.getElem_toArray, Vector.getElem_replicate]
      decide
    have phaseQuiet := preparedQuiet.phase
    split at executed
    · simp only [pure, Option.some.injEq] at executed
      subst executed
      have chosen := idle.choosePrimitive features zero (metaDecision := none)
        (fun drawn same => by cases same) none
      exact ⟨chosen.1, trivial, chosen.2⟩
    · split at executed
      · exact idle.drawBoundary selection features declared (fun ending same => by cases same)
          Inert32.zero executed
      · exact idle.drawBoundary selection features declared (fun ending same => by cases same)
          Inert32.zero executed
      · rename_i slot activation phase
        rw [phase] at phaseQuiet
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential, bind, Option.bind] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          have unattained := (idle.skills slot).unattained potential
          have metaSettled := idle.metaController.snapshot (count := metaCount) features
            (prepared.withPhase .idle).metaRate
          have estimate := Inert32.ofZero (metaSettled.comparison criterion)
          split at executed
          · rename_i next decided
            simp only [pure, Option.some.injEq] at executed
            subst executed
            have quietNext := (idle.skills slot).decide features unattained goal _ _ next decided
            refine ⟨(idle.withoutPlanning.withPhase (PhaseQuiet.afterOption slot (activation :=
              activation.advance next) (fun held => (quietNext held).1) _)).withRng _,
              ⟨phaseQuiet, quietNext⟩, ⟨metaSettled, fun drawn same => by cases same⟩⟩
          · rename_i reason decided
            have closingQuiet : ClosingsQuiet profile.ranksSubtasks
                (some ⟨slot, ⟨activation, value, reason⟩, none⟩ :
                  Option (Closing interface.actions config criterion dimension interface.layout
                    (EndingPayload (profile.mode != .frozen)))) := by
              intro ending same
              cases same
              exact phaseQuiet
            exact idle.drawBoundary selection features declared closingQuiet estimate executed

theorem Quiet.settle (quiet : Quiet state) {owed : Owed interface profile config criterion
    dimension}
    (quietOwed : OwedQuiet profile.ranksSubtasks owed) {models : OptionModelOps criterion dimension}
    (ops : OpsQuiet models) (features : ActiveSet dimension) {reward : Binary32}
    (hr : Inert32 reward) (goal : Bool) : Quiet (state.settle owed models features reward goal) :=
      by
  unfold TemporalControl.settle
  cases owed with
  | settled => exact quiet
  | served skip =>
    dsimp only
    split
    · exact (quiet.oweReward hr).skipMeta
    · exact quiet.oweReward hr
  | continuing slot activation next drawn =>
    dsimp only
    have owedQuiet := quiet.oweReward hr
    rw [TemporalControl.creditOption_eq]
    exact (owedQuiet.withSkill slot ((owedQuiet.skills slot).creditTemporal ops quietOwed.1
      quietOwed.2 drawn hr owedQuiet.rate)).skipMeta
  | boundary closing decision start =>
    obtain ⟨quietClosing, settled, quietStart⟩ := quietOwed
    dsimp only
    have owedQuiet := quiet.oweReward hr
    have closed : Quiet (match closing with
        | none => state.oweReward reward
        | some closing => ((state.oweReward reward).closeOption models features closing.1 reward
            closing.2).1) := by
      split
      · exact owedQuiet
      · rename_i ending
        have quietEnding := quietClosing ending rfl
        exact owedQuiet.closeOption ops features quietEnding.1 hr quietEnding.2
    have credited := closed.learnMeta features settled
    split
    · exact credited
    · rename_i drawn
      rw [TemporalControl.startOption_eq]
      exact credited.withSkill drawn.slot ((credited.skills drawn.slot).startTemporal ops
        credited.value features (quietStart drawn rfl) goal
        (Inert32.ofZero (settled.comparison criterion)) _ hr credited.rate _ drawn.drawn)

theorem Quiet.planAfter (quiet : Quiet state) (planning : PlanningSelection)
    (features : ActiveSet dimension) (decision : TemporalDecision interface.actions) :
    Quiet (state.planAfter planning features decision) := by
  unfold TemporalControl.planAfter
  split
  · exact quiet.planFree planning features
  · exact quiet

theorem Quiet.deferred (quiet : Quiet state) (order : StepOrder) (planning : PlanningSelection)
    (features : ActiveSet dimension) {owed : Owed interface profile config criterion dimension}
    (quietOwed : OwedQuiet profile.ranksSubtasks owed) {reward : Binary32} (hr : Inert32 reward)
    (goal : Bool) (decision : TemporalDecision interface.actions) :
    Quiet (state.deferred order planning features owed reward goal decision) := by
  unfold TemporalControl.deferred
  cases order with
  | learnThenAct => exact quiet
  | planAfterAct => exact quiet.planAfter planning features decision
  | actThenLearn =>
    exact (quiet.settle quietOwed modelOperations_quiet features hr goal).planAfter planning
      features decision

end Draw

section Agent

open Acorn Acorn.Features Acorn.Handcrafted
open Acorn.SwiftTd (ActiveSet Entry)

section Tester

variable {actions : Word.Count} {config : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {rest : List Discount}

structure EnsembleQuiet (learned : Bool)
    (ensemble : Ensemble actions config criterion dimension (.g99 :: rest)) : Prop where
  control : Still ensemble.control
  metaController : Still ensemble.metaController
  skills : ∀ slot, SkillCalm learned (ensemble.skills.get slot)
  demon : learned = true → DemonRest ensemble.demons

theorem DemonRest.retire {bank : DemonBank dimension (.g99 :: rest)} (calm : DemonRest bank)
    (feature : FeatIdx dimension) : DemonRest (bank.retire feature) := by
  cases bank with
  | cons learner others =>
    change Calm (learner.retire feature).state
    rw [Managed.retire_def]
    exact Calm.managed (show Calm learner.state from calm) _ trivial trivial

theorem EnsembleQuiet.retire {learned : Bool}
    {ensemble : Ensemble actions config criterion dimension (.g99 :: rest)}
    (quiet : EnsembleQuiet learned ensemble) (feature : FeatIdx dimension) :
    EnsembleQuiet learned (ensemble.retire feature) where
  control := quiet.control.retire feature
  metaController := quiet.metaController.retire feature
  skills slot := by
    change SkillCalm learned ((ensemble.skills.map (·.retire feature)).get slot)
    rw [get_map_vec]
    exact (quiet.skills slot).retire feature
  demon held := (quiet.demon held).retire feature

theorem EnsembleQuiet.release {learned : Bool}
    {ensemble : Ensemble actions config criterion dimension (.g99 :: rest)}
    (quiet : EnsembleQuiet learned ensemble) (unit : Fin config.units.count) :
    EnsembleQuiet learned (ensemble.release unit) where
  control := quiet.control
  metaController := by
    unfold Ensemble.release
    have folded : ∀ (slots : List (Fin Acorn.FeatureConstants.skillCount))
        (controller : Controller (criterion.config .control) dimension
          Acorn.FeatureConstants.metaActionCount), Still controller →
        Still (slots.foldl (fun controller slot =>
          if ensemble.skills[slot.val].interest.held.holds unit then
            controller.resetAction (metaOfSkill slot)
          else controller) controller) := by
      intro slots
      induction slots with
      | nil => intro controller still; exact still
      | cons slot others ih =>
        intro controller still
        rw [List.foldl_cons]
        apply ih
        split
        · exact still.resetAction _
        · exact still
    exact folded _ _ quiet.metaController
  skills slot := by
    change SkillCalm learned ((ensemble.skills.map _).get slot)
    rw [get_map_vec]
    split
    · exact SkillCalm.initial learned
    · exact quiet.skills slot
  demon := quiet.demon

theorem EnsembleQuiet.releaseAll {learned : Bool} (units : List (Fin config.units.count)) :
    ∀ ensemble : Ensemble actions config criterion dimension (.g99 :: rest),
      EnsembleQuiet learned ensemble → EnsembleQuiet learned (ensemble.releaseAll units) := by
  induction units with
  | nil => intro ensemble quiet; exact quiet
  | cons unit others ih =>
    intro ensemble quiet
    exact ih _ (quiet.release unit)

end Tester

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

theorem Quiet.ensemble {state : TemporalControl interface profile config criterion dimension}
    (quiet : Quiet state) :
    EnsembleQuiet profile.ranksSubtasks state.runtime.lifecycle.consumers :=
  ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon⟩

theorem Quiet.retire {agent : Agent interface profile config criterion dimension planning}
    (quiet : Quiet agent.control) (active : Vector Bool config.units.count) :
    Quiet (agent.retire active).control := by
  unfold Agent.retire
  split
  · exact quiet
  · have tested := agent.control.runtime.lifecycle.test_preserves
      agent.control.runtime.references.phase.free active (EnsembleQuiet profile.ranksSubtasks)
      (fun ensemble feature held => held.retire feature) quiet.ensemble
    have released := EnsembleQuiet.releaseAll
      (agent.control.runtime.lifecycle.test agent.control.runtime.references.phase.free active).2 _
      tested
    exact ⟨released.control, released.metaController, released.skills, released.demon, quiet.gap,
      quiet.credit, quiet.rate, quiet.phase⟩

theorem Quiet.advanceClock {agent : Agent interface profile config criterion dimension planning}
    (quiet : Quiet agent.control) : Quiet agent.advanceClock.control :=
  ⟨quiet.control, quiet.metaController, quiet.skills, quiet.demon, quiet.gap, quiet.credit,
    quiet.rate, quiet.phase⟩

theorem Quiet.choose {agent : Agent interface profile config criterion dimension planning}
    (quiet : Quiet agent.control) (order : StepOrder) (percept : Percept interface)
    (hr : Inert32 percept.reward) :
    Quiet (agent.choose order percept).control ∧
      OwedQuiet profile.ranksSubtasks (agent.choose order percept).owed ∧
      DecisionQuiet (agent.choose order percept).decision ∧
      (agent.choose order percept).percept = percept ∧
      (agent.choose order percept).order = order := by
  have advanced := quiet.advanceClock
  cases order with
  | actThenLearn =>
    obtain ⟨drawn, ordered, perceived, _, _⟩ := agent.choose_drawn percept
    have result := advanced.drawFirst .none _ _ _ drawn
    exact ⟨result.1, result.2.1, result.2.2, perceived, ordered⟩
  | learnThenAct =>
    obtain ⟨selected, ordered, perceived, _, _, owed⟩ :=
      agent.choose_selected .learnThenAct (by decide) percept
    unfold TemporalControl.select at selected
    have result := advanced.selectWithOperations modelOperations_quiet _ _ _ hr _ selected
    refine ⟨result.1, ?_, result.2, perceived, ordered⟩
    rw [owed]
    trivial
  | planAfterAct =>
    obtain ⟨selected, ordered, perceived, _, _, owed⟩ :=
      agent.choose_selected .planAfterAct (by decide) percept
    unfold TemporalControl.select at selected
    have result := advanced.selectWithOperations modelOperations_quiet _ _ _ hr _ selected
    refine ⟨result.1, ?_, result.2, perceived, ordered⟩
    rw [owed]
    trivial

theorem Quiet.actOrdered {agent : Agent interface profile config criterion dimension planning}
    (quiet : Quiet agent.control) (order : StepOrder) (percept : Percept interface)
    (hr : Inert32 percept.reward) : Quiet (agent.actOrdered order percept).1.control := by
  obtain ⟨chosen, owed, decision, perceived, _⟩ := quiet.choose order percept hr
  have reward : Inert32 (agent.choose order percept).percept.reward := by rw [perceived]; exact hr
  have deferred := chosen.deferred (agent.choose order percept).order planning
    (agent.choose order percept).features owed reward
    (agent.choose order percept).percept.frame.achieved (agent.choose order percept).decision
  have learned := deferred.learn (agent.choose order percept).features
    (agent.choose order percept).percept.frame reward
    (agent.choose order percept).percept.frame.achieved decision
  exact Quiet.retire (agent := (agent.choose order percept).learned) learned
    (agent.choose order percept).units

theorem Quiet.reached (order : StepOrder) :
    ∀ (percepts : List (Percept interface))
      (agent : Agent interface profile config criterion dimension planning),
      Quiet agent.control → (∀ percept ∈ percepts, percept.reward.isZero = true) →
      Quiet (percepts.foldl (fun state percept => (state.actOrdered order percept).1) agent).control
        := by
  intro percepts
  induction percepts with
  | nil => intro agent quiet _; exact quiet
  | cons percept others ih =>
    intro agent quiet rewards
    rw [List.foldl_cons]
    exact ih _ (quiet.actOrdered order percept
      (Inert32.ofZero (rewards percept (List.mem_cons_self ..))))
      (fun other held => rewards other (List.mem_cons_of_mem _ held))

end Agent

theorem pre_reward_weights_zero (interface : Interface) (profile : FeatureProfile)
    (config : Features.Config) (criterion : Criterion) (dimension : Dimension)
    (planning : PlanningSelection) (order : StepOrder) (percepts : List (Percept interface))
    (quiet : ∀ percept ∈ percepts, percept.reward.isZero = true) :
    let final := percepts.foldl (fun state percept => (state.actOrdered order percept).1)
      (Agent.initial interface profile config criterion dimension planning)
    Resting final.control.runtime.lifecycle.consumers.control ∧
      Resting final.control.runtime.lifecycle.consumers.metaController ∧
      (profile.subtasks = .learned →
        ∀ slot, Resting (final.control.runtime.lifecycle.consumers.skills.get slot).policy) := by
  intro final
  have reached : Quiet final.control :=
    Quiet.reached order percepts _ Quiet.initial quiet
  refine ⟨reached.control.resting, reached.metaController.resting, fun learned slot => ?_⟩
  have ranks : profile.ranksSubtasks = true := by
    simp [FeatureProfile.ranksSubtasks, learned]
  exact ((reached.skills slot).policy ranks).resting

end AcornVerif.CurrentPreReward
