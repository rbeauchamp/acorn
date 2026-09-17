/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentLearner
import AcornVerif.CurrentRetirementRounding

/-!
# Executing retirement arithmetic

These contracts concern singleton machine predictions and rail admission in
Javed, Sharifnassab & Sutton, *SwiftTD: A Fast and Robust Algorithm for Temporal
Difference Learning*, Reinforcement Learning Journal 2 (2024), Algorithms 1 and 3,
and the retirement interface of Sutton, Bowling & Pilarski, *The Alberta Plan
for AI Research*, arXiv:2208.11173v3 (2023), Step 2 (PAR-11).
-/

open Acorn Acorn.SwiftTd
open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder

namespace AcornVerif.CurrentRetirement

/-- Adding positive zero preserves every finite numerical value, including negative zero. -/
theorem zero_add_numeric (word : Binary32) (finite : word.Finite) :
    (Binary32.zero.add word).Finite ∧
      numerical32 (Binary32.zero.add word) = numerical32 word := by
  have valid := model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)
  change ModelNormalized Format.binary32 (decoded32 word) ∧
    ModelFits Format.binary32 (decoded32 word) at valid
  have normal : ModelNormalized Format.binary32
      (UnpackedFloat.add Format.binary32 (.zero .positive) (decoded32 word)) := by
    cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelNormalized]
  have fits : ModelFits Format.binary32
      (UnpackedFloat.add Format.binary32 (.zero .positive) (decoded32 word)) := by
    cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelFits]
  have decoded := model_add32_decoded .zero word (by decide) finite normal fits
  refine ⟨(model_decoded32_finite _).mp ?_, ?_⟩
  · rw [decoded]
    exact model_normalized_finite _ _ normal
  · change unpackedValue (decoded32 _) = _
    rw [decoded]
    change unpackedValue (UnpackedFloat.add Format.binary32 (.zero .positive) (decoded32 word)) =
      unpackedValue (decoded32 word)
    cases h : decoded32 word with
    | zero sign => cases sign <;> rfl
    | _ => rfl

theorem add_zero_numeric (word : Binary32) (finite : word.Finite) :
    (word.add Binary32.zero).Finite ∧
      numerical32 (word.add Binary32.zero) = numerical32 word := by
  have valid := model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)
  change ModelNormalized Format.binary32 (decoded32 word) ∧
    ModelFits Format.binary32 (decoded32 word) at valid
  have normal : ModelNormalized Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 word) (.zero .positive)) := by
    cases h : decoded32 word with
    | zero sign => cases sign <;> trivial
    | _ => simp_all [UnpackedFloat.add, ModelNormalized]
  have fits : ModelFits Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 word) (.zero .positive)) := by
    cases h : decoded32 word with
    | zero sign => cases sign <;> trivial
    | _ => simp_all [UnpackedFloat.add, ModelFits]
  have decoded := model_add32_decoded word .zero finite (by decide) normal fits
  refine ⟨(model_decoded32_finite _).mp ?_, ?_⟩
  · rw [decoded]
    exact model_normalized_finite _ _ normal
  · change unpackedValue (decoded32 _) = _
    rw [decoded]
    change unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 word) (.zero .positive)) =
      unpackedValue (decoded32 word)
    cases h : decoded32 word with
    | zero sign => cases sign <;> rfl
    | _ => rfl

/-- Subtracting positive zero preserves every finite numerical value. -/
theorem sub_zero_numeric (word : Binary32) (finite : word.Finite) :
    (word.sub Binary32.zero).Finite ∧
      numerical32 (word.sub Binary32.zero) = numerical32 word := by
  have valid := model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)
  change ModelNormalized Format.binary32 (decoded32 word) ∧
    ModelFits Format.binary32 (decoded32 word) at valid
  have normal : ModelNormalized Format.binary32
      (UnpackedFloat.sub Format.binary32 (decoded32 word) (.zero .positive)) := by
    cases h : decoded32 word with
    | zero sign => cases sign <;> trivial
    | _ => simp_all [UnpackedFloat.sub, ModelNormalized]
  have fits : ModelFits Format.binary32
      (UnpackedFloat.sub Format.binary32 (decoded32 word) (.zero .positive)) := by
    cases h : decoded32 word with
    | zero sign => cases sign <;> trivial
    | _ => simp_all [UnpackedFloat.sub, ModelFits, ModelNormalized]
  have decoded : decoded32 (word.sub .zero) =
      UnpackedFloat.sub Format.binary32 (decoded32 word) (.zero .positive) := by
    change unpack Format.binary32 (pack Format.binary32
      (UnpackedFloat.sub Format.binary32 (Float32.Model.ofBits word.bits).unpack
        (Float32.Model.ofBits 0).unpack)) = _
    rw [model_ofBits32_decoded word finite]
    exact model_unpack_pack_normalized _ _ normal fits
  refine ⟨(model_decoded32_finite _).mp ?_, ?_⟩
  · rw [decoded]
    exact model_normalized_finite _ _ normal
  · change unpackedValue (decoded32 _) = _
    rw [decoded]
    change unpackedValue (UnpackedFloat.sub Format.binary32 (decoded32 word) (.zero .positive)) =
      unpackedValue (decoded32 word)
    cases h : decoded32 word with
    | zero sign => cases sign <;> rfl
    | _ => rfl

/-- Equal finite numerical magnitudes entail identical absolute-value words. -/
theorem abs_word_eq (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (same : |numerical32 left| = |numerical32 right|) : left.abs = right.abs := by
  have le := (numerical32_magnitude_order left right hl hr).mp same.le
  have ge := (numerical32_magnitude_order right left hr hl).mp same.ge
  have equal := Nat.le_antisymm le ge
  exact congrArg Binary32.mk (UInt32.toNat.inj equal)

/-- Retiring the sole active feature changes the actual prediction by exactly
its stored weight magnitude, bit for bit, for arbitrary states and dimensions.
Both zero encodings are included. Every transient reset is owned by
`CurrentLearner.retire_registers`. -/
theorem retirement_disruption_bounded {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension)
    (features : ActiveSet dimension) (singleton : features.indices = [idx]) :
    ((state.predict features).sub ((state.retireIndex idx).predict features)).abs =
      (state.weights.get idx).value.abs := by
  have reset := (CurrentLearner.retire_registers state idx).2.1
  have before : state.predict features = Binary32.zero.add (state.weights.get idx).value := by
    simp [NumericState.predict, NumericState.linearPrediction_eq_sumFrom,
      singleton, Binary32.sumFrom]
  have after : (state.retireIndex idx).predict features = Binary32.zero := by
    simp only [NumericState.predict, NumericState.linearPrediction_eq_sumFrom, singleton,
      List.map_cons, List.map_nil, Binary32.sumFrom, List.foldl_cons, List.foldl_nil, reset]
    rfl
  rw [before, after]
  have weightFinite := (weight_legal (state.weights.get idx)).1
  have add := zero_add_numeric (state.weights.get idx).value weightFinite
  have sub := sub_zero_numeric _ add.1
  exact abs_word_eq _ _ sub.1 weightFinite (congrArg (fun x : ℚ => |x|) (sub.2.trans add.2))

set_option maxRecDepth 8192 in
/-- Every configuration derives the same floor from its closed minimum rate. -/
theorem rail_floor_word {config : Config} (rails : StepSizeRails config) :
    rails.range.lower = (⟨3250074865⟩ : Binary32) := by
  rw [rails.lowerIdentity]
  simp only [Config.etaMin]
  decide

set_option maxRecDepth 8192 in
/-- Every role starts strictly above its floor in the executed binary32 order.
This exhausts the three-role configuration, evaluating the same portable
logarithms and projection as initialization; it does not enumerate streams. -/
theorem initial_above_floor {config : Config} (rails : StepSizeRails config) :
    rails.range.lower.key < rails.initial.value.key := by
  simp only [StepSizeRails.initial, LogStepSize.project, Bounded32.project,
    Interval32.saturate, rails.lowerIdentity, rails.upperIdentity]
  rcases config with ⟨role, rule⟩
  cases role <;> simp only [Config.etaMin, Config.alphaInitial, Config.eta] <;> decide

/-- A re-anchored step size vetoes retirement, independently of its weight. -/
theorem initial_beta_veto {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (feature : FeatIdx dimension)
    (initial : (state.beta.get feature).value = state.rails.initial.value) :
    state.unitIsNegligible feature = false := by
  have above := initial_above_floor state.rails
  have different : state.rails.initial.value.key ≠ state.rails.range.lower.key := by omega
  simp [NumericState.unitIsNegligible, NumericState.unitIsNegligibleUnder,
    NumericState.negligibility, initial, Binary32.numericallyEqual_eq_key, different]

/-- A finite multiplier times positive zero produces one of the two zero
words. Finiteness matters: exceptional multiplication cannot justify this step. -/
theorem mul_zero_words (word : Binary32) (finite : word.Finite) :
    word.mul .zero = .zero ∨ word.mul .zero = ⟨0x80000000⟩ := by
  have admitted := (model_decoded32_finite word).mpr finite
  change Binary32.mk (UInt32.ofBitVec (pack Format.binary32
    (UnpackedFloat.mul Format.binary32 (Float32.Model.ofBits word.bits).unpack
      (.zero .positive)))) = .zero ∨
    Binary32.mk (UInt32.ofBitVec (pack Format.binary32
      (UnpackedFloat.mul Format.binary32 (Float32.Model.ofBits word.bits).unpack
        (.zero .positive)))) = ⟨0x80000000⟩
  rw [model_ofBits32_decoded word finite]
  generalize equation : decoded32 word = unpacked at admitted ⊢
  cases unpacked with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign => cases sign <;> first | exact Or.inl rfl | exact Or.inr rfl
  | finite sign mantissa exponent positive =>
    cases sign <;> first | exact Or.inl rfl | exact Or.inr rfl

set_option maxRecDepth 8192 in
/-- Both zero signs leave the actual initial log word unchanged. This checks
six closed role/zero-sign cases, not input trajectories. -/
theorem initial_add_zero_word {config : Config} (rails : StepSizeRails config)
    (word : Binary32) (zero : word = .zero ∨ word = ⟨0x80000000⟩) :
    rails.initial.value.add word = rails.initial.value := by
  rcases zero with rfl | rfl
  all_goals
    simp only [StepSizeRails.initial, LogStepSize.project, Bounded32.project,
      Interval32.saturate, rails.lowerIdentity, rails.upperIdentity]
    rcases config with ⟨role, rule⟩
    cases role <;> simp only [Config.etaMin, Config.alphaInitial, Config.eta] <;> decide

/-- A zero meta-gradient preserves initial beta through a credited first-loop
visit, including its clipping branch, when the pre-zero multiplier is finite.
The explicit regularity premise cannot be dropped for raw machine inputs. -/
theorem initial_zero_meta_first {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32)
    (cold : state.beta.get idx = state.rails.initial)
    (zeroMeta : (state.transient.p.get idx).value = .zero)
    (regular : ((config.metaStep.div state.rails.initial.alpha).mul
      (delta.sub vDelta)).Finite) :
    ((state.firstLoopElement idx delta vDelta decay).1.beta.get idx).value =
      state.rails.initial.value := by
  have product := mul_zero_words _ regular
  have unchanged := initial_add_zero_word state.rails _ product
  simp only [CurrentLearner.vector_get] at cold zeroMeta
  simp only [NumericState.firstLoopElement, CurrentLearner.vector_get,
    Vector.getElem_set_self, cold, zeroMeta, ite_self]
  rw [unchanged]
  exact state.rails.range.saturate_identity _ state.rails.initial.legal

/-- Without overshoot, the entire executed second loop preserves every beta,
including active slots. Exposure alone is not a step-size decrement. -/
theorem second_loop_beta_fixed {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (features : ActiveSet dimension) (vDelta : Binary32)
    (noOvershoot : config.eta.less (Binary32.sumMap .zero features.indices
      (fun idx => (state.beta.get idx).alpha)) = false) (idx : FeatIdx dimension) :
    ((state.learnSecondLoop config features vDelta).1.beta.get idx).value =
      (state.beta.get idx).value := by
  have fold (indices : List (FeatIdx dimension)) (current : NumericState config dimension)
      (vd denominator total : Binary32) :
      ((indices.foldl (fun (s, acc) feature =>
        NumericState.secondLoopElement config false denominator total s acc feature)
          (current, vd)).1.beta.get idx).value = (current.beta.get idx).value := by
    induction indices generalizing current vd with
    | nil => rfl
    | cons feature rest ih =>
      dsimp only [List.foldl_cons]
      rw [ih]
      rfl
  unfold NumericState.learnSecondLoop
  dsimp only
  rw [noOvershoot]
  exact fold _ _ _ _ _

/-- Operational anchor contract for the current second-loop element. The incoming
`h` and `hTemp` must name the same retained sensitivity. Every arithmetic operation
on the right is binary32 in execution order; in particular no distributivity or
zero-product simplification is assumed for the unconstrained intermediate words.
This is a local conditional identity, not construction of a learning path. -/
theorem episode_sensitivity_anchor {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension) (sensitivity : Binary32)
    (finite : sensitivity.Finite)
    (zeroP : (state.transient.p.get idx).value = .zero)
    (zeroZ : (state.transient.z.get idx).value = .zero)
    (zeroZBar : (state.transient.zBar.get idx).value = .zero)
    (zeroOld : (state.transient.hOld.get idx).value = .zero)
    (alignedH : (state.transient.h.get idx).value = sensitivity)
    (alignedTemp : (state.transient.hTemp.get idx).value = sensitivity) :
    let zd := (config.eta.div config.eta).mul (state.beta.get idx).alpha
    let z := Binary32.zero.add (zd.mul (Binary32.one.sub .zero))
    let next := (NumericState.secondLoopElement config false config.eta .zero state .zero idx).1
    next.beta = state.beta ∧
      (next.transient.p.get idx).value.Finite ∧
      numerical32 (next.transient.p.get idx).value = numerical32 sensitivity ∧
      (next.transient.z.get idx).value = z ∧
      (next.transient.zBar.get idx).value =
        Binary32.zero.add (zd.mul ((Binary32.one.sub .zero).sub .zero)) ∧
      (next.transient.hTemp.get idx).value =
        (sensitivity.sub (Binary32.zero.mul (z.sub zd))).sub (sensitivity.mul zd) := by
  have added := zero_add_numeric sensitivity finite
  simp only [CurrentLearner.vector_get] at zeroP zeroZ zeroZBar zeroOld alignedH alignedTemp
  simp only [NumericState.secondLoopElement, Bool.false_eq_true, if_false,
    CurrentLearner.vector_get, Vector.getElem_set_self, zeroP, zeroZ, zeroZBar,
    zeroOld, alignedH, alignedTemp]
  simpa only [true_and, and_true] using added

/-- Initial step sizes and absent meta-gradient, without restrictions on weights
or the other trace registers. This is a transient exposure invariant. -/
def ColdMeta {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) : Prop :=
  ∀ idx, (state.beta.get idx).value = state.rails.initial.value ∧
    (state.transient.p.get idx).value = .zero

private theorem beta_of_value {config : Config} (rails : StepSizeRails config)
    (beta : LogStepSize rails) (same : beta.value = rails.initial.value) :
    beta = rails.initial := by
  have injective {range : Interval32} (left right : Bounded32 range)
      (value : left.value = right.value) : left = right := by
    cases left
    cases right
    cases value
    rfl
  exact injective _ _ same

/-- Clearing one slot preserves the exposure invariant without changing beta. -/
theorem cold_meta_clear {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (cold : ColdMeta state) (idx : FeatIdx dimension) :
    ColdMeta (state.clearFeatureRegisters idx) := by
  intro other
  have entry := cold other
  simp only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha, CurrentLearner.vector_get, Vector.getElem_set]
  constructor
  · exact entry.1
  · split <;> first | rfl | exact entry.2

/-- One credited visit with a finite pre-meta product cannot mature a cold
meta-gradient. A positive finite trajectory decay preserves its exact zero. -/
theorem cold_meta_first {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (cold : ColdMeta state) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) (zeroDecay : Binary32.zero.mul decay = .zero)
    (regular : ((config.metaStep.div state.rails.initial.alpha).mul
      (delta.sub vDelta)).Finite) : ColdMeta (state.firstLoopElement idx delta vDelta decay).1 := by
  intro other
  by_cases same : idx = other
  · subst other
    have entry := cold idx
    have beta := initial_zero_meta_first state idx delta vDelta decay
      (beta_of_value _ _ entry.1) entry.2 regular
    refine ⟨beta, ?_⟩
    simp only [CurrentLearner.vector_get] at entry
    simp only [NumericState.firstLoopElement, CurrentLearner.vector_get,
      Vector.getElem_set_self, entry.2, ite_self, zeroDecay]
  · have frame := CurrentLearner.first_element_frame state idx other same delta vDelta decay
    have metaWord := congrArg (fun words : Vector Binary32 9 => words[8]) frame.2.2
    change ((state.firstLoopElement idx delta vDelta decay).1.transient.p.get other).value =
      (state.transient.p.get other).value at metaWord
    exact ⟨frame.2.1.trans (cold other).1, metaWord.trans (cold other).2⟩

/-- Register clearing preserves the receiver object by construction. -/
theorem clear_feature_rails {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension) :
    (state.clearFeatureRegisters idx).rails = state.rails := by
  simp only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
    NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
    NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
    NumericState.writeLastAlpha]

/-- A first-loop element never reconstructs or replaces its receiver object. -/
theorem first_element_rails {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta vDelta decay : Binary32) :
    (state.firstLoopElement idx delta vDelta decay).1.rails = state.rails := rfl

/-- The executed first-loop worklist preserves a cold meta-gradient even
through pruning and repeated indices. Regularity refers to the fixed receiver,
so the induction uses rail preservation rather than reevaluating its recipe. -/
theorem cold_meta_first_go {config : Config} {dimension : Dimension}
    (rails : StepSizeRails config) (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vDelta decay : Binary32)
    (zeroDecay : Binary32.zero.mul decay = .zero)
    (regular : ((config.metaStep.div rails.initial.alpha).mul (delta.sub vDelta)).Finite)
    (cold : ColdMeta state) (sameRails : state.rails = rails) :
    ColdMeta (NumericState.learnFirstLoopGo config delta vDelta decay state work pos) := by
  induction state, work, pos using
      NumericState.learnFirstLoopGo.induct config delta vDelta decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    have stateRegular : ((config.metaStep.div state.rails.initial.alpha).mul
        (delta.sub vDelta)).Finite := by rw [sameRails]; exact regular
    have nextCold : ColdMeta next := by
      simpa only [equation] using
        cold_meta_first state cold work[pos] delta vDelta decay zeroDecay stateRegular
    have nextRails : next.rails = rails := by
      have preserved := first_element_rails state work[pos] delta vDelta decay
      rw [equation] at preserved
      exact preserved.trans sameRails
    have clearedRails : (next.clearFeatureRegisters work[pos]).rails = rails :=
      (clear_feature_rails next work[pos]).trans nextRails
    have result := ih (cold_meta_clear next nextCold work[pos]) clearedRails
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, ite_true] using result
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    have stateRegular : ((config.metaStep.div state.rails.initial.alpha).mul
        (delta.sub vDelta)).Finite := by rw [sameRails]; exact regular
    have nextCold : ColdMeta next := by
      simpa only [equation] using
        cold_meta_first state cold work[pos] delta vDelta decay zeroDecay stateRegular
    have nextRails : next.rails = rails := by
      have preserved := first_element_rails state work[pos] delta vDelta decay
      rw [equation] at preserved
      exact preserved.trans sameRails
    have result := ih nextCold nextRails
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, if_neg noPrune] using result
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo, dif_neg finished]
    exact cold

/-- Crediting a cold meta-gradient leaves initial beta fixed, even while
weights and other registers learn. This uses the actual pruning traversal. -/
theorem cold_meta_first_loop {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (delta vDelta decay : Binary32)
    (cold : ColdMeta state) (zeroDecay : Binary32.zero.mul decay = .zero)
    (regular : ((config.metaStep.div state.rails.initial.alpha).mul
      (delta.sub vDelta)).Finite) : ColdMeta (state.learnFirstLoop config delta vDelta decay) :=
  cold_meta_first_go state.rails _ _ _ _ _ _ zeroDecay regular cold rfl

/-- Ordered small-word sums retain a linear envelope with explicit rounding
slack. The induction covers arbitrary values and lengths within its bound. -/
private theorem small_sum (count : Nat) (initial : Binary32) (values : List Binary32)
    (small : count + values.length ≤ 1900) (finite : initial.Finite)
    (start : |numerical32 initial| ≤ count / (19000 : ℚ))
    (bounds : ∀ word ∈ values, word.Finite ∧ |numerical32 word| ≤ 1 / (19990 : ℚ)) :
    (Binary32.sumFrom initial values).Finite ∧
      |numerical32 (Binary32.sumFrom initial values)| ≤
        (count + values.length) / (19000 : ℚ) := by
  induction values generalizing count initial with
  | nil => simpa [Binary32.sumFrom] using And.intro finite start
  | cons word rest ih =>
    have current := bounds word (by simp)
    have countBound : (count : ℚ) ≤ 1900 := by exact_mod_cast (show count ≤ 1900 by omega)
    have triangle := abs_add_le (numerical32 initial) (numerical32 word)
    have operation := CurrentPrediction.binary32_add_finite_strict_error initial word
      finite current.1 0 (by decide) (by norm_num; linarith only [triangle, start,
        current.2, countBound])
    have error : |numerical32 (initial.add word) -
        (numerical32 initial + numerical32 word)| ≤ 1 / (33554432 : ℚ) := by
      convert operation.2 using 1
      norm_num
    have next : |numerical32 (initial.add word)| ≤ (count + 1) / (19000 : ℚ) := by
      have roundTriangle := abs_add_le
        (numerical32 (initial.add word) - (numerical32 initial + numerical32 word))
        (numerical32 initial + numerical32 word)
      rw [sub_add_cancel] at roundTriangle
      linarith only [roundTriangle, error, triangle, start, current.2]
    have result := ih (count + 1) (initial.add word)
      (by simp only [List.length_cons] at small; omega)
      operation.1 (by simpa using next) (fun value member => bounds value (by simp [member]))
    simpa [Binary32.sumFrom, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using result

set_option maxRecDepth 8192 in
/-- The current demon role's initialized portable alpha is below 1/19990.
Only its fixed log/exp recipe is reduced; feature sets and streams stay symbolic. -/
theorem initial_demon_alpha_small (rule : ValueRule) (rails : StepSizeRails ⟨.demon, rule⟩) :
    rails.initial.alpha.Finite ∧ |numerical32 rails.initial.alpha| ≤ 1 / (19990 : ℚ) := by
  have numeric := CurrentLearnerArithmetic.alpha_numeric rails.initial
  have raw : rails.initial.alpha.bits.toNat ≤ 0x3851c000 := by
    simp only [LogStepSize.alpha, StepSizeRails.initial, LogStepSize.project, Bounded32.project,
      Interval32.saturate, rails.lowerIdentity, rails.upperIdentity, Config.etaMin,
      Config.alphaInitial, Config.eta]
    decide
  have magnitude : rails.initial.alpha.magnitude ≤ (Binary32.mk 0x3851c000).magnitude :=
    Nat.le_trans Nat.and_le_left raw
  have bound := (numerical32_magnitude_order rails.initial.alpha
    (Binary32.mk 0x3851c000) numeric.1 (by decide)).mpr magnitude
  have value : numerical32 (Binary32.mk 0x3851c000) = 13746176 / (274877906944 : ℚ) := by
    change (1 : ℚ) * 13746176 * 2 ^ (-38 : Int) = _
    norm_num
  refine ⟨numeric.1, le_trans bound ?_⟩
  rw [value]
  norm_num

/-- A cold-beta demon cannot overshoot on at most 1900 active slots. This
derived exposure condition uses the actual ordered sum, not real reassociation. -/
theorem initial_demon_no_overshoot {dimension : Dimension} (rule : ValueRule)
    (state : NumericState ⟨.demon, rule⟩ dimension) (features : ActiveSet dimension)
    (cold : ∀ idx, state.beta.get idx = state.rails.initial)
    (sparse : features.indices.length ≤ 1900) :
    (Config.mk .demon rule).eta.less (Binary32.sumMap .zero features.indices
      (fun idx => (state.beta.get idx).alpha)) = false := by
  have alpha := initial_demon_alpha_small rule state.rails
  have sum := small_sum 0 .zero (features.indices.map fun idx => (state.beta.get idx).alpha)
    (by simpa using sparse) (by decide) (by change |(0 : ℚ)| ≤ 0 / (19000 : ℚ); norm_num) (by
      intro word member
      obtain ⟨idx, _, rfl⟩ := List.mem_map.mp member
      simpa only [cold] using alpha)
  rw [Binary32.sumMap_eq]
  rw [numerical32_less _ _ (CurrentLearnerArithmetic.eta_numeric _).1 sum.1,
    decide_eq_false_iff_not]
  have countBound : (features.indices.length : ℚ) ≤ 1900 := by exact_mod_cast sparse
  have upper := le_trans (le_abs_self _) sum.2
  have eta : (1 : ℚ) / 10 ≤ numerical32 (Config.mk .demon rule).eta := by
    simp only [Config.eta]
    change (1 : ℚ) / 10 ≤ unpackedValue (.finite .positive 13421773 (-27) (by decide))
    norm_num [unpackedValue, signCoefficient]
  simp only [List.length_map, Nat.cast_zero, zero_add] at upper
  linarith only [upper, countBound, eta]

/-- A second-loop visit cannot create a meta-gradient from zero `p` and `h`.
With no overshoot it also preserves the initial beta. Other registers may change. -/
theorem cold_meta_second_element {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (cold : ColdMeta state)
    (zeroH : ∀ idx, (state.transient.h.get idx).value = .zero)
    (e t vd : Binary32) (idx : FeatIdx dimension) :
    let next := (NumericState.secondLoopElement config false e t state vd idx).1
    ColdMeta next ∧ ∀ other, (next.transient.h.get other).value = .zero := by
  constructor
  · intro other
    constructor
    · exact (cold other).1
    · have entry := (cold other).2
      simp only [CurrentLearner.vector_get] at entry zeroH
      simp only [NumericState.secondLoopElement, Bool.false_eq_true, if_false,
        CurrentLearner.vector_get, Vector.getElem_set]
      split
      · rename_i same
        have equal : idx = other := Fin.ext same
        subst other
        simp only [entry, zeroH]
        rfl
      · exact entry
  · exact zeroH

/-- The second-loop fold retains this invariant on every feature list. -/
theorem cold_meta_second_loop {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (features : ActiveSet dimension) (vd : Binary32)
    (cold : ColdMeta state) (zeroH : ∀ idx, (state.transient.h.get idx).value = .zero)
    (noOvershoot : config.eta.less (Binary32.sumMap .zero features.indices
      (fun idx => (state.beta.get idx).alpha)) = false) :
    ColdMeta (state.learnSecondLoop config features vd).1 ∧
      ∀ idx, ((state.learnSecondLoop config features vd).1.transient.h.get idx).value = .zero := by
  have fold (indices : List (FeatIdx dimension)) (current : NumericState config dimension)
      (acc e t : Binary32) (hc : ColdMeta current)
      (hh : ∀ idx, (current.transient.h.get idx).value = .zero) :
      let next := (indices.foldl (fun (s, v) idx =>
        NumericState.secondLoopElement config false e t s v idx) (current, acc)).1
      ColdMeta next ∧ ∀ idx, (next.transient.h.get idx).value = .zero := by
    induction indices generalizing current acc with
    | nil => exact ⟨hc, hh⟩
    | cons idx rest ih =>
      have next := cold_meta_second_element current hc hh e t acc idx
      exact ih _ _ next.1 next.2
  unfold NumericState.learnSecondLoop
  dsimp only
  rw [noOvershoot]
  exact fold _ _ _ _ _ cold zeroH

/-- A sufficiently sparse initiation leaves every demon beta at its initial
word and its meta-gradient zero, regardless of the stored learned weights. -/
theorem short_begin_cold {dimension : Dimension} (rule : ValueRule)
    (state : NumericState ⟨.demon, rule⟩ dimension) (features : ActiveSet dimension)
    (cold : ∀ idx, (state.beta.get idx).value = state.rails.initial.value)
    (sparse : features.indices.length ≤ 1900) :
    ColdMeta (state.beginTrajectory ⟨.demon, rule⟩ features) := by
  have clearCold : ColdMeta state.clearTransient := by
    intro idx
    exact ⟨cold idx, by simp [NumericState.clearTransient, TransientState.zero, Vector.get]⟩
  have clearH : ∀ idx, (state.clearTransient.transient.h.get idx).value = .zero := by
    simp [NumericState.clearTransient, TransientState.zero, Vector.get]
  have noOvershoot := initial_demon_no_overshoot rule state.clearTransient features
    (fun idx => beta_of_value _ _ (cold idx)) sparse
  exact (cold_meta_second_loop state.clearTransient features .zero
    clearCold clearH noOvershoot).1

/-- Closing a trajectory before a nonzero meta-gradient has been assembled
preserves initial beta through the actual terminal credit and transient clear. -/
theorem short_terminal_cold {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (target : Binary32) (cold : ColdMeta state)
    (zeroDecay : Binary32.zero.mul (config.rule.gamma.mul config.lambda) = .zero)
    (regular : ((config.metaStep.div state.rails.initial.alpha).mul
      ((target.sub state.transient.vOld).sub state.transient.vDelta)).Finite) :
    ColdMeta (state.terminalStep config target).1 := by
  have result := cold_meta_first_loop state (target.sub state.transient.vOld)
    state.transient.vDelta (config.rule.gamma.mul config.lambda) cold zeroDecay regular
  intro idx
  exact ⟨(result idx).1, by simp [NumericState.terminalStep, NumericState.clearTransient,
    TransientState.zero, Vector.get]⟩

/-- Initiation's accumulator is zero: every second-loop contribution reads
`deltaWeight` from the just-cleared trajectory, and that loop never writes it. -/
theorem begin_accumulator_zero {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (features : ActiveSet dimension) :
    (state.beginTrajectory config features).transient.vDelta = .zero := by
  have fold (indices : List (FeatIdx dimension)) (current : NumericState config dimension)
      (acc e t : Binary32) (overshoot : Bool)
      (known : ∀ idx, (current.transient.deltaWeight.get idx).value = .zero)
      (zero : acc = .zero) :
      (indices.foldl (fun (s, v) idx =>
        NumericState.secondLoopElement config overshoot e t s v idx) (current, acc)).2 =
        Binary32.zero := by
    induction indices generalizing current acc with
    | nil => exact zero
    | cons idx rest ih =>
      apply ih
      · exact known
      · rw [known, zero]
        rfl
  unfold NumericState.beginTrajectory NumericState.learnSecondLoop
  dsimp only
  apply fold
  · simp [NumericState.clearTransient, TransientState.zero, Vector.get]
  · rfl

/-- The trajectory anchor is the current prediction before any terminal
learning; starting traces neither projects nor replaces that machine sum. -/
theorem begin_anchor {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (features : ActiveSet dimension) :
    (state.beginTrajectory config features).transient.vOld = state.predict features := rfl

/-- Subtraction in the universal prediction envelope cannot overflow.
The loose doubled output bound is sufficient for the following meta product. -/
theorem prediction_difference_finite (left right : Binary32)
    (hl : left.Finite) (hr : right.Finite)
    (bl : |numerical32 left| ≤ 4294967296) (br : |numerical32 right| ≤ 4294967296) :
    (left.sub right).Finite ∧ |numerical32 (left.sub right)| ≤ 17179869184 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have bound : |numerical32 left - numerical32 right| ≤ (2 : ℚ) ^ (33 : Int) := by
    have triangle := abs_sub_le (numerical32 left) 0 (numerical32 right)
    norm_num at triangle ⊢
    linarith only [triangle, bl, br]
  have operation := CurrentOperations.model_sub_dyadic_local Format.binary32
    (decoded32 left) (decoded32 right) ln rn 33 bound
  have error : |unpackedValue (UnpackedFloat.sub Format.binary32
      (decoded32 left) (decoded32 right)) - (numerical32 left - numerical32 right)| ≤ 512 := by
    convert operation.2 using 1 <;>
      norm_num [numerical32, Format.mantissaBits, Format.minExponent]
  have output : |unpackedValue (UnpackedFloat.sub Format.binary32
      (decoded32 left) (decoded32 right))| ≤ 17179869184 := by
    have triangle := abs_add_le
      (unpackedValue (UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right)) -
        (numerical32 left - numerical32 right)) (numerical32 left - numerical32 right)
    rw [sub_add_cancel] at triangle
    norm_num at bound
    linarith only [triangle, error, bound]
  have fits := model_fits_of_value_bound Format.binary32 _
    (model_normalized_finite _ _ operation.1) 34 (by decide) (by norm_num; exact output)
  have decoded : decoded32 (left.sub right) =
      UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right) := by
    change unpack Format.binary32 (pack Format.binary32
      (UnpackedFloat.sub Format.binary32 (Float32.Model.ofBits left.bits).unpack
        (Float32.Model.ofBits right.bits).unpack)) = _
    rw [model_ofBits32_decoded left hl, model_ofBits32_decoded right hr]
    exact model_unpack_pack_normalized _ _ operation.1 fits
  constructor
  · rw [← model_decoded32_finite, decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using output

set_option maxRecDepth 8192 in
/-- The current demon's initial meta multiplier is finite and at most 32.
This evaluates only the single fixed role recipe, under arbitrary value rules. -/
theorem initial_demon_meta_bound (rule : ValueRule) (rails : StepSizeRails ⟨.demon, rule⟩) :
    ((Config.mk .demon rule).metaStep.div rails.initial.alpha).Finite ∧
      |numerical32 ((Config.mk .demon rule).metaStep.div rails.initial.alpha)| ≤ 32 := by
  let scale := (Config.mk .demon rule).metaStep.div rails.initial.alpha
  have raw : scale.Finite ∧ scale.magnitude ≤ (Binary32.mk 0x42000000).magnitude := by
    simp only [scale, LogStepSize.alpha, StepSizeRails.initial, LogStepSize.project,
      Bounded32.project, Interval32.saturate, rails.lowerIdentity, rails.upperIdentity,
      Config.etaMin, Config.alphaInitial, Config.eta, Config.metaStep]
    decide
  have bound := (numerical32_magnitude_order scale (Binary32.mk 0x42000000)
    raw.1 (by decide)).mpr raw.2
  have value : numerical32 (Binary32.mk 0x42000000) = 32 := by
    change (1 : ℚ) * 8388608 * 2 ^ (-18 : Int) = _
    norm_num
  exact ⟨raw.1, by simpa [value] using bound⟩

/-- A bounded terminal error times the actual initial meta multiplier is
finite. This closes the pre-zero arithmetic obligation without assuming a
bounded transient state after arbitrary long learning. -/
theorem initial_demon_meta_finite (rule : ValueRule) (rails : StepSizeRails ⟨.demon, rule⟩)
    (error : Binary32) (finite : error.Finite) (bound : |numerical32 error| ≤ 17179869184) :
    (((Config.mk .demon rule).metaStep.div rails.initial.alpha).mul error).Finite := by
  let scale := (Config.mk .demon rule).metaStep.div rails.initial.alpha
  have known := initial_demon_meta_bound rule rails
  have sn := (model_unpack_format Format.binary32 (by decide) scale.bits.toBitVec
    ((model_decoded32_finite scale).mpr known.1)).1
  have en := (model_unpack_format Format.binary32 (by decide) error.bits.toBitVec
    ((model_decoded32_finite error).mpr finite)).1
  have product : |numerical32 scale * numerical32 error| ≤ (2 : ℚ) ^ (40 : Int) := by
    rw [abs_mul]
    have result := mul_le_mul known.2 bound (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 32)
    norm_num
    linarith only [result]
  have operation := model_mul_dyadic_local Format.binary32 (decoded32 scale) (decoded32 error)
    sn en 40 product
  have roundBound : |unpackedValue (UnpackedFloat.mul Format.binary32
      (decoded32 scale) (decoded32 error)) - numerical32 scale * numerical32 error| ≤ 65536 := by
    convert operation.2 using 1 <;>
      norm_num [numerical32, Format.mantissaBits, Format.minExponent]
  have fits := model_fits_of_value_bound Format.binary32 _
    (model_normalized_finite _ _ operation.1) 41 (by decide) (by
      have triangle := abs_add_le
        (unpackedValue (UnpackedFloat.mul Format.binary32 (decoded32 scale) (decoded32 error)) -
          numerical32 scale * numerical32 error) (numerical32 scale * numerical32 error)
      rw [sub_add_cancel] at triangle
      change |numerical32 scale * numerical32 error| ≤ 1099511627776 at product
      change |unpackedValue (UnpackedFloat.mul Format.binary32
        (decoded32 scale) (decoded32 error))| ≤ 2199023255552
      linarith only [triangle, roundBound, product])
  have decoded := CurrentLearnerArithmetic.mul32_decoded scale error known.1 finite
    operation.1 fits
  apply (model_decoded32_finite _).mp
  rw [decoded]
  exact model_normalized_finite _ _ operation.1

/-- Every current trajectory decay preserves the positive zero word.
This is the closed role/criterion domain, not an assumption about raw caller decay. -/
theorem trajectory_zero_decay (config : Config) :
    Binary32.zero.mul (config.rule.gamma.mul config.lambda) = .zero := by
  rcases config with ⟨role, rule⟩
  cases rule with
  | discounted discount =>
    cases role <;> cases discount <;>
      simp only [Config.lambda, ValueRule.gamma, Discount.gamma] <;> decide
  | differential =>
    cases role <;> simp only [Config.lambda, ValueRule.gamma] <;> decide

/-- A begin/terminal trajectory has no meta-adaptation, for every sparse
feature set, every previously learned weight array, and every finite terminal
target within the universal prediction envelope. These are input conditions,
not a premise that the retirement guard holds or fails. -/
theorem one_action_trajectory_cold {dimension : Dimension} (rule : ValueRule)
    (state : NumericState ⟨.demon, rule⟩ dimension) (features : ActiveSet dimension)
    (target : Binary32) (finite : target.Finite) (bound : |numerical32 target| ≤ 4294967296)
    (cold : ∀ idx, (state.beta.get idx).value = state.rails.initial.value)
    (sparse : features.indices.length ≤ 1900) :
    ColdMeta ((state.beginTrajectory ⟨.demon, rule⟩ features).terminalStep
      ⟨.demon, rule⟩ target).1 := by
  have prediction := CurrentLearner.prediction_bound state features
  have predictionBound : |numerical32 (state.predict features)| ≤ 4294967296 := by
    apply le_trans prediction.2
    have count := Nat.min_le_right features.indices.length (2 ^ 24)
    have lifted : ((min features.indices.length (2 ^ 24) : Nat) : ℚ) ≤ 16777216 := by
      exact_mod_cast count
    unfold CurrentPrediction.predictionRadius
    linarith only [lifted]
  have difference := prediction_difference_finite target (state.predict features)
    finite prediction.1 bound predictionBound
  have zero := sub_zero_numeric _ difference.1
  have regular := initial_demon_meta_finite rule
    (state.beginTrajectory ⟨.demon, rule⟩ features).rails
    ((target.sub (state.predict features)).sub .zero) zero.1 (by rw [zero.2]; exact difference.2)
  apply short_terminal_cold _ target (short_begin_cold rule state features cold sparse)
    (trajectory_zero_decay _)
  simpa only [begin_anchor, begin_accumulator_zero] using regular

/-- The derived floor has exact finite signed components; this closed
identity is checked against the portable logarithm that constructs the rails. -/
theorem rail_floor_decoded {config : Config} (rails : StepSizeRails config) :
    decoded32 rails.range.lower =
      .finite .negative 12072177 (-19) (by decide) := by
  rw [rail_floor_word]
  rfl

/-- Adding any finite nonpositive operand to the rail floor preserves its
negative upper bound in the actual unpacked operation, before overflow packing. -/
theorem floor_add_unpacked {config : Config} (rails : StepSizeRails config)
    (right : UnpackedFloat) (finite : ModelNormalized Format.binary32 right)
    (nonpositive : unpackedValue right ≤ 0) :
    ModelNormalized Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 rails.range.lower) right) ∧
    unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 rails.range.lower) right) ≤
      -(12072177 : ℚ) * 2 ^ (-19 : Int) := by
  rw [rail_floor_decoded]
  cases right with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    constructor
    · change ModelNormalized Format.binary32 (.finite .negative 12072177 (-19) (by decide))
      norm_num [ModelNormalized, Format.minExponent, Format.mantissaBits]
    · change (-1 : ℚ) * (12072177 : Nat) * 2 ^ (-19 : Int) ≤ _
      norm_num
  | finite sign mantissa exponent positive =>
    let target := min (-19 : Int) exponent
    let leftMantissa := (decreaseExponent 12072177 (-19) target).1
    let rightMantissa := (decreaseExponent mantissa exponent target).1
    let sum := Sign.negative.apply leftMantissa + sign.apply rightMantissa
    have left := model_decrease_dyadic_value .negative 12072177 (-19) target
      (Int.min_le_left _ _)
    have right := model_decrease_dyadic_value sign mantissa exponent target
      (Int.min_le_right _ _)
    have exactSum : (sum : ℚ) * 2 ^ target =
        -(12072177 : ℚ) * 2 ^ (-19 : Int) +
          unpackedValue (.finite sign mantissa exponent positive) := by
      change ((Sign.negative.apply leftMantissa + sign.apply rightMantissa : Int) : ℚ) *
        2 ^ target = _
      rw [Int.cast_add, add_mul, left, right]
      simp only [signCoefficient, neg_one_mul, unpackedValue, Nat.cast_ofNat]
    exact CurrentRetirementRounding.normalize_negative_bound sum target 12072177 (-19)
      (by decide) (by decide) (by decide) (by
        rw [exactSum]
        norm_num only [Nat.cast_ofNat]
        linarith only [nonpositive])

/-- Packing a normalized value below the negative rail retains the order
bound. Negative overflow selects negative infinity, which is still below it. -/
theorem packed_floor_key {config : Config} (rails : StepSizeRails config)
    (value : UnpackedFloat) (normal : ModelNormalized Format.binary32 value)
    (bound : unpackedValue value ≤ -(12072177 : ℚ) * 2 ^ (-19 : Int)) :
    (⟨UInt32.ofBitVec (pack Format.binary32 value)⟩ : Binary32).key ≤
      rails.range.lower.key := by
  cases value with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign => norm_num [unpackedValue] at bound
  | finite sign mantissa exponent positive =>
    have negative : sign = .negative := by
      cases sign with
      | negative => rfl
      | positive =>
        have valuePositive : (0 : ℚ) < (mantissa : ℚ) * 2 ^ exponent := by positivity
        norm_num [unpackedValue, signCoefficient] at bound
        linarith only [bound, valuePositive]
    subst sign
    by_cases overflow : 2 ^ Format.binary32.exponentBits ≤
        (exponent + Format.binary32.exponentBias +
          Format.binary32.mantissaBitsWithoutImplicit).toNat + 1
    · rw [pack, if_pos overflow, rail_floor_word]
      decide
    · have fits : ModelFits Format.binary32
          (.finite .negative mantissa exponent positive) := by
        simpa only [ModelFits] using Nat.lt_of_not_ge overflow
      have decoded : decoded32
          (⟨UInt32.ofBitVec (pack Format.binary32
            (.finite .negative mantissa exponent positive))⟩ : Binary32) =
          .finite .negative mantissa exponent positive :=
        model_unpack_pack_normalized _ _ normal fits
      have finite := (model_decoded32_finite _).mp
        (decoded ▸ model_normalized_finite _ _ normal)
      apply (numerical32_order _ rails.range.lower finite rails.range.lowerFinite).mp
      change unpackedValue (decoded32 _) ≤ unpackedValue (decoded32 rails.range.lower)
      rw [decoded, rail_floor_decoded]
      simpa only [unpackedValue, signCoefficient, neg_one_mul, Nat.cast_ofNat] using bound

/-- Actual binary32 floor addition cannot rise above the floor for any finite
nonpositive delta; negative overflow is included. -/
theorem floor_add_key {config : Config} (rails : StepSizeRails config)
    (delta : Binary32) (finite : delta.Finite) (nonpositive : delta.key ≤ 0) :
    (rails.range.lower.add delta).key ≤ rails.range.lower.key := by
  have normal := (model_unpack_format Format.binary32 (by decide) delta.bits.toBitVec
    ((model_decoded32_finite delta).mpr finite)).1
  have order : numerical32 delta ≤ 0 :=
    (numerical32_order delta .zero finite (by decide)).mpr nonpositive
  have operation := floor_add_unpacked rails (decoded32 delta) normal order
  change (⟨UInt32.ofBitVec (pack Format.binary32
    (UnpackedFloat.add Format.binary32 (Float32.Model.ofBits rails.range.lower.bits).unpack
      (Float32.Model.ofBits delta.bits).unpack))⟩ : Binary32).key ≤ _
  rw [model_ofBits32_decoded rails.range.lower rails.range.lowerFinite,
    model_ofBits32_decoded delta finite]
  exact packed_floor_key rails _ operation.1 operation.2

/-- Saturation of any raw word at or below the lower endpoint has precisely
the lower endpoint's key; NaN also selects that endpoint by construction. -/
theorem saturation_floor_key (range : Interval32) (raw : Binary32)
    (bound : raw.key ≤ range.lower.key) :
    (range.saturate raw).key = range.lower.key := by
  have lowerNaN := Binary32.finite_not_nan range.lower range.lowerFinite
  have upperNaN := Binary32.finite_not_nan range.upper range.upperFinite
  by_cases nan : raw.isNaN = true
  · simp [Interval32.saturate, Binary32.saturate, nan]
  · have notNaN : raw.isNaN = false := Bool.eq_false_iff.mpr nan
    by_cases below : raw.key < range.lower.key
    · simp [Interval32.saturate, Binary32.saturate, Binary32.less_eq_key, notNaN,
        lowerNaN, below]
    · have equal : raw.key = range.lower.key := by omega
      simp [Interval32.saturate, Binary32.saturate, Binary32.less_eq_key, notNaN,
        lowerNaN, upperNaN, equal, not_lt_of_ge range.ordered]

/-- Every finite nonpositive meta-update from the rail floor projects back
onto that floor under the actual log-step-size admission function. -/
theorem downward_projection_floor {config : Config} (rails : StepSizeRails config)
    (delta : Binary32) (finite : delta.Finite) (nonpositive : delta.key ≤ 0) :
    (LogStepSize.project rails (rails.range.lower.add delta)).value.numericallyEqual
      rails.range.lower = true := by
  have equal := saturation_floor_key rails.range (rails.range.lower.add delta)
    (floor_add_key rails delta finite nonpositive)
  have legal := (LogStepSize.project rails (rails.range.lower.add delta)).legal.1
  rw [CurrentLearner.finite_equal _ _ legal rails.range.lowerFinite]
  exact decide_eq_true equal

/-- The negative nonzero floor key determines exactly one raw encoding. -/
theorem floor_key_unique {config : Config} (rails : StepSizeRails config) (word : Binary32)
    (equal : word.key = rails.range.lower.key) : word = rails.range.lower := by
  rw [rail_floor_word] at equal ⊢
  change (if word.negative then -(word.magnitude : Int) else word.magnitude) = -1102591217 at equal
  have negative : word.negative = true := by
    by_contra no
    rw [if_neg no] at equal
    omega
  have magnitude : word.magnitude = 1102591217 := by
    rw [if_pos negative] at equal
    omega
  have notZero : word.bits.toNat / 2 ^ 31 ≠ 0 := by
    intro zero
    have bitsZero : word.bits &&& 0x80000000 = 0 := by
      apply UInt32.toNat.inj
      rw [word32_sign_exact, zero, Nat.zero_mul]
      rfl
    simp [Binary32.negative, bitsZero] at negative
  have modulo : word.bits.toNat % 2 ^ 31 = 1102591217 := by
    change word.bits.toNat &&& (2 ^ 31 - 1) = _ at magnitude
    rwa [Nat.and_two_pow_sub_one_eq_mod] at magnitude
  have bound := word.bits.toNat_lt
  have bits : word.bits.toNat = 3250074865 := by omega
  exact congrArg Binary32.mk (UInt32.toNat.inj bits)

/-- The projected beta retains the exact floor word after every finite
nonpositive delta, including negative-overflow producer results. -/
theorem downward_projection_word {config : Config} (rails : StepSizeRails config)
    (delta : Binary32) (finite : delta.Finite) (nonpositive : delta.key ≤ 0) :
    (LogStepSize.project rails (rails.range.lower.add delta)).value = rails.range.lower := by
  exact floor_key_unique rails _ (saturation_floor_key rails.range _
    (floor_add_key rails delta finite nonpositive))

/-- Zero weight is strictly below the positive disruption threshold throughout
the complete closed value-rule domain. -/
theorem zero_below_disruption (config : Config) :
    Binary32.zero.abs.less (disruptionBound config) = true := by
  rcases config with ⟨role, rule⟩
  cases rule with
  | discounted discount => cases discount <;> simp only [disruptionBound, Config.epsilon] <;> decide
  | differential => simp only [disruptionBound, Config.epsilon]; decide

/-- A downward meta-update from the floor and a zero weight inhabit the actual
retirement predicate, for all raw finite nonpositive deltas, configurations,
state dimensions and feature indices. The direct writes prove predicate
inhabitation, not a trajectory from initialization or complete-reader eligibility. -/
theorem retirement_predicate_reachable {config : Config} {dimension : Dimension}
    (state : NumericState config dimension) (idx : FeatIdx dimension)
    (delta : Binary32) (finite : delta.Finite) (nonpositive : delta.key ≤ 0) :
    (LogStepSize.project state.rails (state.rails.range.lower.add delta)).value =
      state.rails.range.lower ∧
    ((state.writeWeight idx .zero).writeBeta idx
      (state.rails.range.lower.add delta)).unitIsNegligible idx = true := by
  refine ⟨downward_projection_word state.rails delta finite nonpositive, ?_⟩
  have zero := config.rule.domain.symmetric_project_identity
    Binary32.zero config.rule.domain.zeroLegal
  have floor := downward_projection_floor state.rails delta finite nonpositive
  have theta := zero_below_disruption config
  simpa only [NumericState.unitIsNegligible, NumericState.unitIsNegligibleUnder,
    NumericState.negligibility, NumericState.writeWeight, NumericState.writeBeta,
    CurrentLearner.vector_get, Vector.getElem_set_self, Weight.project,
    Bounded32.projectSymmetric, Weight.value, zero, theta, Bool.true_and] using floor

/-- Either finite IEEE zero encoding, with no identification of NaNs as numerical zero. -/
abbrev SignedZero (x : Binary32) : Prop := x = .zero ∨ x = ⟨0x80000000⟩

/-- Multiplication of either zero sign by a finite raw word remains signed
zero. The finiteness premise excludes IEEE invalid zero-times-infinity. -/
theorem zero_mul_finite (zero word : Binary32) (hz : SignedZero zero)
    (finite : word.Finite) : SignedZero (zero.mul word) := by
  have admitted := (model_decoded32_finite word).mpr finite
  rcases hz with rfl | rfl
  all_goals
    change SignedZero (Binary32.mk (UInt32.ofBitVec (pack Format.binary32
      (UnpackedFloat.mul Format.binary32 (.zero _)
        (Float32.Model.ofBits word.bits).unpack))))
    rw [model_ofBits32_decoded word finite]
    generalize equation : decoded32 word = unpacked at admitted ⊢
    cases unpacked with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero sign => cases sign <;> first | exact Or.inl rfl | exact Or.inr rfl
    | finite sign mantissa exponent positive =>
      cases sign <;> first | exact Or.inl rfl | exact Or.inr rfl

-- This private classification uses the standard logical float model
-- canonical NaN. Public conclusions concern only finite zero storage.
-- Native NaN payload choices remain within Arithmetic's trusted boundary.
private abbrev ZeroOrNaN (x : Binary32) : Prop := SignedZero x ∨ x = ⟨0x7fc00000⟩
private theorem mul_zero_raw (x : Binary32) : ZeroOrNaN (x.mul .zero) := by
  change ZeroOrNaN (Binary32.mk (UInt32.ofBitVec (pack Format.binary32
    (UnpackedFloat.mul Format.binary32 (Float32.Model.ofBits x.bits).unpack
      (.zero .positive)))))
  generalize (Float32.Model.ofBits x.bits).unpack = raw
  cases raw with
  | notANumber => exact Or.inr rfl
  | infinity sign => cases sign <;> exact Or.inr rfl
  | zero sign => cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)
  | finite sign mantissa exponent positive =>
    cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)

private theorem zero_mul_raw (x : Binary32) : ZeroOrNaN (Binary32.zero.mul x) := by
  change ZeroOrNaN (Binary32.mk (UInt32.ofBitVec (pack Format.binary32
    (UnpackedFloat.mul Format.binary32 (.zero .positive)
      (Float32.Model.ofBits x.bits).unpack))))
  generalize (Float32.Model.ofBits x.bits).unpack = raw
  cases raw with
  | notANumber => exact Or.inr rfl
  | infinity sign => cases sign <;> exact Or.inr rfl
  | zero sign => cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)
  | finite sign mantissa exponent positive =>
    cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)

private theorem mul_signed_zero (x z : Binary32) (hz : SignedZero z) :
    ZeroOrNaN (x.mul z) ∧ ZeroOrNaN (z.mul x) := by
  rcases hz with rfl | rfl
  · exact ⟨mul_zero_raw x, zero_mul_raw x⟩
  · constructor
    · change ZeroOrNaN (Binary32.mk (UInt32.ofBitVec (pack Format.binary32
        (UnpackedFloat.mul Format.binary32 (Float32.Model.ofBits x.bits).unpack
          (.zero .negative)))))
      generalize (Float32.Model.ofBits x.bits).unpack = raw
      cases raw with
      | notANumber => exact Or.inr rfl
      | infinity sign => cases sign <;> exact Or.inr rfl
      | zero sign => cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)
      | finite sign mantissa exponent positive =>
        cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)
    · change ZeroOrNaN (Binary32.mk (UInt32.ofBitVec (pack Format.binary32
        (UnpackedFloat.mul Format.binary32 (.zero .negative)
          (Float32.Model.ofBits x.bits).unpack))))
      generalize (Float32.Model.ofBits x.bits).unpack = raw
      cases raw with
      | notANumber => exact Or.inr rfl
      | infinity sign => cases sign <;> exact Or.inr rfl
      | zero sign => cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)
      | finite sign mantissa exponent positive =>
        cases sign <;> first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr rfl)

private theorem zero_nan_sub (a b : Binary32) (ha : ZeroOrNaN a) (hb : ZeroOrNaN b) :
    ZeroOrNaN (a.sub b) := by
  rcases ha with (rfl | rfl) | rfl <;> rcases hb with (rfl | rfl) | rfl <;>
    decide

private theorem zero_nan_add (a b : Binary32) (ha : ZeroOrNaN a) (hb : ZeroOrNaN b) :
    ZeroOrNaN (a.add b) := by
  rcases ha with (rfl | rfl) | rfl <;> rcases hb with (rfl | rfl) | rfl <;> decide

private theorem zero_nan_mul (a b : Binary32) (ha : ZeroOrNaN a) :
    ZeroOrNaN (a.mul b) := by
  rcases ha with hz | rfl
  · exact (mul_signed_zero b a hz).2
  · change ZeroOrNaN (Binary32.mk (UInt32.ofBitVec (pack Format.binary32
      (UnpackedFloat.mul Format.binary32 .notANumber (Float32.Model.ofBits b.bits).unpack))))
    generalize (Float32.Model.ofBits b.bits).unpack = raw
    cases raw <;> exact Or.inr rfl

private theorem project_zero (rule : ValueRule) (x : Binary32) (hx : SignedZero x) :
    (Weight.project rule x).value = x := by
  apply rule.domain.symmetric_project_identity
  rcases hx with rfl | rfl
  · exact rule.domain.zeroLegal
  · exact ⟨by decide, rule.domain.zeroLegal.2.1, rule.domain.zeroLegal.2.2⟩

private theorem zero_weight_write (rule : ValueRule) (w delta z zd vd : Binary32)
    (hw : SignedZero w) (hd : ZeroOrNaN delta) (hv : SignedZero vd) :
    let dw := (delta.mul z).sub (zd.mul vd)
    let raw := w.add dw
    let projected := (Weight.project rule raw).value
    SignedZero projected ∧
      SignedZero (if !(projected.numericallyEqual raw) then .zero else dw) := by
  have hdw := zero_nan_sub _ _ (zero_nan_mul delta z hd) (mul_signed_zero zd vd hv).1
  rcases hdw with hzero | hnan
  · have rawzero : SignedZero (w.add ((delta.mul z).sub (zd.mul vd))) := by
      rcases hw with rfl | rfl <;> rcases hzero with h | h <;> rw [h] <;> decide
    dsimp only
    rw [project_zero rule _ rawzero]
    refine ⟨rawzero, ?_⟩
    split <;> first | exact Or.inl rfl | exact hzero
  · dsimp only
    rw [hnan]
    have addnan : w.add ⟨0x7fc00000⟩ = ⟨0x7fc00000⟩ := by
      rcases hw with rfl | rfl <;> rfl
    rw [addnan]
    have projectnan : (Weight.project rule ⟨0x7fc00000⟩).value = .zero := rfl
    rw [projectnan]
    decide

variable {config : Config} {dimension : Dimension}
/-- Zero learned weights and update lags. All other raw registers and beta words
remain unconstrained; this predicate does not imply eligibility or cold beta. -/
structure ZeroKnowledge (state : NumericState config dimension) : Prop where
  /-- Every stored prediction weight is zero. -/
  weights : ∀ idx, SignedZero (state.weights.get idx).value
  /-- Every carried per-index weight update is zero. -/
  updates : ∀ idx, SignedZero (state.transient.deltaWeight.get idx).value
  /-- The previous prediction anchor is zero. -/
  old : SignedZero state.transient.vOld
  /-- The previous update accumulator is zero. -/
  delta : SignedZero state.transient.vDelta

/-- Actual cold construction starts in the zero-weight and zero-lag sector. -/
theorem zero_initial : ZeroKnowledge (NumericState.initial config dimension) := by
  constructor
  · intro idx
    simp only [NumericState.initial, CurrentLearner.vector_get, Vector.getElem_replicate]
    rw [project_zero config.rule _ (Or.inl rfl)]
    exact Or.inl rfl
  · intro idx; simp [NumericState.initial, TransientState.zero, Vector.get, SignedZero]
  · exact Or.inl rfl
  · exact Or.inl rfl

private theorem zero_first_element (state : NumericState config dimension)
    (hz : ZeroKnowledge state)
    (idx : FeatIdx dimension) (delta vd decay : Binary32)
    (hd : ZeroOrNaN delta) (hv : SignedZero vd) :
    ZeroKnowledge (state.firstLoopElement idx delta vd decay).1 := by
  have write := zero_weight_write config.rule _ delta (state.transient.z.get idx).value
    (state.transient.zDelta.get idx).value vd (hz.weights idx) hd hv
  constructor
  · intro other
    by_cases heq : idx = other
    · subst other
      simpa only [NumericState.firstLoopElement, CurrentLearner.vector_get,
        Vector.getElem_set_self] using write.1
    · have distinct : idx.val ≠ other.val := fun same => heq (Fin.ext same)
      simpa only [NumericState.firstLoopElement, CurrentLearner.vector_get,
        Vector.getElem_set, distinct, if_false] using hz.weights other
  · intro other
    by_cases heq : idx = other
    · subst other
      simpa only [NumericState.firstLoopElement, CurrentLearner.vector_get,
        Vector.getElem_set_self] using write.2
    · have distinct : idx.val ≠ other.val := fun same => heq (Fin.ext same)
      simpa only [NumericState.firstLoopElement, CurrentLearner.vector_get,
        Vector.getElem_set, distinct, if_false] using hz.updates other
  · exact hz.old
  · exact hz.delta

private theorem zero_clear_feature (state : NumericState config dimension)
    (hz : ZeroKnowledge state)
    (idx : FeatIdx dimension) : ZeroKnowledge (state.clearFeatureRegisters idx) := by
  constructor
  · intro other
    simpa only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
      NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
      NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
      NumericState.writeLastAlpha] using hz.weights other
  · intro other
    simp only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
      NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
      NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
      NumericState.writeLastAlpha, CurrentLearner.vector_get, Vector.getElem_set]
    split
    · exact Or.inl rfl
    · exact hz.updates other
  · simpa only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
      NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
      NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
      NumericState.writeLastAlpha] using hz.old
  · simpa only [NumericState.clearFeatureRegisters, NumericState.writeZ, NumericState.writeP,
      NumericState.writeZBar, NumericState.writeDeltaWeight, NumericState.writeZDelta,
      NumericState.writeH, NumericState.writeHOld, NumericState.writeHTemp,
      NumericState.writeLastAlpha] using hz.delta

private theorem zero_first_go (state : NumericState config dimension)
    (work : Array (FeatIdx dimension)) (pos : Nat) (delta vd decay : Binary32)
    (hz : ZeroKnowledge state) (hd : ZeroOrNaN delta) (hv : SignedZero vd) :
    ZeroKnowledge (NumericState.learnFirstLoopGo config delta vd decay state work pos) := by
  induction state, work, pos using NumericState.learnFirstLoopGo.induct config delta vd decay with
  | case1 state work pos valid idx next equation ih =>
    dsimp only [idx] at equation ih
    have hn : ZeroKnowledge next := by
      simpa only [equation] using zero_first_element state hz work[pos] delta vd decay hd hv
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, ite_true] using ih (zero_clear_feature next hn work[pos])
  | case2 state work pos valid idx next prune equation noPrune ih =>
    dsimp only [idx] at equation ih
    have hn : ZeroKnowledge next := by
      simpa only [equation] using zero_first_element state hz work[pos] delta vd decay hd hv
    rw [NumericState.learnFirstLoopGo, dif_pos valid]
    simpa only [equation, if_neg noPrune] using ih hn
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo, dif_neg finished]
    exact ⟨hz.weights, hz.updates, hz.old, hz.delta⟩

/-- Zero error and update accumulator preserve the sector through the actual
first-loop worklist, including pruning and exceptional trace operands. -/
theorem zero_first_loop (state : NumericState config dimension) (hz : ZeroKnowledge state)
    (delta vd decay : Binary32) (hd : SignedZero delta) (hv : SignedZero vd) :
    ZeroKnowledge (state.learnFirstLoop config delta vd decay) :=
  zero_first_go _ _ _ _ _ _ ⟨hz.weights, hz.updates, hz.old, hz.delta⟩ (Or.inl hd) hv

/-- The actual shared-error snapshot expression preserves zero knowledge with
zero reward, snapshot and lags, for any bootstrap/decay words. Exceptional
bootstrap products become NaN errors and take the same projection/clipping path;
no finiteness of a separately computed power is needed for this zero sector. -/
theorem zero_first_snapshot (state : NumericState config dimension) (hz : ZeroKnowledge state)
    (reward value old vd bootstrap decay : Binary32)
    (hr : SignedZero reward) (hvalue : SignedZero value) (hold : SignedZero old)
    (hv : SignedZero vd) :
    ZeroKnowledge (state.learnFirstLoop config
      ((reward.add (bootstrap.mul value)).sub old) vd decay) := by
  have hd := zero_nan_sub _ _
    (zero_nan_add _ _ (Or.inl hr) (mul_signed_zero bootstrap value hvalue).1) (Or.inl hold)
  exact zero_first_go _ _ _ _ _ _ ⟨hz.weights, hz.updates, hz.old, hz.delta⟩ hd hv

private theorem zero_add (a b : Binary32) (ha : SignedZero a) (hb : SignedZero b) :
    SignedZero (a.add b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private theorem zero_sub (a b : Binary32) (ha : SignedZero a) (hb : SignedZero b) :
    SignedZero (a.sub b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- The actual ordered active loop preserves zero weights and carries only
zero updates, independently of overshoot, beta and raw trace values. -/
theorem zero_second_loop (state : NumericState config dimension) (hz : ZeroKnowledge state)
    (features : ActiveSet dimension) (vd : Binary32) (hv : SignedZero vd) :
    ZeroKnowledge (state.learnSecondLoop config features vd).1 ∧
      SignedZero (state.learnSecondLoop config features vd).2 := by
  have fold (indices : List (FeatIdx dimension)) (current : NumericState config dimension)
      (acc e t : Binary32) (overshoot : Bool) (hc : ZeroKnowledge current) (ha : SignedZero acc) :
      let result := indices.foldl (fun (s, v) idx =>
        NumericState.secondLoopElement config overshoot e t s v idx) (current, acc)
      ZeroKnowledge result.1 ∧ SignedZero result.2 := by
    induction indices generalizing current acc with
    | nil => exact ⟨hc, ha⟩
    | cons idx rest ih =>
      apply ih
      · exact ⟨hc.weights, hc.updates, hc.old, hc.delta⟩
      · exact zero_add _ _ ha (hc.updates idx)
  exact fold _ _ _ _ _ _ hz hv

/-- Clearing actual transient storage preserves zero weights and reinitializes all lags. -/
theorem zero_clear (state : NumericState config dimension)
    (hz : ZeroKnowledge state) :
    ZeroKnowledge state.clearTransient := by
  refine ⟨hz.weights, ?_, Or.inl rfl, Or.inl rfl⟩
  intro idx
  simp [NumericState.clearTransient, TransientState.zero, Vector.get, SignedZero]

/-- Receiver-slot retirement preserves zero knowledge while resetting that
slot's registers and beta. No negligibility, cold-beta or distinct-slot premise
is needed for this numerical reset property. -/
theorem zero_retire (state : NumericState config dimension)
    (hz : ZeroKnowledge state) (idx : FeatIdx dimension) :
    ZeroKnowledge (state.retireIndex idx) := by
  have reset (current : NumericState config dimension) (hc : ZeroKnowledge current) :
      ZeroKnowledge ((current.clearFeatureRegisters idx).writeWeight idx .zero) := by
    have cleared := zero_clear_feature current hc idx
    refine ⟨?_, cleared.updates, cleared.old, cleared.delta⟩
    intro other
    simp only [NumericState.writeWeight, CurrentLearner.vector_get, Vector.getElem_set]
    split
    · rw [project_zero config.rule .zero (Or.inl rfl)]
      exact Or.inl rfl
    · exact cleared.weights other
  unfold NumericState.retireIndex
  split
  · rename_i pos found
    have valid := (Array.findIdx?_eq_some_iff_getElem.mp found).1
    have kept := reset (state.removeEligibleAt pos valid)
      ⟨hz.weights, hz.updates, hz.old, hz.delta⟩
    exact ⟨kept.weights, kept.updates, Or.inl rfl, Or.inl rfl⟩
  · have kept := reset state hz
    exact ⟨kept.weights, kept.updates, Or.inl rfl, Or.inl rfl⟩

/-- Every actual ordered active prediction is a signed zero in the zero sector. -/
theorem zero_prediction (state : NumericState config dimension)
    (hz : ZeroKnowledge state)
    (features : ActiveSet dimension) : SignedZero (state.predict features) := by
  have fold (indices : List (FeatIdx dimension)) (acc : Binary32) (ha : SignedZero acc) :
      SignedZero (indices.foldl (fun a idx => a.add (state.weights.get idx).value) acc) := by
    induction indices generalizing acc with
    | nil => exact ha
    | cons idx rest ih => exact ih _ (zero_add _ _ ha (hz.weights idx))
  exact fold features.indices .zero (Or.inl rfl)

private theorem gamma_zero (rule : ValueRule) (x : Binary32) (hx : SignedZero x) :
    SignedZero (rule.gamma.mul x) := by
  rcases hx with rfl | rfl <;> cases rule with
  | discounted discount => cases discount <;> decide
  | differential => decide

/-- A zero-reward single-learner update preserves the initialized sector for
every active set. This is a numerical transition theorem; the full agent must
still derive this reward and its other learner targets from executed producers. -/
theorem zero_step (state : NumericState config dimension) (hz : ZeroKnowledge state)
    (features : ActiveSet dimension) (reward : Binary32) (hr : SignedZero reward) :
    ZeroKnowledge (state.step config features reward).1 := by
  have prediction := zero_prediction state hz features
  have delta := zero_sub _ _ (zero_add _ _ hr (gamma_zero config.rule _ prediction)) hz.old
  have first := zero_first_loop state hz _ _
    (config.rule.gamma.mul config.lambda) delta hz.delta
  have second := zero_second_loop _ first features .zero (Or.inl rfl)
  exact ⟨second.1.weights, second.1.updates, prediction, second.2⟩

/-- Actual trajectory initialization preserves zero knowledge while freely
changing traces and step sizes. -/
theorem zero_begin (state : NumericState config dimension) (hz : ZeroKnowledge state)
    (features : ActiveSet dimension) : ZeroKnowledge (state.beginTrajectory config features) := by
  have cleared := zero_clear state hz
  have second := zero_second_loop _ cleared features .zero (Or.inl rfl)
  exact ⟨second.1.weights, second.1.updates, zero_prediction _ cleared features, second.2⟩

/-- Zero terminal credit preserves zero knowledge, including when arbitrary
raw trace intermediates become NaN and trigger the actual clipping reset. -/
theorem zero_terminal (state : NumericState config dimension) (hz : ZeroKnowledge state)
    (target : Binary32) (ht : SignedZero target) :
    ZeroKnowledge (state.terminalStep config target).1 :=
  zero_clear _ (zero_first_loop state hz _ _ _ (zero_sub _ _ ht hz.old) hz.delta)

/-- Planning toward a zero target from zero stored knowledge takes the
executed zero-error refusal branch, preserving the entire numerical state. -/
theorem zero_plan_identity (state : NumericState config dimension) (hz : ZeroKnowledge state)
    (features : ActiveSet dimension) (target : Binary32) (ht : SignedZero target) :
    state.planStep config features target = (state, .zero) := by
  have hp := zero_prediction state hz features
  have hd := zero_sub _ _ ht hp
  have he : (target.sub (state.predict features)).numericallyEqual .zero = true := by
    rcases hd with h | h <;> rw [h] <;> decide
  simp only [NumericState.planStep, he, Bool.or_true, if_true]

/-- A finite-register predicate for the single g99 discounted demon. This
records candidate bounds, not preservation by learning callbacks. Readiness is
not required at callback boundaries: eligible zero traces may await pruning.
Legality of beta and weights remains enforced by their existing storage types. -/
structure ColdBox (state : NumericState ⟨.demon, .discounted .g99⟩ dimension) : Prop where
  /-- The explicit capacity domain for the proposed ordered active-sum bound. -/
  capacity : dimension.capacity ≤ 16384
  /-- Reuse the signed-zero learned-weight and update-lag sector. -/
  knowledge : ZeroKnowledge state
  /-- Reuse actual dormant support and pruning-reference legality. -/
  core : CurrentLearner.CoreInv state
  /-- Eligibility has no duplicate indices, without a nonzero-trace premise. -/
  unique : state.transient.eligible.toList.Nodup
  /-- The meta trace has either zero sign. -/
  p : ∀ idx, SignedZero (state.transient.p.get idx).value
  /-- The Dutch-trace auxiliary has either zero sign. -/
  h : ∀ idx, SignedZero (state.transient.h.get idx).value
  /-- The previous auxiliary has either zero sign. -/
  hOld : ∀ idx, SignedZero (state.transient.hOld.get idx).value
  /-- The temporary auxiliary has either zero sign. -/
  hTemp : ∀ idx, SignedZero (state.transient.hTemp.get idx).value
  /-- Trace finiteness is explicit; its box permits negative post-admission values. -/
  z : ∀ idx, (state.transient.z.get idx).value.Finite ∧
    -((2 : ℚ) ^ (21 : Int)) ≤ numerical32 (state.transient.z.get idx).value ∧
    numerical32 (state.transient.z.get idx).value ≤ 64
  /-- The Dutch trace has its own finite symmetric bound. -/
  zBar : ∀ idx, (state.transient.zBar.get idx).value.Finite ∧
    |numerical32 (state.transient.zBar.get idx).value| ≤ (2 : ℚ) ^ (26 : Int)
  /-- The trace increment includes both actual normalization rounding boundaries. -/
  zDelta : ∀ idx, (state.transient.zDelta.get idx).value.Finite ∧
    0 ≤ numerical32 (state.transient.zDelta.get idx).value ∧
    numerical32 (state.transient.zDelta.get idx).value ≤ 101 / (100 : ℚ)
  /-- The stored pruning reference retains the same increment bound. -/
  lastAlpha : ∀ idx, (state.transient.lastAlpha.get idx).value.Finite ∧
    0 ≤ numerical32 (state.transient.lastAlpha.get idx).value ∧
    numerical32 (state.transient.lastAlpha.get idx).value ≤ 101 / (100 : ℚ)

/-- Clearing derives every transient bound from the actual zero constructor.
Incoming trace and sensitivity bounds are not required beyond zero knowledge. -/
private theorem cold_box_cleared
    (state : NumericState ⟨.demon, .discounted .g99⟩ dimension)
    (capacity : dimension.capacity ≤ 16384) (knowledge : ZeroKnowledge state) :
    ColdBox state.clearTransient := by
  refine ⟨capacity, zero_clear state knowledge, CurrentLearner.clear_core state,
    (CurrentLearner.clear_ready state).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx
    simp [NumericState.clearTransient, TransientState.zero, Vector.get, SignedZero]
  · intro idx
    simp [NumericState.clearTransient, TransientState.zero, Vector.get, SignedZero]
  · intro idx
    simp [NumericState.clearTransient, TransientState.zero, Vector.get, SignedZero]
  · intro idx
    simp [NumericState.clearTransient, TransientState.zero, Vector.get, SignedZero]
  · intro idx
    simp only [NumericState.clearTransient, TransientState.zero,
      CurrentLearner.vector_get, Vector.getElem_replicate]
    exact ⟨by decide, by change -((2 : ℚ) ^ (21 : Int)) ≤ 0; norm_num,
      by change (0 : ℚ) ≤ 64; norm_num⟩
  · intro idx
    simp only [NumericState.clearTransient, TransientState.zero,
      CurrentLearner.vector_get, Vector.getElem_replicate]
    exact ⟨by decide, by change |(0 : ℚ)| ≤ (2 : ℚ) ^ (26 : Int); norm_num⟩
  · intro idx
    simp only [NumericState.clearTransient, TransientState.zero,
      CurrentLearner.vector_get, Vector.getElem_replicate]
    exact ⟨by decide, le_refl 0, by change (0 : ℚ) ≤ 101 / 100; norm_num⟩
  · intro idx
    simp only [NumericState.clearTransient, TransientState.zero,
      CurrentLearner.vector_get, Vector.getElem_replicate]
    exact ⟨by decide, le_refl 0, by change (0 : ℚ) ≤ 101 / 100; norm_num⟩

/-- The actual discounted-demon constructor satisfies the finite-register box.
The constructor's transient storage is definitionally its cleared storage. -/
theorem cold_box_initial (dimension : Dimension) (capacity : dimension.capacity ≤ 16384) :
    ColdBox (NumericState.initial ⟨.demon, .discounted .g99⟩ dimension) :=
  cold_box_cleared (NumericState.initial ⟨.demon, .discounted .g99⟩ dimension)
    capacity zero_initial

/-- Actual trajectory clearing preserves the box without asserting anything
about an intervening learning callback or restored primary knowledge. -/
theorem cold_box_clear (state : NumericState ⟨.demon, .discounted .g99⟩ dimension)
    (box : ColdBox state) : ColdBox state.clearTransient :=
  cold_box_cleared state box.capacity box.knowledge

end AcornVerif.CurrentRetirement
