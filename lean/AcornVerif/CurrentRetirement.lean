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
state dimensions and feature indices. -/
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

end AcornVerif.CurrentRetirement
