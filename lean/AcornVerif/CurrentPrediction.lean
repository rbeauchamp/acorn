/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentOrder
import Acorn.State
/-!
# Ordered binary32 prediction bounds

Strict power-of-two bounds retain the smaller rounding radius below a binade
endpoint. The closed weight domain supplies a common finite envelope; raw word
spacing closes the global cap. Induction composes the actual left-to-right sum
for arbitrary finite lists. No runtime trajectory enumeration or output clipping
is used to infer a transient-state bound. Native primitive/compiler behavior
remains the declared trust boundary.
-/
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open Float.Model.UnpackedFloat
open AcornVerif.CurrentFloat AcornVerif.CurrentPower AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder
namespace AcornVerif.CurrentPrediction

/-- A strict power-of-two magnitude bound gives the smaller half-unit radius below its binade
endpoint. -/
theorem model_round_uniform_error_strict (spec : Format) (sign : Sign) (mantissa : Nat)
    (exponent limit : Int)
    (bound : |signCoefficient sign * mantissa * (2 : ℚ) ^ exponent| < (2 : ℚ) ^ limit) :
    |unpackedValue (round spec sign mantissa exponent) -
      signCoefficient sign * mantissa * (2 : ℚ) ^ exponent| ≤
      (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 := by
  by_cases hz : mantissa = 0
  · rw [hz, model_round_zero]
    simp only [unpackedValue, Nat.cast_zero, mul_zero, zero_mul, sub_self, abs_zero]
    exact div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  · have hp : 0 < mantissa := by omega
    have habs : |signCoefficient sign * mantissa * (2:ℚ)^exponent| =
        mantissa*(2:ℚ)^exponent := model_finite_abs sign mantissa exponent hp
    rw [habs] at bound
    have hlo := (model_positive_dyadic_window mantissa exponent hp).1
    have htotal : totalExponent mantissa exponent ≤ limit := by
      have he := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ) < 2)).mp (lt_of_le_of_lt hlo bound)
      omega
    have htarget : spec.targetExponent (totalExponent mantissa exponent) ≤
        max (limit-spec.mantissaBits) spec.minExponent := by
      dsimp only [Format.targetExponent]
      omega
    apply le_trans (model_round_error spec sign mantissa exponent)
    exact div_le_div_of_nonneg_right
      (zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2) htarget) (by norm_num)

/-- Signed normalization inherits the strict magnitude rounding radius, including either zero
sign. -/
theorem model_signed_round_value_strict (spec : Format) (mantissa : Int) (exponent : Int)
    (zeroSign : Sign)
    (limit : Int) (bound : |(mantissa : ℚ) * (2 : ℚ) ^ exponent| < (2 : ℚ) ^ limit) :
    ModelNormalized spec (normalize spec mantissa exponent zeroSign) ∧
      |unpackedValue (normalize spec mantissa exponent zeroSign) -
        (mantissa : ℚ) * (2 : ℚ) ^ exponent| ≤
        (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 := by
  unfold normalize
  split
  · rename_i negative
    have hn : mantissa < 0 := (Int.compare_eq_lt).mp negative
    have hs : (signCoefficient Sign.negative * (-mantissa).toNat : ℚ) = mantissa := by
      simp only [signCoefficient]
      have he : ((-mantissa).toNat : Int) = -mantissa := Int.toNat_of_nonneg (by omega)
      have hc : ((-mantissa).toNat : ℚ) = -(mantissa:ℚ) := by exact_mod_cast he
      rw [hc]
      ring
    refine ⟨model_round_normalized _ _ _ _, ?_⟩
    have proof := model_round_uniform_error_strict spec .negative (-mantissa).toNat exponent limit
      (by simpa only [hs] using bound)
    simpa only [hs] using proof
  · rename_i zero
    have hn : mantissa = 0 := (Int.compare_eq_eq).mp zero
    subst mantissa
    refine ⟨True.intro, ?_⟩
    simp only [unpackedValue, Int.cast_zero, zero_mul, sub_self, abs_zero]
    exact div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  · rename_i positive
    have hn : 0 < mantissa := (Int.compare_eq_gt).mp positive
    have hs : (signCoefficient Sign.positive * mantissa.toNat : ℚ) = mantissa := by
      simp only [signCoefficient, one_mul]
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ mantissa)
    refine ⟨model_round_normalized _ _ _ _, ?_⟩
    have proof := model_round_uniform_error_strict spec .positive mantissa.toNat exponent limit
      (by simpa only [hs] using bound)
    simpa only [hs] using proof

/-- Actual unpacked addition preserves normalization and the strict-domain radius before packing. -/
theorem model_add_dyadic_local_strict (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (limit : Int)
    (bound : |unpackedValue left + unpackedValue right| < (2 : ℚ) ^ limit) :
    ModelNormalized spec (UnpackedFloat.add spec left right) ∧
      |unpackedValue (UnpackedFloat.add spec left right) -
        (unpackedValue left + unpackedValue right)| ≤
        (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 := by
  have epsilon : (0:ℚ) ≤ (2:ℚ)^(max (limit-spec.mantissaBits) spec.minExponent)/2 :=
    div_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 2) _)) (by norm_num)
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right with
    | notANumber => contradiction
    | infinity s => contradiction
    | zero s =>
      cases sign <;> cases s <;>
        change True ∧ |(0:ℚ)-(0+0)| ≤ _
      all_goals exact ⟨True.intro, by simpa only [add_zero, sub_self, abs_zero] using epsilon⟩
    | finite s m e hp =>
      simpa only [UnpackedFloat.add, unpackedValue, zero_add, sub_self, abs_zero] using
        And.intro rightNormal epsilon
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero rightSign =>
      simpa only [UnpackedFloat.add, unpackedValue, add_zero, sub_self, abs_zero] using
        And.intro leftNormal epsilon
    | finite rightSign rm re rp =>
      simp only [UnpackedFloat.add]
      let target := min le re
      let lmantissa := (decreaseExponent lm le target).1
      let rmantissa := (decreaseExponent rm re target).1
      let sum := leftSign.apply lmantissa + rightSign.apply rmantissa
      have hl := model_decrease_dyadic_value leftSign lm le target (Int.min_le_left _ _)
      have hr := model_decrease_dyadic_value rightSign rm re target (Int.min_le_right _ _)
      have heq : (sum:ℚ)*(2:ℚ)^target =
          unpackedValue (.finite leftSign lm le lp)+unpackedValue (.finite rightSign rm re rp) := by
        change ((leftSign.apply lmantissa + rightSign.apply rmantissa : Int):ℚ)*(2:ℚ)^target = _
        rw [Int.cast_add, add_mul, hl, hr]
        rfl
      have proof := model_signed_round_value_strict spec sum target .positive limit
        (by simpa only [heq] using bound)
      change ModelNormalized spec (normalize spec sum target .positive) ∧ _
      simpa only [heq] using proof

/-- Actual binary32 addition remains finite and inherits the strict rounding radius whenever
the exact sum is below an admitted power of two, through exponent 33. -/
theorem binary32_add_finite_strict_error (left right : Binary32)
    (leftFinite : left.Finite) (rightFinite : right.Finite) (limit : Int) (range : limit ≤ 33)
    (bound : |numerical32 left + numerical32 right| < (2 : ℚ) ^ limit) :
    (left.add right).Finite ∧
      |numerical32 (left.add right)-(numerical32 left+numerical32 right)| ≤
        (2:ℚ)^(max (limit-24) (-149))/2 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr leftFinite)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr rightFinite)).1
  have operation := model_add_dyadic_local_strict Format.binary32 (decoded32 left)
    (decoded32 right) ln rn limit bound
  have error : |unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 left)
      (decoded32 right))-(numerical32 left+numerical32 right)| ≤
        (2:ℚ)^(max (limit-24) (-149))/2 := operation.2
  have radiusBound : (2:ℚ)^(max (limit-24) (-149))/2 ≤ 256 := by
    have power := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2)
      (show max (limit-24) (-149) ≤ 9 by omega)
    norm_num at power
    linarith only [power]
  have sumBound : |numerical32 left+numerical32 right| ≤ 8589934592 := by
    have power := zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2) range
    norm_num at power
    exact le_trans (le_of_lt bound) power
  have fits : ModelFits Format.binary32 (UnpackedFloat.add Format.binary32
      (decoded32 left) (decoded32 right)) := by
    apply model_fits_of_value_bound Format.binary32 _
      (model_normalized_finite _ _ operation.1) 34 (by decide)
    have triangle := abs_add_le
      (unpackedValue (UnpackedFloat.add Format.binary32 (decoded32 left) (decoded32 right))-
        (numerical32 left+numerical32 right)) (numerical32 left+numerical32 right)
    rw [sub_add_cancel] at triangle
    norm_num
    linarith only [triangle,error,radiusBound,sumBound]
  have decoded := model_add32_decoded left right leftFinite rightFinite operation.1 fits
  constructor
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32,decoded] using error

/-- Every legal weight under any closed current criterion is finite and bounded in magnitude by
101. The small margin includes the rounded machine horizon for the longest discount. -/
theorem weight_numerical_bound (rule : ValueRule) (weight : Weight rule) :
    weight.value.Finite ∧ |numerical32 weight.value| ≤ 101 := by
  have legal := weight_legal weight
  have lo : -(0x42ca0000:Int) ≤ rule.domain.range.lower.key := by
    cases rule with
    | discounted discount => cases discount <;> decide
    | differential => decide
  have hi : rule.domain.range.upper.key ≤ (0x42ca0000:Int) := by
    cases rule with
    | discounted discount => cases discount <;> decide
    | differential => decide
  let lower : Binary32 := ⟨0xc2ca0000⟩
  let upper : Binary32 := ⟨0x42ca0000⟩
  have lowerFinite : lower.Finite := by decide
  have upperFinite : upper.Finite := by decide
  have lowerKey : lower.key = -(0x42ca0000:Int) := by dsimp only [lower]; rfl
  have upperKey : upper.key = (0x42ca0000:Int) := by dsimp only [upper]; rfl
  have lowerValue : numerical32 lower = -101 := by
    dsimp only [lower]
    change (-1:ℚ)*13238272*(2:ℚ)^(-17:Int) = _
    norm_num
  have upperValue : numerical32 upper = 101 := by
    dsimp only [upper]
    change (1:ℚ)*13238272*(2:ℚ)^(-17:Int) = _
    norm_num
  have lowerProof := (numerical32_order lower weight.value lowerFinite legal.1).mpr
    (by rw [lowerKey]; exact le_trans lo legal.2.1)
  have upperProof := (numerical32_order weight.value upper legal.1 upperFinite).mpr
    (by rw [upperKey]; exact le_trans legal.2.2 hi)
  rw [lowerValue] at lowerProof
  rw [upperValue] at upperProof
  exact ⟨legal.1,abs_le.mpr ⟨lowerProof,upperProof⟩⟩

/-- Every finite binary32 magnitude above 2^32 is at least 2^32+512, by discrete raw-magnitude
order. This includes both signs. -/
theorem numerical32_prediction_cap_gap (value : Binary32) (finite : value.Finite)
    (above : 4294967296 < |numerical32 value|) :
    4294967808 ≤ |numerical32 value| := by
  let cap : Binary32 := ⟨0x4f800000⟩
  let next : Binary32 := ⟨0x4f800001⟩
  have capFinite : cap.Finite := by decide
  have nextFinite : next.Finite := by decide
  have capValue : numerical32 cap = 4294967296 := by
    dsimp only [cap]
    change (1:ℚ)*8388608*(2:ℚ)^(9:Int) = _
    norm_num
  have nextValue : numerical32 next = 4294967808 := by
    dsimp only [next]
    change (1:ℚ)*8388609*(2:ℚ)^(9:Int) = _
    norm_num
  have capMagnitude : cap.magnitude = 0x4f800000 := by dsimp only [cap]; rfl
  have nextMagnitude : next.magnitude = 0x4f800001 := by dsimp only [next]; rfl
  have raw : cap.magnitude < value.magnitude := by
    by_contra notLess
    have order := (numerical32_magnitude_order value cap finite capFinite).mpr (by omega)
    rw [capValue] at order
    norm_num only [abs_of_pos (by norm_num : (0:ℚ)<4294967296)] at order
    linarith only [above,order]
  have nextRaw : next.magnitude ≤ value.magnitude := by
    rw [capMagnitude] at raw
    rw [nextMagnitude]
    omega
  have order := (numerical32_magnitude_order next value nextFinite finite).mpr nextRaw
  rw [nextValue] at order
  simpa only [abs_of_pos (by norm_num : (0:ℚ)<4294967808)] using order

/-- At the global prediction cap, every admitted weight leaves the actual rounded sum finite
and within the cap; the weight and rounding error cannot reach the next representable value. -/
theorem prediction_sum_cap (sum weight : Binary32) (sumFinite : sum.Finite)
    (weightFinite : weight.Finite) (sumBound : |numerical32 sum| ≤ 4294967296)
    (weightBound : |numerical32 weight| ≤ 101) :
    (sum.add weight).Finite ∧ |numerical32 (sum.add weight)| ≤ 4294967296 := by
  have exactBound : |numerical32 sum+numerical32 weight| ≤ 4294967397 :=
    le_trans (abs_add_le _ _) (by linarith only [sumBound,weightBound])
  have operation := binary32_add_finite_strict_error sum weight sumFinite weightFinite 33
    (by decide) (lt_of_le_of_lt exactBound (by norm_num))
  have error : |numerical32 (sum.add weight)-(numerical32 sum+numerical32 weight)| ≤ 256 := by
    convert operation.2 using 1
    norm_num
  refine ⟨operation.1,?_⟩
  by_contra greater
  have gap := numerical32_prediction_cap_gap (sum.add weight) operation.1
    (by linarith only [greater])
  have triangle := abs_add_le
    (numerical32 (sum.add weight)-(numerical32 sum+numerical32 weight))
    (numerical32 sum+numerical32 weight)
  rw [sub_add_cancel] at triangle
  linarith only [gap,triangle,error,exactBound]

/-- The derived prediction envelope grows by 256 per addition and caps at 2^32. -/
def predictionRadius (count : Nat) : ℚ := (min count (2^24) : Nat)*256

/-- Every actual rounded addition preserves the count-indexed envelope, over all counts and all
finite admitted machine sums and weights. -/
theorem prediction_sum_step (count : Nat) (sum weight : Binary32)
    (sumFinite : sum.Finite) (weightFinite : weight.Finite)
    (sumBound : |numerical32 sum| ≤ predictionRadius count)
    (weightBound : |numerical32 weight| ≤ 101) :
    (sum.add weight).Finite ∧ |numerical32 (sum.add weight)| ≤ predictionRadius (count+1) := by
  by_cases growing : count < 2^24
  · have before : predictionRadius count = (count:ℚ)*256 := by
      simp only [predictionRadius,Nat.min_eq_left (show count ≤ 2^24 by omega)]
    have after : predictionRadius (count+1) = ((count:ℚ)+1)*256 := by
      simp only [predictionRadius,Nat.min_eq_left (show count+1 ≤ 2^24 by omega),
        Nat.cast_add,Nat.cast_one]
    rw [before] at sumBound
    rw [after]
    have countBound : (count:ℚ) ≤ 16777215 := by exact_mod_cast (show count≤16777215 by omega)
    have exactBound : |numerical32 sum+numerical32 weight| ≤ (count:ℚ)*256+101 :=
      le_trans (abs_add_le _ _) (add_le_add sumBound weightBound)
    have operation := binary32_add_finite_strict_error sum weight sumFinite weightFinite 32
      (by decide) (by norm_num; linarith only [exactBound,countBound])
    have error : |numerical32 (sum.add weight)-(numerical32 sum+numerical32 weight)| ≤ 128 := by
      convert operation.2 using 1
      norm_num
    have triangle := abs_add_le
      (numerical32 (sum.add weight)-(numerical32 sum+numerical32 weight))
      (numerical32 sum+numerical32 weight)
    rw [sub_add_cancel] at triangle
    exact ⟨operation.1,by linarith only [triangle,error,exactBound]⟩
  · have before : predictionRadius count = 4294967296 := by
      simp only [predictionRadius,Nat.min_eq_right (show 2^24 ≤ count by omega)]
      norm_num
    have after : predictionRadius (count+1) = 4294967296 := by
      simp only [predictionRadius,Nat.min_eq_right (show 2^24 ≤ count+1 by omega)]
      norm_num
    rw [before] at sumBound
    rw [after]
    exact prediction_sum_cap sum weight sumFinite weightFinite sumBound weightBound

/-- Arbitrary finite ordered lists preserve the prediction envelope at every prefix, through
induction on the actual rounded accumulator rather than a real-valued reassociation. -/
theorem prediction_sumFrom_bound (count : Nat) (initial : Binary32) (values : List Binary32)
    (finite : initial.Finite) (bound : |numerical32 initial| ≤ predictionRadius count)
    (weights : ∀ value ∈ values, value.Finite ∧ |numerical32 value| ≤ 101) :
    (Binary32.sumFrom initial values).Finite ∧
      |numerical32 (Binary32.sumFrom initial values)| ≤ predictionRadius (count+values.length) := by
  induction values generalizing count initial with
  | nil => simpa only [Binary32.sumFrom,List.foldl_nil,List.length_nil,Nat.add_zero] using
      And.intro finite bound
  | cons value rest ih =>
    have next := prediction_sum_step count initial value finite (weights value (by simp)).1
      bound (weights value (by simp)).2
    have tailProof := ih (count+1) (initial.add value) next.1 next.2
      (fun v hv => weights v (List.mem_cons_of_mem value hv))
    simpa only [Binary32.sumFrom,List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm,
      Nat.add_left_comm] using tailProof

/-- Starting from zero, the actual ordered sum of any list of legally stored weights is finite
and satisfies the derived envelope without projecting the transient accumulator. -/
theorem legal_weight_sum_bound (rule : ValueRule) (weights : List (Weight rule)) :
    (Binary32.sumFrom .zero (weights.map Weight.value)).Finite ∧
      |numerical32 (Binary32.sumFrom .zero (weights.map Weight.value))| ≤
        predictionRadius weights.length := by
  have values : ∀ value ∈ weights.map Weight.value,
      value.Finite ∧ |numerical32 value| ≤ 101 := by
    intro value member
    obtain ⟨weight,_,rfl⟩ := List.mem_map.mp member
    exact weight_numerical_bound rule weight
  have sum := prediction_sumFrom_bound 0 .zero (weights.map Weight.value) (by decide)
    (by change |(0:ℚ)| ≤ (0:ℚ)*256; norm_num) values
  simpa only [List.length_map,Nat.zero_add] using sum

end AcornVerif.CurrentPrediction
