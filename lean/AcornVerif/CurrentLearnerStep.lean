import Acorn.SwiftTd
import AcornVerif.CurrentArithmetic
import AcornVerif.CurrentBackupBounds
import AcornVerif.CurrentCreditHorizon
import AcornVerif.CurrentDivision
import AcornVerif.CurrentLearner
import AcornVerif.CurrentLearnerArithmetic
import AcornVerif.CurrentPrediction
import AcornVerif.CurrentPreReward
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace AcornVerif.CurrentLearnerStep
open Acorn
open Float.Model (Format totalExponent UnpackedFloat)
open AcornVerif.CurrentArithmetic AcornVerif.CurrentBackupBounds AcornVerif.CurrentCreditHorizon
open AcornVerif.CurrentDivision AcornVerif.CurrentLearner AcornVerif.CurrentLearnerArithmetic
open AcornVerif.CurrentPrediction AcornVerif.CurrentPreReward

private theorem zero_add_inert_project (rule : ValueRule) {dw : Binary32} (hdw : Inert32 dw) :
    (Weight.project rule (Binary32.zero.add dw)).value = .zero := by
  rcases hdw with hz | hn
  · rcases isZero_bits dw hz with bits | bits
    · have hEq : dw = ⟨0⟩ := by obtain ⟨r⟩ := dw; simp only at bits; subst bits; rfl
      have hAdd : Binary32.zero.add ⟨0⟩ = .zero := by decide
      rw [hEq, hAdd, Weight.project_zero]
    · have hEq : dw = ⟨0x80000000⟩ := by
        obtain ⟨r⟩ := dw; simp only at bits; subst bits; rfl
      have hAdd : Binary32.zero.add ⟨0x80000000⟩ = .zero := by decide
      rw [hEq, hAdd, Weight.project_zero]
  · have hm : (Float32.ofBits dw.bits).toModel.unpack = .notANumber := by
      change UnpackedFloat.unpack Format.binary32
        (UnpackedFloat.pack Format.binary32
          (UnpackedFloat.unpack Format.binary32 dw.bits.toBitVec)) = _
      rw [CurrentPreReward.nan_unpack dw hn]
      rfl
    have hNaN : (Binary32.zero.add dw).isNaN = true := by
      change (⟨(Float32.Model.pack (UnpackedFloat.add Format.binary32
        (Float32.ofBits Binary32.zero.bits).toModel.unpack
        (Float32.ofBits dw.bits).toModel.unpack)).toBits⟩ : Binary32).isNaN = true
      rw [hm]
      decide
    rw [Weight.project_eq]
    change (Binary32.zero.add dw).project rule.domain.range.upper = .zero
    unfold Binary32.project
    simp only [hNaN, ↓reduceIte]

structure ExactZeroCalm {cfg : Acorn.Config} {dim : Dimension}
    (st : NumericState cfg dim) : Prop where
  calm : Calm st
  exactWeights : ∀ idx, (st.weights.get idx).value = .zero

theorem exactZeroCalm_initial {cfg : Acorn.Config} {dim : Dimension} :
    ExactZeroCalm (NumericState.initial cfg dim) where
  calm := Calm.initial
  exactWeights idx := by
    change ((Vector.replicate _ (Weight.project cfg.rule .zero)).get idx).value = .zero
    rw [get_replicate_vec, Weight.project_zero]

private theorem exactZeroCalm_firstLoop {cfg : Acorn.Config} {dim : Dimension}
    (st : NumericState cfg dim) (hEz : ExactZeroCalm st) (delta vDelta decay : Binary32)
    (hd : Inert32 delta) (hv : Inert32 vDelta) :
    ExactZeroCalm (st.learnFirstLoop cfg delta vDelta decay) := by
  refine ⟨hEz.calm.learnFirstLoop hd hv decay, ?_⟩
  have stepZero : ∀ (n : Nat) (cur : NumericState cfg dim) (work : Array (FeatIdx dim))
      (pos : Nat), work.size - pos = n → ExactZeroCalm cur →
      ∀ idx, ((NumericState.learnFirstLoopGo cfg delta vDelta decay cur work pos).weights.get
        idx).value = .zero := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro cur work pos hn hCur idx
      rw [NumericState.learnFirstLoopGo_def]
      split
      · rename_i hIn
        dsimp only
        let elem := cur.firstLoopElement work[pos] delta vDelta decay
        have hElemW : ∀ j, (elem.1.weights.get j).value = .zero := by
          intro j
          by_cases hj : work[pos] = j
          · subst j
            have hWUpd : (elem.1.weights.get work[pos]).value =
                (Weight.project cfg.rule ((cur.weights.get work[pos]).value.add
                  ((delta.mul (cur.transient.z.get work[pos]).value).sub
                    ((cur.transient.zDelta.get work[pos]).value.mul vDelta)))).value := by
              dsimp only [elem, NumericState.firstLoopElement]
              rw [get_set_vec]
              simp
            rw [hWUpd, hCur.exactWeights work[pos]]
            exact zero_add_inert_project cfg.rule
              ((Inert32.mulLeft hd _).sub (Inert32.mulRight _ hv))
          · exact (first_element_frame cur work[pos] j hj delta vDelta decay).1 ▸
              hCur.exactWeights j
        have hElemC : Calm elem.1 := hCur.calm.firstLoopElement work[pos] hd hv decay
        have hEz1 : ExactZeroCalm elem.1 := ⟨hElemC, hElemW⟩
        split
        · have hSz : (SwiftTd.swapRemove work pos hIn).size - pos < n := by
            simp only [SwiftTd.swapRemove, Array.size_pop, Array.size_set]
            omega
          exact ih _ hSz (elem.1.clearFeatureRegisters work[pos])
            (SwiftTd.swapRemove work pos hIn) pos rfl
            ⟨hElemC.clearFeatureRegisters work[pos], fun j => hElemW j⟩ idx
        · exact ih _ (by omega : work.size - (pos + 1) < n)
            elem.1 work (pos + 1) rfl hEz1 idx
      · exact hCur.exactWeights idx
  intro idx
  rw [NumericState.learnFirstLoop_def]
  exact stepZero st.transient.eligible.size
    { st with transient := { st.transient with eligible := #[] } }
    st.transient.eligible 0 (Nat.sub_zero _)
    ⟨⟨hEz.calm.weights, hEz.calm.deltaWeight, hEz.calm.vOld, hEz.calm.vDelta⟩,
      hEz.exactWeights⟩ idx

theorem exactZeroCalm_step {cfg : Acorn.Config} {dim : Dimension}
    (st : NumericState cfg dim) (hEz : ExactZeroCalm st)
    (features : SwiftTd.ActiveSet dim) {reward : Binary32} (hr : Inert32 reward) :
    ExactZeroCalm (st.step cfg features reward).1 := by
  refine ⟨hEz.calm.step features hr, ?_⟩
  intro idx
  rw [NumericState.step_def]
  dsimp only
  have hv := hEz.calm.predict features
  have hd : Inert32 ((reward.add (cfg.rule.gamma.mul (st.linearPrediction features))).sub
      st.transient.vOld) := (hr.add (Inert32.mulRight _ hv)).sub hEz.calm.vOld
  rw [second_loop_weights]
  exact (exactZeroCalm_firstLoop st hEz _ _ _ hd hEz.calm.vDelta).exactWeights idx

private theorem strict32_fits (value : UnpackedFloat) (exactValue : ℚ) (limit : Int)
    (normal : ModelNormalized Format.binary32 value) (range : limit ≤ 33)
    (bound : |exactValue| < (2 : ℚ) ^ limit)
    (error : |unpackedValue value - exactValue| ≤ (2 : ℚ) ^ (max (limit - 24) (-149)) / 2) :
    ModelFits Format.binary32 value := by
  have radiusBound : (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 ≤ 256 := by
    have power := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
      (show max (limit - 24) (-149) ≤ 9 by omega)
    norm_num at power
    linarith only [power]
  have exactBound : |exactValue| ≤ 8589934592 := by
    have power := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) range
    norm_num at power
    exact le_trans (le_of_lt bound) power
  apply model_fits_of_value_bound Format.binary32 value
    (model_normalized_finite _ _ normal) 34 (by decide)
  have triangle := abs_add_le (unpackedValue value - exactValue) exactValue
  rw [sub_add_cancel] at triangle
  norm_num
  linarith only [triangle, error, radiusBound, exactBound]

private theorem model_mul_dyadic_local_strict (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (limit : Int) (bound : |unpackedValue left * unpackedValue right| < (2 : ℚ) ^ limit) :
    ModelNormalized spec (UnpackedFloat.mul spec left right) ∧
      |unpackedValue (UnpackedFloat.mul spec left right) -
        unpackedValue left * unpackedValue right| ≤
        (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 := by
  have epsilon :
      (0 : ℚ) ≤ (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 :=
    div_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _)) (by norm_num)
  cases left with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign =>
    cases right <;> first | contradiction |
      simpa only [UnpackedFloat.mul, ModelNormalized, unpackedValue, zero_mul,
        sub_self, abs_zero, true_and] using epsilon
  | finite leftSign lm le lp =>
    cases right with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero rightSign =>
      simpa only [UnpackedFloat.mul, ModelNormalized, unpackedValue, mul_zero,
        sub_self, abs_zero, true_and] using epsilon
    | finite rightSign rm re rp =>
      have ready := model_product_exponent_ready spec lm rm le re leftSign rightSign lp rp
        leftNormal rightNormal
      simp only [UnpackedFloat.mul]
      rw [← model_round_without_padding spec _ _ _ ready]
      have heq : signCoefficient (leftSign * rightSign) * (lm * rm : Nat) * (2 : ℚ) ^ (le + re) =
          unpackedValue (.finite leftSign lm le lp) *
            unpackedValue (.finite rightSign rm re rp) := by
        rw [model_sign_product_value, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        simp only [unpackedValue, Nat.cast_mul]
        ring
      exact ⟨model_round_normalized _ _ _ _, by
        simpa only [heq] using model_round_uniform_error_strict spec (leftSign * rightSign)
          (lm * rm) (le + re) limit (by simpa only [heq] using bound)⟩

theorem binary32_mul_strict_error (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (limit : Int) (range : limit ≤ 33)
    (bound : |numerical32 left * numerical32 right| < (2 : ℚ) ^ limit) :
    (left.mul right).Finite ∧
      |numerical32 (left.mul right) - numerical32 left * numerical32 right| ≤
        (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_mul_dyadic_local_strict Format.binary32 (decoded32 left)
    (decoded32 right) ln rn limit (by simpa only [numerical32] using bound)
  have hFmt : max (limit - (Format.binary32.mantissaBits : Int)) Format.binary32.minExponent =
      max (limit - 24) (-149) := by
    simp only [Format.mantissaBits, Format.minExponent]
    norm_num
  have hErr : |unpackedValue (UnpackedFloat.mul Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left * numerical32 right| ≤
      (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 := by
    simpa only [numerical32, hFmt] using operation.2
  have decoded := mul32_decoded left right hl hr operation.1
    (strict32_fits _ _ limit operation.1 range bound hErr)
  refine ⟨?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using hErr

theorem binary32_sub_strict_error (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (limit : Int) (range : limit ≤ 33)
    (bound : |numerical32 left - numerical32 right| < (2 : ℚ) ^ limit) :
    (left.sub right).Finite ∧
      |numerical32 (left.sub right) - (numerical32 left - numerical32 right)| ≤
        (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 :=
  binary32_sub_finite_strict_error left right hl hr limit range bound

private def AccMatches (em : UnpackedFloat.ExtendedMantissa) (num den : Nat) : Prop :=
  em.mantissa = num / den ∧
  em.roundBit = decide (den ≤ 2 * (num % den)) ∧
  em.stickyBit = decide (0 < num % den ∧ 2 * (num % den) ≠ den)

private theorem accMatches_init (num den : Nat) (hDen : 0 < den) :
    AccMatches (UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy (num / den)
      (UnpackedFloat.accuracyOfFraction (num % den) den)) num den := by
  unfold AccMatches UnpackedFloat.accuracyOfFraction
  by_cases hr : num % den = 0
  · simp only [hr, ite_true, UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
      Nat.mul_zero, Nat.lt_irrefl, false_and, decide_false, and_true, true_and]
    exact (decide_eq_false (by omega)).symm
  · simp only [hr, ite_false]
    by_cases hlt : 2 * (num % den) < den
    · have hc : compare (2 * (num % den)) den = .lt := Nat.compare_eq_lt.mpr hlt
      rw [hc]
      simp only [UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy, true_and]
      exact ⟨(decide_eq_false (by omega)).symm, (decide_eq_true (by omega)).symm⟩
    · by_cases heq : 2 * (num % den) = den
      · have hc : compare (2 * (num % den)) den = .eq := Nat.compare_eq_eq.mpr heq
        rw [hc]
        simp only [UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy, true_and]
        exact ⟨(decide_eq_true (by omega)).symm, (decide_eq_false (by omega)).symm⟩
      · have hgt : den < 2 * (num % den) := by omega
        have hc : compare (2 * (num % den)) den = .gt := Nat.compare_eq_gt.mpr hgt
        rw [hc]
        simp only [UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy, true_and]
        exact ⟨(decide_eq_true (by omega)).symm, (decide_eq_true (by omega)).symm⟩

private theorem accMatches_shiftRightOne {em : UnpackedFloat.ExtendedMantissa} {num den : Nat}
    (hDen : 0 < den) (h : AccMatches em num den) :
    AccMatches em.shiftRightOne num (den * 2) := by
  have hMod : num % (den * 2) = num % den + den * (num / den % 2) := Nat.mod_mul
  have hrLt : num % den < den := Nat.mod_lt num hDen
  refine ⟨?_, ?_, ?_⟩
  · change em.mantissa / 2 = num / (den * 2)
    rw [h.1, Nat.div_div_eq_div_mul]
  · change (em.mantissa % 2 != 0) = decide (den * 2 ≤ 2 * (num % (den * 2)))
    rw [h.1, hMod]
    rcases Nat.mod_two_eq_zero_or_one (num / den) with hb | hb
    · rw [hb, Nat.mul_zero, Nat.add_zero]
      exact (decide_eq_false (by omega)).symm
    · rw [hb, Nat.mul_one]
      exact (decide_eq_true (by omega)).symm
  · change (em.roundBit || em.stickyBit) =
      decide (0 < num % (den * 2) ∧ 2 * (num % (den * 2)) ≠ den * 2)
    rw [h.2.1, h.2.2, hMod]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rcases Nat.mod_two_eq_zero_or_one (num / den) with hb | hb <;>
      simp only [hb, Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega

private theorem accMatches_shift (em : UnpackedFloat.ExtendedMantissa) (num den shift : Nat)
    (hDen : 0 < den) (h : AccMatches em num den) :
    AccMatches (em >>> shift) num (den * 2 ^ shift) := by
  induction shift with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one]
    exact h
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    exact accMatches_shiftRightOne (Nat.mul_pos hDen (Nat.two_pow_pos k)) ih

private theorem accMatches_rounded_dist {em : UnpackedFloat.ExtendedMantissa} {num den : Nat}
    (hDen : 0 < den) (h : AccMatches em num den) :
    |(em.roundedMantissa : ℚ) - (num : ℚ) / den| ≤ 1 / 2 := by
  have hDenQ : (0 : ℚ) < den := by exact_mod_cast hDen
  have hDecomp : (num : ℚ) / den = (num / den : Nat) + (num % den : Nat) / (den : ℚ) := by
    have hEq := Nat.div_add_mod' num den
    have hCast : (num : ℚ) = (num / den : Nat) * (den : ℚ) + (num % den : Nat) := by
      exact_mod_cast hEq.symm
    rw [hCast, add_div, mul_div_cancel_right₀ _ (ne_of_gt hDenQ)]
  have hrLt : num % den < den := Nat.mod_lt num hDen
  rw [hDecomp]
  rcases em with ⟨m, r, s⟩
  rcases h with ⟨hm, hr, hs⟩
  dsimp only at hm hr hs
  subst hm
  cases r <;> cases s
  · have hZero : num % den = 0 := by
      have h1 := of_decide_eq_false hr.symm
      have h2 := of_decide_eq_false hs.symm
      omega
    simp only [UnpackedFloat.ExtendedMantissa.roundedMantissa,
      UnpackedFloat.ExtendedMantissa.accuracy, UnpackedFloat.Accuracy.roundToNearestEven,
      hZero, Nat.cast_zero, zero_div, add_zero, sub_self, abs_zero]
    norm_num
  · have hLt : 2 * (num % den) < den := by
      have h1 := of_decide_eq_false hr.symm
      omega
    have hFrac : ((num % den : Nat) : ℚ) / den ≤ 1 / 2 := by
      rw [div_le_iff₀ hDenQ]
      have hCast : 2 * ((num % den : Nat) : ℚ) ≤ den := by
        exact_mod_cast (by omega : 2 * (num % den) ≤ den)
      linarith
    have hNonneg : (0 : ℚ) ≤ ((num % den : Nat) : ℚ) / den := by positivity
    simp only [UnpackedFloat.ExtendedMantissa.roundedMantissa,
      UnpackedFloat.ExtendedMantissa.accuracy, UnpackedFloat.Accuracy.roundToNearestEven]
    rw [abs_le]
    constructor <;> linarith
  · have hEq : 2 * (num % den) = den := by
      have h1 := of_decide_eq_true hr.symm
      have h2 := of_decide_eq_false hs.symm
      omega
    have hHalf : ((num % den : Nat) : ℚ) / den = 1 / 2 := by
      rw [div_eq_iff (ne_of_gt hDenQ)]
      have hCast : 2 * ((num % den : Nat) : ℚ) = den := by exact_mod_cast hEq
      linarith
    simp only [UnpackedFloat.ExtendedMantissa.roundedMantissa,
      UnpackedFloat.ExtendedMantissa.accuracy, UnpackedFloat.Accuracy.roundToNearestEven, hHalf]
    have hPar := Nat.mod_two_eq_zero_or_one (num / den)
    rcases hPar with hp | hp <;> simp only [hp, Nat.add_zero, Nat.cast_add, Nat.cast_one] <;>
      rw [abs_le] <;> constructor <;> linarith
  · have hGt : den < 2 * (num % den) := by
      have h1 := of_decide_eq_true hr.symm
      have h2 := of_decide_eq_true hs.symm
      omega
    have hFrac : (1 : ℚ) / 2 ≤ ((num % den : Nat) : ℚ) / den := by
      rw [le_div_iff₀ hDenQ]
      have hCast : (den : ℚ) ≤ 2 * (num % den : Nat) := by
        exact_mod_cast (by omega : den ≤ 2 * (num % den))
      linarith
    have hLe1 : ((num % den : Nat) : ℚ) / den ≤ 1 := by
      rw [div_le_one hDenQ]
      exact_mod_cast le_of_lt hrLt
    simp only [UnpackedFloat.ExtendedMantissa.roundedMantissa,
      UnpackedFloat.ExtendedMantissa.accuracy, UnpackedFloat.Accuracy.roundToNearestEven,
      Nat.cast_add, Nat.cast_one]
    rw [abs_le]
    constructor <;> linarith

private theorem model_divCore_strict_error (spec : Format) (sign : UnpackedFloat.Sign)
    (left right : Nat) (leftExponent rightExponent limit : Int)
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (bound :
      ((left : ℚ) / right) * (2 : ℚ) ^ (leftExponent - rightExponent) < (2 : ℚ) ^ limit) :
    let core := UnpackedFloat.divCore spec left leftExponent right rightExponent
    let result := UnpackedFloat.roundWithAccuracy spec sign core.1 core.2.1 core.2.2
    ModelNormalized spec result ∧
      |unpackedValue result - signCoefficient sign * ((left : ℚ) / right) *
        (2 : ℚ) ^ (leftExponent - rightExponent)| ≤
        (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 := by
  dsimp only
  let core := UnpackedFloat.divCore spec left leftExponent right rightExponent
  let ratio := ((left : ℚ) / right) * (2 : ℚ) ^ (leftExponent - rightExponent)
  let shift := (spec.targetExponent (totalExponent core.1 core.2.1) - core.2.1).toNat
  let radiusExponent := max (limit - spec.mantissaBits) spec.minExponent
  have bracket := model_divCore_bracket spec left right leftExponent rightExponent rightPositive
  have ready := model_divCore_ready spec left right leftExponent rightExponent
    leftPositive rightPositive
  change (if core.1 = 0 then core.2.1 ≤ spec.minExponent
    else core.2.1 ≤ spec.targetExponent (totalExponent core.1 core.2.1)) at ready
  have normal : ModelNormalized spec
      (UnpackedFloat.roundWithAccuracy spec sign core.1 core.2.1 core.2.2) := by
    by_cases zero : core.1 = 0
    · simp only [zero, ↓reduceIte] at ready
      rw [zero]
      exact model_round_accuracy_zero_normalized spec sign core.2.1 core.2.2 ready
    · simp only [zero, ↓reduceIte] at ready
      exact model_round_accuracy_normalized spec sign core.1 core.2.1 core.2.2 (by omega) ready
  have hExpLe : core.2.1 ≤ spec.targetExponent (totalExponent core.1 core.2.1) := by
    by_cases zero : core.1 = 0
    · simp only [zero, ↓reduceIte] at ready
      dsimp only [Format.targetExponent]
      omega
    · simp only [zero, ↓reduceIte] at ready
      exact ready
  have targetBound : spec.targetExponent (totalExponent core.1 core.2.1) ≤ radiusExponent := by
    by_cases zero : core.1 = 0
    · simp only [zero, ↓reduceIte] at ready
      have precision : 0 < spec.mantissaBits := by simp [Format.mantissaBits]
      simp only [zero, totalExponent, Nat.log2_zero, Nat.cast_zero, zero_add,
        Format.targetExponent]
      dsimp only [radiusExponent]
      omega
    · have lo := (model_positive_dyadic_window core.1 core.2.1 (by omega)).1
      have h := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp
        (lt_of_le_of_lt (le_trans lo bracket.2.2.1) bound)
      dsimp only [Format.targetExponent, radiusExponent]
      omega
  have outputBound : core.2.1 + shift ≤ radiusExponent := by
    dsimp only [shift]
    omega
  refine ⟨normal, ?_⟩
  let shiftAmt := (leftExponent - rightExponent - core.2.1).toNat
  let m := left * 2 ^ shiftAmt
  have hCore1 : core.1 = m / right := by
    dsimp only [core, m, shiftAmt, UnpackedFloat.divCore]
    rw [Nat.shiftLeft_eq]
  have hCoreAcc : core.2.2 = UnpackedFloat.accuracyOfFraction (m % right) right := by
    dsimp only [core, m, shiftAmt, UnpackedFloat.divCore]
    rw [Nat.shiftLeft_eq]
  let first := UnpackedFloat.shiftToTargetExponent spec core.1 core.2.1 core.2.2
  have hMatch : AccMatches first.1 m (right * 2 ^ shift) := by
    change AccMatches (UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy core.1 core.2.2 >>>
      shift) m (right * 2 ^ shift)
    rw [hCore1, hCoreAcc]
    exact accMatches_shift _ m right shift rightPositive (accMatches_init m right rightPositive)
  have hDist := accMatches_rounded_dist
    (Nat.mul_pos rightPositive (Nat.two_pow_pos shift)) hMatch
  have hRatio :
      ((m : ℚ) / (right * 2 ^ shift : Nat)) * (2 : ℚ) ^ (core.2.1 + shift) = ratio := by
    have hShifted : (shiftAmt : Int) + core.2.1 = leftExponent - rightExponent := by
      have hb1 := bracket.1
      dsimp only [shiftAmt, core] at *
      omega
    have hPow1 : (2 : ℚ) ^ shiftAmt * (2 : ℚ) ^ core.2.1 =
        (2 : ℚ) ^ (leftExponent - rightExponent) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), hShifted]
    have hPow2 : (2 : ℚ) ^ (core.2.1 + shift) = (2 : ℚ) ^ core.2.1 * (2 : ℚ) ^ shift := by
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    have hTwoNe : (2 : ℚ) ^ shift ≠ 0 := ne_of_gt (pow_pos (by norm_num) _)
    calc
      ((m : ℚ) / (right * 2 ^ shift : Nat)) * (2 : ℚ) ^ (core.2.1 + shift)
        = (((left : ℚ) * (2 : ℚ) ^ shiftAmt / (right : ℚ)) / (2 : ℚ) ^ shift) *
            (2 : ℚ) ^ shift * (2 : ℚ) ^ core.2.1 := by
          dsimp only [m]
          push_cast
          rw [hPow2, div_mul_eq_div_div]
          ring
      _ = ((left : ℚ) * (2 : ℚ) ^ shiftAmt / (right : ℚ)) * (2 : ℚ) ^ core.2.1 := by
          rw [div_mul_cancel₀ _ hTwoNe]
      _ = ((left : ℚ) / (right : ℚ)) * ((2 : ℚ) ^ shiftAmt * (2 : ℚ) ^ core.2.1) := by ring
      _ = ratio := by rw [hPow1]
  rw [model_round_accuracy_value]
  change |signCoefficient sign * (first.1.roundedMantissa : ℚ) * (2 : ℚ) ^ (core.2.1 + shift) -
      signCoefficient sign * ((left : ℚ) / right) *
      (2 : ℚ) ^ (leftExponent - rightExponent)| ≤
      (2 : ℚ) ^ radiusExponent / 2
  have hId : signCoefficient sign * ((left : ℚ) / right) *
      (2 : ℚ) ^ (leftExponent - rightExponent) =
      signCoefficient sign * ((m : ℚ) / (right * 2 ^ shift : Nat)) *
      (2 : ℚ) ^ (core.2.1 + shift) := by
    dsimp only [ratio] at hRatio
    rw [mul_assoc, ← hRatio]
    ring
  rw [hId]
  have hFactor :
      signCoefficient sign * (first.1.roundedMantissa : ℚ) * (2 : ℚ) ^ (core.2.1 + shift) -
      signCoefficient sign * ((m : ℚ) / (right * 2 ^ shift : Nat)) *
        (2 : ℚ) ^ (core.2.1 + shift) =
      signCoefficient sign *
        ((first.1.roundedMantissa : ℚ) - (m : ℚ) / (right * 2 ^ shift : Nat)) *
        (2 : ℚ) ^ (core.2.1 + shift) := by ring
  rw [hFactor, abs_mul, abs_mul]
  have hSign : |signCoefficient sign| = 1 := by
    cases sign <;> norm_num [signCoefficient]
  have hPos : (0 : ℚ) < (2 : ℚ) ^ (core.2.1 + shift) := zpow_pos (by norm_num) _
  rw [hSign, one_mul, abs_of_pos hPos]
  calc
    _ ≤ (1 / 2) * (2 : ℚ) ^ (core.2.1 + shift) :=
      mul_le_mul_of_nonneg_right hDist hPos.le
    _ = (2 : ℚ) ^ (core.2.1 + shift) / 2 := by ring
    _ ≤ (2 : ℚ) ^ radiusExponent / 2 :=
      div_le_div_of_nonneg_right
        (zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) outputBound) (by norm_num)

private theorem model_div_dyadic_local_strict (spec : Format) (left right : UnpackedFloat)
    (leftNormal : ModelNormalized spec left) (rightNormal : ModelNormalized spec right)
    (nonzero : unpackedValue right ≠ 0) (limit : Int)
    (bound : |unpackedValue left / unpackedValue right| < (2 : ℚ) ^ limit) :
    ModelNormalized spec (UnpackedFloat.div spec left right) ∧
      |unpackedValue (UnpackedFloat.div spec left right) -
        unpackedValue left / unpackedValue right| ≤
        (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 := by
  have epsilon :
      (0 : ℚ) ≤ (2 : ℚ) ^ (max (limit - spec.mantissaBits) spec.minExponent) / 2 :=
    div_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _)) (by norm_num)
  cases right with
  | notANumber => contradiction
  | infinity sign => contradiction
  | zero sign => exact False.elim (nonzero rfl)
  | finite rightSign rm re rp =>
    cases left with
    | notANumber => contradiction
    | infinity sign => contradiction
    | zero sign =>
      change True ∧ |(0 : ℚ) - 0 / (signCoefficient rightSign * rm * (2 : ℚ) ^ re)| ≤ _
      exact ⟨True.intro, by simpa only [zero_div, sub_self, abs_zero] using epsilon⟩
    | finite leftSign lm le lp =>
      have equality : unpackedValue (.finite leftSign lm le lp) /
          unpackedValue (.finite rightSign rm re rp) =
          signCoefficient (leftSign / rightSign) * ((lm : ℚ) / rm) * (2 : ℚ) ^ (le - re) :=
        model_signed_ratio leftSign rightSign lm rm le re
      have magnitude : |signCoefficient (leftSign / rightSign) * ((lm : ℚ) / rm) *
          (2 : ℚ) ^ (le - re)| = ((lm : ℚ) / rm) * (2 : ℚ) ^ (le - re) := by
        have positive := model_ratio_positive lm rm le re lp rp
        cases (leftSign / rightSign) <;>
          simp only [signCoefficient, one_mul, neg_mul, abs_neg]
        all_goals exact abs_of_pos positive
      have ratioBound : ((lm : ℚ) / rm) * (2 : ℚ) ^ (le - re) < (2 : ℚ) ^ limit := by
        simpa only [equality, magnitude] using bound
      have proof := model_divCore_strict_error spec (leftSign / rightSign) lm rm le re limit
        lp rp ratioBound
      simpa only [UnpackedFloat.div, equality] using proof

theorem binary32_div_strict_error (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (nz : numerical32 right ≠ 0) (limit : Int) (range : limit ≤ 33)
    (bound : |numerical32 left / numerical32 right| < (2 : ℚ) ^ limit) :
    (left.div right).Finite ∧
      |numerical32 (left.div right) - numerical32 left / numerical32 right| ≤
        (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_div_dyadic_local_strict Format.binary32 (decoded32 left)
    (decoded32 right) ln rn nz limit (by simpa only [numerical32] using bound)
  have hFmt : max (limit - (Format.binary32.mantissaBits : Int)) Format.binary32.minExponent =
      max (limit - 24) (-149) := by
    simp only [Format.mantissaBits, Format.minExponent]
    norm_num
  have hErr : |unpackedValue (UnpackedFloat.div Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left / numerical32 right| ≤
      (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 := by
    simpa only [numerical32, hFmt] using operation.2
  have decoded := div32_decoded left right hl hr operation.1
    (strict32_fits _ _ limit operation.1 range bound hErr)
  refine ⟨?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded] using hErr

private theorem sumFrom_error_aux (acc : Binary32) (hAcc : acc.Finite)
    (exactAcc M : ℚ) (used : Nat) (limit : Int) (hLim : limit ≤ 33) (xs : List Binary32)
    (hXs : ∀ x ∈ xs, x.Finite)
    (hErr : |numerical32 acc - exactAcc| ≤
      (used : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2))
    (hPref : ∀ p q, xs = p ++ q → p ≠ [] → |exactAcc + (p.map numerical32).sum| ≤ M)
    (hCap : M + ((used + xs.length : Nat) : ℚ) *
      ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) < (2 : ℚ) ^ limit) :
    (Binary32.sumFrom acc xs).Finite ∧
      |numerical32 (Binary32.sumFrom acc xs) - (exactAcc + (xs.map numerical32).sum)| ≤
        ((used + xs.length : Nat) : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
  let eps := (2 : ℚ) ^ (max (limit - 24) (-149)) / 2
  have hEpsNonneg : 0 ≤ eps := by positivity
  induction xs generalizing acc exactAcc used with
  | nil =>
    simpa [Binary32.sumFrom_def] using And.intro hAcc hErr
  | cons x rest ih =>
    have hX : x.Finite := hXs x List.mem_cons_self
    have hRest : ∀ y ∈ rest, y.Finite := fun y hy => hXs y (List.mem_cons_of_mem x hy)
    have hP1 := hPref [x] rest rfl (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hP1
    have hTriSum : |numerical32 acc + numerical32 x| < (2 : ℚ) ^ limit := by
      have h1 : numerical32 acc + numerical32 x =
          (numerical32 acc - exactAcc) + (exactAcc + numerical32 x) := by ring
      have h2 : |numerical32 acc + numerical32 x| ≤
          |numerical32 acc - exactAcc| + |exactAcc + numerical32 x| := by
        rw [h1]; exact abs_add_le _ _
      have hUsedLe : (used : ℚ) ≤ (used + (rest.length + 1) : Nat) := by
        exact_mod_cast (by omega : used ≤ used + (rest.length + 1))
      have hMul : (used : ℚ) * eps ≤ ((used + (rest.length + 1) : Nat) : ℚ) * eps :=
        mul_le_mul_of_nonneg_right hUsedLe hEpsNonneg
      dsimp only [eps] at hMul
      simp only [List.length_cons] at hCap
      linarith
    have hStep := binary32_add_finite_strict_error acc x hAcc hX limit hLim hTriSum
    have hErr' : |numerical32 (acc.add x) - (exactAcc + numerical32 x)| ≤
        ((used + 1 : Nat) : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
      have h1 : numerical32 (acc.add x) - (exactAcc + numerical32 x) =
          (numerical32 (acc.add x) - (numerical32 acc + numerical32 x)) +
          (numerical32 acc - exactAcc) := by ring
      have h2 : |numerical32 (acc.add x) - (exactAcc + numerical32 x)| ≤
          |numerical32 (acc.add x) - (numerical32 acc + numerical32 x)| +
          |numerical32 acc - exactAcc| := by
        rw [h1]; exact abs_add_le _ _
      have hEq : ((used + 1 : Nat) : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) =
          (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 +
          (used : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
        push_cast; ring
      linarith
    have hPref' : ∀ p q, rest = p ++ q → p ≠ [] →
        |(exactAcc + numerical32 x) + (p.map numerical32).sum| ≤ M := by
      intro p q hpq hpne
      have hp' := hPref (x :: p) q (by rw [hpq]; rfl) (by simp)
      simpa only [List.map_cons, List.sum_cons, add_assoc] using hp'
    have hCap' : M + ((used + 1 + rest.length : Nat) : ℚ) * eps < (2 : ℚ) ^ limit := by
      have hEqU : used + 1 + rest.length = used + (x :: rest).length := by
        simp [List.length_cons]; omega
      rw [hEqU]
      exact hCap
    have hIh := ih (acc.add x) hStep.1 (exactAcc + numerical32 x)
      (used + 1) hRest hErr' hPref' hCap'
    have hSumEq : Binary32.sumFrom acc (x :: rest) = Binary32.sumFrom (acc.add x) rest := by
      simp [Binary32.sumFrom_def]
    have hAddEq : exactAcc + ((x :: rest).map numerical32).sum =
        (exactAcc + numerical32 x) + (rest.map numerical32).sum := by
      simp [List.map_cons, List.sum_cons, add_assoc]
    have hLenEq : used + 1 + rest.length = used + (x :: rest).length := by
      simp [List.length_cons]; omega
    rw [hSumEq, hAddEq]
    rwa [hLenEq] at hIh

theorem sumFrom_error_bound (xs : List Binary32) (hXs : ∀ x ∈ xs, x.Finite)
    (M : ℚ) (limit : Int) (hLim : limit ≤ 33)
    (hPref : ∀ p q, xs = p ++ q → p ≠ [] → |(p.map numerical32).sum| ≤ M)
    (hCap : M + (xs.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) <
      (2 : ℚ) ^ limit) :
    (Binary32.sumFrom .zero xs).Finite ∧
      |numerical32 (Binary32.sumFrom .zero xs) - (xs.map numerical32).sum| ≤
        (xs.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
  have hZeroF : (Binary32.zero).Finite := by decide
  have hZeroE : numerical32 Binary32.zero = 0 := zero_value
  have hErr0 : |numerical32 Binary32.zero - 0| ≤
      ((0 : Nat) : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
    simp [hZeroE]
  have hPref0 : ∀ p q, xs = p ++ q → p ≠ [] → |0 + (p.map numerical32).sum| ≤ M := by
    intro p q hpq hne; rw [zero_add]; exact hPref p q hpq hne
  have hRes := sumFrom_error_aux Binary32.zero hZeroF 0 M 0 limit hLim xs hXs hErr0 hPref0
    (by simpa only [Nat.zero_add] using hCap)
  simpa only [zero_add, Nat.zero_add] using hRes

private theorem nonneg_prefix_bound (xs : List Binary32)
    (hXs : ∀ x ∈ xs, 0 ≤ numerical32 x) (M : ℚ) (hSum : (xs.map numerical32).sum ≤ M) :
    ∀ p q, xs = p ++ q → p ≠ [] → |(p.map numerical32).sum| ≤ M := by
  intro p q hpq _
  have hpN : 0 ≤ (p.map numerical32).sum := List.sum_nonneg (fun r hr => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact hXs y (hpq ▸ List.mem_append_left _ hy))
  have hqN : 0 ≤ (q.map numerical32).sum := List.sum_nonneg (fun r hr => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact hXs y (hpq ▸ List.mem_append_right _ hy))
  have hSplit : (xs.map numerical32).sum =
      (p.map numerical32).sum + (q.map numerical32).sum := by
    rw [hpq, List.map_append, List.sum_append]
  rw [abs_of_nonneg hpN]
  linarith

private theorem sumFrom_nonneg_sign (xs : List Binary32)
    (hXs : ∀ x ∈ xs, x.Finite ∧ 0 ≤ numerical32 x)
    (M : ℚ) (limit : Int) (hLim : limit ≤ 33) (hSum : (xs.map numerical32).sum ≤ M)
    (hCap : M + (xs.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) <
      (2 : ℚ) ^ limit) :
    0 ≤ numerical32 (Binary32.sumFrom .zero xs) := by
  induction xs using List.reverseRecOn with
  | nil =>
    rw [Binary32.sumFrom_def, List.foldl_nil, zero_value]
  | append_singleton init x ih =>
    have hX := hXs x (List.mem_append_right _ List.mem_cons_self)
    have hInitXs : ∀ y ∈ init, y.Finite ∧ 0 ≤ numerical32 y :=
      fun y hy => hXs y (List.mem_append_left _ hy)
    have hSumEq : ((init ++ [x]).map numerical32).sum =
        (init.map numerical32).sum + numerical32 x := by
      simp [List.map_append, List.sum_append]
    have hInitSum : (init.map numerical32).sum ≤ M := by linarith [hX.2]
    have hEpsN : (0 : ℚ) ≤ (2 : ℚ) ^ (max (limit - 24) (-149)) / 2 := by positivity
    have hLenLt : (init.length : ℚ) ≤ ((init ++ [x]).length : ℚ) := by
      simp only [List.length_append, List.length_singleton]
      exact_mod_cast (by omega : init.length ≤ init.length + 1)
    have hInitCap : M + (init.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) <
        (2 : ℚ) ^ limit := by
      have hMul := mul_le_mul_of_nonneg_right hLenLt hEpsN
      linarith
    have hInitNonneg := ih hInitXs hInitSum hInitCap
    have hInitErr := sumFrom_error_bound init (fun y hy => (hInitXs y hy).1)
      M limit hLim (nonneg_prefix_bound init (fun y hy => (hInitXs y hy).2) M hInitSum) hInitCap
    have hPowCap : (2 : ℚ) ^ limit ≤ 8589934592 := by
      have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hLim
      norm_num at hP
      exact hP
    have hBd : |numerical32 (Binary32.sumFrom .zero init) + numerical32 x| ≤ 8589934592 := by
      rw [abs_of_nonneg (add_nonneg hInitNonneg hX.2)]
      have hUp := (abs_le.mp hInitErr.2).2
      have hMul := mul_le_mul_of_nonneg_right hLenLt hEpsN
      linarith
    have hFold : Binary32.sumFrom .zero (init ++ [x]) =
        (Binary32.sumFrom .zero init).add x := by
      simp [Binary32.sumFrom_def, List.foldl_append]
    rw [hFold]
    exact rounded_nonneg (binary32_rounded_add _ x hInitErr.1 hX.1 hBd).2
      (add_nonneg hInitNonneg hX.2)

theorem sumFrom_nonneg_bound (xs : List Binary32)
    (hXs : ∀ x ∈ xs, x.Finite ∧ 0 ≤ numerical32 x)
    (M : ℚ) (limit : Int) (hLim : limit ≤ 33) (hSum : (xs.map numerical32).sum ≤ M)
    (hCap : M + (xs.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) <
      (2 : ℚ) ^ limit) :
    (Binary32.sumFrom .zero xs).Finite ∧ 0 ≤ numerical32 (Binary32.sumFrom .zero xs) ∧
      |numerical32 (Binary32.sumFrom .zero xs) - (xs.map numerical32).sum| ≤
        (xs.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
  have hErr := sumFrom_error_bound xs (fun x hx => (hXs x hx).1) M limit hLim
    (nonneg_prefix_bound xs (fun x hx => (hXs x hx).2) M hSum) hCap
  exact ⟨hErr.1, sumFrom_nonneg_sign xs hXs M limit hLim hSum hCap, hErr.2⟩

private theorem registers_fields_eq {cfg : Acorn.Config} {dim : Dimension}
    {s1 s2 : NumericState cfg dim} {idx : FeatIdx dim}
    (hEq : registers s1 idx = registers s2 idx) :
    (s1.transient.z.get idx).value = (s2.transient.z.get idx).value ∧
    (s1.transient.zDelta.get idx).value = (s2.transient.zDelta.get idx).value ∧
    (s1.transient.zBar.get idx).value = (s2.transient.zBar.get idx).value ∧
    (s1.transient.lastAlpha.get idx).value = (s2.transient.lastAlpha.get idx).value ∧
    (s1.transient.deltaWeight.get idx).value = (s2.transient.deltaWeight.get idx).value ∧
    (s1.transient.h.get idx).value = (s2.transient.h.get idx).value ∧
    (s1.transient.hOld.get idx).value = (s2.transient.hOld.get idx).value ∧
    (s1.transient.hTemp.get idx).value = (s2.transient.hTemp.get idx).value ∧
    (s1.transient.p.get idx).value = (s2.transient.p.get idx).value := by
  refine ⟨congrArg (·[0]) hEq, congrArg (·[1]) hEq, congrArg (·[2]) hEq,
    congrArg (·[3]) hEq, congrArg (·[4]) hEq, congrArg (·[5]) hEq,
    congrArg (·[6]) hEq, congrArg (·[7]) hEq, congrArg (·[8]) hEq⟩

private theorem ite_bounded_val {r : Interval32} (c : Bool) (a b : Bounded32 r) :
    (if c then a else b).value = if c then a.value else b.value := by
  cases c <;> rfl

private theorem weight_eq_of_val {rule : ValueRule} {a b : Weight rule}
    (h : a.value = b.value) : a = b := by
  cases a with
  | mk ab =>
    cases b with
    | mk bb =>
      cases ab
      cases bb
      cases h
      rfl

private theorem slotOf_eq_iff {cfg : Acorn.Config} {dim : Dimension}
    {s1 s2 : NumericState cfg dim} {idx : FeatIdx dim} :
    slotOf s1 idx = slotOf s2 idx ↔
      s1.weights.get idx = s2.weights.get idx ∧
      (s1.beta.get idx).value = (s2.beta.get idx).value ∧
      registers s1 idx = registers s2 idx := by
  constructor
  · intro h
    exact ⟨weight_eq_of_val (congrArg Slot.weight h),
      congrArg Slot.beta h, congrArg Slot.regs h⟩
  · rintro ⟨hw, hb, hr⟩
    simp only [slotOf, hw, hb, hr]

private theorem firstLoopElement_congr {cfg : Acorn.Config} {dim : Dimension}
    (s1 s2 : NumericState cfg dim) (idx : FeatIdx dim) (delta vDelta decay : Binary32)
    (hRails : s1.rails = s2.rails) (hSlot : slotOf s1 idx = slotOf s2 idx) :
    let r1 := s1.firstLoopElement idx delta vDelta decay
    let r2 := s2.firstLoopElement idx delta vDelta decay
    r1.2 = r2.2 ∧ slotOf r1.1 idx = slotOf r2.1 idx := by
  obtain ⟨hW, hB, hR⟩ := slotOf_eq_iff.mp hSlot
  have hF := registers_fields_eq hR
  have hSt : s1.stepSize idx = s2.stepSize idx := by
    rw [s1.stepSize_eq, s2.stepSize_eq]
    unfold LogStepSize.alpha
    rw [hB]
  have hSet : ∀ {α : Type} (v : Vector α dim.capacity) (x : α),
      (v.set idx.val x idx.isLt).get idx = x := by
    intro α v x
    rw [vector_get, Vector.getElem_set_self]
  refine ⟨?_, slotOf_eq_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · simp only [NumericState.firstLoopElement]
    rw [hF.1, hF.2.2.2.1]
  · simp only [NumericState.firstLoopElement, hSet]
    rw [hW, hF.1, hF.2.1]
  · simp only [NumericState.firstLoopElement, hSet, ite_bounded_val]
    rw [hW, hF.1, hF.2.1, hF.2.2.2.2.2.2.2.2, hB, hSt, hRails]
  · simp only [NumericState.firstLoopElement, registers, hSet, hW, hF.1, hF.2.1, hF.2.2.1,
      hF.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2]

private theorem firstLoop_go_lags {cfg : Acorn.Config} {dim : Dimension}
    (delta vDelta decay : Binary32) (state : NumericState cfg dim)
    (work : Array (FeatIdx dim)) (pos : Nat) :
    let res := NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos
    res.transient.vOld = state.transient.vOld ∧
    res.transient.vDelta = state.transient.vDelta := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct cfg delta vDelta decay with
  | case1 state work pos valid idx0 next equation ih =>
    dsimp only [idx0] at equation ih
    have hN : next = (state.firstLoopElement work[pos] delta vDelta decay).1 :=
      (congrArg Prod.fst equation).symm
    have hVO : (next.clearFeatureRegisters work[pos]).transient.vOld = state.transient.vOld := by
      rw [hN]; rfl
    have hVD : (next.clearFeatureRegisters work[pos]).transient.vDelta =
        state.transient.vDelta := by
      rw [hN]; rfl
    dsimp only
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simp only [equation, ite_true]
    exact ⟨ih.1.trans hVO, ih.2.trans hVD⟩
  | case2 state work pos valid idx0 next prune equation noPrune ih =>
    dsimp only [idx0] at equation ih
    have hN : next = (state.firstLoopElement work[pos] delta vDelta decay).1 :=
      (congrArg Prod.fst equation).symm
    have hVO : next.transient.vOld = state.transient.vOld := by rw [hN]; rfl
    have hVD : next.transient.vDelta = state.transient.vDelta := by rw [hN]; rfl
    dsimp only
    rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
    simp only [equation, ite_eq_right noPrune]
    exact ⟨ih.1.trans hVO, ih.2.trans hVD⟩
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    exact ⟨rfl, rfl⟩

theorem firstLoop_pointwise {cfg : Acorn.Config} {dim : Dimension}
    (st : NumericState cfg dim) (hUnique : st.transient.eligible.toList.Nodup)
    (delta vDelta decay : Binary32) :
    let next := st.learnFirstLoop cfg delta vDelta decay
    next.rails = st.rails ∧
    next.transient.vOld = st.transient.vOld ∧
    next.transient.vDelta = st.transient.vDelta ∧
    next.transient.eligible.toList.Nodup ∧
    (∀ idx, idx ∈ next.transient.eligible ↔
      idx ∈ st.transient.eligible ∧ (st.firstLoopElement idx delta vDelta decay).2 = false) ∧
    (∀ idx, idx ∉ st.transient.eligible →
      next.weights.get idx = st.weights.get idx ∧
      (next.beta.get idx).value = (st.beta.get idx).value ∧
      registers next idx = registers st idx) ∧
    (∀ idx, idx ∈ st.transient.eligible →
      let elem := st.firstLoopElement idx delta vDelta decay
      next.weights.get idx = elem.1.weights.get idx ∧
      (next.beta.get idx).value = (elem.1.beta.get idx).value ∧
      registers next idx =
        (if elem.2 then Vector.replicate 9 Binary32.zero else registers elem.1 idx)) := by
  let Pre : FeatIdx dim → Slot → Prop :=
    fun idx s => idx ∈ st.transient.eligible ∧ s = slotOf st idx
  let Post : FeatIdx dim → Slot → Prop :=
    fun idx s => idx ∈ st.transient.eligible ∧
      (st.firstLoopElement idx delta vDelta decay).2 = false ∧
      s = slotOf (st.firstLoopElement idx delta vDelta decay).1 idx
  let Out : FeatIdx dim → Slot → Prop :=
    fun idx s => (idx ∉ st.transient.eligible ∧ s = slotOf st idx) ∨
      (idx ∈ st.transient.eligible ∧ (st.firstLoopElement idx delta vDelta decay).2 = true ∧
        s = slotOf ((st.firstLoopElement idx delta vDelta decay).1.clearFeatureRegisters idx) idx)
  have hVisit : ∀ (current : NumericState cfg dim) (idx : FeatIdx dim),
      current.rails = st.rails → Pre idx (slotOf current idx) →
      ((current.firstLoopElement idx delta vDelta decay).2 = true →
        Out idx (slotOf ((current.firstLoopElement idx delta vDelta decay).1.clearFeatureRegisters
          idx) idx)) ∧
      ((current.firstLoopElement idx delta vDelta decay).2 = false →
        Post idx (slotOf (current.firstLoopElement idx delta vDelta decay).1 idx)) := by
    intro current idx hRails ⟨hMem, hSlot⟩
    have hCg := firstLoopElement_congr current st idx delta vDelta decay hRails hSlot
    refine ⟨fun hPr => Or.inr ⟨hMem, hCg.1.symm.trans hPr, ?_⟩,
      fun hKeep => ⟨hMem, hCg.1.symm.trans hKeep, hCg.2⟩⟩
    obtain ⟨hW, hB, _⟩ := slotOf_eq_iff.mp hCg.2
    apply slotOf_eq_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [(clear_feature_knowledge _ idx idx).1, (clear_feature_knowledge _ idx idx).1]
      exact hW
    · rw [(clear_feature_knowledge _ idx idx).2, (clear_feature_knowledge _ idx idx).2]
      exact hB
    · rw [clear_feature_self, clear_feature_self]
  have hSlots := first_loop_slots Pre Post Out delta vDelta decay st.rails hVisit st rfl hUnique
    (fun idx hMem => ⟨hMem, rfl⟩) (fun idx hNot => Or.inl ⟨hNot, rfl⟩)
  have hLags : (st.learnFirstLoop cfg delta vDelta decay).transient.vOld = st.transient.vOld ∧
      (st.learnFirstLoop cfg delta vDelta decay).transient.vDelta = st.transient.vDelta := by
    rw [NumericState.learnFirstLoop_def]
    exact firstLoop_go_lags delta vDelta decay
      { st with transient := { st.transient with eligible := #[] } } st.transient.eligible 0
  have hMemIff : ∀ idx, idx ∈ (st.learnFirstLoop cfg delta vDelta decay).transient.eligible ↔
      idx ∈ st.transient.eligible ∧
        (st.firstLoopElement idx delta vDelta decay).2 = false := by
    intro idx
    constructor
    · intro hIn
      have hP := hSlots.2.2.1 idx hIn
      exact ⟨hP.1, hP.2.1⟩
    · rintro ⟨hIn, hKeep⟩
      by_contra hOut
      rcases hSlots.2.2.2 idx hOut with ⟨hNot, _⟩ | ⟨_, hPr, _⟩
      · exact hNot hIn
      · rw [hKeep] at hPr
        contradiction
  refine ⟨hSlots.1, hLags.1, hLags.2, hSlots.2.1, hMemIff, ?_, ?_⟩
  · intro idx hNot
    have hOut : idx ∉ (st.learnFirstLoop cfg delta vDelta decay).transient.eligible :=
      fun hIn => hNot ((hMemIff idx).mp hIn).1
    rcases hSlots.2.2.2 idx hOut with ⟨_, hEq⟩ | ⟨hIn, _⟩
    · exact slotOf_eq_iff.mp hEq
    · exact absurd hIn hNot
  · intro idx hMem
    dsimp only
    cases hPr : (st.firstLoopElement idx delta vDelta decay).2
    · have hIn := (hMemIff idx).mpr ⟨hMem, hPr⟩
      simpa only [Bool.false_eq_true, ite_false] using slotOf_eq_iff.mp (hSlots.2.2.1 idx hIn).2.2
    · have hOut : idx ∉ (st.learnFirstLoop cfg delta vDelta decay).transient.eligible := by
        intro hIn
        have hF := ((hMemIff idx).mp hIn).2
        rw [hPr] at hF
        contradiction
      rcases hSlots.2.2.2 idx hOut with ⟨hNot, _⟩ | ⟨_, _, hEq⟩
      · exact absurd hMem hNot
      · obtain ⟨hW, hB, hR⟩ := slotOf_eq_iff.mp hEq
        rw [(clear_feature_knowledge _ idx idx).1] at hW
        rw [(clear_feature_knowledge _ idx idx).2] at hB
        rw [clear_feature_self] at hR
        simpa only [ite_true] using And.intro hW (And.intro hB hR)

private theorem logStep_project_rails_eq {cfg : Acorn.Config} {r1 r2 : StepSizeRails cfg}
    (hr : r1 = r2) (x : Binary32) :
    (LogStepSize.project r1 x).value = (LogStepSize.project r2 x).value := by
  subst hr; rfl

private theorem secondLoopElement_congr {cfg : Acorn.Config} {dim : Dimension}
    (overshoot : Bool) (e t : Binary32) (s1 s2 : NumericState cfg dim)
    (v1 v2 : Binary32) (idx : FeatIdx dim)
    (hRails : s1.rails = s2.rails) (hSlot : slotOf s1 idx = slotOf s2 idx) :
    slotOf (NumericState.secondLoopElement cfg overshoot e t s1 v1 idx).1 idx =
      slotOf (NumericState.secondLoopElement cfg overshoot e t s2 v2 idx).1 idx := by
  obtain ⟨hW, hB, hR⟩ := slotOf_eq_iff.mp hSlot
  have hF := registers_fields_eq hR
  have hSet : ∀ {α : Type} (v : Vector α dim.capacity) (x : α),
      (v.set idx.val x idx.isLt).get idx = x := by
    intro α v x
    rw [vector_get, Vector.getElem_set_self]
  have hA : (s1.beta.get idx).alpha = (s2.beta.get idx).alpha := by
    unfold LogStepSize.alpha
    rw [hB]
  apply slotOf_eq_iff.mpr
  cases overshoot
  · simp only [NumericState.secondLoopElement, NumericState.secondLoopElementAt, registers, hSet,
      hW, hB, hA, hF.1, hF.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1,
      hF.2.2.2.2.2.2.2.2, Bool.false_eq_true, ite_false, and_self]
  · simp only [NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      NumericState.writeBetaValue, registers, hSet, hW, hB, hA, hRails, hF.1, hF.2.2.1,
      hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1,
      hF.2.2.2.2.2.2.2.2, ite_true]
    exact ⟨trivial, logStep_project_rails_eq hRails _, trivial⟩

private theorem second_fold_lags {cfg : Acorn.Config} {dim : Dimension}
    (overshoot : Bool) (e t : Binary32) (indices : List (FeatIdx dim))
    (s : NumericState cfg dim) (vd : Binary32) :
    let res := (indices.foldl (fun p i =>
      NumericState.secondLoopElement cfg overshoot e t p.1 p.2 i) (s, vd)).1
    res.transient.vOld = s.transient.vOld ∧ res.transient.vDelta = s.transient.vDelta := by
  induction indices generalizing s vd with
  | nil => exact ⟨rfl, rfl⟩
  | cons a rest ih =>
    rw [List.foldl_cons]
    have hIh := ih (NumericState.secondLoopElement cfg overshoot e t s vd a).1
      (NumericState.secondLoopElement cfg overshoot e t s vd a).2
    cases overshoot <;> exact hIh

private theorem second_fold_vDelta {cfg : Acorn.Config} {dim : Dimension}
    (overshoot : Bool) (e t : Binary32) (indices : List (FeatIdx dim))
    (s : NumericState cfg dim) (vd : Binary32) :
    (indices.foldl (fun p i =>
      NumericState.secondLoopElement cfg overshoot e t p.1 p.2 i) (s, vd)).2 =
      Binary32.sumFrom vd (indices.map fun idx => (s.transient.deltaWeight.get idx).value) := by
  induction indices generalizing s vd with
  | nil => rfl
  | cons a rest ih =>
    rw [List.foldl_cons, List.map_cons]
    have hDW : ∀ idx : FeatIdx dim,
        ((NumericState.secondLoopElement cfg overshoot e t s vd a).1.transient.deltaWeight.get
          idx).value = (s.transient.deltaWeight.get idx).value := by
      intro idx
      cases overshoot <;> rfl
    have hMap : rest.map (fun idx =>
        ((NumericState.secondLoopElement cfg overshoot e t s vd a).1.transient.deltaWeight.get
          idx).value) = rest.map (fun idx => (s.transient.deltaWeight.get idx).value) :=
      List.map_congr_left (fun idx _ => hDW idx)
    rw [ih, hMap]
    have hV2 : (NumericState.secondLoopElement cfg overshoot e t s vd a).2 =
        vd.add (s.transient.deltaWeight.get a).value := by
      cases overshoot <;> rfl
    rw [hV2]
    rfl

theorem secondLoop_pointwise {cfg : Acorn.Config} {dim : Dimension}
    (st : NumericState cfg dim) (features : SwiftTd.ActiveSet dim) (vDelta : Binary32) :
    let rate := Binary32.sumFrom .zero (features.indices.map fun idx => (st.beta.get idx).alpha)
    let overshoot := cfg.eta.less rate
    let e := if overshoot then rate else cfg.eta
    let t := Binary32.sumFrom .zero
      (features.indices.map fun idx => (st.transient.z.get idx).value)
    let out := st.learnSecondLoop cfg features vDelta
    out.2 = Binary32.sumFrom vDelta
      (features.indices.map fun idx => (st.transient.deltaWeight.get idx).value) ∧
    out.1.rails = st.rails ∧
    out.1.transient.vOld = st.transient.vOld ∧
    out.1.transient.vDelta = st.transient.vDelta ∧
    out.1.transient.eligible.toList = st.transient.eligible.toList ++
      features.indices.filter (fun idx => (st.transient.z.get idx).value.isZero) ∧
    (∀ idx, idx ∉ features.indices →
      out.1.weights.get idx = st.weights.get idx ∧
      (out.1.beta.get idx).value = (st.beta.get idx).value ∧
      registers out.1 idx = registers st idx) ∧
    (∀ idx, idx ∈ features.indices →
      let step1 := (NumericState.secondLoopElement cfg overshoot e t st .zero idx).1
      out.1.weights.get idx = step1.weights.get idx ∧
      (out.1.beta.get idx).value = (step1.beta.get idx).value ∧
      registers out.1 idx = registers step1 idx) := by
  dsimp only
  let rate := Binary32.sumFrom .zero (features.indices.map fun idx => (st.beta.get idx).alpha)
  let overshoot := cfg.eta.less rate
  let e := if overshoot then rate else cfg.eta
  let t := Binary32.sumFrom .zero
    (features.indices.map fun idx => (st.transient.z.get idx).value)
  let Pre : FeatIdx dim → Slot → Prop := fun idx s => s = slotOf st idx
  let Post : FeatIdx dim → Slot → Prop :=
    fun idx s => s = slotOf (NumericState.secondLoopElement cfg overshoot e t st .zero idx).1 idx
  have hSlots := second_loop_slots Pre Post (fun _ => True) st.rails st features vDelta
    (fun current vd' idx hRails _ hSlot =>
      ⟨secondLoopElement_congr overshoot e t current st vd' .zero idx hRails hSlot, trivial⟩)
    rfl trivial (fun _ _ => rfl)
  have hLags : (st.learnSecondLoop cfg features vDelta).1.transient.vOld = st.transient.vOld ∧
      (st.learnSecondLoop cfg features vDelta).1.transient.vDelta = st.transient.vDelta := by
    rw [NumericState.learnSecondLoop_eq_sumFrom]
    exact second_fold_lags overshoot e t features.indices st vDelta
  have hVd : (st.learnSecondLoop cfg features vDelta).2 = Binary32.sumFrom vDelta
      (features.indices.map fun idx => (st.transient.deltaWeight.get idx).value) := by
    rw [NumericState.learnSecondLoop_eq_sumFrom]
    exact second_fold_vDelta overshoot e t features.indices st vDelta
  refine ⟨hVd, hSlots.1, hLags.1, hLags.2, second_loop_eligible st features vDelta, ?_, ?_⟩
  · intro idx hAbs
    exact slotOf_eq_iff.mp (hSlots.2.2.2 idx hAbs)
  · intro idx hMem
    exact slotOf_eq_iff.mp (hSlots.2.2.1 idx hMem)

end AcornVerif.CurrentLearnerStep
