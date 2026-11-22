import Acorn.SwiftTd
import AcornVerif.CurrentArithmetic
import AcornVerif.CurrentBackupBounds
import AcornVerif.CurrentCreditHorizon
import AcornVerif.CurrentDivision
import AcornVerif.CurrentLearner
import AcornVerif.CurrentLearnerArithmetic
import AcornVerif.CurrentModelArithmetic
import AcornVerif.CurrentOperations
import AcornVerif.CurrentOrder
import AcornVerif.CurrentPrediction
import AcornVerif.CurrentPreReward
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace AcornVerif.CurrentLearnerStep
open Acorn
open Float.Model (Format UnpackedFloat)
open AcornVerif.CurrentArithmetic AcornVerif.CurrentBackupBounds AcornVerif.CurrentCreditHorizon
open AcornVerif.CurrentDivision AcornVerif.CurrentLearner AcornVerif.CurrentLearnerArithmetic
open AcornVerif.CurrentModelArithmetic AcornVerif.CurrentOperations AcornVerif.CurrentOrder
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

private theorem exactZeroCalm_secondLoop {cfg : Acorn.Config} {dim : Dimension}
    (st : NumericState cfg dim) (hEz : ExactZeroCalm st)
    (features : SwiftTd.ActiveSet dim) (vDelta : Binary32) :
    ∀ idx, ((st.learnSecondLoop cfg features vDelta).1.weights.get idx).value = .zero := by
  intro idx
  rw [NumericState.learnSecondLoop_eq_sumFrom]
  have hFold : ∀ (overshoot : Bool) (e t : Binary32) (indices : List (FeatIdx dim))
      (s : NumericState cfg dim) (vd : Binary32),
      (∀ j, (s.weights.get j).value = .zero) →
      ∀ j, ((indices.foldl (fun p i =>
        NumericState.secondLoopElement cfg overshoot e t p.1 p.2 i) (s, vd)).1.weights.get
          j).value = .zero := by
    intro overshoot e t indices
    induction indices with
    | nil => intro s vd hs j; exact hs j
    | cons h tail ih =>
      intro s vd hs j
      apply ih
      intro k
      by_cases hk : h = k
      · subst k
        cases overshoot <;> exact hs h
      · exact (second_element_frame s h k hk overshoot e t vd).1 ▸ hs k
  exact hFold _ _ _ features.indices st vDelta hEz.exactWeights idx

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
  exact exactZeroCalm_secondLoop _ (exactZeroCalm_firstLoop st hEz _ _ _ hd hEz.calm.vDelta)
    features .zero idx

theorem binary32_mul_strict_error (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (limit : Int) (range : limit ≤ 9)
    (bound : |numerical32 left * numerical32 right| ≤ (2 : ℚ) ^ limit) :
    (left.mul right).Finite ∧
      |numerical32 (left.mul right) - numerical32 left * numerical32 right| ≤
        (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) / 2 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_mul_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn limit (by simpa only [numerical32] using bound)
  have hPowLim : (2 : ℚ) ^ limit ≤ 512 := by
    have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) range
    norm_num at hP; exact hP
  have hEps : (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) / 2 ≤ 1 := by
    have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
      (show max (limit + 1 - 24) (-149) ≤ 0 by omega)
    rw [zpow_zero] at hP; linarith
  have err1 : |unpackedValue (UnpackedFloat.mul Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left * numerical32 right| ≤ 1 := by
    apply le_trans operation.2
    change (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) / 2 ≤ 1
    exact hEps
  have decoded := mul32_decoded left right hl hr operation.1
    (small_fits _ _ operation.1 (le_trans bound hPowLim) err1)
  have hFmt : max (limit + 1 - (Format.binary32.mantissaBits : Int))
      Format.binary32.minExponent = max (limit + 1 - 24) (-149) := by
    simp only [Format.mantissaBits, Format.minExponent]
    norm_num
  refine ⟨?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded, hFmt] using operation.2

theorem binary32_sub_strict_error (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (limit : Int) (range : limit ≤ 9)
    (bound : |numerical32 left - numerical32 right| ≤ (2 : ℚ) ^ limit) :
    (left.sub right).Finite ∧
      |numerical32 (left.sub right) - (numerical32 left - numerical32 right)| ≤
        (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) / 2 := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_sub_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn limit (by simpa only [numerical32] using bound)
  have hPowLim : (2 : ℚ) ^ limit ≤ 512 := by
    have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) range
    norm_num at hP; exact hP
  have hEps : (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) / 2 ≤ 1 := by
    have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
      (show max (limit + 1 - 24) (-149) ≤ 0 by omega)
    rw [zpow_zero] at hP; linarith
  have err1 : |unpackedValue (UnpackedFloat.sub Format.binary32
      (decoded32 left) (decoded32 right)) - (numerical32 left - numerical32 right)| ≤ 1 := by
    apply le_trans operation.2
    change (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) / 2 ≤ 1
    exact hEps
  have decoded : decoded32 (left.sub right) =
      UnpackedFloat.sub Format.binary32 (decoded32 left) (decoded32 right) := by
    change UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.sub Format.binary32 (Float32.Model.ofBits left.bits).unpack
        (Float32.Model.ofBits right.bits).unpack)) = _
    rw [model_ofBits32_decoded left hl, model_ofBits32_decoded right hr]
    exact model_unpack_pack_normalized _ _ operation.1
      (small_fits _ _ operation.1 (le_trans bound hPowLim) err1)
  have hFmt : max (limit + 1 - (Format.binary32.mantissaBits : Int))
      Format.binary32.minExponent = max (limit + 1 - 24) (-149) := by
    simp only [Format.mantissaBits, Format.minExponent]
    norm_num
  refine ⟨?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded, hFmt] using operation.2

theorem binary32_div_strict_error (left right : Binary32) (hl : left.Finite) (hr : right.Finite)
    (nz : numerical32 right ≠ 0) (limit : Int) (range : limit ≤ 1)
    (bound : |numerical32 left / numerical32 right| ≤ (2 : ℚ) ^ limit) :
    (left.div right).Finite ∧
      |numerical32 (left.div right) - numerical32 left / numerical32 right| ≤
        2 * (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) := by
  have ln := (model_unpack_format Format.binary32 (by decide) left.bits.toBitVec
    ((model_decoded32_finite left).mpr hl)).1
  have rn := (model_unpack_format Format.binary32 (by decide) right.bits.toBitVec
    ((model_decoded32_finite right).mpr hr)).1
  have operation := model_div_dyadic_local Format.binary32 (decoded32 left) (decoded32 right)
    ln rn nz limit (by simpa only [numerical32] using bound)
  have hPowLim : (2 : ℚ) ^ limit ≤ 4 := by
    have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega : limit ≤ 2)
    norm_num at hP; exact hP
  have hEps : 2 * (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) ≤ 1 := by
    have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
      (show max (limit + 1 - 24) (-149) ≤ -2 by omega)
    norm_num at hP; linarith
  have err1 : |unpackedValue (UnpackedFloat.div Format.binary32
      (decoded32 left) (decoded32 right)) - numerical32 left / numerical32 right| ≤ 1 := by
    apply le_trans operation.2
    change 2 * (2 : ℚ) ^ (max (limit + 1 - 24) (-149)) ≤ 1
    exact hEps
  have decoded := div32_decoded left right hl hr operation.1
    (local32_fits _ _ operation.1 (le_trans bound hPowLim) err1)
  have hFmt : max (limit + 1 - (Format.binary32.mantissaBits : Int))
      Format.binary32.minExponent = max (limit + 1 - 24) (-149) := by
    simp only [Format.mantissaBits, Format.minExponent]
    norm_num
  refine ⟨?_, ?_⟩
  · apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  · simpa only [numerical32, decoded, hFmt] using operation.2

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

private theorem add32_ge_left (a b : Binary32) (ha : a.Finite) (hb : b.Finite)
    (hpb : 0 ≤ numerical32 b) (hBd : |numerical32 a + numerical32 b| ≤ 8589934592) :
    (a.add b).Finite ∧ numerical32 a ≤ numerical32 (a.add b) := by
  have ha1 := binary32_rounded_add a b ha hb hBd
  exact ⟨ha1.1, Rounded.mono (binary32_rounded_exact a ha) ha1.2 (le_add_of_nonneg_right hpb)⟩

private theorem sumFrom_nonneg_aux (acc : Binary32) (hAccF : acc.Finite)
    (hAccN : 0 ≤ numerical32 acc)
    (exactAcc M : ℚ) (used : Nat) (limit : Int) (hLim : limit ≤ 33) (xs : List Binary32)
    (hXs : ∀ x ∈ xs, x.Finite ∧ 0 ≤ numerical32 x)
    (hExN : 0 ≤ exactAcc)
    (hErr : |numerical32 acc - exactAcc| ≤
      (used : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2))
    (hSum : exactAcc + (xs.map numerical32).sum ≤ M)
    (hCap : M + ((used + xs.length : Nat) : ℚ) *
      ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) < (2 : ℚ) ^ limit) :
    (Binary32.sumFrom acc xs).Finite ∧ 0 ≤ numerical32 (Binary32.sumFrom acc xs) ∧
      |numerical32 (Binary32.sumFrom acc xs) - (exactAcc + (xs.map numerical32).sum)| ≤
        ((used + xs.length : Nat) : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
  let eps := (2 : ℚ) ^ (max (limit - 24) (-149)) / 2
  have hEpsNonneg : 0 ≤ eps := by positivity
  induction xs generalizing acc exactAcc used with
  | nil =>
    simpa [Binary32.sumFrom_def] using ⟨hAccF, hAccN, hErr⟩
  | cons x rest ih =>
    have hX := hXs x List.mem_cons_self
    have hRest : ∀ y ∈ rest, y.Finite ∧ 0 ≤ numerical32 y :=
      fun y hy => hXs y (List.mem_cons_of_mem x hy)
    have hRestN : 0 ≤ (rest.map numerical32).sum := List.sum_nonneg (fun q hq => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
      exact (hRest y hy).2)
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hSum hCap
    have hUsedLe : (used : ℚ) ≤ (used + (rest.length + 1) : Nat) := by
      exact_mod_cast (by omega : used ≤ used + (rest.length + 1))
    have hMul : (used : ℚ) * eps ≤ ((used + (rest.length + 1) : Nat) : ℚ) * eps :=
      mul_le_mul_of_nonneg_right hUsedLe hEpsNonneg
    dsimp only [eps] at hMul
    have hTri : |numerical32 acc + numerical32 x| < (2 : ℚ) ^ limit := by
      rw [abs_of_nonneg (add_nonneg hAccN hX.2)]
      have hUp := (abs_le.mp hErr).2
      linarith
    have hStep := binary32_add_finite_strict_error acc x hAccF hX.1 limit hLim hTri
    have hPowCap : (2 : ℚ) ^ limit ≤ 8589934592 := by
      have hP := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hLim
      norm_num at hP; exact hP
    have hGe := add32_ge_left acc x hAccF hX.1 hX.2
      (le_of_lt (lt_of_lt_of_le hTri hPowCap))
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
    have hCap' : M + ((used + 1 + rest.length : Nat) : ℚ) * eps < (2 : ℚ) ^ limit := by
      have hEqU : used + 1 + rest.length = used + (rest.length + 1) := by omega
      rwa [hEqU]
    have hIh := ih (acc.add x) hStep.1 (le_trans hAccN hGe.2) (exactAcc + numerical32 x)
      (used + 1) hRest (add_nonneg hExN hX.2) hErr' (by linarith) hCap'
    have hSumEq : Binary32.sumFrom acc (x :: rest) = Binary32.sumFrom (acc.add x) rest := by
      simp [Binary32.sumFrom_def]
    have hLenEq : used + 1 + rest.length = used + (x :: rest).length := by
      simp [List.length_cons]; omega
    have hAddEq : exactAcc + (numerical32 x + (rest.map numerical32).sum) =
        (exactAcc + numerical32 x) + (rest.map numerical32).sum := by ring
    simp only [List.map_cons, List.sum_cons]
    rw [hSumEq, hAddEq]
    rwa [hLenEq] at hIh

theorem sumFrom_nonneg_bound (xs : List Binary32)
    (hXs : ∀ x ∈ xs, x.Finite ∧ 0 ≤ numerical32 x)
    (M : ℚ) (limit : Int) (hLim : limit ≤ 33) (hSum : (xs.map numerical32).sum ≤ M)
    (hCap : M + (xs.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) <
      (2 : ℚ) ^ limit) :
    (Binary32.sumFrom .zero xs).Finite ∧ 0 ≤ numerical32 (Binary32.sumFrom .zero xs) ∧
      |numerical32 (Binary32.sumFrom .zero xs) - (xs.map numerical32).sum| ≤
        (xs.length : ℚ) * ((2 : ℚ) ^ (max (limit - 24) (-149)) / 2) := by
  have hRes := sumFrom_nonneg_aux .zero (by decide) (le_of_eq zero_value.symm) 0 M 0 limit hLim
    xs hXs le_rfl (by simp [zero_value]) (by linarith) (by simpa using hCap)
  simpa only [zero_add, Nat.zero_add] using hRes

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

private theorem firstLoopElement_congr {cfg : Acorn.Config} {dim : Dimension}
    (s1 s2 : NumericState cfg dim) (idx : FeatIdx dim) (delta vDelta decay : Binary32)
    (hRails : s1.rails = s2.rails)
    (hW : s1.weights.get idx = s2.weights.get idx)
    (hB : (s1.beta.get idx).value = (s2.beta.get idx).value)
    (hR : registers s1 idx = registers s2 idx) :
    let r1 := s1.firstLoopElement idx delta vDelta decay
    let r2 := s2.firstLoopElement idx delta vDelta decay
    r1.2 = r2.2 ∧
    r1.1.weights.get idx = r2.1.weights.get idx ∧
    (r1.1.beta.get idx).value = (r2.1.beta.get idx).value ∧
    registers r1.1 idx = registers r2.1 idx := by
  have hF := registers_fields_eq hR
  have hSt : s1.stepSize idx = s2.stepSize idx := by
    rw [s1.stepSize_eq, s2.stepSize_eq]
    unfold LogStepSize.alpha
    rw [hB]
  have hSet : ∀ {α : Type} (v : Vector α dim.capacity) (x : α),
      (v.set idx.val x idx.isLt).get idx = x := by
    intro α v x
    rw [vector_get, Vector.getElem_set_self]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [NumericState.firstLoopElement]
    rw [hF.1, hF.2.2.2.1]
  · simp only [NumericState.firstLoopElement, hSet]
    rw [hW, hF.1, hF.2.1]
  · simp only [NumericState.firstLoopElement, hSet]
    rw [ite_bounded_val, ite_bounded_val, hW, hF.1, hF.2.1, hF.2.2.2.2.2.2.2.2, hB, hSt, hRails]
  · simp only [NumericState.firstLoopElement, registers, hSet, hW, hF.1, hF.2.1, hF.2.2.1,
      hF.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2]

private def hasTail {dim : Dimension} (work : Array (FeatIdx dim)) (pos : Nat)
    (idx : FeatIdx dim) : Prop :=
  ∃ j, pos ≤ j ∧ ∃ hj : j < work.size, work[j] = idx

private theorem firstLoop_go_absent {cfg : Acorn.Config} {dim : Dimension}
    (delta vDelta decay : Binary32) (state : NumericState cfg dim)
    (work : Array (FeatIdx dim)) (pos : Nat) (idx : FeatIdx dim)
    (hAbs : ¬ hasTail work pos idx) :
    let res := NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos
    res.weights.get idx = state.weights.get idx ∧
    (res.beta.get idx).value = (state.beta.get idx).value ∧
    registers res idx = registers state idx ∧
    res.rails = state.rails ∧
    res.transient.vOld = state.transient.vOld ∧
    res.transient.vDelta = state.transient.vDelta := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct cfg delta vDelta decay with
  | case1 state work pos valid idx0 next equation ih =>
    dsimp only [idx0] at equation ih
    have hN : next = (state.firstLoopElement work[pos] delta vDelta decay).1 :=
      (congrArg Prod.fst equation).symm
    have hNe : work[pos] ≠ idx := fun hEq => hAbs ⟨pos, le_rfl, valid, hEq⟩
    have hAbs' : ¬ hasTail (SwiftTd.swapRemove work pos valid) pos idx := by
      intro ⟨j, hle, hj, heq⟩
      have hjSz : j < work.size - 1 := by simpa [swap_remove_size] using hj
      rw [swap_remove_get] at heq
      split at heq
      · exact hAbs ⟨work.size - 1, by omega, by omega, heq⟩
      · exact hAbs ⟨j, hle, by omega, heq⟩
    have hIh := ih hAbs'
    have hFr := first_element_frame state work[pos] idx hNe delta vDelta decay
    have hRls : (next.clearFeatureRegisters work[pos]).rails = state.rails := by
      rw [hN]; rfl
    have hVO : (next.clearFeatureRegisters work[pos]).transient.vOld = state.transient.vOld := by
      rw [hN]; rfl
    have hVD : (next.clearFeatureRegisters work[pos]).transient.vDelta =
        state.transient.vDelta := by
      rw [hN]; rfl
    have hWK : ((next.clearFeatureRegisters work[pos]).weights.get idx) =
        state.weights.get idx := by
      rw [(clear_feature_knowledge next work[pos] idx).1, hN]; exact hFr.1
    have hBK : (((next.clearFeatureRegisters work[pos]).beta.get idx).value) =
        (state.beta.get idx).value := by
      rw [(clear_feature_knowledge next work[pos] idx).2, hN]; exact hFr.2.1
    have hRK : registers (next.clearFeatureRegisters work[pos]) idx = registers state idx := by
      rw [clear_feature_other next work[pos] idx hNe, hN]; exact hFr.2.2
    have hStep : NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos =
        NumericState.learnFirstLoopGo cfg delta vDelta decay
          (next.clearFeatureRegisters work[pos]) (SwiftTd.swapRemove work pos valid) pos := by
      rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
      dsimp only
      rw [equation]
      rfl
    dsimp only
    rw [hStep]
    exact ⟨hIh.1.trans hWK, hIh.2.1.trans hBK, hIh.2.2.1.trans hRK,
      hIh.2.2.2.1.trans hRls, hIh.2.2.2.2.1.trans hVO, hIh.2.2.2.2.2.trans hVD⟩
  | case2 state work pos valid idx0 next prune equation noPrune ih =>
    dsimp only [idx0] at equation ih
    have hN : next = (state.firstLoopElement work[pos] delta vDelta decay).1 :=
      (congrArg Prod.fst equation).symm
    have hNe : work[pos] ≠ idx := fun hEq => hAbs ⟨pos, le_rfl, valid, hEq⟩
    have hAbs' : ¬ hasTail work (pos + 1) idx := fun ⟨j, hle, hj, heq⟩ =>
      hAbs ⟨j, by omega, hj, heq⟩
    have hIh := ih hAbs'
    have hFr := first_element_frame state work[pos] idx hNe delta vDelta decay
    have hRls : next.rails = state.rails := by rw [hN]; rfl
    have hVO : next.transient.vOld = state.transient.vOld := by rw [hN]; rfl
    have hVD : next.transient.vDelta = state.transient.vDelta := by rw [hN]; rfl
    have hStep : NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos =
        NumericState.learnFirstLoopGo cfg delta vDelta decay next work (pos + 1) := by
      rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
      dsimp only
      rw [equation]
      exact ite_eq_right noPrune
    dsimp only
    rw [← hN] at hFr
    rw [hStep]
    exact ⟨hIh.1.trans hFr.1, hIh.2.1.trans hFr.2.1, hIh.2.2.1.trans hFr.2.2,
      hIh.2.2.2.1.trans hRls, hIh.2.2.2.2.1.trans hVO, hIh.2.2.2.2.2.trans hVD⟩
  | case3 state work pos finished =>
    rw [NumericState.learnFirstLoopGo_def, dite_eq_right finished]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem firstLoop_go_present {cfg : Acorn.Config} {dim : Dimension}
    (delta vDelta decay : Binary32) (state : NumericState cfg dim)
    (work : Array (FeatIdx dim)) (pos : Nat) (idx : FeatIdx dim)
    (hUnique : work.toList.Nodup) (hHas : hasTail work pos idx) :
    let res := NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos
    let elem := state.firstLoopElement idx delta vDelta decay
    res.weights.get idx = elem.1.weights.get idx ∧
    (res.beta.get idx).value = (elem.1.beta.get idx).value ∧
    registers res idx =
      (if elem.2 then Vector.replicate 9 Binary32.zero else registers elem.1 idx) ∧
    res.rails = state.rails ∧
    res.transient.vOld = state.transient.vOld ∧
    res.transient.vDelta = state.transient.vDelta := by
  induction state, work, pos using
      NumericState.learnFirstLoopGoCosted.induct cfg delta vDelta decay with
  | case1 state work pos valid idx0 next equation ih =>
    dsimp only [idx0] at equation ih
    have hN : (state.firstLoopElement work[pos] delta vDelta decay).1 = next :=
      congrArg Prod.fst equation
    have hStep : NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos =
        NumericState.learnFirstLoopGo cfg delta vDelta decay
          (next.clearFeatureRegisters work[pos]) (SwiftTd.swapRemove work pos valid) pos := by
      rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
      dsimp only
      rw [equation]
      rfl
    dsimp only
    rw [hStep]
    by_cases hHere : work[pos] = idx
    · subst idx
      have hPr : (state.firstLoopElement work[pos] delta vDelta decay).2 = true := by
        rw [equation]
      have hNotIn : work[pos] ∉ SwiftTd.swapRemove work pos valid :=
        swap_remove_absent work pos valid hUnique
      have hAbs : ¬ hasTail (SwiftTd.swapRemove work pos valid) pos work[pos] := by
        intro ⟨j, _, hj, heq⟩
        exact hNotIn (heq ▸ Array.getElem_mem hj)
      have hG := firstLoop_go_absent delta vDelta decay
        (next.clearFeatureRegisters work[pos]) (SwiftTd.swapRemove work pos valid) pos
        work[pos] hAbs
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hG.1, (clear_feature_knowledge next work[pos] work[pos]).1, hN]
      · rw [hG.2.1, (clear_feature_knowledge next work[pos] work[pos]).2, hN]
      · rw [hG.2.2.1, clear_feature_self, hPr]; rfl
      · rw [hG.2.2.2.1, ← hN]; rfl
      · rw [hG.2.2.2.2.1, ← hN]; rfl
      · rw [hG.2.2.2.2.2, ← hN]; rfl
    · have hHas' : hasTail (SwiftTd.swapRemove work pos valid) pos idx := by
        rcases hHas with ⟨j, hle, hj, heq⟩
        have hjNe : j ≠ pos := fun h => hHere (h ▸ heq)
        by_cases hLast : j = work.size - 1
        · have hPLt : pos < work.size - 1 := by omega
          have hPIn : pos < (SwiftTd.swapRemove work pos valid).size := by
            rw [swap_remove_size]; exact hPLt
          have hGet : work[work.size - 1] = work[j] := by congr 1; exact hLast.symm
          refine ⟨pos, le_rfl, hPIn, ?_⟩
          rw [swap_remove_get, ite_eq_left rfl, hGet, heq]
        · have hJIn : j < (SwiftTd.swapRemove work pos valid).size := by
            rw [swap_remove_size]; omega
          refine ⟨j, hle, hJIn, ?_⟩
          rw [swap_remove_get, ite_eq_right (fun h => hjNe h.symm), heq]
      have hIh := ih (swap_remove_nodup work pos valid hUnique) hHas'
      have hFr := first_element_frame state work[pos] idx hHere delta vDelta decay
      have hRls : (next.clearFeatureRegisters work[pos]).rails = state.rails := by
        rw [← hN]; rfl
      have hWK : (next.clearFeatureRegisters work[pos]).weights.get idx =
          state.weights.get idx := by
        rw [(clear_feature_knowledge next work[pos] idx).1, ← hN]; exact hFr.1
      have hBK : ((next.clearFeatureRegisters work[pos]).beta.get idx).value =
          (state.beta.get idx).value := by
        rw [(clear_feature_knowledge next work[pos] idx).2, ← hN]; exact hFr.2.1
      have hRK : registers (next.clearFeatureRegisters work[pos]) idx = registers state idx := by
        rw [clear_feature_other next work[pos] idx hHere, ← hN]; exact hFr.2.2
      have hCg := firstLoopElement_congr (next.clearFeatureRegisters work[pos]) state idx
        delta vDelta decay hRls hWK hBK hRK
      dsimp only at hIh hCg
      have hVO : (next.clearFeatureRegisters work[pos]).transient.vOld = state.transient.vOld := by
        rw [← hN]; rfl
      have hVD : (next.clearFeatureRegisters work[pos]).transient.vDelta =
          state.transient.vDelta := by
        rw [← hN]; rfl
      refine ⟨hIh.1.trans hCg.2.1, hIh.2.1.trans hCg.2.2.1, ?_,
        hIh.2.2.2.1.trans hRls, hIh.2.2.2.2.1.trans hVO, hIh.2.2.2.2.2.trans hVD⟩
      rw [hIh.2.2.1, hCg.1, hCg.2.2.2]
  | case2 state work pos valid idx0 next prune equation noPrune ih =>
    dsimp only [idx0] at equation ih
    have hN : (state.firstLoopElement work[pos] delta vDelta decay).1 = next :=
      congrArg Prod.fst equation
    have hStep : NumericState.learnFirstLoopGo cfg delta vDelta decay state work pos =
        NumericState.learnFirstLoopGo cfg delta vDelta decay next work (pos + 1) := by
      rw [NumericState.learnFirstLoopGo_def, dite_eq_left valid]
      dsimp only
      rw [equation]
      exact ite_eq_right noPrune
    dsimp only
    rw [hStep]
    by_cases hHere : work[pos] = idx
    · subst idx
      have hPr : (state.firstLoopElement work[pos] delta vDelta decay).2 = false := by
        rw [equation]; exact Bool.eq_false_iff.mpr noPrune
      have hAbs : ¬ hasTail work (pos + 1) work[pos] := by
        intro ⟨j, hle, hj, heq⟩
        have hEqPos := (array_nodup_iff work).mp hUnique pos j valid hj heq.symm
        omega
      have hG := firstLoop_go_absent delta vDelta decay next work (pos + 1) work[pos] hAbs
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hG.1, hN]
      · rw [hG.2.1, hN]
      · rw [hG.2.2.1, hPr, hN]; rfl
      · rw [hG.2.2.2.1, ← hN]; rfl
      · rw [hG.2.2.2.2.1, ← hN]; rfl
      · rw [hG.2.2.2.2.2, ← hN]; rfl
    · have hHas' : hasTail work (pos + 1) idx := by
        rcases hHas with ⟨j, hle, hj, heq⟩
        have hNeJ : j ≠ pos := fun h => hHere (h ▸ heq)
        exact ⟨j, by omega, hj, heq⟩
      have hIh := ih hUnique hHas'
      have hFr := first_element_frame state work[pos] idx hHere delta vDelta decay
      have hRls : next.rails = state.rails := by rw [← hN]; rfl
      rw [hN] at hFr
      have hCg := firstLoopElement_congr next state idx delta vDelta decay
        hRls hFr.1 hFr.2.1 hFr.2.2
      dsimp only at hIh hCg
      have hVO : next.transient.vOld = state.transient.vOld := by rw [← hN]; rfl
      have hVD : next.transient.vDelta = state.transient.vDelta := by rw [← hN]; rfl
      refine ⟨hIh.1.trans hCg.2.1, hIh.2.1.trans hCg.2.2.1, ?_,
        hIh.2.2.2.1.trans hRls, hIh.2.2.2.2.1.trans hVO, hIh.2.2.2.2.2.trans hVD⟩
      rw [hIh.2.2.1, hCg.1, hCg.2.2.2]
  | case3 state work pos finished =>
    exfalso
    rcases hHas with ⟨j, hle, hj, _⟩
    omega

theorem firstLoop_pointwise {cfg : Acorn.Config} {dim : Dimension}
    (st : NumericState cfg dim) (hReady : Ready st) (delta vDelta decay : Binary32) :
    let next := st.learnFirstLoop cfg delta vDelta decay
    next.rails = st.rails ∧
    next.transient.vOld = st.transient.vOld ∧
    next.transient.vDelta = st.transient.vDelta ∧
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
  rw [NumericState.learnFirstLoop_def]
  let st0 : NumericState cfg dim := { st with transient := { st.transient with eligible := #[] } }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases hHas : hasTail st.transient.eligible 0 ⟨0, dim.positive⟩
    · exact (firstLoop_go_present delta vDelta decay st0 st.transient.eligible 0 _
        hReady.1 hHas).2.2.2.1
    · exact (firstLoop_go_absent delta vDelta decay st0 st.transient.eligible 0 _ hHas).2.2.2.1
  · by_cases hHas : hasTail st.transient.eligible 0 ⟨0, dim.positive⟩
    · exact (firstLoop_go_present delta vDelta decay st0 st.transient.eligible 0 _
        hReady.1 hHas).2.2.2.2.1
    · exact (firstLoop_go_absent delta vDelta decay st0 st.transient.eligible 0 _ hHas).2.2.2.2.1
  · by_cases hHas : hasTail st.transient.eligible 0 ⟨0, dim.positive⟩
    · exact (firstLoop_go_present delta vDelta decay st0 st.transient.eligible 0 _
        hReady.1 hHas).2.2.2.2.2
    · exact (firstLoop_go_absent delta vDelta decay st0 st.transient.eligible 0 _ hHas).2.2.2.2.2
  · intro idx hNotMem
    have hAbs : ¬ hasTail st.transient.eligible 0 idx := by
      intro ⟨j, _, hj, heq⟩
      exact hNotMem (heq ▸ Array.getElem_mem hj)
    have hG := firstLoop_go_absent delta vDelta decay st0 st.transient.eligible 0 idx hAbs
    exact ⟨hG.1, hG.2.1, hG.2.2.1⟩
  · intro idx hMem
    obtain ⟨j, hj, heq⟩ := Array.mem_iff_getElem.mp hMem
    have hHas : hasTail st.transient.eligible 0 idx := ⟨j, Nat.zero_le _, hj, heq⟩
    have hG := firstLoop_go_present delta vDelta decay st0 st.transient.eligible 0 idx
      hReady.1 hHas
    have hCg := firstLoopElement_congr st0 st idx delta vDelta decay rfl rfl rfl rfl
    dsimp only at hG hCg
    rw [hCg.1, hCg.2.1, hCg.2.2.1, hCg.2.2.2] at hG
    exact ⟨hG.1, hG.2.1, hG.2.2.1⟩

private theorem logStep_project_rails_eq {cfg : Acorn.Config} {r1 r2 : StepSizeRails cfg}
    (hr : r1 = r2) (x : Binary32) :
    (LogStepSize.project r1 x).value = (LogStepSize.project r2 x).value := by
  subst hr; rfl

private theorem secondLoopElement_congr {cfg : Acorn.Config} {dim : Dimension}
    (overshoot : Bool) (e t : Binary32) (s1 s2 : NumericState cfg dim)
    (v1 v2 : Binary32) (idx : FeatIdx dim)
    (hRails : s1.rails = s2.rails)
    (hW : s1.weights.get idx = s2.weights.get idx)
    (hB : (s1.beta.get idx).value = (s2.beta.get idx).value)
    (hR : registers s1 idx = registers s2 idx) :
    let r1 := (NumericState.secondLoopElement cfg overshoot e t s1 v1 idx).1
    let r2 := (NumericState.secondLoopElement cfg overshoot e t s2 v2 idx).1
    r1.weights.get idx = r2.weights.get idx ∧
    (r1.beta.get idx).value = (r2.beta.get idx).value ∧
    registers r1 idx = registers r2 idx := by
  have hF := registers_fields_eq hR
  have hSet : ∀ {α : Type} (v : Vector α dim.capacity) (x : α),
      (v.set idx.val x idx.isLt).get idx = x := by
    intro α v x
    rw [vector_get, Vector.getElem_set_self]
  have hA : (s1.beta.get idx).alpha = (s2.beta.get idx).alpha := by
    unfold LogStepSize.alpha
    rw [hB]
  cases overshoot
  · simp only [NumericState.secondLoopElement, NumericState.secondLoopElementAt, registers, hSet,
      hW, hB, hA, hF.1, hF.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1,
      hF.2.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2, Bool.false_eq_true, ite_false, and_self]
  · simp only [NumericState.secondLoopElement, NumericState.secondLoopElementAt,
      NumericState.writeBetaValue, registers, hSet, hW, hB, hA, hRails, hF.1, hF.2.2.1,
      hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.1,
      hF.2.2.2.2.2.2.2.2, ite_true]
    exact ⟨trivial, logStep_project_rails_eq hRails _, trivial⟩

private theorem second_fold_absent {cfg : Acorn.Config} {dim : Dimension}
    (overshoot : Bool) (e t : Binary32) (indices : List (FeatIdx dim))
    (s : NumericState cfg dim) (vd : Binary32) (idx : FeatIdx dim) (hAbs : idx ∉ indices) :
    let res := indices.foldl (fun p i =>
      NumericState.secondLoopElement cfg overshoot e t p.1 p.2 i) (s, vd)
    res.1.weights.get idx = s.weights.get idx ∧
    (res.1.beta.get idx).value = (s.beta.get idx).value ∧
    registers res.1 idx = registers s idx ∧
    res.1.rails = s.rails ∧
    res.1.transient.vOld = s.transient.vOld := by
  induction indices generalizing s vd with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons a rest ih =>
    rw [List.foldl_cons]
    have hNe : a ≠ idx := fun h => hAbs (h ▸ List.mem_cons_self)
    have hAbsR : idx ∉ rest := fun h => hAbs (List.mem_cons_of_mem _ h)
    have hFr := second_element_frame s a idx hNe overshoot e t vd
    have hRls : (NumericState.secondLoopElement cfg overshoot e t s vd a).1.rails = s.rails := by
      cases overshoot <;> rfl
    have hVO : (NumericState.secondLoopElement cfg overshoot e t s vd a).1.transient.vOld =
        s.transient.vOld := by
      cases overshoot <;> rfl
    have hIh := ih (NumericState.secondLoopElement cfg overshoot e t s vd a).1
      (NumericState.secondLoopElement cfg overshoot e t s vd a).2 hAbsR
    exact ⟨hIh.1.trans hFr.1, hIh.2.1.trans hFr.2.1, hIh.2.2.1.trans hFr.2.2,
      hIh.2.2.2.1.trans hRls, hIh.2.2.2.2.trans hVO⟩

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

private theorem second_fold_present {cfg : Acorn.Config} {dim : Dimension}
    (overshoot : Bool) (e t : Binary32) (indices : List (FeatIdx dim))
    (hNd : indices.Nodup) (s : NumericState cfg dim) (vd : Binary32) (idx : FeatIdx dim)
    (hMem : idx ∈ indices) :
    let res := (indices.foldl (fun p i =>
      NumericState.secondLoopElement cfg overshoot e t p.1 p.2 i) (s, vd)).1
    let step1 := (NumericState.secondLoopElement cfg overshoot e t s .zero idx).1
    res.weights.get idx = step1.weights.get idx ∧
    (res.beta.get idx).value = (step1.beta.get idx).value ∧
    registers res idx = registers step1 idx ∧
    res.rails = s.rails ∧
    res.transient.vOld = s.transient.vOld := by
  induction indices generalizing s vd with
  | nil => cases hMem
  | cons a rest ih =>
    have hcons := List.nodup_cons.mp hNd
    rw [List.foldl_cons]
    by_cases hHere : a = idx
    · subst idx
      have hAbs := second_fold_absent overshoot e t rest
        (NumericState.secondLoopElement cfg overshoot e t s vd a).1
        (NumericState.secondLoopElement cfg overshoot e t s vd a).2 a hcons.1
      have hCg := secondLoopElement_congr overshoot e t
        s s vd .zero a rfl rfl rfl rfl
      have hRls : (NumericState.secondLoopElement cfg overshoot e t s vd a).1.rails = s.rails := by
        cases overshoot <;> rfl
      have hVO : (NumericState.secondLoopElement cfg overshoot e t s vd a).1.transient.vOld =
          s.transient.vOld := by
        cases overshoot <;> rfl
      exact ⟨hAbs.1.trans hCg.1, hAbs.2.1.trans hCg.2.1, hAbs.2.2.1.trans hCg.2.2,
        hAbs.2.2.2.1.trans hRls, hAbs.2.2.2.2.trans hVO⟩
    · have hMemR : idx ∈ rest := (List.mem_cons.mp hMem).resolve_left (Ne.symm hHere)
      have hIh := ih hcons.2 (NumericState.secondLoopElement cfg overshoot e t s vd a).1
        (NumericState.secondLoopElement cfg overshoot e t s vd a).2 hMemR
      have hFr := second_element_frame s a idx hHere overshoot e t vd
      have hRls : (NumericState.secondLoopElement cfg overshoot e t s vd a).1.rails = s.rails := by
        cases overshoot <;> rfl
      have hVO : (NumericState.secondLoopElement cfg overshoot e t s vd a).1.transient.vOld =
          s.transient.vOld := by
        cases overshoot <;> rfl
      have hCg := secondLoopElement_congr overshoot e t
        (NumericState.secondLoopElement cfg overshoot e t s vd a).1 s .zero .zero idx
        hRls hFr.1 hFr.2.1 hFr.2.2
      exact ⟨hIh.1.trans hCg.1, hIh.2.1.trans hCg.2.1, hIh.2.2.1.trans hCg.2.2,
        hIh.2.2.2.1.trans hRls, hIh.2.2.2.2.trans hVO⟩

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
  rw [NumericState.learnSecondLoop_eq_sumFrom]
  refine ⟨second_fold_vDelta overshoot e t features.indices st vDelta, ?_, ?_, ?_, ?_⟩
  · cases hId : features.indices with
    | nil => rfl
    | cons a rest =>
      rw [← hId]
      exact (second_fold_present overshoot e t features.indices features.nodup st vDelta a
        (by rw [hId]; exact List.mem_cons_self)).2.2.2.1
  · cases hId : features.indices with
    | nil => rfl
    | cons a rest =>
      rw [← hId]
      exact (second_fold_present overshoot e t features.indices features.nodup st vDelta a
        (by rw [hId]; exact List.mem_cons_self)).2.2.2.2
  · intro idx hAbs
    have hA := second_fold_absent overshoot e t features.indices st vDelta idx hAbs
    exact ⟨hA.1, hA.2.1, hA.2.2.1⟩
  · intro idx hMem
    have hP := second_fold_present overshoot e t features.indices features.nodup st vDelta idx hMem
    exact ⟨hP.1, hP.2.1, hP.2.2.1⟩

end AcornVerif.CurrentLearnerStep
