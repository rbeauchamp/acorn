import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace AcornVerif

noncomputable section

structure StepInput where
  delta : ℝ
  zbar : ℝ
  zdeltaPrev : ℝ
  zdelta : ℝ
  vdelta : ℝ
  z : ℝ
  phi : ℝ

def StepInput.increment (p : StepInput) : ℝ :=
  p.delta * p.zbar - p.zdeltaPrev * p.vdelta

structure Regs where
  h : ℝ
  hTemp : ℝ
  hOld : ℝ

def eq32 (prev prev2 : ℝ) (p : StepInput) : ℝ :=
  prev + p.increment - prev2 * p.phi * (p.z - p.zdelta) - prev * p.zdelta * p.phi

def stepPaper (r : Regs) (p : StepInput) : Regs :=
  let hOld := r.h
  let h := r.hTemp
  let hTemp := h + p.increment
  { h := h
    hTemp := hTemp - hOld * p.phi * (p.z - p.zdelta) - h * p.zdelta * p.phi
    hOld := hOld }

def stepRef (r : Regs) (p : StepInput) : Regs :=
  let hOld := r.h
  let h := r.hTemp + p.increment
  { h := h
    hTemp := h - hOld * p.phi * (p.z - p.zdelta) - h * p.zdelta * p.phi
    hOld := hOld }

theorem stepPaper_eq_eq32 (r : Regs) (p : StepInput) :
    (stepPaper r p).hTemp = eq32 r.hTemp r.h p := rfl

theorem stepPaper_shifts_lags (r : Regs) (p : StepInput) :
    (stepPaper r p).h = r.hTemp ∧ (stepPaper r p).hOld = r.h := by
  constructor <;> rfl

def run (p : ℕ → StepInput) : ℕ → Regs
  | 0 => { h := 0, hTemp := 0, hOld := 0 }
  | n + 1 => stepPaper (run p n) (p n)

theorem run_realizes_eq32 (p : ℕ → StepInput) (n : ℕ) :
    (run p (n + 2)).hTemp
      = eq32 (run p (n + 1)).hTemp (run p n).hTemp (p (n + 1)) := by
  have hlag : (run p (n + 1)).h = (run p n).hTemp := rfl
  calc (run p (n + 2)).hTemp
      = eq32 (run p (n + 1)).hTemp (run p (n + 1)).h (p (n + 1)) :=
        stepPaper_eq_eq32 _ _
    _ = eq32 (run p (n + 1)).hTemp (run p n).hTemp (p (n + 1)) := by rw [hlag]

theorem stepRef_hTemp_error (r : Regs) (p : StepInput) :
    (stepRef r p).hTemp - (stepPaper r p).hTemp
      = -(p.increment * p.zdelta * p.phi) := by
  simp only [stepRef, stepPaper]
  ring

theorem stepRef_h_error (r : Regs) (p : StepInput) :
    (stepRef r p).h - (stepPaper r p).h = p.increment := by
  simp only [stepRef, stepPaper]
  ring

def metaTraceIncrementPaper (r : Regs) (p : StepInput) : ℝ := p.phi * r.hTemp

def metaTraceIncrementRef (r : Regs) (p : StepInput) : ℝ := p.phi * r.h

theorem metaTrace_lag (r : Regs) (p : StepInput) :
    metaTraceIncrementRef r p - metaTraceIncrementPaper r p
      = p.phi * (r.h - r.hTemp) := by
  simp only [metaTraceIncrementRef, metaTraceIncrementPaper]
  ring

def metaGain (theta beta : ℝ) : ℝ := theta / Real.exp beta

def metaGainStabilised (theta beta epsilon : ℝ) : ℝ := theta / (Real.exp beta + epsilon)

theorem metaGain_at_floor (theta etaMin : ℝ) (h : 0 < etaMin) :
    metaGain theta (Real.log etaMin) = theta / etaMin := by
  simp [metaGain, Real.exp_log h]

theorem metaGain_strictAnti (theta : ℝ) (hθ : 0 < theta) :
    StrictAnti (metaGain theta) := by
  intro a b hab
  simp only [metaGain]
  exact div_lt_div_of_pos_left hθ (Real.exp_pos a) (Real.exp_lt_exp.2 hab)

theorem metaGainStabilised_le (theta beta epsilon : ℝ) (hθ : 0 ≤ theta)
    (hε : 0 < epsilon) :
    metaGainStabilised theta beta epsilon ≤ theta / epsilon := by
  simp only [metaGainStabilised]
  exact div_le_div_of_nonneg_left hθ hε (by linarith [Real.exp_pos beta])

theorem beta_floor_reachable (theta beta etaMin : ℝ) (hθ : 0 < theta) :
    ∃ g < 0, beta + metaGain theta beta * g ≤ Real.log etaMin := by
  let target := min (Real.log etaMin - 1) (beta - 1)
  have h_diff : target - beta < 0 := by
    have : target ≤ beta - 1 := min_le_right _ _
    linarith
  have h_exp : 0 < Real.exp beta := Real.exp_pos beta
  let g := (Real.exp beta / theta) * (target - beta)
  have hg : g < 0 := by
    apply mul_neg_of_pos_of_neg (div_pos h_exp hθ) h_diff
  refine ⟨g, hg, ?_⟩
  dsimp [metaGain, g]
  have hθ_ne : theta ≠ 0 := ne_of_gt hθ
  have hexp_ne : Real.exp beta ≠ 0 := ne_of_gt h_exp
  have h_cancel :
      (theta / Real.exp beta) * ((Real.exp beta / theta) * (target - beta)) =
        target - beta := by
    field_simp [hθ_ne, hexp_ne]
  rw [h_cancel]
  have : target ≤ Real.log etaMin - 1 := min_le_left _ _
  linarith

theorem beta_floor_absorbing (theta beta etaMin g : ℝ) (hθ : 0 ≤ theta)
    (hβ : beta ≤ Real.log etaMin) (hg : g ≤ 0) :
    beta + metaGain theta beta * g ≤ Real.log etaMin := by
  have h_prod : metaGain theta beta * g ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hθ (le_of_lt (Real.exp_pos beta))) hg
  linarith

def cycleMat (aBg aDec : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  let mu := aBg + aDec
  ((1 - mu + aBg ^ 2, -aBg), (-aBg * (1 - mu), 1 - mu))

def cycleTr (aBg aDec : ℝ) : ℝ :=
  2 * (1 - (aBg + aDec)) + aBg ^ 2

def cycleDet (aBg aDec : ℝ) : ℝ :=
  (1 - (aBg + aDec)) ^ 2

def cycleDisc (aBg aDec : ℝ) : ℝ :=
  (cycleTr aBg aDec) ^ 2 - 4 * cycleDet aBg aDec

def cycleLambdaMinus (aBg aDec : ℝ) : ℝ :=
  (1 - (aBg + aDec)) + aBg ^ 2 / 2 -
    aBg * Real.sqrt (1 - (aBg + aDec) + aBg ^ 2 / 4)

def cycleLambdaPlus (aBg aDec : ℝ) : ℝ :=
  (1 - (aBg + aDec)) + aBg ^ 2 / 2 +
    aBg * Real.sqrt (1 - (aBg + aDec) + aBg ^ 2 / 4)

theorem alternating_cycle_matrix_invariants (aBg aDec : ℝ)
    (hBg : 0 < aBg) (hMu : aBg + aDec < 1) :
    let m := cycleMat aBg aDec
    m.1.1 + m.2.2 = cycleTr aBg aDec ∧
    m.1.1 * m.2.2 - m.1.2 * m.2.1 = cycleDet aBg aDec ∧
    cycleDisc aBg aDec = aBg ^ 2 * (4 * (1 - (aBg + aDec)) + aBg ^ 2) ∧
    0 < cycleDisc aBg aDec := by
  dsimp only [cycleMat, cycleTr, cycleDet, cycleDisc]
  refine ⟨by ring, by ring, by ring, ?_⟩
  have hBg2 : 0 < aBg ^ 2 := sq_pos_of_pos hBg
  have hInner : 0 < 4 * (1 - (aBg + aDec)) + aBg ^ 2 := by nlinarith
  have hEq :
      (2 * (1 - (aBg + aDec)) + aBg ^ 2) ^ 2 - 4 * (1 - (aBg + aDec)) ^ 2 =
      aBg ^ 2 * (4 * (1 - (aBg + aDec)) + aBg ^ 2) := by ring
  rw [hEq]
  exact mul_pos hBg2 hInner

theorem alternating_cycle_spectrum (aBg aDec : ℝ)
    (hBg : 0 < aBg) (hDec : 0 < aDec) (hMu : aBg + aDec < 1) :
    let lm := cycleLambdaMinus aBg aDec
    let lp := cycleLambdaPlus aBg aDec
    lm ^ 2 - cycleTr aBg aDec * lm + cycleDet aBg aDec = 0 ∧
    lp ^ 2 - cycleTr aBg aDec * lp + cycleDet aBg aDec = 0 ∧
    0 < lm ∧ lm < lp ∧ lp < 1 ∧
    1 - lp =
      (aDec * (2 * aBg + aDec)) /
        ((aBg + aDec) - aBg ^ 2 / 2 +
          aBg * Real.sqrt (1 - (aBg + aDec) + aBg ^ 2 / 4)) := by
  dsimp only [cycleLambdaMinus, cycleLambdaPlus, cycleTr, cycleDet]
  set mu : ℝ := aBg + aDec
  set rad : ℝ := 1 - mu + aBg ^ 2 / 4
  set s : ℝ := Real.sqrt rad
  have hRadPos : 0 < rad := by
    dsimp only [rad]
    have hBg2 : 0 ≤ aBg ^ 2 := sq_nonneg aBg
    linarith
  have hsPos : 0 < s := Real.sqrt_pos.mpr hRadPos
  have hs2 : s ^ 2 = rad := Real.sq_sqrt hRadPos.le
  have hRootMinus :
      ((1 - mu) + aBg ^ 2 / 2 - aBg * s) ^ 2 -
        (2 * (1 - mu) + aBg ^ 2) * ((1 - mu) + aBg ^ 2 / 2 - aBg * s) +
        (1 - mu) ^ 2 = 0 := by
    dsimp only [rad] at hs2
    nlinarith [hs2]
  have hRootPlus :
      ((1 - mu) + aBg ^ 2 / 2 + aBg * s) ^ 2 -
        (2 * (1 - mu) + aBg ^ 2) * ((1 - mu) + aBg ^ 2 / 2 + aBg * s) +
        (1 - mu) ^ 2 = 0 := by
    dsimp only [rad] at hs2
    nlinarith [hs2]
  have hLpPos : 0 < (1 - mu) + aBg ^ 2 / 2 + aBg * s := by
    have hBg2 : 0 < aBg ^ 2 := sq_pos_of_pos hBg
    have hAs : 0 < aBg * s := mul_pos hBg hsPos
    linarith
  have hProd :
      ((1 - mu) + aBg ^ 2 / 2 - aBg * s) * ((1 - mu) + aBg ^ 2 / 2 + aBg * s) =
      (1 - mu) ^ 2 := by
    dsimp only [rad] at hs2
    nlinarith [hs2]
  have hLmPos : 0 < (1 - mu) + aBg ^ 2 / 2 - aBg * s := by
    have hOneSubSq : 0 < (1 - mu) ^ 2 := sq_pos_of_pos (by linarith)
    nlinarith [hProd, hLpPos, hOneSubSq]
  have hLt : (1 - mu) + aBg ^ 2 / 2 - aBg * s < (1 - mu) + aBg ^ 2 / 2 + aBg * s := by
    have hAs : 0 < aBg * s := mul_pos hBg hsPos
    linarith
  have hDenPos : 0 < mu - aBg ^ 2 / 2 + aBg * s := by
    have hBgLt1 : aBg < 1 := by linarith
    have hBgSqLt : aBg ^ 2 < aBg := by nlinarith
    have hAs : 0 < aBg * s := mul_pos hBg hsPos
    linarith
  have hGapProd :
      (1 - ((1 - mu) + aBg ^ 2 / 2 + aBg * s)) * (mu - aBg ^ 2 / 2 + aBg * s) =
      aDec * (2 * aBg + aDec) := by
    dsimp only [rad, mu] at hs2 ⊢
    nlinarith [hs2]
  have hGapEq :
      1 - ((1 - mu) + aBg ^ 2 / 2 + aBg * s) =
      (aDec * (2 * aBg + aDec)) / (mu - aBg ^ 2 / 2 + aBg * s) := by
    rw [eq_div_iff hDenPos.ne']
    exact hGapProd
  have hLpLt1 : (1 - mu) + aBg ^ 2 / 2 + aBg * s < 1 := by
    have hNumPos : 0 < aDec * (2 * aBg + aDec) := by nlinarith
    have hQuotPos : 0 < (aDec * (2 * aBg + aDec)) / (mu - aBg ^ 2 / 2 + aBg * s) :=
      div_pos hNumPos hDenPos
    linarith [hGapEq, hQuotPos]
  exact ⟨hRootMinus, hRootPlus, hLmPos, hLt, hLpLt1, hGapEq⟩

theorem swamping_ratio_parametric (mSh mDec : ℚ)
    (hDec : 0 < mDec) (hRatio : 223 * mDec < 27 * mSh) :
    (223 : ℚ) / 250 < mSh / (mSh + mDec) := by
  have hDen : 0 < mSh + mDec := by linarith
  rw [div_lt_div_iff₀ (by norm_num) hDen]
  linarith

theorem swamping_ratio :
    (223 : ℚ) / 250 < (1712 : ℚ) / (1712 + 8) ∧
    (223 : ℚ) / 250 < (1712 : ℚ) / (1712 + 1) := by
  norm_num

structure TraceStepState where
  hOld : ℝ
  h : ℝ
  hTemp : ℝ
  p : ℝ

def lag2Step (theta alpha rho zStar zD err inc : ℝ)
    (st : TraceStepState) : TraceStepState × ℝ :=
  let dBeta := (theta / alpha) * err * st.p
  let hOld1 := st.h
  let h1 := st.hTemp
  let hTemp1 := st.hTemp + inc
  let p1 := rho * st.p
  let p2 := p1 + h1
  let hTemp2 := hTemp1 - hOld1 * (zStar - zD) - h1 * zD
  (⟨hOld1, h1, hTemp2, p2⟩, dBeta)

def repairedStep (theta alpha rho zStar zD err inc : ℝ)
    (st : TraceStepState) : TraceStepState × ℝ :=
  let dBeta := (theta / alpha) * err * st.p
  let hOld1 := st.h
  let h1 := st.hTemp + inc
  let p1 := rho * st.p
  let p2 := p1 + h1
  let hTemp2 := h1 - hOld1 * (zStar - zD) - h1 * zD
  (⟨hOld1, h1, hTemp2, p2⟩, dBeta)

def altSign (t : Nat) : ℝ :=
  (-1 : ℝ) ^ t

theorem altSign_sq (t : Nat) : altSign t * altSign t = 1 := by
  unfold altSign
  rw [← sq, ← pow_mul, mul_comm, pow_mul]
  norm_num

theorem altSign_succ (t : Nat) : altSign (t + 1) = -altSign t := by
  unfold altSign
  rw [pow_succ]
  ring

def period2Amp (zStar zD zBar kappa d : ℝ) : ℝ :=
  d * (zBar + zD * kappa) / (2 + zStar - 2 * zD)

def lag2Period2State (rho zStar zD zBar kappa d : ℝ) (t : Nat) : TraceStepState :=
  let aH := period2Amp zStar zD zBar kappa d
  let s := altSign t
  ⟨-s * aH, s * aH, -s * aH, s * aH / (1 + rho)⟩

def repairedPeriod2State (rho zStar zD zBar kappa d : ℝ) (t : Nat) : TraceStepState :=
  let aH := period2Amp zStar zD zBar kappa d
  let s := altSign t
  ⟨s * aH, -s * aH, -s * (1 + zStar - 2 * zD) * aH, -s * aH / (1 + rho)⟩

theorem lag2Step_period2_invariant
    (theta alpha rho zStar zD zBar kappa d : ℝ)
    (hRho : 1 + rho ≠ 0) (hDen : 2 + zStar - 2 * zD ≠ 0) (t : Nat) :
    let err := altSign t * d * (1 + kappa)
    let inc := altSign t * d * (zBar + zD * kappa)
    (lag2Step theta alpha rho zStar zD err inc
      (lag2Period2State rho zStar zD zBar kappa d t)).1 =
    lag2Period2State rho zStar zD zBar kappa d (t + 1) := by
  dsimp only [lag2Step, lag2Period2State]
  set aH : ℝ := period2Amp zStar zD zBar kappa d
  have hAmp : d * (zBar + zD * kappa) = (2 + zStar - 2 * zD) * aH := by
    dsimp only [aH, period2Amp]
    rw [mul_div_cancel₀ _ hDen]
  have hInc : altSign t * d * (zBar + zD * kappa) =
      altSign t * ((2 + zStar - 2 * zD) * aH) := by
    rw [mul_assoc, hAmp]
  rw [altSign_succ, hInc]
  congr 1
  · ring
  · ring
  · field_simp [hRho]
    ring

theorem repairedStep_period2_invariant
    (theta alpha rho zStar zD zBar kappa d : ℝ)
    (hRho : 1 + rho ≠ 0) (hDen : 2 + zStar - 2 * zD ≠ 0) (t : Nat) :
    let err := altSign t * d * (1 + kappa)
    let inc := altSign t * d * (zBar + zD * kappa)
    (repairedStep theta alpha rho zStar zD err inc
      (repairedPeriod2State rho zStar zD zBar kappa d t)).1 =
    repairedPeriod2State rho zStar zD zBar kappa d (t + 1) := by
  dsimp only [repairedStep, repairedPeriod2State]
  set aH : ℝ := period2Amp zStar zD zBar kappa d
  have hAmp : d * (zBar + zD * kappa) = (2 + zStar - 2 * zD) * aH := by
    dsimp only [aH, period2Amp]
    rw [mul_div_cancel₀ _ hDen]
  have hInc : altSign t * d * (zBar + zD * kappa) =
      altSign t * ((2 + zStar - 2 * zD) * aH) := by
    rw [mul_assoc, hAmp]
  rw [altSign_succ, hInc]
  congr 1
  · ring
  · ring
  · have hH1 : -(altSign t) * (1 + zStar - 2 * zD) * aH +
        altSign t * ((2 + zStar - 2 * zD) * aH) = altSign t * aH := by ring
    rw [hH1]
    field_simp [hRho]
    ring

theorem lag2_alternating_sign_inversion
    (theta alpha rho zStar zD zBar kappa d : ℝ)
    (hTheta : 0 < theta) (hAlpha : 0 < alpha)
    (hRho0 : 0 ≤ rho) (hRho1 : rho < 1)
    (hD : d ≠ 0) (hKappa : 0 ≤ kappa) (hZBar : 0 < zBar) (hZD : 0 ≤ zD)
    (hDen : 0 < 2 + zStar - 2 * zD) (t : Nat) :
    let err := altSign t * d * (1 + kappa)
    let inc := altSign t * d * (zBar + zD * kappa)
    let out := lag2Step theta alpha rho zStar zD err inc
      (lag2Period2State rho zStar zD zBar kappa d t)
    out.1 = lag2Period2State rho zStar zD zBar kappa d (t + 1) ∧
    out.2 = (theta / alpha) *
      (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
        ((1 + rho) * (2 + zStar - 2 * zD))) ∧
    0 < out.2 := by
  have hRhoPos : 0 < 1 + rho := by linarith
  have _ : 1 + rho < 2 := by linarith
  have hInv := lag2Step_period2_invariant
    theta alpha rho zStar zD zBar kappa d hRhoPos.ne' hDen.ne' t
  dsimp only
  have hFormula :
      (lag2Step theta alpha rho zStar zD
        (altSign t * d * (1 + kappa)) (altSign t * d * (zBar + zD * kappa))
        (lag2Period2State rho zStar zD zBar kappa d t)).2 =
      (theta / alpha) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD))) := by
    dsimp only [lag2Step, lag2Period2State, period2Amp]
    have hSq : altSign t * altSign t = 1 := altSign_sq t
    have hRearr :
        theta / alpha * (altSign t * d * (1 + kappa)) *
          (altSign t * (d * (zBar + zD * kappa) / (2 + zStar - 2 * zD)) / (1 + rho)) =
        (altSign t * altSign t) *
          ((theta / alpha) *
            (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
              ((1 + rho) * (2 + zStar - 2 * zD)))) := by
      field_simp [hAlpha.ne', hRhoPos.ne', hDen.ne']
    rw [hRearr, hSq, one_mul]
  have hPos :
      0 < (theta / alpha) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD))) := by
    have hRatio : 0 < theta / alpha := div_pos hTheta hAlpha
    have hD2 : 0 < d ^ 2 := sq_pos_of_ne_zero hD
    have hK1 : 0 < 1 + kappa := by linarith
    have hZB : 0 < zBar + zD * kappa := by nlinarith
    have hNum : 0 < d ^ 2 * (1 + kappa) * (zBar + zD * kappa) :=
      mul_pos (mul_pos hD2 hK1) hZB
    have hDenProd : 0 < (1 + rho) * (2 + zStar - 2 * zD) := mul_pos hRhoPos hDen
    exact mul_pos hRatio (div_pos hNum hDenProd)
  exact ⟨hInv, hFormula, hFormula ▸ hPos⟩

theorem repaired_alternating_sign_preservation
    (theta alpha rho zStar zD zBar kappa d : ℝ)
    (hTheta : 0 < theta) (hAlpha : 0 < alpha)
    (hRho0 : 0 ≤ rho) (hRho1 : rho < 1)
    (hD : d ≠ 0) (hKappa : 0 ≤ kappa) (hZBar : 0 < zBar) (hZD : 0 ≤ zD)
    (hDen : 0 < 2 + zStar - 2 * zD) (t : Nat) :
    let err := altSign t * d * (1 + kappa)
    let inc := altSign t * d * (zBar + zD * kappa)
    let out := repairedStep theta alpha rho zStar zD err inc
      (repairedPeriod2State rho zStar zD zBar kappa d t)
    out.1 = repairedPeriod2State rho zStar zD zBar kappa d (t + 1) ∧
    out.2 = -((theta / alpha) *
      (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
        ((1 + rho) * (2 + zStar - 2 * zD)))) ∧
    out.2 < 0 := by
  have hRhoPos : 0 < 1 + rho := by linarith
  have _ : 1 + rho < 2 := by linarith
  have hInv := repairedStep_period2_invariant
    theta alpha rho zStar zD zBar kappa d hRhoPos.ne' hDen.ne' t
  dsimp only
  have hFormula :
      (repairedStep theta alpha rho zStar zD
        (altSign t * d * (1 + kappa)) (altSign t * d * (zBar + zD * kappa))
        (repairedPeriod2State rho zStar zD zBar kappa d t)).2 =
      -((theta / alpha) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD)))) := by
    dsimp only [repairedStep, repairedPeriod2State, period2Amp]
    have hSq : altSign t * altSign t = 1 := altSign_sq t
    have hRearr :
        theta / alpha * (altSign t * d * (1 + kappa)) *
          (-(altSign t) * (d * (zBar + zD * kappa) / (2 + zStar - 2 * zD)) / (1 + rho)) =
        -(altSign t * altSign t) *
          ((theta / alpha) *
            (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
              ((1 + rho) * (2 + zStar - 2 * zD)))) := by
      field_simp [hAlpha.ne', hRhoPos.ne', hDen.ne']
    rw [hRearr, hSq]
    ring
  have hPos :
      0 < (theta / alpha) *
        (d ^ 2 * (1 + kappa) * (zBar + zD * kappa) /
          ((1 + rho) * (2 + zStar - 2 * zD))) := by
    have hRatio : 0 < theta / alpha := div_pos hTheta hAlpha
    have hD2 : 0 < d ^ 2 := sq_pos_of_ne_zero hD
    have hK1 : 0 < 1 + kappa := by linarith
    have hZB : 0 < zBar + zD * kappa := by nlinarith
    have hNum : 0 < d ^ 2 * (1 + kappa) * (zBar + zD * kappa) :=
      mul_pos (mul_pos hD2 hK1) hZB
    have hDenProd : 0 < (1 + rho) * (2 + zStar - 2 * zD) := mul_pos hRhoPos hDen
    exact mul_pos hRatio (div_pos hNum hDenProd)
  refine ⟨hInv, hFormula, ?_⟩
  linarith

theorem recurrence_jury_conditions (zStar zD : ℝ)
    (hZD0 : 0 < zD) (hZD1 : zD < 1) (hLe : zD ≤ zStar) (hUpper : zStar < 1 + zD) :
    |zStar - zD| < 1 ∧ 0 < zStar ∧ 0 < 2 + zStar - 2 * zD := by
  refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem repaired_sparse_exact_derivative (alpha r1 r2 : ℝ) :
    let st0 : TraceStepState := ⟨0, 0, 0, 0⟩
    let st1 := (repairedStep 1 alpha 0 alpha alpha r1 (alpha * r1) st0).1
    let delta2 := r2 - alpha * r1
    let h2 := st1.hTemp + delta2 * alpha
    st1.p = alpha * r1 ∧
    h2 = alpha * r1 * (1 - 2 * alpha) + alpha * r2 := by
  dsimp only [repairedStep]
  constructor <;> ring

end

end AcornVerif
