import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
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

end

end AcornVerif
