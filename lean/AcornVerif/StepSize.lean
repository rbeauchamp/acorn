import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace AcornVerif

open Real

noncomputable section

def clipBeta (β η ηmin : ℝ) : ℝ :=
  if Real.exp β > η then Real.log η
  else if Real.exp β < ηmin then Real.log ηmin
  else β

theorem step_size_pos_after_clip (β η ηmin : ℝ) (hη : 0 < η) (hm : 0 < ηmin) :
    0 < Real.exp (clipBeta β η ηmin) := by
  unfold clipBeta
  by_cases h1 : Real.exp β > η
  · simp [h1, Real.exp_log hη, hη]
  · by_cases h2 : Real.exp β < ηmin
    · simp [h1, h2, Real.exp_log hm, hm]
    · simp [h1, h2, Real.exp_pos]

theorem step_size_upper_after_clip (β η ηmin : ℝ) (hm : 0 < ηmin) (h : ηmin ≤ η) :
    Real.exp (clipBeta β η ηmin) ≤ η := by
  unfold clipBeta
  by_cases h1 : Real.exp β > η
  · simp [h1, Real.exp_log (lt_of_lt_of_le hm h)]
  · by_cases h2 : Real.exp β < ηmin
    · simp [h1, h2, Real.exp_log hm, h]
    · simp [h1, h2, le_of_not_gt]

theorem step_size_lower_after_clip (β η ηmin : ℝ) (hm : 0 < ηmin) (h : ηmin ≤ η) :
    ηmin ≤ Real.exp (clipBeta β η ηmin) := by
  unfold clipBeta
  by_cases h1 : Real.exp β > η
  · simp [h1, Real.exp_log (lt_of_lt_of_le hm h), h]
  · by_cases h2 : Real.exp β < ηmin
    · simp [h1, h2, Real.exp_log hm]
    · simp [h1, h2, le_of_not_gt]

def overshootE (η rate : ℝ) : ℝ := max η rate

def traceIncrement (η α : ℝ) (E : ℝ) : ℝ := (η / E) * α

theorem total_trace_increment_bounded (η rate : ℝ) (hη : 0 < η) :
    (η / overshootE η rate) * rate ≤ η := by
  unfold overshootE
  by_cases hle : rate ≤ η
  · have hmax : max η rate = η := max_eq_left hle
    rw [hmax]
    field_simp [ne_of_gt hη]
    exact hle
  · have hgt : η < rate := lt_of_not_ge hle
    have hmax : max η rate = rate := max_eq_right (le_of_lt hgt)
    rw [hmax]
    have hrate : rate ≠ 0 := ne_of_gt (lt_of_lt_of_le hη (le_of_lt hgt))
    field_simp [hrate]
    norm_num

theorem trace_increment_le_step_size (η rate α : ℝ) (hη : 0 < η) (hα : 0 ≤ α) :
    traceIncrement η α (overshootE η rate) ≤ α := by
  unfold traceIncrement overshootE
  have hEpos : 0 < max η rate := lt_of_lt_of_le hη (le_max_left η rate)
  have hratio : η / max η rate ≤ 1 := (div_le_one hEpos).2 (le_max_left η rate)
  exact mul_le_of_le_one_left hα hratio

theorem decay_shrinks_step_size (β d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    Real.exp (β + Real.log d) ≤ Real.exp β := by
  rw [Real.exp_add, Real.exp_log hd0, mul_comm]
  exact mul_le_of_le_one_left (le_of_lt (Real.exp_pos β)) hd1

end

end AcornVerif
