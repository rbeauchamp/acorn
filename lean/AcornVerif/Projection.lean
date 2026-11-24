import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import AcornVerif.ModelConstants

namespace AcornVerif

open AcornVerif.ModelConstants

def projectR (b v : ℝ) : ℝ := max (-b) (min b v)

theorem project_mem_range (b v : ℝ) (hb : 0 ≤ b) :
    -b ≤ projectR b v ∧ projectR b v ≤ b := by
  constructor
  · exact le_max_left _ _
  · unfold projectR
    rcases le_total (-b) (min b v) with h | h
    · rw [max_eq_right h]
      exact min_le_left _ _
    · rw [max_eq_left h]
      linarith

theorem project_id_of_mem (b v : ℝ) (h1 : -b ≤ v) (h2 : v ≤ b) :
    projectR b v = v := by
  unfold projectR
  rw [min_eq_right h2, max_eq_right h1]

theorem project_nonexpansive (b v t : ℝ) (ht1 : -b ≤ t) (ht2 : t ≤ b) :
    |projectR b v - t| ≤ |v - t| := by
  have hb : (0 : ℝ) ≤ b := by linarith
  unfold projectR
  rcases le_total v (-b) with h | h
  · have hmin : min b v = v := min_eq_right (by linarith)
    rw [hmin, max_eq_left h, abs_of_nonpos (by linarith : -b - t ≤ 0),
      abs_of_nonpos (by linarith : v - t ≤ 0)]
    linarith
  · rcases le_total v b with h2 | h2
    · rw [min_eq_right h2, max_eq_right h]
    · rw [min_eq_left h2, max_eq_right (by linarith : (-b : ℝ) ≤ b),
        abs_of_nonneg (by linarith : 0 ≤ b - t),
        abs_of_nonneg (by linarith : 0 ≤ v - t)]
      linarith

theorem horizon_covers_true_bound :
    ∀ p ∈ ModelConstants.discounts, 1 / (1 - p.1) ≤ p.2 := by
  intro p hp
  simp only [ModelConstants.discounts] at hp
  fin_cases hp <;>
    norm_num [ModelConstants.gammaG90, ModelConstants.gammaG95, ModelConstants.gammaG99,
      ModelConstants.horizonG90, ModelConstants.horizonG95, ModelConstants.horizonG99]

theorem constant_cumulant_fixed_point (c γ : ℝ) (hγ : γ < 1) :
    c / (1 - γ) = c + γ * (c / (1 - γ)) := by
  have h : (1 : ℝ) - γ ≠ 0 := by linarith
  field_simp
  ring

theorem constant_cumulant_fixed_point_unique (c γ v : ℝ) (hγ : γ < 1)
    (hv : v = c + γ * v) : v = c / (1 - γ) := by
  have h : (1 : ℝ) - γ ≠ 0 := by linarith
  rw [eq_div_iff h]
  linear_combination hv

theorem gamma_is_contraction :
    ∀ p ∈ ModelConstants.discounts, 0 < p.1 ∧ p.1 < 1 := by
  intro p hp
  simp only [ModelConstants.discounts] at hp
  fin_cases hp <;>
    norm_num [ModelConstants.gammaG90, ModelConstants.gammaG95, ModelConstants.gammaG99]

end AcornVerif
