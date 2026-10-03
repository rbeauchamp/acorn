/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The extragradient step cannot grow the weights from their own bootstrap

Exact arithmetic over any finite index set; no executed definition appears here.
`AcornVerif.CurrentOffPolicy` connects these statements to `Acorn.OffPolicy`.

GTD2-MP (Liu, Liu, Ghavamzadeh, Mahadevan & Petrik, *Finite-Sample Analysis of
Proximal Gradient TD Algorithms*, UAI 2015, arXiv:2006.14364v2, §5, Algorithm 2, p. 7)
at importance ratio one keeps main weights `w` and second weights `u`. For a
transition with feature vector `φ` and `a = φ − γφ'`, signal `c` and step `h`, write
`p = ⟨u, φ⟩`, `δ = c − ⟨a, w⟩`, `τ = h|φ|²` and `κ = h|a|²`. The step is

  `u ← u + h((1 − τ)(δ − p) − κp)·φ`, `w ← w + h(p + τ(δ − p))·a`.

Fix any reference `w*` and measure the weights by `N = |u|² + |w − w*|²`, the squared
distance from `(u, w)` to `(0, w*)`. Write `ε = c − ⟨a, w*⟩`, the TD error `w*` leaves
on the transition. `extragradient_energy` proves, for every vector, feature vector,
signal and reference, that if `N ≤ t²` and `hτ ≤ s²` then after the step
`N ≤ (t + |ε|·s)²`, whenever `τ(τ + 2κ) ≤ 1` and `κ ≤ 2 − τ`. With `ε = 0` the
distance never grows: the step's linear part is a skew rotation, which keeps `N` to
first order, plus a part that only shrinks `u` (`zero_residual_change`). So no growth
of the weights from their own bootstrap is possible on any stream; growth is at most
linear in the accumulated residual.

`gtd2_change` shows the plain GTD2 step (Sutton, Maei, Precup, Bhatnagar, Silver,
Szepesvári & Wiewiora, ICML 2009, eqs. (8)–(9)) lacks the property: with `p = 0` and
`q ≠ 0` it raises `N`. `semigradient_family` is the off-policy growth of semi-gradient
TD that the correction answers: the expected update of a family of `K` equally weighted
binary-feature transitions whose successor is never updated scales the direction
`w₀ = W` by `2γ − 1 − 1/K` per unit step size, positive exactly when `γ > (K + 1)/(2K)`.
-/
namespace AcornVerif.Extragradient

variable {ι : Type} [Fintype ι]

/-- The change of `N` per unit step for one step with zero residual, as a function of
`p = ⟨u, φ⟩`, `q = ⟨w − w*, a⟩`, `τ` and `κ` (the scalar identity of the step). -/
theorem zero_residual_change (p q τ κ : ℚ) :
    let e := -(p + q)
    let pm := p + τ * e
    let em := (1 - τ) * e - κ * p
    2 * p * em + τ * em ^ 2 + 2 * q * pm + κ * pm ^ 2
      = -(2 * pm ^ 2 + τ * e ^ 2 + κ * p ^ 2
          - τ * (τ * e + κ * p) ^ 2 - κ * τ ^ 2 * e ^ 2) := by
  intro e pm em
  simp only [e, pm, em]
  ring

/-- With zero residual, one step never increases `N` whenever `τ, κ ≥ 0` and
`τ(τ + 2κ) ≤ 1`. -/
theorem zero_residual_nonincreasing (p q τ κ : ℚ) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (guard : τ * (τ + 2 * κ) ≤ 1) :
    let e := -(p + q)
    let pm := p + τ * e
    let em := (1 - τ) * e - κ * p
    2 * p * em + τ * em ^ 2 + 2 * q * pm + κ * pm ^ 2 ≤ 0 := by
  intro e pm em
  have identity := zero_residual_change p q τ κ
  simp only at identity
  have spread : 0 ≤ τ * e ^ 2 + κ * p ^ 2 :=
    add_nonneg (mul_nonneg hτ (sq_nonneg _)) (mul_nonneg hκ (sq_nonneg _))
  have cross : (τ * e + κ * p) ^ 2 ≤ (τ + κ) * (τ * e ^ 2 + κ * p ^ 2) := by
    have split : (τ + κ) * (τ * e ^ 2 + κ * p ^ 2) - (τ * e + κ * p) ^ 2 =
        τ * κ * (e - p) ^ 2 := by ring
    have nonneg : 0 ≤ τ * κ * (e - p) ^ 2 := mul_nonneg (mul_nonneg hτ hκ) (sq_nonneg _)
    linarith
  have scaled : τ * (τ * e + κ * p) ^ 2 ≤ τ * ((τ + κ) * (τ * e ^ 2 + κ * p ^ 2)) :=
    mul_le_mul_of_nonneg_left cross hτ
  have third : κ * τ ^ 2 * e ^ 2 ≤ κ * τ * (τ * e ^ 2 + κ * p ^ 2) := by
    have nonneg : 0 ≤ κ * τ * (κ * p ^ 2) :=
      mul_nonneg (mul_nonneg hκ hτ) (mul_nonneg hκ (sq_nonneg _))
    nlinarith [nonneg]
  have small : τ * (τ + 2 * κ) * (τ * e ^ 2 + κ * p ^ 2) ≤ τ * e ^ 2 + κ * p ^ 2 := by
    have := mul_le_mul_of_nonneg_right guard spread
    linarith
  have square : 0 ≤ (p + τ * e) ^ 2 := sq_nonneg _
  simp only [e, pm, em] at *
  nlinarith [scaled, third, small, square]

/-- The plain GTD2 step, with `δ − p` and `p` in place of the midpoint's two inner
products, raises `N` by `τ·q²` per unit step when `p = 0`. -/
theorem gtd2_change (q τ κ : ℚ) :
    let p : ℚ := 0
    let e := -(p + q)
    2 * p * e + τ * e ^ 2 + 2 * q * p + κ * p ^ 2 = τ * q ^ 2 := by
  intro p e
  simp only [p, e]
  ring

/-- The semi-gradient family: `K` predecessor states share one feature with weight
`w₀` and own one each, summing to `W`; each leads to one successor in which all `K + 1`
features are active and which is never updated. The signal is zero. The TD errors of
the `K` transitions sum to `Kγ(w₀ + W) − (Kw₀ + W)`. Weighting the predecessors equally,
the expected semi-gradient update of both `w₀` and `W` per unit step size is that sum
divided by `K`, which is `(γ − 1)w₀ + (γ − 1/K)W`, so the direction `w₀ = W` is scaled by
`2γ − 1 − 1/K` and grows whenever `γ > (K + 1)/(2K)`. -/
theorem semigradient_family (K γ w₀ W : ℚ) (positive : 0 < K) :
    (K * (γ * (w₀ + W)) - (K * w₀ + W)) / K = (γ - 1) * w₀ + (γ - 1 / K) * W ∧
      (γ - 1) * w₀ + (γ - 1 / K) * w₀ = (2 * γ - 1 - 1 / K) * w₀ ∧
      (0 < 2 * γ - 1 - 1 / K ↔ (K + 1) / (2 * K) < γ) := by
  have nonzero : K ≠ 0 := ne_of_gt positive
  have inverse : 1 / K * K = 1 := one_div_mul_cancel nonzero
  have expand : (2 * γ - 1 - 1 / K) * K = 2 * γ * K - K - 1 := by
    rw [sub_mul, inverse]
    ring
  have mean : (K * (γ * (w₀ + W)) - (K * w₀ + W)) / K = (γ - 1) * w₀ + (γ - 1 / K) * W := by
    have split : ((γ - 1) * w₀ + (γ - 1 / K) * W) * K =
        (γ - 1) * w₀ * K + γ * W * K - W * (1 / K * K) := by ring
    rw [div_eq_iff nonzero, split, inverse]
    ring
  refine ⟨mean, by ring, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  constructor
  · intro grows
    have product := mul_pos grows positive
    rw [expand] at product
    linarith
  · intro threshold
    have product : 0 < (2 * γ - 1 - 1 / K) * K := by
      rw [expand]
      linarith
    exact (mul_pos_iff_of_pos_right positive).mp product

/-- Cauchy–Schwarz for a pair of vectors read as one. -/
theorem pair_inner (f₁ f₂ g₁ g₂ : ι → ℚ) :
    (∑ i, f₁ i * g₁ i + ∑ i, f₂ i * g₂ i) ^ 2 ≤
      (∑ i, f₁ i ^ 2 + ∑ i, f₂ i ^ 2) * (∑ i, g₁ i ^ 2 + ∑ i, g₂ i ^ 2) := by
  have joint := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Bool × ι))
    (fun x => if x.1 then f₁ x.2 else f₂ x.2) (fun x => if x.1 then g₁ x.2 else g₂ x.2)
  simp only [← Finset.univ_product_univ, Finset.sum_product, Fintype.sum_bool, ↓reduceIte,
    Bool.false_eq_true] at joint
  exact joint

/-- A pair of vectors within `t` plus a pair within `s` is within `t + s`, in squared
length. -/
theorem pair_add (f₁ f₂ g₁ g₂ : ι → ℚ) {t s : ℚ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hf : ∑ i, f₁ i ^ 2 + ∑ i, f₂ i ^ 2 ≤ t ^ 2) (hg : ∑ i, g₁ i ^ 2 + ∑ i, g₂ i ^ 2 ≤ s ^ 2) :
    ∑ i, (f₁ i + g₁ i) ^ 2 + ∑ i, (f₂ i + g₂ i) ^ 2 ≤ (t + s) ^ 2 := by
  have expand : ∑ i, (f₁ i + g₁ i) ^ 2 + ∑ i, (f₂ i + g₂ i) ^ 2 =
      (∑ i, f₁ i ^ 2 + ∑ i, f₂ i ^ 2) + 2 * (∑ i, f₁ i * g₁ i + ∑ i, f₂ i * g₂ i) +
        (∑ i, g₁ i ^ 2 + ∑ i, g₂ i ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
    exact Finset.sum_congr rfl fun i _ => by ring
  have fNonneg : 0 ≤ ∑ i, f₁ i ^ 2 + ∑ i, f₂ i ^ 2 :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have gNonneg : 0 ≤ ∑ i, g₁ i ^ 2 + ∑ i, g₂ i ^ 2 :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have cross : (∑ i, f₁ i * g₁ i + ∑ i, f₂ i * g₂ i) ^ 2 ≤ (t * s) ^ 2 := by
    calc (∑ i, f₁ i * g₁ i + ∑ i, f₂ i * g₂ i) ^ 2
        ≤ (∑ i, f₁ i ^ 2 + ∑ i, f₂ i ^ 2) * (∑ i, g₁ i ^ 2 + ∑ i, g₂ i ^ 2) :=
          pair_inner f₁ f₂ g₁ g₂
      _ ≤ t ^ 2 * s ^ 2 := mul_le_mul hf hg gNonneg (sq_nonneg t)
      _ = (t * s) ^ 2 := by ring
  have bound := (abs_le_of_sq_le_sq' cross (mul_nonneg ht hs)).2
  rw [expand]
  nlinarith [bound]

/-- One extragradient step as vectors: the second weights `u`, the main weights' offset
`v = w − w*` from the reference, the feature vector `φ` and `a = φ − γφ'`, the step `h`
and the residual `ε = c − ⟨a, w*⟩`. If `N = |u|² + |v|² ≤ t²` and `h·τ ≤ s²`, then after
the step `N ≤ (t + |ε|·s)²`, whenever `h ≥ 0`, `τ(τ + 2κ) ≤ 1` and `κ ≤ 2 − τ`. Here
`δ = ε − ⟨v, a⟩` is the TD error of `w = w* + v`. -/
theorem extragradient_energy (u v φ a : ι → ℚ) (h ε t s : ℚ) (hh : 0 ≤ h)
    (guard : h * (∑ i, φ i ^ 2) * (h * (∑ i, φ i ^ 2) + 2 * (h * ∑ i, a i ^ 2)) ≤ 1)
    (curvature : h * (∑ i, a i ^ 2) ≤ 2 - h * (∑ i, φ i ^ 2))
    (ht : 0 ≤ t) (hs : 0 ≤ s) (start : ∑ i, u i ^ 2 + ∑ i, v i ^ 2 ≤ t ^ 2)
    (push : h * (h * ∑ i, φ i ^ 2) ≤ s ^ 2) :
    let p := ∑ i, u i * φ i
    let δ := ε - ∑ i, v i * a i
    let τ := h * ∑ i, φ i ^ 2
    let κ := h * ∑ i, a i ^ 2
    let pm := p + τ * (δ - p)
    let em := (1 - τ) * (δ - p) - κ * p
    ∑ i, (u i + h * em * φ i) ^ 2 + ∑ i, (v i + h * pm * a i) ^ 2 ≤ (t + |ε| * s) ^ 2 := by
  intro p δ τ κ pm em
  have Xnonneg : 0 ≤ ∑ i, φ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have Anonneg : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hτ : 0 ≤ τ := mul_nonneg hh Xnonneg
  have hκ : 0 ≤ κ := mul_nonneg hh Anonneg
  -- The step is its zero-residual part plus `ε` times a fixed push.
  let q := ∑ i, v i * a i
  let em₀ := (1 - τ) * (-(p + q)) - κ * p
  let pm₀ := p + τ * (-(p + q))
  have emSplit : em = em₀ + ε * (1 - τ) := by
    simp only [em, em₀, δ, q]
    ring
  have pmSplit : pm = pm₀ + ε * τ := by
    simp only [pm, pm₀, δ, q]
    ring
  have uSplit : ∀ i, u i + h * em * φ i = (u i + h * em₀ * φ i) + ε * (h * (1 - τ) * φ i) := by
    intro i
    rw [emSplit]
    ring
  have vSplit : ∀ i, v i + h * pm * a i = (v i + h * pm₀ * a i) + ε * (h * τ * a i) := by
    intro i
    rw [pmSplit]
    ring
  simp only [uSplit, vSplit]
  -- The zero-residual part does not increase `N`.
  have linear : ∑ i, (u i + h * em₀ * φ i) ^ 2 + ∑ i, (v i + h * pm₀ * a i) ^ 2 ≤ t ^ 2 := by
    have uExpand : ∑ i, (u i + h * em₀ * φ i) ^ 2 =
        ∑ i, u i ^ 2 + h * (2 * p * em₀ + τ * em₀ ^ 2) := by
      have term : ∀ i, (u i + h * em₀ * φ i) ^ 2 =
          u i ^ 2 + (2 * h * em₀) * (u i * φ i) + (h * h * em₀ ^ 2) * φ i ^ 2 := by
        intro i
        ring
      simp only [term, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [p, τ]
      ring
    have vExpand : ∑ i, (v i + h * pm₀ * a i) ^ 2 =
        ∑ i, v i ^ 2 + h * (2 * q * pm₀ + κ * pm₀ ^ 2) := by
      have term : ∀ i, (v i + h * pm₀ * a i) ^ 2 =
          v i ^ 2 + (2 * h * pm₀) * (v i * a i) + (h * h * pm₀ ^ 2) * a i ^ 2 := by
        intro i
        ring
      simp only [term, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [q, κ]
      ring
    have change := zero_residual_nonincreasing p q τ κ hτ hκ guard
    simp only at change
    have scaled : h * (2 * p * em₀ + τ * em₀ ^ 2) + h * (2 * q * pm₀ + κ * pm₀ ^ 2) ≤ 0 :=
      calc h * (2 * p * em₀ + τ * em₀ ^ 2) + h * (2 * q * pm₀ + κ * pm₀ ^ 2)
          = h * (2 * p * em₀ + τ * em₀ ^ 2 + 2 * q * pm₀ + κ * pm₀ ^ 2) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh change
    rw [uExpand, vExpand]
    linarith [scaled, start]
  -- The push has squared length `hτ((1 − τ)² + τκ) ≤ hτ ≤ s²`.
  have pushBound : ∑ i, (ε * (h * (1 - τ) * φ i)) ^ 2 + ∑ i, (ε * (h * τ * a i)) ^ 2 ≤
      (|ε| * s) ^ 2 := by
    have uPush : ∑ i, (ε * (h * (1 - τ) * φ i)) ^ 2 = ε ^ 2 * (h * τ * (1 - τ) ^ 2) := by
      have term : ∀ i, (ε * (h * (1 - τ) * φ i)) ^ 2 =
          (ε ^ 2 * h ^ 2 * (1 - τ) ^ 2) * φ i ^ 2 := by
        intro i
        ring
      simp only [term, ← Finset.mul_sum]
      simp only [τ]
      ring
    have vPush : ∑ i, (ε * (h * τ * a i)) ^ 2 = ε ^ 2 * (h * τ * (τ * κ)) := by
      have term : ∀ i, (ε * (h * τ * a i)) ^ 2 = (ε ^ 2 * h ^ 2 * τ ^ 2) * a i ^ 2 := by
        intro i
        ring
      simp only [term, ← Finset.mul_sum]
      simp only [κ]
      ring
    have shape : (1 - τ) ^ 2 + τ * κ ≤ 1 := by
      have room : 0 ≤ τ * (2 - τ - κ) := mul_nonneg hτ (by linarith [curvature])
      nlinarith [room]
    have hτh : 0 ≤ h * τ := mul_nonneg hh hτ
    have total : h * τ * ((1 - τ) ^ 2 + τ * κ) ≤ s ^ 2 :=
      calc h * τ * ((1 - τ) ^ 2 + τ * κ) ≤ h * τ * 1 := mul_le_mul_of_nonneg_left shape hτh
        _ = h * τ := mul_one _
        _ ≤ s ^ 2 := push
    rw [uPush, vPush, mul_pow, sq_abs]
    have scaledPush := mul_le_mul_of_nonneg_left total (sq_nonneg ε)
    calc ε ^ 2 * (h * τ * (1 - τ) ^ 2) + ε ^ 2 * (h * τ * (τ * κ))
        = ε ^ 2 * (h * τ * ((1 - τ) ^ 2 + τ * κ)) := by ring
      _ ≤ ε ^ 2 * s ^ 2 := scaledPush
  exact pair_add (fun i => u i + h * em₀ * φ i) (fun i => v i + h * pm₀ * a i)
    (fun i => ε * (h * (1 - τ) * φ i)) (fun i => ε * (h * τ * a i)) ht
    (mul_nonneg (abs_nonneg ε) hs) linear pushBound

end AcornVerif.Extragradient
