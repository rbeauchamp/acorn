/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import AcornVerif.Generated

/-!
# The value-range projection

A GVF demon estimates a discounted sum of a cumulant in `[0,1]`, so its value
cannot leave `[0, 1/(1-γ)]`. Bounding the weights with `!is_finite()` instead
would be a predicate on the wrong set: it admits all of ±3.4e38, while the
reachable range for `γ = 0.99` is `[0, 100]`. Everything between those two is
finite and illegal, so such a guard never fires on a diverged weight.

`agent::swifttd::project` is the predicate on the right set. Note the scope:
`projectR` below models
the *symmetric* `project`, which guards weights (`Weight::set`, bound
`Discount::horizon`). The `[0, horizon]` guard on the prediction itself is
`project_nonneg` / `Prediction::project`, whose totality is covered by the Kani
harness `project_nonneg_is_total_and_bounded` and which is not modelled here.

The theorems supply the two things a projection needs in order to be
*principled rather than cosmetic*:

* it must not discard reachable values — the projection set has to contain the
  fixed point (`horizon_covers_true_bound`, checked over the exact `f32`
  constants this build uses), and
* it must not increase error — projection onto a convex set containing the
  target is non-expansive (`project_nonexpansive`).

Bit-precise totality over every `f32` (including `NaN` and `±inf`) is the
complementary obligation and lives in Kani, `src/proofs.rs`: the range invariant
is *inductive*, so one update step suffices and no reasoning over 10⁷ steps is
needed.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- The projection `agent::swifttd::project` applies, over the reals:
clamp `v` into `[-b, b]`. -/
def projectR (b v : ℝ) : ℝ := max (-b) (min b v)

/-- The projection lands inside the bound. Mirrors the Kani harness
`project_is_total_and_bounded`, which additionally covers `NaN` and `±inf`. -/
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

/-- The projection fixes what is already in range: it discards no reachable
value. Mirrors the Kani harness `project_is_identity_in_range`. -/
theorem project_id_of_mem (b v : ℝ) (h1 : -b ≤ v) (h2 : v ≤ b) :
    projectR b v = v := by
  unfold projectR
  rw [min_eq_right h2, max_eq_right h1]

/-- **Projection is non-expansive** toward any target inside the bound.

The target is assumed to lie inside the rail. This establishes non-increasing
distance, not strict contraction, convergence, or admissibility of that rail
for each coefficient of a learned representation. -/
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

/-- **The generated-constant link.**

For every discount in the closed Rust set, the horizon the Rust build actually
computes in `f32` is at least the true bound `1/(1-γ)` — so the projection set
contains every value the GVF can reach, and `project_nonexpansive` applies.

The constants come from `AcornVerif.Generated`, emitted by `acorn emit-lean` as the
*exact* rationals the `f32`s hold.

Be precise about what enforces what. If a constant changes in Rust and
`Generated.lean` is *not* regenerated, this proof still succeeds — about the old
number. What catches that is the CI step `acorn emit-lean && git diff
--exit-code`, i.e. regeneration, not the proof. The proof catches the other half:
a *regenerated* constant that fails to cover its true bound fails here. And
because the Lean package is deliberately not in CI (Mathlib's toolchain weight),
that half is a **local** gate — `lake build` on a developer's machine.

The margin is thin and in the right direction — for `γ = 0.99` the computed
horizon exceeds the true bound by about 4·10⁻⁶ — which is precisely the kind of
fact that is invisible without a link like this. -/
theorem horizon_covers_true_bound :
    ∀ p ∈ Generated.discounts, 1 / (1 - p.1) ≤ p.2 := by
  intro p hp
  simp only [Generated.discounts] at hp
  fin_cases hp <;>
    norm_num [Generated.gammaG90, Generated.gammaG95, Generated.gammaG99,
      Generated.horizonG90, Generated.horizonG95, Generated.horizonG99]

/-- **The fixed point of a constant-cumulant GVF.**

If the cumulant is the constant `c` at every step, the TD target `v = c + γ·v`
has the unique solution `c / (1 - γ)`. For `c = 1` and `γ = 0.99` that is
exactly `100`.

This is stated because a learner's convergence to it is the one property worth
knowing about a constant-reward problem, and it is *decidable* — a sampled run
that watches an estimate approach 100 observes one trajectory, where this
settles every one. It also says what `Discount.horizon` is: the fixed point of
the largest cumulant the demons admit, which is why projecting onto it discards
nothing reachable. -/
theorem constant_cumulant_fixed_point (c γ : ℝ) (hγ : γ < 1) :
    c / (1 - γ) = c + γ * (c / (1 - γ)) := by
  have h : (1 : ℝ) - γ ≠ 0 := by linarith
  field_simp
  ring

/-- The fixed point is *unique*: nothing else satisfies the TD equation, so a
learner that reaches a stationary point of a constant-cumulant problem has
reached this value and no other. -/
theorem constant_cumulant_fixed_point_unique (c γ v : ℝ) (hγ : γ < 1)
    (hv : v = c + γ * v) : v = c / (1 - γ) := by
  have h : (1 : ℝ) - γ ≠ 0 := by linarith
  rw [eq_div_iff h]
  linear_combination hv

/-- Every discount in the closed set is a proper contraction. -/
theorem gamma_is_contraction :
    ∀ p ∈ Generated.discounts, 0 < p.1 ∧ p.1 < 1 := by
  intro p hp
  simp only [Generated.discounts] at hp
  fin_cases hp <;>
    norm_num [Generated.gammaG90, Generated.gammaG95, Generated.gammaG99]

end AcornVerif
