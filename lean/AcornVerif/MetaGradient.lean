/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The meta-gradient registers of SwiftTD

SwiftTD carries the derivative `h[i] = ∂w[i]/∂β[i]` in **three** scalar
registers rather than a history, because equation (32) of the paper needs both
`h_{t−1}` and `h_{t−2}` at once, and equation (30) supplies the second:
`∂δ′_t/∂β[i] ≈ −h_{t−2}[i]·ϕ_{t−1}[i]`.

Which register holds which lag is the whole content of the scheme, and it is
invisible from the assignment statements alone. That is what this file makes
machine-checked: the update in `src/agent/swifttd.rs` is the recurrence the
paper derives, for every input — not for a sample of them.

Reference: Javed, Sharifnassab & Sutton, *SwiftTD: A Fast and Robust Algorithm
for Temporal Difference Learning*, Reinforcement Learning Journal, vol. 2
(2024), pp. 840–863, Algorithm 1, Algorithm 3 and equations (23), (30), (32).
<https://rlj.cs.umass.edu/2024/papers/RLJ_RLC_2024_111.pdf>
Opened that PDF (24 pages; labels 1–24; header `RLJ| RLC 2024`). Algorithm 1
is printed page 9 (`"Algorithm 1: SwiftTD"` / `"p[i] ← p[i] + φ[i] h[i]"`).
§6 on printed page 10: `"6 SwiftTD: Fast and Robust Learning by Combining the
Three Ideas"` / `"Algorithm 1 is the pseudocode for SwiftTD."` Equation (32)
is printed page 18: `"The final h_t[i] update is:"`. Companion HTML
`Paper111.html` records the journal span pp. 840–863; those numbers are not
on this PDF's face. **Status:** this file is the proof owner of that
recurrence over ℝ. The Lean↔Rust transcription match is **assumed**.

## What this file does and does not establish

The definitions below are a **hand transcription** of the register updates in
`src/agent/swifttd.rs`. Lean checks the algebra; that the transcription matches
the Rust is *assumed*, and reviewed by reading the two side by side. The
generated constants in `AcornVerif.Generated` exist because that class of drift is
real — the dynamics get no such treatment, and a reader should hold this file to
the weaker standard accordingly.

Scope of the model, stated so it is not read as more: it covers a feature that
runs **both** loops on a step — eligible and active. A feature that is active
but not eligible runs only the second loop; pruning clears every register for
such a feature (`SwiftTd::drop_from_eligible`), so it re-enters with all three
at zero, which is the state `run` starts from. The clip re-anchor and the
step-size decay branch both zero registers rather than evolving them, and are
outside the model.

Everything here is real arithmetic. `f32` rounding is outside the model, and
nothing below should be read as covering it.
-/

namespace AcornVerif

noncomputable section

/-- One feature's inputs over a single step: the TD error `δ′`, the dutch trace
`z̄`, the trace increment `zδ`, the shared accumulator `vδ`, the eligibility
trace `z` after the second loop's increment, and the feature value `ϕ`. -/
structure StepInput where
  /-- The TD error `δ′ = r + γv − v_old`. -/
  delta : ℝ
  /-- The dutch trace `z̄` at the start of the step. -/
  zbar : ℝ
  /-- The trace increment `zδ` **from the previous step**, which the first loop
  applies before zeroing it (`swifttd.rs`: the `z_delta[idx] * v_delta` term,
  then `self.z_delta[idx] = 0.0`). -/
  zdeltaPrev : ℝ
  /-- The trace increment `zδ` computed for **this** step, which the second loop
  applies (`swifttd.rs`: `z_delta[idx] = (eta / e) * alpha`). Distinct from
  `zdeltaPrev`: conflating them would make the model agree with the code only
  when a feature's increment happens to be unchanged between steps. -/
  zdelta : ℝ
  /-- The shared `δw·ϕ` accumulator `vδ` carried from the previous step. -/
  vdelta : ℝ
  /-- The eligibility trace `z` after the second loop's increment. -/
  z : ℝ
  /-- The feature value `ϕ` (1 on the active set, for binary features). -/
  phi : ℝ

/-- The increment equation (32) adds to the previous meta-gradient:
`Δ_t = δ′·z̄ − zδ·vδ`. -/
def StepInput.increment (p : StepInput) : ℝ :=
  p.delta * p.zbar - p.zdeltaPrev * p.vdelta

/-- The three meta-gradient registers, named as the code names them. -/
structure Regs where
  /-- `h` — the register the second loop multiplies by `zδ·ϕ`. -/
  h : ℝ
  /-- `h_temp` — the register the meta-gradient accumulates into. -/
  hTemp : ℝ
  /-- `h_old` — the register the second loop multiplies by `ϕ·(z − zδ)`. -/
  hOld : ℝ

/-- Equation (32), printed page 18 of the opened SwiftTD PDF (`"The final
h_t[i] update is:"`), as a recurrence on two successive meta-gradients.

`prev` is `h_{t−1}` and `prev2` is `h_{t−2}`; the result is `h_t`. This is the
specification — the right-hand side of (32) with `ϕ`-factors kept explicit and
`e^{β}ϕ` written as the trace increment `zδ` that the algorithm computes for
it. -/
def eq32 (prev prev2 : ℝ) (p : StepInput) : ℝ :=
  prev + p.increment - prev2 * p.phi * (p.z - p.zdelta) - prev * p.zdelta * p.phi

/-- One step of the register discipline of **Algorithm 1** (printed page 9;
named by §6 printed page 10) and **Algorithm 3**.

First loop: `h_old ← h`, `h ← h_temp`, `h_temp ← h + δ′z̄ − zδ·vδ`.
Second loop: `h_temp ← h_temp − h_old·ϕ·(z − zδ) − h·zδ·ϕ`.

`h` *lags*: it takes the previous step's completed value, and this step's
increment goes to `h_temp`. -/
def stepPaper (r : Regs) (p : StepInput) : Regs :=
  let hOld := r.h
  let h := r.hTemp
  let hTemp := h + p.increment
  { h := h
    hTemp := hTemp - hOld * p.phi * (p.z - p.zdelta) - h * p.zdelta * p.phi
    hOld := hOld }

/-- One step of the register discipline of the authors' reference C++
implementation (`github.com/kjaved0/swifttd`, `SwiftTDBinaryFeatures::Step`),
which **Swift-Sarsa**'s Algorithm 1 also prints.

First loop: `h_old ← h`, `h ← h_temp + δ′z̄ − zδ·vδ`, `h_temp ← h`.
Second loop: `h_temp ← h − h_old·ϕ·(z − zδ) − h·zδ·ϕ`.

The increment is folded into `h` instead of `h_temp`, so `h` no longer lags. -/
def stepRef (r : Regs) (p : StepInput) : Regs :=
  let hOld := r.h
  let h := r.hTemp + p.increment
  { h := h
    hTemp := h - hOld * p.phi * (p.z - p.zdelta) - h * p.zdelta * p.phi
    hOld := hOld }

/-- One step of Algorithm 1's registers (printed page 9) computes the
right-hand side of equation (32) (printed page 18), with `h_temp` carrying
`h_{t−1}` and `h` carrying `h_{t−2}` on entry.

Holds by `rfl`: `eq32` and `stepPaper` are two spellings of one expression, and
that is the point of stating it — it names the correspondence a reader must
check against the paper. The transcription from `src/agent/swifttd.rs` is
`assumed`; see the module note. -/
theorem stepPaper_eq_eq32 (r : Regs) (p : StepInput) :
    (stepPaper r p).hTemp = eq32 r.hTemp r.h p := rfl

/-- The register roles Algorithm 1 maintains, stated so they cannot be read off
wrongly: after a step, `h` holds what `h_temp` held (the completed `h_{t−1}`)
and `h_old` holds what `h` held (`h_{t−2}`). -/
theorem stepPaper_shifts_lags (r : Regs) (p : StepInput) :
    (stepPaper r p).h = r.hTemp ∧ (stepPaper r p).hOld = r.h := by
  constructor <;> rfl

/-- The register state after `n` steps of Algorithm 1's discipline, from the
all-zero start every learner begins in. -/
def run (p : ℕ → StepInput) : ℕ → Regs
  | 0 => { h := 0, hTemp := 0, hOld := 0 }
  | n + 1 => stepPaper (run p n) (p n)

/-- The lag discipline, stated over a trajectory: after `n+2` steps the
accumulated meta-gradient is the equation-(32) recurrence applied to the **two
previous completed meta-gradients**, from steps `n+1` and `n`.

Scope, stated plainly because the opposite is tempting: this holds by
`rfl`. `stepPaper` was *defined* to shift the lags, so unfolding it produces
this statement, and definitional equality is transitive through the `calc`
below. It is a legibility result — it puts the register roles in a form a reader
can check against equation (32) — and it is **not** independent evidence that
the code is right. The evidence that the code differs from the alternative is
`stepRef_hTemp_error` and `metaTrace_lag`, which are algebraic identities that
`rfl` cannot reach. -/
theorem run_realizes_eq32 (p : ℕ → StepInput) (n : ℕ) :
    (run p (n + 2)).hTemp
      = eq32 (run p (n + 1)).hTemp (run p n).hTemp (p (n + 1)) := by
  have hlag : (run p (n + 1)).h = (run p n).hTemp := rfl
  calc (run p (n + 2)).hTemp
      = eq32 (run p (n + 1)).hTemp (run p (n + 1)).h (p (n + 1)) :=
        stepPaper_eq_eq32 _ _
    _ = eq32 (run p (n + 1)).hTemp (run p n).hTemp (p (n + 1)) := by rw [hlag]

/-- **The discrepancy, as an identity.** From the same state and inputs, the
reference form's meta-gradient differs from equation (32) by exactly
`−Δ_t · zδ · ϕ`.

This is the whole error and it is stated for every state and every input, so no
choice of parameters escapes it. The mechanism it names: folding step `t`'s
increment into `h` before the second loop means the `h·zδ·ϕ` term decays the
current increment along with the accumulated gradient, which (32) does not do.
It vanishes only where `Δ_t`, `zδ` or `ϕ` is zero — that is, on a step that
contributes no meta-gradient at all. -/
theorem stepRef_hTemp_error (r : Regs) (p : StepInput) :
    (stepRef r p).hTemp - (stepPaper r p).hTemp
      = -(p.increment * p.zdelta * p.phi) := by
  simp only [stepRef, stepPaper]
  ring

/-- The reference form also breaks the lag: its `h` carries this step's
increment, where Algorithm 1's carries the previous step's completed value.
The two differ by `Δ_t` at every step. -/
theorem stepRef_h_error (r : Regs) (p : StepInput) :
    (stepRef r p).h - (stepPaper r p).h = p.increment := by
  simp only [stepRef, stepPaper]
  ring

/-- The meta-trace `p` accumulates `h_{t−1}·ϕ_t` — equation (23): *"accumulating
`h_{t−1}[i]ϕ_t[i]` in a trace decayed by `λγ`"*. Algorithm 1's second loop
therefore reads `h`, which holds `h_{t−1}` at that point. -/
def metaTraceIncrementPaper (r : Regs) (p : StepInput) : ℝ := p.phi * r.hTemp

/-- The reference implementation and Swift-Sarsa's Algorithm 1 read `h_old`
instead. -/
def metaTraceIncrementRef (r : Regs) (p : StepInput) : ℝ := p.phi * r.h

/-- **The meta-trace lag, as an identity.** Reading `h_old` rather than `h`
accumulates `h_{t−2}·ϕ_t` where equation (23) specifies `h_{t−1}·ϕ_t`: the
meta-trace is one step stale, by exactly `ϕ·(h_{t−2} − h_{t−1})`. -/
theorem metaTrace_lag (r : Regs) (p : StepInput) :
    metaTraceIncrementRef r p - metaTraceIncrementPaper r p
      = p.phi * (r.h - r.hTemp) := by
  simp only [metaTraceIncrementRef, metaTraceIncrementPaper]
  ring

/-!
## The meta-update gain

Algorithm 1 updates `β` by `β ← β + (θ / e^{β}) · (δ′ − vδ) · p`. The
coefficient on the meta-gradient is therefore a function of `β` alone, and it
*grows* as the step size falls. Algorithm 3 — the derivation's own listing —
writes the same coefficient as `θ / (e^{β} + ϵ)`, which bounds it by `θ/ϵ`;
Algorithm 1 drops that `ϵ`, having reassigned the symbol to the step-size decay
factor.
-/

/-- The coefficient Algorithm 1 applies to the meta-gradient. -/
def metaGain (theta beta : ℝ) : ℝ := theta / Real.exp beta

/-- The coefficient Algorithm 3 applies, with its stabiliser. -/
def metaGainStabilised (theta beta epsilon : ℝ) : ℝ := theta / (Real.exp beta + epsilon)

/-- At the floor of the configured range the gain is `θ / η_min`.

This crate configures three `θ`: `1e-3` for `SwiftTdConfig::demon` and
`::control`, and `3e-2` for `::option_skill`. Against `η_min = 1e-10` that is a
gain of `1e7` for the first two and **`3e8`** for the third — the worst case,
and the one worth quoting. A meta-gradient of magnitude `g` moves `β` by
`3e8 · g` in a single step, while the whole range `[ln η_min, ln η]` is about
`21` wide. -/
theorem metaGain_at_floor (theta etaMin : ℝ) (h : 0 < etaMin) :
    metaGain theta (Real.log etaMin) = theta / etaMin := by
  simp [metaGain, Real.exp_log h]

/-- The gain is strictly decreasing in `β`: the smaller the step size, the
larger the multiplier on the meta-gradient. -/
theorem metaGain_strictAnti (theta : ℝ) (hθ : 0 < theta) :
    StrictAnti (metaGain theta) := by
  intro a b hab
  simp only [metaGain]
  exact div_lt_div_of_pos_left hθ (Real.exp_pos a) (Real.exp_lt_exp.2 hab)

/-- Algorithm 3's stabiliser bounds the gain by `θ/ϵ` for every `β`, which
Algorithm 1's form admits no analogue of. -/
theorem metaGainStabilised_le (theta beta epsilon : ℝ) (hθ : 0 ≤ theta)
    (hε : 0 < epsilon) :
    metaGainStabilised theta beta epsilon ≤ theta / epsilon := by
  simp only [metaGainStabilised]
  exact div_le_div_of_nonneg_left hθ hε (by linarith [Real.exp_pos beta])

/-- Reachability of the step-size floor: for any current log step size `β`
and configuration `(θ > 0, η_min > 0)`, there exists a negative meta-gradient
increment `g < 0` such that the updated log step size `β + metaGain θ β * g`
reaches or crosses the floor `ln η_min`.

Citations: Javed, Sharifnassab & Sutton, SwiftTD (RLJ 2024, eq. 20, Algorithm 1;
eq. 27, Algorithm 3). -/
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

/-- The step-size floor is absorbing under non-positive meta-updates:
if `β ≤ ln η_min` and `g ≤ 0`, then the updated `β + metaGain θ β * g ≤ ln η_min`.

Citations: Javed, Sharifnassab & Sutton, SwiftTD (RLJ 2024, eq. 20, Algorithm 1;
eq. 27, Algorithm 3). -/
theorem beta_floor_absorbing (theta beta etaMin g : ℝ) (hθ : 0 ≤ theta)
    (hβ : beta ≤ Real.log etaMin) (hg : g ≤ 0) :
    beta + metaGain theta beta * g ≤ Real.log etaMin := by
  have h_prod : metaGain theta beta * g ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hθ (le_of_lt (Real.exp_pos beta))) hg
  linarith

end

end AcornVerif
