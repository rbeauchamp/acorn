/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebra of bounded-disruption feature retirement

The tester's threshold is `θ = ε · 1/(1−γ)` — PAR-1's relative
negligibility, applied to the Weight projection's γ-derived horizon.
Rust writes that product as `SwiftTdConfig::disruption_bound`. These
theorems are the identities that product claims, universally over ℝ.

No `native_decide`. Each argument is an algebraic identity or a one-line
rearrangement.
-/

namespace AcornVerif

/-- The derived retirement bound: ε times the discount's horizon. -/
noncomputable def theta (ε γ : ℝ) : ℝ := ε * (1 / (1 - γ))

/-- `θ = ε / (1−γ)` whenever `γ ≠ 1` — the same product the Rust
`const fn` writes as `epsilon * discount.horizon()`. -/
theorem theta_eq_epsilon_div_one_sub_gamma (ε γ : ℝ) (hγ : γ ≠ 1) :
    theta ε γ = ε / (1 - γ) := by
  have h : 1 - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  unfold theta
  field_simp [h]

/-- Binary features: zeroing a unit whose weight is `w` changes the
prediction `v = ⋯ + w + ⋯` by exactly `|w|`. -/
theorem prediction_change_eq_abs_weight (v w : ℝ) :
    |v - (v - w)| = |w| := by
  rw [sub_sub_cancel]

/-- A weight below `ε · H` is a relative disruption below ε of the
horizon — the same ε PAR-1 already uses for traces. -/
theorem relative_disruption {w ε H : ℝ} (hH : 0 < H)
    (hw : |w| < ε * H) : |w| / H < ε :=
  (div_lt_iff₀ hH).mpr hw

/-- If every consumer satisfies `|w_i| < θ_i`, then every consumer's
prediction change — which equals `|w_i|` by
`prediction_change_eq_abs_weight` — is below that consumer's own θ.
The every-consumer predicate is this pointwise bound, not a max
taken in one learner and read in another. -/
theorem every_consumer_prediction_change {ι : Type*} (v w θ : ι → ℝ)
    (h : ∀ i, |w i| < θ i) (i : ι) :
    |v i - (v i - w i)| < θ i := by
  rw [prediction_change_eq_abs_weight]
  exact h i

end AcornVerif

namespace AcornVerif.Retirement

/-- A transcript event's lifetime step and bank unit, embedded in naturals. -/
abbrev Event := ℕ × ℕ

/-- An event follows an optional predecessor strictly; the first may be at zero. -/
def After (previous : Option ℕ) (step : ℕ) : Prop :=
  match previous with
  | none => True
  | some p => p < step

/-- The loop performed by `RetirementProgress::from_events`. The complete-body
source bridge in `gates/src/retirement_contract.rs` pins its capacity precheck,
initial predecessor, ordered traversal, rejection and predecessor update. Kani
`retirement_transcript_admission` refines each transition over all Rust words. -/
def admitsFrom (units steps : ℕ) (previous : Option ℕ) : List Event → Prop
  | [] => True
  | e :: es => e.2 < units ∧ e.1 ≤ steps ∧ After previous e.1 ∧
      admitsFrom units steps (some e.1) es

/-- Loop induction characterizes every event and every ordered pair, over lists
of arbitrary length. No bounded unwinding or certified re-execution is used. -/
theorem admitsFrom_iff (units steps : ℕ) (previous : Option ℕ) (events : List Event) :
    admitsFrom units steps previous events ↔
      (∀ e ∈ events, e.2 < units ∧ e.1 ≤ steps ∧ After previous e.1) ∧
      events.Pairwise (fun a b => a.1 < b.1) := by
  induction events generalizing previous with
  | nil => simp [admitsFrom]
  | cons e es ih =>
    simp only [admitsFrom, ih, List.forall_mem_cons, List.pairwise_cons]
    constructor
    · rintro ⟨hu, hs, hp, ht, ho⟩
      refine ⟨⟨⟨hu, hs, hp⟩, ?_⟩, ?_, ho⟩
      · intro a ha
        obtain ⟨au, ast, ae⟩ := ht a ha
        refine ⟨au, ast, ?_⟩
        cases previous with
        | none => trivial
        | some p => exact Nat.lt_trans hp ae
      · intro a ha
        exact (ht a ha).2.2
    · rintro ⟨⟨⟨hu, hs, hp⟩, ht⟩, he, ho⟩
      exact ⟨hu, hs, hp, fun a ha => ⟨(ht a ha).1, (ht a ha).2.1, he a ha⟩, ho⟩

/-- Admission is exactly the bounded, in-bank, lifetime-bounded, strictly ordered
transcript predicate, for every supported length and beyond. -/
theorem transcript_admission_iff (units steps : ℕ) (events : List Event) :
    (events.length ≤ units ∧ admitsFrom units steps none events) ↔
      events.length ≤ units ∧ (∀ e ∈ events, e.2 < units ∧ e.1 ≤ steps) ∧
      events.Pairwise (fun a b => a.1 < b.1) := by
  simp [admitsFrom_iff, After]

/-- The final timestamp of a prefix, retaining the incoming predecessor when
there are no events. This is the logical state threaded by admission. -/
def finalStep (previous : Option ℕ) : List Event → Option ℕ
  | [] => previous
  | e :: es => finalStep (some e.1) es

/-- Raising the lifetime bound preserves every admitted transcript, for every
length. Rust's saturating successor is monotone over every `u64` by Kani. -/
theorem clock_advance_preserves (units steps next : ℕ) (previous : Option ℕ)
    (events : List Event) (hnext : steps ≤ next)
    (h : admitsFrom units steps previous events) :
    admitsFrom units next previous events := by
  rw [admitsFrom_iff] at h ⊢
  exact ⟨fun e he => ⟨(h.1 e he).1, le_trans (h.1 e he).2.1 hnext,
    (h.1 e he).2.2⟩, h.2⟩

/-- Appending one event preserves the entire arbitrary prefix exactly when
that event passes admission after the prefix's final timestamp. -/
theorem append_admission_iff (units steps : ℕ) (previous : Option ℕ)
    (events : List Event) (event : Event) :
    admitsFrom units steps previous (events ++ [event]) ↔
      admitsFrom units steps previous events ∧ event.2 < units ∧
      event.1 ≤ steps ∧ After (finalStep previous events) event.1 := by
  induction events generalizing previous with
  | nil => simp [admitsFrom, finalStep]
  | cons e es ih => simp [admitsFrom, finalStep, ih, and_assoc]

/-- With no incoming predecessor, the loop state is the actual final event's
step. This connects the append theorem to Rust's `events.last()`. -/
theorem finalStep_eq_last (previous : Option ℕ) (events : List Event) :
    finalStep previous events =
      (events.getLast?.map Prod.fst).or previous := by
  induction events generalizing previous with
  | nil => simp [finalStep]
  | cons e es ih =>
    cases es with
    | nil => simp [finalStep]
    | cons a tail =>
      simpa [finalStep, List.getLast?_eq_some_getLast (List.cons_ne_nil a tail)]
        using ih (some e.1)

/-- A reserved slot and a fresh current timestamp preserve all transcript
bounds and ordering. The clock is stored with the transcript, so no independent
restore can lower its bound while retaining the same events. -/
theorem record_preserves (units steps : ℕ) (events : List Event) (unit : ℕ)
    (hprefix : admitsFrom units steps none events)
    (hroom : events.length < units) (hunit : unit < units)
    (hfresh : After (finalStep none events) steps) :
    (events ++ [(steps, unit)]).length ≤ units ∧
      admitsFrom units steps none (events ++ [(steps, unit)]) := by
  constructor
  · simpa using Nat.succ_le_of_lt hroom
  · rw [append_admission_iff]
    exact ⟨hprefix, hunit, le_refl _, hfresh⟩

end AcornVerif.Retirement
