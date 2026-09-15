/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Encoding

/-!
# Machine-state interval admission

An interval includes finite ordered endpoints. A stored inhabitant carries the
same interval as a type index, so a value cannot be installed under a different
configuration without a new admission. Projection selects original words rather
than reconstructing floats; identity admission retains signed zero exactly.
The interval theorem is about machine order, not an ideal-real error estimate.
-/

namespace Acorn

/-- Closed finite machine interval, with legality supplied at construction. -/
structure Interval32 where
  /-- Lower endpoint, retained bit for bit. -/
  lower : Binary32
  /-- Upper endpoint, retained bit for bit. -/
  upper : Binary32
  /-- The lower endpoint excludes infinities and NaNs. -/
  lowerFinite : lower.Finite
  /-- The upper endpoint excludes infinities and NaNs. -/
  upperFinite : upper.Finite
  /-- Endpoints are ordered by signed machine magnitude. -/
  ordered : lower.key ≤ upper.key

namespace Interval32

/-- Word-order admission is equivalent to the stored finite endpoint predicate. -/
theorem ordered_word_iff (lower upper : Binary32) :
    (lower.Finite ∧ upper.Finite ∧ upper.less lower = false) ↔
      (lower.Finite ∧ upper.Finite ∧ lower.key ≤ upper.key) := by
  constructor <;> rintro ⟨hl, hu, ho⟩
  · refine ⟨hl, hu, ?_⟩
    rw [Binary32.less_finite _ _ hu hl] at ho
    simp only [decide_eq_false_iff_not] at ho
    omega
  · refine ⟨hl, hu, ?_⟩
    rw [Binary32.less_finite _ _ hu hl]
    simp only [decide_eq_false_iff_not]
    omega

/-- The interval constructor's decision procedure compares fixed-width fields. -/
def orderedDecidable (lower upper : Binary32) :
    Decidable (lower.Finite ∧ upper.Finite ∧ lower.key ≤ upper.key) :=
  decidable_of_iff (lower.Finite ∧ upper.Finite ∧ upper.less lower = false)
    (ordered_word_iff lower upper)

/-- Admit raw endpoints without changing their bits; refuse unordered or
nonfinite endpoints before constructing an interval. -/
def admit (lower upper : Binary32) : Option Interval32 :=
  letI := orderedDecidable lower upper
  if h : lower.Finite ∧ upper.Finite ∧ lower.key ≤ upper.key then
    some ⟨lower, upper, h.1, h.2.1, h.2.2⟩
  else none

/-- Successful interval admission retains both original endpoint encodings. -/
theorem interval_admit_exact (lower upper : Binary32) (range : Interval32)
    (h : admit lower upper = some range) : range.lower = lower ∧ range.upper = upper := by
  unfold admit at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · contradiction

/-- Interval refusal is precisely failure of finite ordered endpoint admission. -/
theorem interval_admit_refuses (lower upper : Binary32) :
    admit lower upper = none ↔ ¬ (lower.Finite ∧ upper.Finite ∧ lower.key ≤ upper.key) := by
  simp [admit]

/-- The stored invariant, including finiteness independently of observations. -/
def Contains (range : Interval32) (value : Binary32) : Prop :=
  value.Finite ∧ range.lower.key ≤ value.key ∧ value.key ≤ range.upper.key

/-- Finite interval membership can be decided with two fixed-word comparisons. -/
theorem contains_word_iff (range : Interval32) (value : Binary32) :
    (value.Finite ∧ value.less range.lower = false ∧ range.upper.less value = false) ↔
      range.Contains value := by
  constructor <;> rintro ⟨hf, hl, hu⟩
  · rw [Binary32.less_finite _ _ hf range.lowerFinite] at hl
    rw [Binary32.less_finite _ _ range.upperFinite hf] at hu
    simp only [decide_eq_false_iff_not] at hl hu
    exact ⟨hf, by omega, by omega⟩
  · refine ⟨hf, ?_, ?_⟩
    · rw [Binary32.less_finite _ _ hf range.lowerFinite]
      simp only [decide_eq_false_iff_not]
      omega
    · rw [Binary32.less_finite _ _ range.upperFinite hf]
      simp only [decide_eq_false_iff_not]
      omega

instance (range : Interval32) (value : Binary32) : Decidable (range.Contains value) :=
  decidable_of_iff
    (value.Finite ∧ value.less range.lower = false ∧ range.upper.less value = false)
    (contains_word_iff range value)

/-- Machine-order bounds between finite endpoints exclude all infinite/NaN words. -/
theorem finite_between (range : Interval32) (value : Binary32)
    (hl : range.lower.key ≤ value.key) (hu : value.key ≤ range.upper.key) :
    value.Finite := by
  have hlf := range.lowerFinite
  have huf := range.upperFinite
  unfold Binary32.Finite at *
  cases hv : value.negative <;> cases hlower : range.lower.negative <;>
    cases hupper : range.upper.negative <;>
    simp only [Binary32.key, hv, hlower, hupper, Bool.false_eq_true,
      if_false, if_true] at hl hu <;> omega

/-- Total saturation, following the current low-before-high branch order.
All input encodings are admitted; a NaN selects the original lower endpoint. -/
def saturate (range : Interval32) (value : Binary32) : Binary32 :=
  value.saturate range.lower range.upper

/-- The actual saturation definition establishes the invariant for every word. -/
theorem saturate_contains (range : Interval32) (value : Binary32) :
    range.Contains (range.saturate value) := by
  unfold saturate Binary32.saturate
  by_cases hn : value.isNaN = true
  · simp only [hn, Bool.true_or, ↓reduceIte]
    exact ⟨range.lowerFinite, Int.le_refl _, range.ordered⟩
  have hnf : value.isNaN = false := Bool.eq_false_iff.mpr hn
  simp only [Binary32.less_eq_key, hnf,
    Binary32.finite_not_nan range.lower range.lowerFinite,
    Binary32.finite_not_nan range.upper range.upperFinite,
    Bool.not_false, Bool.true_and, Bool.false_or, decide_eq_true_eq]
  split
  · exact ⟨range.lowerFinite, Int.le_refl _, range.ordered⟩
  · rename_i hlo
    split
    · exact ⟨range.upperFinite, range.ordered, Int.le_refl _⟩
    · rename_i hhi
      have hl : range.lower.key ≤ value.key := by omega
      have hu : value.key ≤ range.upper.key := by omega
      exact ⟨range.finite_between value hl hu, hl, hu⟩

/-- Legal inputs are preserved bit for bit, including either zero encoding. -/
theorem saturate_identity (range : Interval32) (value : Binary32)
    (h : range.Contains value) : range.saturate value = value := by
  rcases h with ⟨hf, hl, hu⟩
  have hln : ¬ value.key < range.lower.key := by omega
  have hun : ¬ range.upper.key < value.key := by omega
  simp [saturate, Binary32.saturate, Binary32.less_eq_key,
    Binary32.finite_not_nan value hf,
    Binary32.finite_not_nan range.lower range.lowerFinite,
    Binary32.finite_not_nan range.upper range.upperFinite, hln, hun]

/-- Saturation is idempotent on every raw encoding, not only finite inputs. -/
theorem saturate_idempotent (range : Interval32) (value : Binary32) :
    range.saturate (range.saturate value) = range.saturate value :=
  range.saturate_identity _ (range.saturate_contains value)

end Interval32

/-- A zero-centered interval used by signed numerical state. Symmetry is a
stored relation between its endpoints, not a caller-supplied larger budget. -/
structure Symmetric32 where
  /-- Owning finite interval. -/
  range : Interval32
  /-- Its lower endpoint is the exact sign change of the upper endpoint. -/
  symmetric : range.lower = range.upper.negate
  /-- Positive zero is legal, including for NaN recovery. -/
  zeroLegal : range.Contains .zero

namespace Symmetric32

/-- The original high-before-low projection establishes the owning interval
on all raw inputs, preserving zero signs and returning zero on every NaN. -/
theorem symmetric_project_contains (domain : Symmetric32) (raw : Binary32) :
    domain.range.Contains (raw.project domain.range.upper) := by
  unfold Binary32.project
  split
  · exact domain.zeroLegal
  · rename_i hn
    have hnf : raw.isNaN = false := Bool.eq_false_iff.mpr hn
    simp only [Binary32.less_eq_key, hnf,
      Binary32.finite_not_nan _ domain.range.upperFinite,
      ← domain.symmetric, Binary32.finite_not_nan _ domain.range.lowerFinite,
      Bool.not_false, Bool.true_and, decide_eq_true_eq]
    split
    · exact ⟨domain.range.upperFinite, domain.range.ordered, Int.le_refl _⟩
    · rename_i hu
      split
      · exact ⟨domain.range.lowerFinite, Int.le_refl _, domain.range.ordered⟩
      · rename_i hl
        have hlo : domain.range.lower.key ≤ raw.key := by omega
        have hhi : raw.key ≤ domain.range.upper.key := by omega
        exact ⟨domain.range.finite_between raw hlo hhi, hlo, hhi⟩

/-- Signed projection preserves every legal storage word, including signed zero. -/
theorem symmetric_project_identity (domain : Symmetric32) (raw : Binary32)
    (h : domain.range.Contains raw) : raw.project domain.range.upper = raw := by
  rcases h with ⟨hf, hl, hu⟩
  have hlo : ¬ raw.key < domain.range.lower.key := by omega
  have hhi : ¬ domain.range.upper.key < raw.key := by omega
  simp [Binary32.project, Binary32.less_eq_key, ← domain.symmetric,
    Binary32.finite_not_nan raw hf,
    Binary32.finite_not_nan _ domain.range.lowerFinite,
    Binary32.finite_not_nan _ domain.range.upperFinite, hlo, hhi]

/-- Repeated signed projection changes no word after the first legal write. -/
theorem symmetric_project_idempotent (domain : Symmetric32) (raw : Binary32) :
    (raw.project domain.range.upper).project domain.range.upper = raw.project domain.range.upper :=
  domain.symmetric_project_identity _ (domain.symmetric_project_contains raw)

end Symmetric32

/-- A machine value indexed by the exact immutable interval owning every write. -/
structure Bounded32 (range : Interval32) where
  /-- Original stored word. -/
  value : Binary32
  /-- Evidence of the stored invariant. -/
  legal : range.Contains value

namespace Bounded32

/-- Signed projection retains the exact branch semantics of machine projection. -/
def projectSymmetric (domain : Symmetric32) (raw : Binary32) : Bounded32 domain.range :=
  ⟨raw.project domain.range.upper, domain.symmetric_project_contains raw⟩

/-- Project arbitrary raw machine input through the receiving interval. -/
def project (range : Interval32) (raw : Binary32) : Bounded32 range :=
  ⟨range.saturate raw, range.saturate_contains raw⟩

/-- Durable admission is identity or refusal; it never clamps file values. -/
def admit (range : Interval32) (raw : Binary32) : Option (Bounded32 range) :=
  if h : range.Contains raw then some ⟨raw, h⟩ else none

/-- Legal stored words round-trip exactly, including the sign bit of zero. -/
theorem admit_self {range : Interval32} (stored : Bounded32 range) :
    admit range stored.value = some stored := by
  simp only [admit, dif_pos stored.legal]

/-- Successful admission preserves the exact raw input and establishes legality. -/
theorem admit_exact (range : Interval32) (raw : Binary32) (stored : Bounded32 range)
    (h : admit range raw = some stored) : stored.value = raw ∧ range.Contains raw := by
  unfold admit at h
  split at h
  · rename_i hlegal
    cases h
    exact ⟨rfl, hlegal⟩
  · contradiction

/-- Refusal occurs exactly for an input outside the receiving invariant. -/
theorem admit_refuses (range : Interval32) (raw : Binary32) :
    admit range raw = none ↔ ¬ range.Contains raw := by
  simp [admit]

end Bounded32
end Acorn
