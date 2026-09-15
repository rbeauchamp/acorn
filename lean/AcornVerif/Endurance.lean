/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Endurance
import AcornVerif.CurrentState

/-! # Endurance reduction contracts

Horizon selection uses small closed rational bounds and an analytic power
identity, not replay or native reflection. The invariant is a truncation bound
for unit-bounded cumulants on the frame stream; native binary64 rounding and the
telemetry callback schedule remain separate implementation assumptions.
-/
namespace AcornVerif.Endurance
open Acorn Acorn.Host.Endurance AcornVerif.CurrentArithmetic

/-- Exact numerical values of the complete discount domain. -/
theorem gamma_values (discount : Discount) : numerical32 discount.gamma =
    match discount with
    | .g90 => 7549747 / 8388608
    | .g95 => 15938355 / 16777216
    | .g99 => 4152361 / 4194304 := by
  cases discount
  · change (1:ℚ) * 15099494 * (2:ℚ)^(-24:Int) = _
    norm_num
  · change (1:ℚ) * 15938355 * (2:ℚ)^(-24:Int) = _
    norm_num
  · change (1:ℚ) * 16609444 * (2:ℚ)^(-24:Int) = _
    norm_num

/-- Grouping powers into a short block avoids full-horizon re-execution. -/
theorem block_power (gamma bound : ℚ) (block repetitions : Nat)
    (hg : 0 ≤ gamma) (h : gamma ^ block ≤ bound) :
    gamma ^ (block * repetitions) ≤ bound ^ repetitions := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg hg _) h _

/-- Every closed horizon meets the geometric truncation bound on its exact
binary32 discount. This does not bound accumulated binary64 rounding error. -/
theorem horizon_tail (discount : Discount) :
    numerical32 discount.gamma ^ horizon discount / (1 - numerical32 discount.gamma) <
      (2 / 10000000 : ℚ) := by
  have positive := (AcornVerif.CurrentState.discount_numeric_contract discount).2.1
  have contract := (AcornVerif.CurrentState.discount_numeric_contract discount).2.2.1
  apply (div_lt_iff₀ (by linarith : 0 < 1 - numerical32 discount.gamma)).mpr
  cases discount
  · rw [gamma_values]
    change (7549747 / 8388608 : ℚ) ^ (100 * 2) < _
    have bound : (7549747 / 8388608 : ℚ) ^ 100 ≤ 1 / 30000 := by norm_num
    have grouped := block_power (7549747 / 8388608) (1 / 30000) 100 2 (by norm_num) bound
    exact lt_of_le_of_lt grouped (by norm_num)
  · rw [gamma_values]
    change (15938355 / 16777216 : ℚ) ^ (100 * 4) < _
    have bound : (15938355 / 16777216 : ℚ) ^ 100 ≤ 7 / 1000 := by norm_num
    have grouped := block_power (15938355 / 16777216) (7 / 1000) 100 4 (by norm_num) bound
    exact lt_of_le_of_lt grouped (by norm_num)
  · rw [gamma_values]
    change (4152361 / 4194304 : ℚ) ^ (100 * 20) < _
    have bound : (4152361 / 4194304 : ℚ) ^ 100 ≤ 367 / 1000 := by norm_num
    have grouped := block_power (4152361 / 4194304) (367 / 1000) 100 20 (by norm_num) bound
    exact lt_of_le_of_lt grouped (by norm_num)

/-- Every input frame contributes exactly one count, irrespective of sample timing. -/
theorem ingest_count (r : Reduction) (f : Frame) : (r.ingest f).frames = r.frames + 1 := rfl

/-- Window closure changes neither stream population nor return history. -/
theorem close_preserves (r : Reduction) :
    r.closeWindow.frames = r.frames ∧ r.closeWindow.history = r.history := ⟨rfl, rfl⟩

/-- Every write preserves the history's fixed storage size and bounded retained count. -/
theorem history_bounded (h : History) (f : Channels) :
    (h.push f).slots.size = historyCapacity ∧ (h.push f).count.val ≤ historyCapacity :=
  ⟨by simp, Nat.le_of_lt_succ (h.push f).count.isLt⟩

/-- Rank selection is a first crossing for arbitrary histograms and natural counts. -/
theorem rankIndex_spec (target denominator seen : Nat) (counts : List Nat) (i : Nat)
    (h : rankIndex target denominator seen counts = some i) :
    target ≤ denominator * (seen + (counts.take (i + 1)).sum) ∧
      ∀ j, j < i → denominator * (seen + (counts.take (j + 1)).sum) < target := by
  induction counts generalizing seen i with
  | nil => simp [rankIndex] at h
  | cons count rest ih =>
    simp only [rankIndex] at h
    split at h
    · rename_i crossed
      cases h
      simp only [Nat.zero_add, List.take_succ_cons, List.take_zero, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      exact ⟨crossed, by intro j hj; omega⟩
    · rename_i below
      cases hr : rankIndex target denominator (seen + count) rest with
      | none => simp [hr] at h
      | some k =>
        rw [hr] at h
        change some (Nat.succ k) = some i at h
        cases h
        obtain ⟨hit, first⟩ := ih _ _ hr
        constructor
        · simpa [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using hit
        · intro j hj
          cases j with
          | zero => simpa using (Nat.lt_of_not_ge below)
          | succ j =>
            have earlier := first j (by omega)
            simpa [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using earlier

end AcornVerif.Endurance
