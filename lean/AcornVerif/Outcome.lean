/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import AcornSpec.Collapse

/-!
# The outcome tally behind every published probability of improvement

`AcornSpec.Collapse` classifies each paired seed difference once into the
closed `Outcome` (win, tie, loss), folds only those outcomes into a
`Tally`, and defines the point probability of improvement from the counts:
`Tally.poi = (wins + ties/2) / seeds`. Three facts make that a decomposition
of the registered statistic rather than a second one, and this file proves
them over every population, not the recorded ones:

- `winCredit` is the registered piecewise credit (1, ½, 0);
- the tally partitions the population — every seed is exactly one outcome;
- the tally's `poi` is the mean of the per-seed credits, which is the
  registered definition of the point probability of improvement.

A count folded from the wrong arm — a tie recorded as a win — leaves the
partition intact and breaks the mean identity, so it cannot pass this file.
-/

namespace AcornVerif

open AcornSpec

/-- `winCredit` is the registered piecewise credit: 1 for a positive
difference, ½ for zero, 0 otherwise. -/
theorem winCredit_eq_registered (d : Rat) :
    winCredit d = if 0 < d then 1 else if d == 0 then 1/2 else 0 := by
  unfold winCredit Outcome.ofDiff
  split_ifs <;> rfl

/-- Recording an outcome grows the tally by exactly one seed. -/
theorem tally_record_seeds (t : Tally) (o : Outcome) :
    (t.record o).seeds = t.seeds + 1 := by
  cases o <;> simp [Tally.record, Tally.seeds] <;> omega

/-- Recording an outcome adds exactly its credit to `wins + ties/2`. -/
theorem tally_record_credit (t : Tally) (o : Outcome) :
    ((t.record o).wins : Rat) + ((t.record o).ties : Rat) / 2
      = ((t.wins : Rat) + (t.ties : Rat) / 2) + o.credit := by
  cases o <;> simp [Tally.record, Outcome.credit] <;> ring

/-- Over a list, the tally fold adds one seed per difference. -/
theorem tally_foldl_seeds (l : List Rat) (t : Tally) :
    (l.foldl (fun t d => t.record (Outcome.ofDiff d)) t).seeds = t.seeds + l.length := by
  induction l generalizing t with
  | nil => simp
  | cons d l ih => rw [List.foldl_cons, ih, tally_record_seeds, List.length_cons]; omega

/-- Over a list, the tally fold adds each difference's win credit to
`wins + ties/2`. -/
theorem tally_foldl_credit (l : List Rat) (t : Tally) :
    ((l.foldl (fun t d => t.record (Outcome.ofDiff d)) t).wins : Rat)
        + ((l.foldl (fun t d => t.record (Outcome.ofDiff d)) t).ties : Rat) / 2
      = ((t.wins : Rat) + (t.ties : Rat) / 2) + (l.map winCredit).sum := by
  induction l generalizing t with
  | nil => simp
  | cons d l ih =>
    rw [List.foldl_cons, ih, tally_record_credit, List.map_cons, List.sum_cons]
    unfold winCredit
    ring

/-- Partition: the tally's seeds are the population's size — every paired
difference is exactly one of win, tie, loss. -/
theorem tally_partitions (diffs : Array Rat) : (tally diffs).seeds = diffs.size := by
  unfold tally
  rw [← Array.foldl_toList, tally_foldl_seeds]
  simp [Tally.zero, Tally.seeds]

/-- A left fold of `+` from `a` is `a` plus the sum — the form `ratMean`
computes. -/
theorem foldl_add_eq_sum (l : List Rat) (a : Rat) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons]; ring

/-- The point probability of improvement is the mean win credit: for every
nonempty population, `ratMean` of the per-seed credits is exactly the
tally's `(wins + ties/2) / seeds`. -/
theorem tally_poi_eq_mean_credit (diffs : Array Rat) (h : diffs.size ≠ 0) :
    ratMean (diffs.map winCredit) = some (tally diffs).poi := by
  have hne : ¬ (diffs.map winCredit).isEmpty = true := by
    rw [Array.isEmpty_iff_size_eq_zero, Array.size_map]
    exact h
  have hsum : (diffs.map winCredit).foldl (· + ·) 0
      = ((tally diffs).wins : Rat) + ((tally diffs).ties : Rat) / 2 := by
    rw [← Array.foldl_toList, Array.toList_map, foldl_add_eq_sum]
    unfold tally
    rw [← Array.foldl_toList, tally_foldl_credit]
    simp [Tally.zero]
  unfold ratMean
  rw [if_neg hne, hsum, Array.size_map, Tally.poi, tally_partitions]

/-- A paired summary's `poi` is its tally's, by definition. -/
theorem pairedSummary_poi_is_tally (domain : UInt64) (diffs : SeedDiffs) :
    (pairedSummaryAt domain diffs).poi = (tally diffs.toArray).poi := rfl

end AcornVerif
