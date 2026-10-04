/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval

/-!
# Lattice points near a walk

A counting argument over the integer lattice, with no reference to a world. A walk is a
sequence of lattice points in which each point is its predecessor or one unit from it
along one axis (`Near`). `box` is the square of points within a radius of a center on
both axes, and `swept` the union of the boxes of a walk's first points.

`card_swept` bounds the swept set: a walk of `steps` moves comes within `radius` of at
most `(2 radius + 1)² + (2 radius + 1) steps` points. The first box has
`(2 radius + 1)²` points (`card_box`), and each move brings at most one new row or
column of `2 radius + 1` points into the box (`card_box_sdiff`). At radius 3 the bound
is `49 + 7 steps`.

The bound is an upper bound for every walk. It is attained by a walk that never turns
and is not attained by one that revisits a point.
-/

namespace AcornVerif.Coverage

/-- Two lattice points that are equal or one unit apart along one axis. -/
def Near (first second : ℤ × ℤ) : Prop :=
  (second.1 - first.1).natAbs + (second.2 - first.2).natAbs ≤ 1

/-- A point is near itself. -/
theorem Near.refl (point : ℤ × ℤ) : Near point point := by
  unfold Near
  omega

/-- The lattice points within a radius of a center on both axes. -/
def box (radius : ℕ) (center : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc (center.1 - radius) (center.1 + radius) ×ˢ
    Finset.Icc (center.2 - radius) (center.2 + radius)

/-- A point is in a box exactly when it is within the radius of the center on both
axes. -/
theorem mem_box {radius : ℕ} {center point : ℤ × ℤ} :
    point ∈ box radius center ↔
      (point.1 - center.1).natAbs ≤ radius ∧ (point.2 - center.2).natAbs ≤ radius := by
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  omega

/-- An interval of a radius on both sides of a point has `2 radius + 1` integers. -/
theorem card_span (radius : ℕ) (middle : ℤ) :
    (Finset.Icc (middle - radius) (middle + radius)).card = 2 * radius + 1 := by
  rw [Int.card_Icc]
  omega

/-- A box has `(2 radius + 1)²` points. -/
theorem card_box (radius : ℕ) (center : ℤ × ℤ) :
    (box radius center).card = (2 * radius + 1) * (2 * radius + 1) := by
  rw [box, Finset.card_product, card_span, card_span]

/-- A move brings at most one row or column into the box: the points of the new box
outside the old one number at most `2 radius + 1`. -/
theorem card_box_sdiff (radius : ℕ) (first second : ℤ × ℤ) (near : Near first second) :
    (box radius second \ box radius first).card ≤ 2 * radius + 1 := by
  have column (edge : ℤ) : (({edge} : Finset ℤ) ×ˢ
      Finset.Icc (second.2 - radius) (second.2 + radius)).card = 2 * radius + 1 := by
    rw [Finset.card_product, Finset.card_singleton, card_span, Nat.one_mul]
  have row (edge : ℤ) : (Finset.Icc (second.1 - radius) (second.1 + radius) ×ˢ
      ({edge} : Finset ℤ)).card = 2 * radius + 1 := by
    rw [Finset.card_product, Finset.card_singleton, card_span, Nat.mul_one]
  unfold Near at near
  by_cases level : second.2 = first.2
  · by_cases east : first.1 ≤ second.1
    · refine Nat.le_trans (Finset.card_le_card ?_) (Nat.le_of_eq (column (second.1 + radius)))
      intro point member
      simp only [box, Finset.mem_sdiff, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_singleton] at member ⊢
      omega
    · refine Nat.le_trans (Finset.card_le_card ?_) (Nat.le_of_eq (column (second.1 - radius)))
      intro point member
      simp only [box, Finset.mem_sdiff, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_singleton] at member ⊢
      omega
  · by_cases south : first.2 ≤ second.2
    · refine Nat.le_trans (Finset.card_le_card ?_) (Nat.le_of_eq (row (second.2 + radius)))
      intro point member
      simp only [box, Finset.mem_sdiff, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_singleton] at member ⊢
      omega
    · refine Nat.le_trans (Finset.card_le_card ?_) (Nat.le_of_eq (row (second.2 - radius)))
      intro point member
      simp only [box, Finset.mem_sdiff, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_singleton] at member ⊢
      omega

/-- The points within a radius of one of a walk's first `steps + 1` points. -/
def swept (radius : ℕ) (walk : ℕ → ℤ × ℤ) : ℕ → Finset (ℤ × ℤ)
  | 0 => box radius (walk 0)
  | steps + 1 => swept radius walk steps ∪ box radius (walk (steps + 1))

/-- The box of each of a walk's first points lies in the swept set. -/
theorem box_subset_swept (radius : ℕ) (walk : ℕ → ℤ × ℤ) (steps index : ℕ)
    (within : index ≤ steps) : box radius (walk index) ⊆ swept radius walk steps := by
  induction steps with
  | zero =>
    have first : index = 0 := Nat.le_zero.mp within
    subst first
    exact Finset.Subset.refl _
  | succ steps ih =>
    change box radius (walk index) ⊆ swept radius walk steps ∪ box radius (walk (steps + 1))
    rcases Nat.lt_or_eq_of_le within with earlier | last
    · exact Finset.Subset.trans (ih (Nat.le_of_lt_succ earlier)) Finset.subset_union_left
    · subst last
      exact Finset.subset_union_right

/-- A walk of `steps` moves comes within a radius of at most
`(2 radius + 1)² + (2 radius + 1) steps` lattice points. -/
theorem card_swept (radius : ℕ) (walk : ℕ → ℤ × ℤ) (steps : ℕ)
    (near : ∀ index, index < steps → Near (walk index) (walk (index + 1))) :
    (swept radius walk steps).card ≤
      (2 * radius + 1) * (2 * radius + 1) + (2 * radius + 1) * steps := by
  induction steps with
  | zero =>
    rw [Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_eq (card_box radius (walk 0))
  | succ steps ih =>
    have earlier := ih (fun index before => near index (Nat.lt_succ_of_lt before))
    have fresh := card_box_sdiff radius (walk steps) (walk (steps + 1))
      (near steps (Nat.lt_succ_self steps))
    have old : box radius (walk steps) ⊆ swept radius walk steps :=
      box_subset_swept radius walk steps steps (Nat.le_refl steps)
    calc (swept radius walk (steps + 1)).card
        = (swept radius walk steps ∪
            (box radius (walk (steps + 1)) \ swept radius walk steps)).card :=
          congrArg Finset.card Finset.union_sdiff_self_eq_union.symm
      _ ≤ (swept radius walk steps).card +
            (box radius (walk (steps + 1)) \ swept radius walk steps).card :=
          Finset.card_union_le _ _
      _ ≤ (swept radius walk steps).card +
            (box radius (walk (steps + 1)) \ box radius (walk steps)).card :=
          Nat.add_le_add_left
            (Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) old)) _
      _ ≤ ((2 * radius + 1) * (2 * radius + 1) + (2 * radius + 1) * steps) +
            (2 * radius + 1) := Nat.add_le_add earlier fresh
      _ = (2 * radius + 1) * (2 * radius + 1) + (2 * radius + 1) * (steps + 1) :=
          (Nat.add_assoc _ _ _).trans
            (congrArg (fun rest => (2 * radius + 1) * (2 * radius + 1) + rest)
              (Nat.mul_succ (2 * radius + 1) steps).symm)

end AcornVerif.Coverage
