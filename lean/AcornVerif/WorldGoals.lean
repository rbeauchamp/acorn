/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import AcornVerif.Generated

/-!
# Goal-error semantics

Every installed goal carries the error relation that determines completion.
This file states the four goal-family relations over exact integers/naturals
and proves universally that zero remaining error is equivalent to the host
completion predicate. `reachRadius` is generated from `Goal::REACH_RADIUS`;
the other relations contain their required quantity directly.

The theorems establish observation/completion agreement. They do not establish
that the shipped learner selects actions that reduce the error.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- Exact remaining distance to the completed Reach region. -/
def reachRemaining (dx dy : ℤ) : ℕ :=
  (max dx.natAbs dy.natAbs).sub reachRadius

/-- Host Reach completion predicate. -/
def reachSatisfied (dx dy : ℤ) : Prop :=
  max dx.natAbs dy.natAbs ≤ reachRadius

/-- Reach error is zero exactly in the rewarded region. -/
theorem reach_remaining_zero_iff (dx dy : ℤ) :
    reachRemaining dx dy = 0 ↔ reachSatisfied dx dy := by
  simp [reachRemaining, reachSatisfied, Nat.sub_eq_zero_iff_le]

/-- Remaining inventory units for a collect goal. -/
def collectRemaining (held required : ℕ) : ℕ := required - held

/-- Host collect completion predicate. -/
def collectSatisfied (held required : ℕ) : Prop := required ≤ held

/-- Collect error is zero exactly when inventory meets the requirement. -/
theorem collect_remaining_zero_iff (held required : ℕ) :
    collectRemaining held required = 0 ↔ collectSatisfied held required := by
  simp [collectRemaining, collectSatisfied, Nat.sub_eq_zero_iff_le]

/-- Remaining binary error for a craft goal. -/
def craftRemaining (completed : Bool) : ℕ := if completed then 0 else 1

/-- Host craft completion predicate. -/
def craftSatisfied (completed : Bool) : Prop := completed = true

/-- Craft error is zero exactly when the named tool exists. -/
theorem craft_remaining_zero_iff (completed : Bool) :
    craftRemaining completed = 0 ↔ craftSatisfied completed := by
  cases completed <;> simp [craftRemaining, craftSatisfied]

/-- Remaining duration for a survival goal. -/
def surviveRemaining (elapsed required : ℕ) : ℕ := required - elapsed

/-- Host survival completion predicate. -/
def surviveSatisfied (elapsed required : ℕ) : Prop := required ≤ elapsed

/-- Survival error is zero exactly when the required duration has elapsed. -/
theorem survive_remaining_zero_iff (elapsed required : ℕ) :
    surviveRemaining elapsed required = 0 ↔ surviveSatisfied elapsed required := by
  simp [surviveRemaining, surviveSatisfied, Nat.sub_eq_zero_iff_le]

/-- Closed goal-error domain. Each variant contains every value its own
completion predicate needs; there is no cue-plus-optional-fields state. -/
inductive GoalError where
  /-- Exact signed coordinate displacement. -/
  | reach (dx dy : ℤ)
  /-- Current and required inventory count. -/
  | collect (held required : ℕ)
  /-- Whether the named craftable exists. -/
  | craft (completed : Bool)
  /-- Elapsed and required survival duration. -/
  | survive (elapsed required : ℕ)
  deriving DecidableEq, Repr

/-- Remaining error carried by one legal goal observation. -/
def GoalError.remaining : GoalError → ℕ
  | .reach dx dy => reachRemaining dx dy
  | .collect held required => collectRemaining held required
  | .craft completed => craftRemaining completed
  | .survive elapsed required => surviveRemaining elapsed required

/-- Host completion semantics for one legal goal observation. -/
def GoalError.satisfied : GoalError → Prop
  | .reach dx dy => reachSatisfied dx dy
  | .collect held required => collectSatisfied held required
  | .craft completed => craftSatisfied completed
  | .survive elapsed required => surviveSatisfied elapsed required

/-- Every goal-family relation agrees with its completion predicate. -/
theorem goal_remaining_zero_iff_satisfied (error : GoalError) :
    error.remaining = 0 ↔ error.satisfied := by
  cases error with
  | reach dx dy => exact reach_remaining_zero_iff dx dy
  | collect held required => exact collect_remaining_zero_iff held required
  | craft completed => exact craft_remaining_zero_iff completed
  | survive elapsed required => exact survive_remaining_zero_iff elapsed required

/-- Moving one coordinate one unit toward zero cannot increase Chebyshev
distance. This is a world-geometry fact, not a claim that the policy chooses
the corresponding action. -/
theorem chebyshev_reduces_when_x_reduces (x y : ℕ) :
    max (x - 1) y ≤ max x y := by
  exact max_le_max (Nat.sub_le x 1) le_rfl

/-- Non-vacuity at the generated Reach boundary. -/
example : reachSatisfied (reachRadius : ℤ) 0 := by
  norm_num [reachSatisfied, reachRadius]

end AcornVerif
