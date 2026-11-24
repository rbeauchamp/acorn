import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import AcornVerif.ModelConstants

namespace AcornVerif

open AcornVerif.ModelConstants

def reachRemaining (dx dy : ℤ) : ℕ :=
  (max dx.natAbs dy.natAbs).sub reachRadius

def reachSatisfied (dx dy : ℤ) : Prop :=
  max dx.natAbs dy.natAbs ≤ reachRadius

theorem reach_remaining_zero_iff (dx dy : ℤ) :
    reachRemaining dx dy = 0 ↔ reachSatisfied dx dy := by
  simp [reachRemaining, reachSatisfied, Nat.sub_eq_zero_iff_le]

def collectRemaining (held required : ℕ) : ℕ := required - held

def collectSatisfied (held required : ℕ) : Prop := required ≤ held

theorem collect_remaining_zero_iff (held required : ℕ) :
    collectRemaining held required = 0 ↔ collectSatisfied held required := by
  simp [collectRemaining, collectSatisfied, Nat.sub_eq_zero_iff_le]

def craftRemaining (completed : Bool) : ℕ := if completed then 0 else 1

def craftSatisfied (completed : Bool) : Prop := completed = true

theorem craft_remaining_zero_iff (completed : Bool) :
    craftRemaining completed = 0 ↔ craftSatisfied completed := by
  cases completed <;> simp [craftRemaining, craftSatisfied]

def surviveRemaining (elapsed required : ℕ) : ℕ := required - elapsed

def surviveSatisfied (elapsed required : ℕ) : Prop := required ≤ elapsed

theorem survive_remaining_zero_iff (elapsed required : ℕ) :
    surviveRemaining elapsed required = 0 ↔ surviveSatisfied elapsed required := by
  simp [surviveRemaining, surviveSatisfied, Nat.sub_eq_zero_iff_le]

inductive GoalError where
  | reach (dx dy : ℤ)
  | collect (held required : ℕ)
  | craft (completed : Bool)
  | survive (elapsed required : ℕ)
  deriving DecidableEq, Repr

def GoalError.remaining : GoalError → ℕ
  | .reach dx dy => reachRemaining dx dy
  | .collect held required => collectRemaining held required
  | .craft completed => craftRemaining completed
  | .survive elapsed required => surviveRemaining elapsed required

def GoalError.satisfied : GoalError → Prop
  | .reach dx dy => reachSatisfied dx dy
  | .collect held required => collectSatisfied held required
  | .craft completed => craftSatisfied completed
  | .survive elapsed required => surviveSatisfied elapsed required

theorem goal_remaining_zero_iff_satisfied (error : GoalError) :
    error.remaining = 0 ↔ error.satisfied := by
  cases error with
  | reach dx dy => exact reach_remaining_zero_iff dx dy
  | collect held required => exact collect_remaining_zero_iff held required
  | craft completed => exact craft_remaining_zero_iff completed
  | survive elapsed required => exact survive_remaining_zero_iff elapsed required

theorem chebyshev_reduces_when_x_reduces (x y : ℕ) :
    max (x - 1) y ≤ max x y := by
  exact max_le_max (Nat.sub_le x 1) le_rfl

example : reachSatisfied (reachRadius : ℤ) 0 := by
  norm_num [reachSatisfied, reachRadius]

end AcornVerif
