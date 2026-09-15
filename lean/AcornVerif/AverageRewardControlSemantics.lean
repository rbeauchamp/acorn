/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import AcornSpec.AverageRewardControl
import AcornVerif.Outcome

/-!
# Admission and assessment of the differential-control comparison

The scientific owner is `studies/average-reward-control/protocols/{v1,v2}/protocol.md`.
These are universal input and report contracts, not empirical outcomes or
certified re-execution. The opportunity bound follows from the runtime's
complete-goal obligations: a failed goal exhausts every capped attempt, and a
successful goal consumes at least one environment step. The same bound is a
field of the calculator's admitted cycle type.
-/

namespace AcornVerif.AverageRewardControlSemantics

open AcornSpec AcornSpec.AverageRewardControl

/-- Number of successful goals in any list of success/exposure pairs. -/
def successes : List (Bool × Nat) → Nat
  | [] => 0
  | (success, _) :: rest => (if success then 1 else 0) + successes rest

/-- Each goal contributes at most one success, for every possible goal list. -/
theorem successes_le_length (rows : List (Bool × Nat)) : successes rows ≤ rows.length := by
  induction rows with
  | nil => simp [successes]
  | cons row rest ih =>
    rcases row with ⟨success, steps⟩
    cases success <;> simp [successes] <;> omega

/-- Summing complete goal obligations gives the exact aggregate lower bound.
`limit` is attempts times the step cap; no selected scenario establishes it. -/
theorem complete_goals_exposure (limit : Nat) (rows : List (Bool × Nat))
    (complete : ∀ row ∈ rows, (if row.1 then 1 else limit) ≤ row.2) :
    (rows.length - successes rows) * limit + successes rows ≤
      (rows.map Prod.snd).sum := by
  induction rows with
  | nil => simp [successes]
  | cons row rest ih =>
    have first := complete row (by simp)
    have tail := ih (fun item member => complete item (by simp [member]))
    have count := successes_le_length rest
    rcases row with ⟨success, steps⟩
    cases success with
    | false =>
      simp only [successes, Bool.false_eq_true, ↓reduceIte, zero_add,
        List.length_cons, List.map_cons, List.sum_cons] at *
      have size : rest.length + 1 - successes rest = (rest.length - successes rest) + 1 := by
        omega
      rw [size, Nat.add_mul]
      omega
    | true =>
      simp only [successes, ↓reduceIte, List.length_cons, List.map_cons,
        List.sum_cons] at *
      have size : rest.length + 1 - (1 + successes rest) = rest.length - successes rest := by
        omega
      rw [size]
      omega

/-- Every admitted cycle owes the complete failed-goal exposure, regardless of
which input bytes or constructor produced it. -/
theorem admitted_cycle_exposure (cycle : Cycle) :
    (Constants.averageRewardGoals - cycle.achieved) * Constants.averageRewardAttempts *
      Constants.averageRewardStepCap + cycle.achieved ≤ cycle.steps := cycle.exposure

/-- Every admitted cycle's latency maximum is a summand and bounds its sum. -/
theorem admitted_cycle_latency (cycle : Cycle) :
    cycle.maxUpdateMicros ≤ cycle.updateMicros ∧
      cycle.updateMicros ≤ cycle.steps * cycle.maxUpdateMicros := cycle.latency

/-- A supported assessment is exactly the registered positive-direction rule. -/
theorem supported_iff (counts : Tally) (mean : Rat) :
    assessment counts mean = .supported ↔
      signTail counts.wins counts.losses ≤ (1 : Rat) / 20 ∧
      0 < mean ∧ counts.losses < counts.wins := by
  unfold assessment
  split_ifs <;> simp_all

/-- A refuted assessment is exactly the registered negative-direction rule. -/
theorem refuted_iff (counts : Tally) (mean : Rat) :
    assessment counts mean = .refuted ↔
      signTail counts.wins counts.losses ≤ (1 : Rat) / 20 ∧
      mean < 0 ∧ counts.wins < counts.losses := by
  unfold assessment
  split_ifs <;> simp_all
  omega

/-- The dossier verdict and directional label always describe the same assessment. -/
theorem assessment_labels (result : Assessment) :
    (result.verdict = "supported" ↔ result.direction = "positive") ∧
    (result.verdict = "refuted" ↔ result.direction = "negative") ∧
    (result.verdict = "inconclusive" ↔ result.direction = "inconclusive") := by
  cases result <;> simp [Assessment.verdict, Assessment.direction]

/-- The canonical tally partitions exactly any complete protocol population. -/
theorem complete_report_population {population : Nat}
    (differences : Vector Rat population) :
    (tally differences.toArray).seeds = population := by
  rw [tally_partitions, Vector.size_toArray]

/-- Every admitted process has positive memory bounded by the registered byte capacity. -/
theorem admitted_process_peak (resources : ProcessResources) :
    0 < resources.peakKiB ∧ resources.peakKiB * 1024 ≤ Constants.averageRewardRssBudget :=
  ⟨resources.positive, resources.bounded⟩

/-- The calculator's factorial agrees with the mathematical owner on all naturals. -/
theorem factorial_correct (n : Nat) : factorial n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial, Nat.factorial_succ, ih]

/-- Every calculator binomial count is the exact mathematical subset count. -/
theorem binomial_correct (n k : Nat) : binomial n k = n.choose k := by
  unfold binomial
  split_ifs with h
  · rw [factorial_correct, factorial_correct, factorial_correct]
    exact (Nat.choose_eq_factorial_div_factorial h).symm
  · exact (Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)).symm

/-- The shared count satisfies Pascal's identity on the entire natural domain. -/
theorem binomial_pascal (n k : Nat) :
    binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1) :=
by
  simp only [binomial_correct]
  exact Nat.choose_succ_succ n k

/-- Exhaustion of every attainable no-tie win count in the registered v2 design.
This is small static kernel arithmetic, not reflection or agent re-execution. -/
theorem revision_sign_threshold (wins : Fin (Constants.averageRewardRevisionSeeds.length + 1)) :
    signTail wins.val (Constants.averageRewardRevisionSeeds.length - wins.val) ≤ (1 : Rat) / 20 ↔
      wins.val ≤ 5 ∨ 15 ≤ wins.val := by
  fin_cases wins <;> decide +kernel

/-- Exact binomial design calibration at the hypothetical independent win
probability 4/5. It calibrates only the no-tie sign component, not the mean veto. -/
theorem revision_large_effect_resolution :
    (4 : Rat) / 5 <
      (((List.range 6).map (fun j => binomial 20 (15 + j) * 4 ^ (15 + j))).sum : Rat) /
        (5 ^ 20 : Nat) := by
  decide +kernel

/-- Every admitted invocation contains the complete population within both budgets. -/
theorem admitted_invocation_complete (completion : InvocationComplete) :
    completion.streams = Constants.averageRewardRevisionSeeds.length * 2 ∧
      completion.wallMillis < Constants.averageRewardWallBudget * 1000 ∧
      completion.rawBytes ≤ Constants.averageRewardRevisionRawBudget :=
  ⟨completion.population, completion.wallBounded, completion.rawBounded⟩

end AcornVerif.AverageRewardControlSemantics
