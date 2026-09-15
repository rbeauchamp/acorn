/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import AcornVerif.Generated
import AcornSpec.AgentBaselineAcceptance

/-!
# Exact agent-baseline study and score semantics

This file owns the decidable mathematics of the frozen agent-baseline protocol. It
does not assume or assert that the shipped learner passes. The conclusion of a
positive performance claim depends on the exact occurrence outcomes produced
by the coupled Rust learner and world; those values enter only through
`StudyResult`.

The benchmark population is the fixed generated list of 30 Rust seeds. It is
not a theorem about arbitrary worlds or a sampling claim about a wider seed
distribution. Scores are rational, so no floating-point rounding is hidden in
the mathematical owner.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- Closed evaluator arms, in the Rust execution order. -/
inductive AgentBaselineArm where
  /-- Shipped hierarchical learner. -/
  | final
  /-- Deterministic pseudorandom primitive comparator. -/
  | random
  /-- Identically initialized hierarchy with learning disabled. -/
  | frozen
  /-- Hierarchy without the Reach relation. -/
  | ablatedGoalRelation
  /-- Primitive learner without option/meta control. -/
  | ablatedTemporalAbstraction
  deriving DecidableEq, Repr

/-- The complete closed evaluator-arm domain. -/
def AgentBaselineArm.all : List AgentBaselineArm :=
  [.final, .random, .frozen, .ablatedGoalRelation, .ablatedTemporalAbstraction]

/-- Closed goal-family domain used by the stratified score. -/
inductive GoalFamily where
  /-- Coordinate-region goal. -/
  | reach
  /-- Inventory-count goal. -/
  | collect
  /-- Crafting goal. -/
  | craft
  /-- Fixed-duration goal, excluded from the primary score. -/
  | survive
  deriving DecidableEq, Repr

/-- A valid collapsed goal occurrence.

`elapsed` is intrinsically capped. Failure is definitionally tied to the cap,
and a success must consume at least one environment step. These proof fields
make an out-of-domain result uninhabitable rather than something an analyzer
may accept accidentally. -/
structure Occurrence where
  /-- Goal family used for equal-family weighting. -/
  family : GoalFamily
  /-- Cumulative steps through first success, in `0..=studyStepsPerGoal`. -/
  elapsed : Fin (studyStepsPerGoal + 1)
  /-- Whether any attempt achieved the goal. -/
  achieved : Bool
  /-- Whether the goal was satisfied on the occurrence's first observation. -/
  initiallySatisfied : Bool
  /-- A failure is represented by the cap, never a shorter observed prefix. -/
  failureAtCap : achieved = false → elapsed.val = studyStepsPerGoal
  /-- A reported success consumes at least one world transition. -/
  successPositive : achieved = true → 0 < elapsed.val

/-- Exact capped goal efficiency, with failure equal to zero. -/
def goalEfficiency (o : Occurrence) : ℚ :=
  1 - (o.elapsed.val : ℚ) / studyStepsPerGoal

/-- The cumulative cap is derived from attempts and the per-attempt cap. -/
theorem study_goal_cap_is_derived :
    studyStepsPerGoal = studyAttemptsPerGoal * studyStepsPerAttempt := by
  norm_num [studyStepsPerGoal, studyAttemptsPerGoal, studyStepsPerAttempt]

/-- The generated Rust seed list has exactly the generated population size. -/
theorem study_seed_population_is_closed :
    studySeeds.length = studySeedCount := by
  norm_num [studySeeds, studySeedCount]

/-- Every registered seed occurs exactly once in the closed population. -/
theorem study_seed_population_is_nodup : studySeeds.Nodup := by
  decide

/-- The Lean arm enumeration has the generated Rust arm count. -/
theorem study_arm_domain_is_closed :
    AgentBaselineArm.all.length = studyArmCount := by
  norm_num [AgentBaselineArm.all, studyArmCount]

/-- Every legal occurrence score is in the closed unit interval. -/
theorem goal_efficiency_mem_unit (o : Occurrence) :
    0 ≤ goalEfficiency o ∧ goalEfficiency o ≤ 1 := by
  have helapsed : (o.elapsed.val : ℚ) ≤ studyStepsPerGoal := by
    exact_mod_cast Nat.le_of_lt_succ o.elapsed.isLt
  have hnonneg : (0 : ℚ) ≤ o.elapsed.val := by positivity
  have hcap : (0 : ℚ) < studyStepsPerGoal := by
    norm_num [studyStepsPerGoal]
  have hratio_nonneg : 0 ≤ (o.elapsed.val : ℚ) / studyStepsPerGoal :=
    div_nonneg hnonneg (le_of_lt hcap)
  have hratio_le : (o.elapsed.val : ℚ) / studyStepsPerGoal ≤ 1 :=
    (div_le_one hcap).mpr helapsed
  unfold goalEfficiency
  constructor <;> linarith

/-- Failure has exactly zero efficiency. -/
theorem goal_efficiency_failure (o : Occurrence) (h : o.achieved = false) :
    goalEfficiency o = 0 := by
  rw [goalEfficiency, o.failureAtCap h]
  norm_num [studyStepsPerGoal]

/-- Registered capped Reach time assigns cap plus one to every failure. -/
def reachCappedTime (o : Occurrence) : ℕ :=
  if o.achieved then o.elapsed.val else studyReachFailureTime

/-- A failed Reach occurrence has exactly the registered failure time. -/
theorem reach_capped_time_failure (o : Occurrence) (h : o.achieved = false) :
    reachCappedTime o = studyReachFailureTime := by
  simp [reachCappedTime, h]

/-- Every capped Reach time is positive and no greater than cap plus one. -/
theorem reach_capped_time_bounds (o : Occurrence) :
    1 ≤ reachCappedTime o ∧ reachCappedTime o ≤ studyReachFailureTime := by
  cases h : o.achieved with
  | false =>
      simp [reachCappedTime, h, studyReachFailureTime]
  | true =>
      have hpositive := o.successPositive h
      have hupper : o.elapsed.val ≤ studyStepsPerGoal := Nat.le_of_lt_succ o.elapsed.isLt
      simp only [reachCappedTime, h, ↓reduceIte]
      constructor
      · exact hpositive
      · calc
          o.elapsed.val ≤ studyStepsPerGoal := hupper
          _ ≤ studyReachFailureTime := by
            norm_num [studyReachFailureTime, studyStepsPerGoal]

/-- More elapsed steps can never improve a capped score. -/
theorem goal_efficiency_antitone (left right : Occurrence)
    (h : left.elapsed.val ≤ right.elapsed.val) :
    goalEfficiency right ≤ goalEfficiency left := by
  have hq : (left.elapsed.val : ℚ) ≤ right.elapsed.val := by exact_mod_cast h
  have hcap : (0 : ℚ) ≤ studyStepsPerGoal := by
    norm_num [studyStepsPerGoal]
  have hdiv := div_le_div_of_nonneg_right hq hcap
  unfold goalEfficiency
  linarith

/-- Strictly more elapsed steps strictly reduce the capped score. -/
theorem goal_efficiency_strict_antitone (left right : Occurrence)
    (h : left.elapsed.val < right.elapsed.val) :
    goalEfficiency right < goalEfficiency left := by
  have hq : (left.elapsed.val : ℚ) < right.elapsed.val := by exact_mod_cast h
  have hcap : (0 : ℚ) < studyStepsPerGoal := by
    norm_num [studyStepsPerGoal]
  have hdiv := (div_lt_div_iff_of_pos_right hcap).mpr hq
  unfold goalEfficiency
  linarith

/-- Comparison-local primary eligibility. Both arms participate in the
predicate, so its symmetry is a theorem rather than an analyzer convention. -/
def primaryEligible (left right : Occurrence) : Prop :=
  left.family = right.family ∧ left.family ≠ .survive ∧
    left.initiallySatisfied = false ∧ right.initiallySatisfied = false

/-- Union exclusion is symmetric in the paired arms. -/
theorem primary_eligibility_symmetric (left right : Occurrence) :
    primaryEligible left right ↔ primaryEligible right left := by
  simp only [primaryEligible]
  aesop

/-- Win credit used by probability of improvement: one for a win, one half
for a tie, and zero for a loss. -/
def winCredit (left right : ℚ) : ℚ :=
  if right < left then 1 else if left = right then 1 / 2 else 0

/-- Every paired win credit lies in the unit interval. -/
theorem win_credit_mem_unit (left right : ℚ) :
    0 ≤ winCredit left right ∧ winCredit left right ≤ 1 := by
  unfold winCredit
  split_ifs <;> norm_num

/-- Arithmetic mean of an exact rational list. Empty input is deliberately
zero; primary scoring separately requires a nonempty stratum. -/
def rationalMean (values : List ℚ) : ℚ :=
  values.sum / values.length

/-- The sum of unit-interval values is nonnegative and no larger than the
list length. -/
theorem rational_sum_bounds (values : List ℚ)
    (hvalues : ∀ value ∈ values, 0 ≤ value ∧ value ≤ 1) :
    0 ≤ values.sum ∧ values.sum ≤ values.length := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead := hvalues head (by simp)
      have htail : ∀ value ∈ tail, 0 ≤ value ∧ value ≤ 1 := by
        intro value hmem
        exact hvalues value (by simp [hmem])
      have hrest := ih htail
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith

/-- A nonempty mean of unit-interval values remains in the unit interval. -/
theorem rational_mean_mem_unit (values : List ℚ) (hne : values ≠ [])
    (hvalues : ∀ value ∈ values, 0 ≤ value ∧ value ≤ 1) :
    0 ≤ rationalMean values ∧ rationalMean values ≤ 1 := by
  have hbounds := rational_sum_bounds values hvalues
  have hlenNat : 0 < values.length := by
    exact Nat.pos_of_ne_zero fun hzero => hne (List.length_eq_zero_iff.mp hzero)
  have hlen : (0 : ℚ) < values.length := by exact_mod_cast hlenNat
  constructor
  · unfold rationalMean
    exact div_nonneg hbounds.1 (le_of_lt hlen)
  · unfold rationalMean
    exact (div_le_one hlen).mpr hbounds.2

/-- Equal-family weighting: average within each nonempty family, then average
the nonempty family means. -/
def stratifiedScore (families : List (List ℚ)) : ℚ :=
  rationalMean (families.map rationalMean)

/-- Equal family weighting preserves the score range. -/
theorem stratified_score_mem_unit (families : List (List ℚ))
    (hfamilies : families ≠ [])
    (hnonempty : ∀ family ∈ families, family ≠ [])
    (hscores : ∀ family ∈ families, ∀ score ∈ family, 0 ≤ score ∧ score ≤ 1) :
    0 ≤ stratifiedScore families ∧ stratifiedScore families ≤ 1 := by
  unfold stratifiedScore
  apply rational_mean_mem_unit
  · simpa using hfamilies
  · intro value hvalue
    rw [List.mem_map] at hvalue
    obtain ⟨family, hfamily, rfl⟩ := hvalue
    exact rational_mean_mem_unit family (hnonempty family hfamily) (hscores family hfamily)

/-- A paired comparison summary. Interval construction is a separate closed
computation; this structure records only the two values acceptance consumes. -/
structure PairedComparison where
  /-- Mean win/tie credit over the fixed seed population. -/
  probabilityOfImprovement : ℚ
  /-- Registered lower interval bound. -/
  lowerBound : ℚ

/-- The complete scalar result consumed by agent-baseline acceptance. -/
structure StudyResult where
  /-- Final learner versus the deterministic pseudorandom comparator. -/
  finalVsRandom : PairedComparison
  /-- Final learner versus frozen learner. -/
  finalVsFrozen : PairedComparison
  /-- Held-out Reach success rate. -/
  reachSuccess : ℚ
  /-- Lower interval bound for random-minus-final capped Reach time. -/
  reachTimeLower : ℚ
  /-- Lower interval bound for later-cycle minus first-cycle efficiency. -/
  continualLower : ℚ

/-- Exact agent-baseline acceptance predicate over a closed result object. -/
def AgentBaselineAcceptance (result : StudyResult) : Prop :=
  result.finalVsRandom.probabilityOfImprovement ≥ studyProbabilityThreshold ∧
  result.finalVsRandom.lowerBound > studyIntervalThreshold ∧
  result.finalVsFrozen.probabilityOfImprovement ≥ studyProbabilityThreshold ∧
  result.finalVsFrozen.lowerBound > studyIntervalThreshold ∧
  result.reachSuccess ≥ studyReachThreshold ∧
  result.reachTimeLower > 0 ∧
  result.continualLower > 0

/-- Acceptance is decidable once the closed result object exists. -/
def agentBaselineAcceptanceDecidable (result : StudyResult) :
    Decidable (AgentBaselineAcceptance result) := by
  unfold AgentBaselineAcceptance
  infer_instance

/-- Every named executable acceptance flag uses its corresponding generated
threshold and result field. Record equality binds the labels as well as their
aggregate verdict, for every possible exact-rational result. -/
theorem baseline_acceptance_flags (r : AcornSpec.Result7) :
    AcornSpec.baselineAcceptance r = {
      controlRandom := decide (studyProbabilityThreshold ≤ r.randomPoi)
      controlRandomInterval := decide (studyIntervalThreshold < r.randomProbLower)
      learningFrozen := decide (studyProbabilityThreshold ≤ r.frozenPoi)
      learningFrozenInterval := decide (studyIntervalThreshold < r.frozenProbLower)
      reachSuccess := decide (studyReachThreshold ≤ r.reachSuccess)
      reachTime := decide (0 < r.reachTimeLower)
      continualImprovement := decide (0 < r.continualLower) } := rfl

/-- The native calculator's verdict is exactly the proof layer's registered
acceptance predicate on the same seven rational values, for every result. -/
theorem baseline_acceptance_iff (r : AcornSpec.Result7) :
    (AcornSpec.baselineAcceptance r).all = true ↔ AgentBaselineAcceptance {
      finalVsRandom := ⟨r.randomPoi, r.randomProbLower⟩
      finalVsFrozen := ⟨r.frozenPoi, r.frozenProbLower⟩
      reachSuccess := r.reachSuccess
      reachTimeLower := r.reachTimeLower
      continualLower := r.continualLower } := by
  rw [baseline_acceptance_flags]
  simp [AcornSpec.BaselineAcceptance.all, AgentBaselineAcceptance, and_assoc]

/-- Non-vacuity: the generated thresholds admit a result object. This does not
claim that the shipped learner produces it. -/
example : AgentBaselineAcceptance {
    finalVsRandom := ⟨1, 1⟩
    finalVsFrozen := ⟨1, 1⟩
    reachSuccess := 1
    reachTimeLower := 1
    continualLower := 1
  } := by
  norm_num [AgentBaselineAcceptance, studyProbabilityThreshold, studyIntervalThreshold,
    studyReachThreshold]

end AcornVerif
