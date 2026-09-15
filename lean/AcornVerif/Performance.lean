/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Experiment
import AcornVerif.WorldGoals

/-!
# Performance proof boundary

The protocol and score theorems constrain result fields but do not choose them.
This file characterises that limited fact at the scalar-record boundary: every
combination inside the fieldwise envelope constructs a `StudyResult`. It does
not show that every such tuple is attainable by the analyzer or learner/world
system. A positive theorem must additionally define and refine the exact
coupled learner/world computation and analyzer.

`PerformanceCertificate` is a conditional schema: once a canonical computation
has been independently defined, the certificate must prove both acceptance and
equality with it. The caller supplies `computed`; this structure alone cannot
distinguish a canonical computation from a hand-authored value.
-/

namespace AcornVerif

open AcornVerif.Generated

/-- Membership in the closed rational unit interval. -/
def InUnit (value : ℚ) : Prop := 0 ≤ value ∧ value ≤ 1

/-- Structural ranges implied by the study-score definitions. Reach-time
differences are capped in either direction; cycle score differences lie in
`[-1, 1]`. These bounds deliberately contain no positive-performance premise. -/
def StructurallyLegalResult (result : StudyResult) : Prop :=
  InUnit result.finalVsRandom.probabilityOfImprovement ∧
  InUnit result.finalVsRandom.lowerBound ∧
  InUnit result.finalVsFrozen.probabilityOfImprovement ∧
  InUnit result.finalVsFrozen.lowerBound ∧
  InUnit result.reachSuccess ∧
  -(studyStepsPerGoal : ℚ) ≤ result.reachTimeLower ∧
  result.reachTimeLower ≤ studyStepsPerGoal ∧
  -1 ≤ result.continualLower ∧ result.continualLower ≤ 1

/-- Construct the complete scalar result without adding assumptions. -/
def resultAt (randomProbability randomLower frozenProbability frozenLower
    reachSuccess reachTimeLower continualLower : ℚ) : StudyResult where
  finalVsRandom := ⟨randomProbability, randomLower⟩
  finalVsFrozen := ⟨frozenProbability, frozenLower⟩
  reachSuccess := reachSuccess
  reachTimeLower := reachTimeLower
  continualLower := continualLower

/-- Every coordinate combination inside the fieldwise envelope constructs a
structurally legal scalar record. This says nothing about which records are
attainable from raw attempts or coupled learner/world transitions. -/
theorem fieldwise_result_envelope_has_every_coordinate_combination
    (randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower : ℚ)
    (hrp : InUnit randomProbability) (hrl : InUnit randomLower)
    (hfp : InUnit frozenProbability) (hfl : InUnit frozenLower)
    (hrs : InUnit reachSuccess)
    (hrtLower : -(studyStepsPerGoal : ℚ) ≤ reachTimeLower)
    (hrtUpper : reachTimeLower ≤ studyStepsPerGoal)
    (hcontinualLower : -1 ≤ continualLower)
    (hcontinualUpper : continualLower ≤ 1) :
    StructurallyLegalResult
      (resultAt randomProbability randomLower frozenProbability frozenLower
        reachSuccess reachTimeLower continualLower) ∧
    (resultAt randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower).finalVsRandom.probabilityOfImprovement =
        randomProbability ∧
    (resultAt randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower).finalVsRandom.lowerBound = randomLower ∧
    (resultAt randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower).finalVsFrozen.probabilityOfImprovement =
        frozenProbability ∧
    (resultAt randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower).finalVsFrozen.lowerBound = frozenLower ∧
    (resultAt randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower).reachSuccess = reachSuccess ∧
    (resultAt randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower).reachTimeLower = reachTimeLower ∧
    (resultAt randomProbability randomLower frozenProbability frozenLower
      reachSuccess reachTimeLower continualLower).continualLower = continualLower := by
  exact ⟨⟨hrp, hrl, hfp, hfl, hrs, hrtLower, hrtUpper, hcontinualLower,
    hcontinualUpper⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Acceptance consumes exactly seven outcome inequalities. This theorem is a
cold-readable expansion of the predicate, not evidence that any inequality is
true for the shipped computation. -/
theorem agent_baseline_acceptance_iff_outcomes (result : StudyResult) :
    AgentBaselineAcceptance result ↔
      result.finalVsRandom.probabilityOfImprovement ≥ studyProbabilityThreshold ∧
      result.finalVsRandom.lowerBound > studyIntervalThreshold ∧
      result.finalVsFrozen.probabilityOfImprovement ≥ studyProbabilityThreshold ∧
      result.finalVsFrozen.lowerBound > studyIntervalThreshold ∧
      result.reachSuccess ≥ studyReachThreshold ∧
      result.reachTimeLower > 0 ∧
      result.continualLower > 0 := Iff.rfl

/-- A proof-carrying result schema for an independently defined computation.

`grounded` is load-bearing only after `computed` has a separate canonical
definition and refinement proof. -/
structure PerformanceCertificate (computed : StudyResult) where
  /-- Result whose thresholds are proved. -/
  claimed : StudyResult
  /-- Refinement/evaluation proof tying the claim to the exact computation. -/
  grounded : claimed = computed
  /-- Kernel-checked positive acceptance proposition. -/
  accepted : AgentBaselineAcceptance claimed

/-- Any constructible performance certificate establishes acceptance of the
exact computed result. -/
theorem performance_certificate_sound (computed : StudyResult)
    (certificate : PerformanceCertificate computed) :
    AgentBaselineAcceptance computed := by
  rw [← certificate.grounded]
  exact certificate.accepted

/-- Half-credit units for a paired seed: loss `0`, tie `1`, win `2`. -/
def requiredWinUnits : ℕ :=
  (2 * studySeedCount * studyProbabilityThresholdNumerator +
    studyProbabilityThresholdDenominator - 1) /
      studyProbabilityThresholdDenominator

/-- At the generated population and threshold, acceptance requires at least
45 half-credit units out of 60. -/
theorem required_win_units_at_build : requiredWinUnits = 45 := by
  norm_num [requiredWinUnits, studySeedCount, studyProbabilityThresholdNumerator,
    studyProbabilityThresholdDenominator]

/-- Exact paired point estimate represented by half-credit units. -/
def pairedProbabilityFromUnits (units : ℕ) : ℚ :=
  units / (2 * studySeedCount)

/-- At the shipped population and threshold, the rational probability gate is
equivalent to the exact integer half-credit requirement. -/
theorem paired_probability_threshold_iff (units : ℕ) :
    pairedProbabilityFromUnits units ≥ studyProbabilityThreshold ↔
      requiredWinUnits ≤ units := by
  have hden : (2 * studySeedCount : ℚ) = 60 := by
    norm_num [studySeedCount]
  have hthreshold : studyProbabilityThreshold = (3 : ℚ) / 4 := by
    norm_num [studyProbabilityThreshold]
  rw [pairedProbabilityFromUnits, hden, hthreshold, required_win_units_at_build]
  constructor
  · intro h
    have hq : (45 : ℚ) ≤ units := by linarith
    exact_mod_cast hq
  · intro h
    have hq : (45 : ℚ) ≤ units := by exact_mod_cast h
    linarith

/-- Worst-case environment transitions in the complete frozen population. -/
def studyMaxTransitions : ℕ :=
  studySeedCount * studyArmCount * studyCycles * studyGoals *
    studyAttemptsPerGoal * studyStepsPerAttempt

/-- Any transition-by-transition certificate for the complete fixed benchmark
must account for a domain containing up to 70.2 million environment steps. -/
theorem study_max_transitions_at_build : studyMaxTransitions = 70_200_000 := by
  norm_num [studyMaxTransitions, studySeedCount, studyArmCount, studyCycles,
    studyGoals, studyAttemptsPerGoal, studyStepsPerAttempt]

/-- **Exact futility rule.** If even wins on every uncomputed seed cannot reach
the point-estimate threshold, no completion of the remaining population can
reach it. This can stop a failing campaign early, but cannot certify a pass
without the other interval/effect outcomes. -/
theorem paired_point_futility (completedUnits remainingUnits uncomputed : ℕ)
    (hremaining : remainingUnits ≤ 2 * uncomputed)
    (himpossible : completedUnits + 2 * uncomputed < requiredWinUnits) :
    completedUnits + remainingUnits < requiredWinUnits := by
  omega

/-- The futility condition makes the formal rational probability threshold
unreachable for every legal completion of the remaining population. -/
theorem paired_probability_futility (completedUnits remainingUnits uncomputed : ℕ)
    (hremaining : remainingUnits ≤ 2 * uncomputed)
    (himpossible : completedUnits + 2 * uncomputed < requiredWinUnits) :
    ¬(pairedProbabilityFromUnits (completedUnits + remainingUnits) ≥
      studyProbabilityThreshold) := by
  rw [paired_probability_threshold_iff]
  exact Nat.not_le_of_lt (paired_point_futility completedUnits remainingUnits uncomputed
    hremaining himpossible)

/-- Non-vacuity of the proof-carrying interface. The example uses a proposition
already proved by normalization and says nothing about the shipped run. -/
example (computed : StudyResult) (h : AgentBaselineAcceptance computed) :
    PerformanceCertificate computed :=
  ⟨computed, rfl, h⟩

end AcornVerif
