/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Task

/-!
# Current metric and audit folds

Attempt rows preserve raw machine metrics. Streaming aggregation retains only
the running outcome fold and checked total steps; a report collector may retain
rows separately. Digest identity detects mutation and is not correctness evidence.
-/
namespace Acorn.Host

/-- Learner-owned terminal observations; no finite-value assumption is imposed. -/
structure LearnerMetrics where
  /-- Mean absolute demon TD error. -/
  demonError : Binary32
  /-- Current exploration rate. -/
  epsilon : Binary32
  /-- Mean primitive-controller step size. -/
  meanAlpha : Binary32

/-- One complete attempt outcome in the current metric field order. -/
structure GoalOutcome where
  /-- Curriculum index in the 64-bit host domain. -/
  index : UInt64
  /-- Exact within-goal attempt number. -/
  attempt : UInt64
  /-- Curriculum difficulty tier. -/
  tier : UInt8
  /-- Number of actions executed in this attempt. -/
  steps : UInt64
  /-- Completion flag after the last world step, or carried flag for an empty attempt. -/
  achieved : Bool
  /-- Ordered reward sum. -/
  reward : Binary32
  /-- Last learner observations. -/
  learner : LearnerMetrics

/-- Exact current action-fingerprint recurrence, with wrapping word arithmetic. -/
def foldAction (fold : UInt64) (action : Action) : UInt64 :=
  fold * 0x100000001b3 + action.index.val.toUInt64 + 1

/-- FNV byte fold used by the source's literal domain separators.
Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake 3rd and Tony Hansen,
The FNV Non-Cryptographic Hash Algorithm, RFC 9923 (2026), sections 2 and 5;
the same verified reference and primitive ordering as `Acorn.Rng`. -/
def hashBytes (bytes : ByteArray) : UInt64 :=
  bytes.data.foldl Rng.fnvStep Rng.fnvOffset

/-- Initial action fingerprint is independent of observer and stop state. -/
def initialBehavior : UInt64 := hashBytes "decision-stream-v1".toUTF8

/-- One outcome term in the current audit recurrence. -/
def foldOutcome (fold : UInt64) (outcome : GoalOutcome) : UInt64 :=
  let mixed : UInt64 := fold * (0x100000001b3 : UInt64)
  let achieved : UInt64 := if outcome.achieved then 1 else 0
  mixed + outcome.steps + achieved + (outcome.tier.toUInt64 <<< (32 : UInt64))

/-- Persistent retirement event fields folded after all attempt outcomes. -/
structure AuditRetirement where
  /-- Lifetime step. -/
  step : UInt64
  /-- Unit number. -/
  unit : UInt32

/-- One retirement event in the source's exact field order. -/
def foldRetirement (fold : UInt64) (event : AuditRetirement) : UInt64 :=
  (fold * 0x100000001b3 + event.step) * 0x100000001b3 + event.unit.toUInt64

/-- Complete report-based audit definition, retaining existing domain separation. -/
def auditDigest (behavior totalSteps : UInt64) (outcomes : Array GoalOutcome)
    (retirements : Array AuditRetirement) : UInt64 :=
  let start := hashBytes "deterministic-audit-v2".toUTF8 ^^^ behavior
  let outcomeFold := outcomes.foldl foldOutcome start
  retirements.foldl foldRetirement (outcomeFold ^^^ Rng.rotateLeft totalSteps 29)

/-- Resource refusal for aggregate totals that have no unsigned machine representation. -/
inductive MetricError where
  /-- The complete retained step total would overflow. -/
  | totalStepsOverflow
  deriving DecidableEq

/-- Atomic total-step aggregation, checked before accepting another outcome. -/
def addOutcomeSteps (total : UInt64) (outcome : GoalOutcome) : Except MetricError UInt64 :=
  match Word.advanceClock total outcome.steps with
  | some next => .ok next
  | none => .error .totalStepsOverflow

/-- Accepted totals equal the exact sum of their admitted words. -/
theorem addOutcomeSteps_exact (total next : UInt64) (outcome : GoalOutcome)
    (h : addOutcomeSteps total outcome = .ok next) : next.toNat = total.toNat + outcome.steps.toNat := by
  unfold addOutcomeSteps at h
  cases hc : Word.advanceClock total outcome.steps with
  | none => simp [hc] at h
  | some value =>
    simp only [hc, Except.ok.injEq] at h
    cases h
    exact Word.clock_advance_exact _ _ _ hc

/-- An affine word fold retains all outcome influence without retaining outcomes.
The final behavior fingerprint can be supplied after the campaign ends. -/
structure OutcomeFold where
  /-- Product of the per-outcome multipliers. -/
  multiplier : UInt64 := 1
  /-- Folded additive contribution of outcomes. -/
  offset : UInt64 := 0

/-- Extend the affine summary with exactly one outcome in stream order. -/
def OutcomeFold.push (summary : OutcomeFold) (outcome : GoalOutcome) : OutcomeFold :=
  ⟨summary.multiplier * 0x100000001b3, foldOutcome summary.offset outcome⟩

/-- Evaluate the retained affine function on a final audit starting word. -/
def OutcomeFold.apply (summary : OutcomeFold) (initial : UInt64) : UInt64 :=
  initial * summary.multiplier + summary.offset

/-- Word distributivity proves the incremental summary for every incoming fold,
without replay, enumeration, or ideal-integer overflow assumptions. -/
theorem OutcomeFold.push_apply (summary : OutcomeFold) (outcome : GoalOutcome) (initial : UInt64) :
    (summary.push outcome).apply initial = foldOutcome (summary.apply initial) outcome := by
  simp [push, apply, foldOutcome, UInt64.add_mul, UInt64.mul_assoc, UInt64.add_assoc]

/-- Every finite outcome sequence is represented by the same two-word summary. -/
theorem OutcomeFold.fold_apply (outcomes : List GoalOutcome) (summary : OutcomeFold) (initial : UInt64) :
    (outcomes.foldl push summary).apply initial = outcomes.foldl foldOutcome (summary.apply initial) := by
  induction outcomes generalizing summary with
  | nil => rfl
  | cons outcome tail ih => simp only [List.foldl_cons, ih, push_apply]

/-- Final audit construction uses the exact source order without retaining rows. -/
def streamingAudit (summary : OutcomeFold) (behavior totalSteps : UInt64)
    (retirements : Array AuditRetirement) : UInt64 :=
  let initial := hashBytes "deterministic-audit-v2".toUTF8 ^^^ behavior
  retirements.foldl foldRetirement (summary.apply initial ^^^ Rng.rotateLeft totalSteps 29)

/-- The streaming audit equals the report fold for all outcome and retirement arrays. -/
theorem streamingAudit_eq_report (outcomes : Array GoalOutcome) (behavior totalSteps : UInt64)
    (retirements : Array AuditRetirement) :
    streamingAudit (outcomes.foldl OutcomeFold.push {}) behavior totalSteps retirements =
      auditDigest behavior totalSteps outcomes retirements := by
  have h := OutcomeFold.fold_apply outcomes.toList ({} : OutcomeFold)
    (hashBytes "deterministic-audit-v2".toUTF8 ^^^ behavior)
  simp only [OutcomeFold.apply, UInt64.mul_one, UInt64.add_zero] at h
  simpa [streamingAudit, auditDigest, OutcomeFold.apply, ← Array.foldl_toList] using
    congrArg (fun value => retirements.foldl foldRetirement (value ^^^ Rng.rotateLeft totalSteps 29)) h

end Acorn.Host
