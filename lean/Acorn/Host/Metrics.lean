import Acorn.Host.Task

namespace Acorn.Host

structure LearnerMetrics where
  demonError : Binary32
  epsilon : Binary32
  meanAlpha : Binary32

structure GoalOutcome where
  index : UInt64
  attempt : UInt64
  tier : UInt8
  steps : UInt64
  achieved : Bool
  reward : Binary32
  learner : LearnerMetrics
  position : Position

def foldAction (fold : UInt64) (action : Action) : UInt64 :=
  fold * 0x100000001b3 + action.index.val.toUInt64 + 1

def hashBytes (bytes : ByteArray) : UInt64 :=
  bytes.data.foldl Rng.fnvStep Rng.fnvOffset

def initialBehavior : UInt64 := hashBytes "decision-stream-v1".toUTF8

def foldOutcome (fold : UInt64) (outcome : GoalOutcome) : UInt64 :=
  let mixed : UInt64 := fold * (0x100000001b3 : UInt64)
  let achieved : UInt64 := if outcome.achieved then 1 else 0
  mixed + outcome.steps + achieved + (outcome.tier.toUInt64 <<< (32 : UInt64))

structure AuditRetirement where
  step : UInt64
  unit : UInt32

def foldRetirement (fold : UInt64) (event : AuditRetirement) : UInt64 :=
  (fold * 0x100000001b3 + event.step) * 0x100000001b3 + event.unit.toUInt64

def auditDigest (behavior totalSteps : UInt64) (outcomes : Array GoalOutcome)
    (retirements : Array AuditRetirement) : UInt64 :=
  let start := hashBytes "deterministic-audit-v2".toUTF8 ^^^ behavior
  let outcomeFold := outcomes.foldl foldOutcome start
  retirements.foldl foldRetirement (outcomeFold ^^^ Rng.rotateLeft totalSteps 29)

theorem foldOutcome_position (fold : UInt64) (outcome : GoalOutcome) (position : Position) :
    foldOutcome fold { outcome with position := position } = foldOutcome fold outcome := rfl

inductive MetricError where
  | totalStepsOverflow
  deriving DecidableEq

def addOutcomeSteps (total : UInt64) (outcome : GoalOutcome) : Except MetricError UInt64 :=
  match Word.advanceClock total outcome.steps with
  | some next => .ok next
  | none => .error .totalStepsOverflow

theorem addOutcomeSteps_position (total : UInt64) (outcome : GoalOutcome) (position : Position) :
    addOutcomeSteps total { outcome with position := position } = addOutcomeSteps total outcome := rfl

theorem addOutcomeSteps_exact (total next : UInt64) (outcome : GoalOutcome)
    (h : addOutcomeSteps total outcome = .ok next) : next.toNat = total.toNat + outcome.steps.toNat := by
  unfold addOutcomeSteps at h
  cases hc : Word.advanceClock total outcome.steps with
  | none => simp [hc] at h
  | some value =>
    simp only [hc, Except.ok.injEq] at h
    cases h
    exact Word.clock_advance_exact _ _ _ hc

structure OutcomeFold where
  multiplier : UInt64 := 1
  offset : UInt64 := 0

def OutcomeFold.push (summary : OutcomeFold) (outcome : GoalOutcome) : OutcomeFold :=
  ⟨summary.multiplier * 0x100000001b3, foldOutcome summary.offset outcome⟩

def OutcomeFold.apply (summary : OutcomeFold) (initial : UInt64) : UInt64 :=
  initial * summary.multiplier + summary.offset

theorem OutcomeFold.push_apply (summary : OutcomeFold) (outcome : GoalOutcome) (initial : UInt64) :
    (summary.push outcome).apply initial = foldOutcome (summary.apply initial) outcome := by
  simp [push, apply, foldOutcome, UInt64.add_mul, UInt64.mul_assoc, UInt64.add_assoc]

theorem OutcomeFold.fold_apply (outcomes : List GoalOutcome) (summary : OutcomeFold) (initial : UInt64) :
    (outcomes.foldl push summary).apply initial = outcomes.foldl foldOutcome (summary.apply initial) := by
  induction outcomes generalizing summary with
  | nil => rfl
  | cons outcome tail ih => simp only [List.foldl_cons, ih, push_apply]

def streamingAudit (summary : OutcomeFold) (behavior totalSteps : UInt64)
    (retirements : Array AuditRetirement) : UInt64 :=
  let initial := hashBytes "deterministic-audit-v2".toUTF8 ^^^ behavior
  retirements.foldl foldRetirement (summary.apply initial ^^^ Rng.rotateLeft totalSteps 29)

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
