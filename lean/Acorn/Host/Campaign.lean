import Acorn.Host.Attempt

namespace Acorn.Host

inductive CampaignError where
  | stepCapZero
  | emptyUnbounded
  | nonresumableProfile
  deriving DecidableEq

structure CampaignSpec where
  steps : UInt64
  attempts : UInt64
  goals : UInt64
  cycles : UInt64

structure CampaignPlan (curriculumSize : Nat) where
  stepCap : UInt64
  positiveSteps : 0 < stepCap.toNat
  attempts : UInt64
  positiveAttempts : 0 < attempts.toNat
  goals : Fin (curriculumSize + 1)
  cycles : UInt64
  productive : cycles.toNat ≠ 0 ∨ goals.val > 0

def CampaignPlan.admit (curriculumSize : Nat) (spec : CampaignSpec) :
    Except CampaignError (CampaignPlan curriculumSize) :=
  if hs : 0 < spec.steps.toNat then
    let goals : Fin (curriculumSize + 1) := ⟨min spec.goals.toNat curriculumSize, by omega⟩
    if hp : spec.cycles.toNat ≠ 0 ∨ goals.val > 0 then
      let attempts : UInt64 := if spec.attempts == 0 then 1 else spec.attempts
      .ok ⟨spec.steps, hs, attempts, by
        dsimp [attempts]
        split
        · decide
        · rename_i h
          have hn : spec.attempts ≠ 0 := by simpa using h
          have hz : spec.attempts.toNat ≠ 0 := by
            intro hz
            exact hn (UInt64.toNat.inj hz)
          omega,
        goals, spec.cycles, hp⟩
    else .error .emptyUnbounded
  else .error .stepCapZero

structure CampaignCursor {size : Nat} (plan : CampaignPlan size) where
  cycle : UInt64
  goal : Fin plan.goals.val
  attempt : Fin plan.attempts.toNat

def saturatingIncrement64 (value : UInt64) : UInt64 :=
  (min (value.toNat + 1) (2 ^ 64 - 1)).toUInt64

def saturatingIncrement32 (value : UInt32) : UInt32 :=
  (min (value.toNat + 1) (2 ^ 32 - 1)).toUInt32

inductive BoundaryDecision {size : Nat} (plan : CampaignPlan size) where
  | continue (cursor : CampaignCursor plan)
  | complete
  | stopped

def BoundaryDecision.closing {size : Nat} {plan : CampaignPlan size} : BoundaryDecision plan → Bool
  | .continue _ => false
  | .complete | .stopped => true

def atAttemptBoundary {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (achieved stopping : Bool) : BoundaryDecision plan :=
  if stopping then .stopped
  else if !achieved then
    if ha : cursor.attempt.val + 1 < plan.attempts.toNat then
      .continue { cursor with attempt := ⟨cursor.attempt.val + 1, ha⟩ }
    else nextGoal
  else nextGoal
where
  nextGoal : BoundaryDecision plan :=
    if hg : cursor.goal.val + 1 < plan.goals.val then
      .continue ⟨cursor.cycle, ⟨cursor.goal.val + 1, hg⟩, ⟨0, plan.positiveAttempts⟩⟩
    else
      let cycle := saturatingIncrement64 cursor.cycle
      if plan.cycles != 0 && cycle ≥ plan.cycles then .complete
      else .continue ⟨cycle, ⟨0, by have := cursor.goal.isLt; omega⟩, ⟨0, plan.positiveAttempts⟩⟩

theorem atAttemptBoundary_stop {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (achieved : Bool) : atAttemptBoundary cursor achieved true = .stopped := rfl

def CampaignPlan.initial {size : Nat} (plan : CampaignPlan size) : BoundaryDecision plan :=
  if hg : 0 < plan.goals.val then
    .continue ⟨0, ⟨0, hg⟩, ⟨0, plan.positiveAttempts⟩⟩
  else .complete

theorem CampaignPlan.empty_finite {size : Nat} (plan : CampaignPlan size) (h : plan.goals.val = 0) :
    plan.cycles.toNat ≠ 0 := by have := plan.productive; omega

inductive CheckpointAdmission where
  | loaded
  | missing
  | refused
  deriving DecidableEq

structure WritableCheckpoint where
  private mk ::
  path : System.FilePath
  interval : UInt32
  positive : 0 < interval.toNat
  phase : Fin interval.toNat

def WritableCheckpoint.admit (path : System.FilePath) (interval : UInt32) (status : CheckpointAdmission) :
    Option WritableCheckpoint :=
  match status with
  | .refused => none
  | .loaded | .missing => if h : 0 < interval.toNat then some ⟨path, interval, h, ⟨0, h⟩⟩ else none

def WritableCheckpoint.advance (capability : WritableCheckpoint) : WritableCheckpoint :=
  { capability with phase := ⟨(capability.phase.val + 1) % capability.interval.toNat,
      Nat.mod_lt _ capability.positive⟩ }

theorem WritableCheckpoint.advance_phase (capability : WritableCheckpoint) :
    capability.advance.phase.val = (capability.phase.val + 1) % capability.interval.toNat := rfl

def WritableCheckpoint.advanceBy (capability : WritableCheckpoint) : Nat → WritableCheckpoint
  | 0 => capability
  | count + 1 => capability.advance.advanceBy count

theorem WritableCheckpoint.advanceBy_interval (capability : WritableCheckpoint) (count : Nat) :
    (capability.advanceBy count).interval = capability.interval := by
  induction count generalizing capability with
  | zero => rfl
  | succ count ih => exact ih capability.advance

theorem WritableCheckpoint.advanceBy_phase (capability : WritableCheckpoint) (count : Nat) :
    (capability.advanceBy count).phase.val =
      (capability.phase.val + count) % capability.interval.toNat := by
  induction count generalizing capability with
  | zero => exact (Nat.mod_eq_of_lt capability.phase.isLt).symm
  | succ count ih =>
    simp only [advanceBy, ih, advance, Nat.mod_add_mod]
    congr 1
    omega

def WritableCheckpoint.due (capability : WritableCheckpoint) (closing : Bool) : Bool :=
  closing || capability.phase.val == 0

def WritableCheckpoint.dueAt {size : Nat} {plan : CampaignPlan size}
    (capability : WritableCheckpoint) (decision : BoundaryDecision plan) : Bool :=
  capability.due decision.closing

theorem WritableCheckpoint.closing_due {size : Nat} {plan : CampaignPlan size}
    (capability : WritableCheckpoint) (decision : BoundaryDecision plan)
    (closing : decision.closing = true) : capability.dueAt decision = true := by
  simp [dueAt, due, closing]

theorem WritableCheckpoint.stop_due {size : Nat} {plan : CampaignPlan size}
    (capability : WritableCheckpoint) (cursor : CampaignCursor plan)
    (achieved : Bool) : capability.dueAt (atAttemptBoundary cursor achieved true) = true := by
  simp [atAttemptBoundary_stop, dueAt, BoundaryDecision.closing, due]

theorem WritableCheckpoint.refused (path : System.FilePath) (interval : UInt32) :
    admit path interval .refused = none := rfl

end Acorn.Host
