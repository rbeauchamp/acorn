/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Attempt

/-!
# Current campaign admission and boundary progression

Only a completed attempt reaches the supervision boundary. Goal and attempt
indices carry their receiving bounds, while the cycle and checkpoint counters
retain their source-specific saturation rules. An empty unbounded campaign
cannot be constructed. No action-selection callback receives a stop request.
-/
namespace Acorn.Host

/-- Campaign-domain errors precede world/agent construction or checkpoint I/O. -/
inductive CampaignError where
  /-- A campaign must permit at least one step per attempt. -/
  | stepCapZero
  /-- An unbounded campaign must reach attempt boundaries. -/
  | emptyUnbounded
  /-- Only ranked agent constructions have a durable encoding. -/
  | nonresumableProfile
  deriving DecidableEq

/-- Public campaign fields in the 64-bit native host domain. -/
structure CampaignSpec where
  /-- Steps per attempt; zero is refused for campaigns. -/
  steps : UInt64
  /-- Requested attempts per goal; zero normalizes to one. -/
  attempts : UInt64
  /-- Requested goal count, clipped to the supplied curriculum. -/
  goals : UInt64
  /-- Zero means unbounded repetitions. -/
  cycles : UInt64

/-- Receiving campaign plan, with every loop admission invariant stored in its type. -/
structure CampaignPlan (curriculumSize : Nat) where
  /-- Positive per-attempt cap. -/
  stepCap : UInt64
  /-- No admitted campaign has a zero attempt length. -/
  positiveSteps : 0 < stepCap.toNat
  /-- Positive effective attempt count. -/
  attempts : UInt64
  /-- Attempt count normalization is complete before execution. -/
  positiveAttempts : 0 < attempts.toNat
  /-- Effective goal count, bounded by the receiving curriculum. -/
  goals : Fin (curriculumSize + 1)
  /-- Repetition budget; zero denotes unbounded execution. -/
  cycles : UInt64
  /-- Unbounded execution always reaches a nonempty goal range. -/
  productive : cycles.toNat ≠ 0 ∨ goals.val > 0

/-- Complete campaign admission, before constructing a world or invoking any agent hook. -/
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

/-- A live cursor always names an existing goal and a legal within-goal attempt. -/
structure CampaignCursor {size : Nat} (plan : CampaignPlan size) where
  /-- Zero-based cycle number, saturating over unbounded execution. -/
  cycle : UInt64
  /-- In-range goal index. -/
  goal : Fin plan.goals.val
  /-- In-range attempt number before source-compatible telemetry narrowing. -/
  attempt : Fin plan.attempts.toNat

/-- Saturating unsigned 64-bit increment. -/
def saturatingIncrement64 (value : UInt64) : UInt64 :=
  (min (value.toNat + 1) (2 ^ 64 - 1)).toUInt64

/-- Saturating unsigned 32-bit increment, including checkpoint schedule counters. -/
def saturatingIncrement32 (value : UInt32) : UInt32 :=
  (min (value.toNat + 1) (2 ^ 32 - 1)).toUInt32

/-- The boundary can continue, exhaust a finite budget, or honor graceful stop. -/
inductive BoundaryDecision {size : Nat} (plan : CampaignPlan size) where
  /-- Start the named next attempt in the same continual stream. -/
  | continue (cursor : CampaignCursor plan)
  /-- The finite campaign is complete. -/
  | complete
  /-- Stop is honored after the completed attempt. -/
  | stopped

/-- Final boundaries require an armed checkpoint before returning the campaign. -/
def BoundaryDecision.closing {size : Nat} {plan : CampaignPlan size} : BoundaryDecision plan → Bool
  | .continue _ => false
  | .complete | .stopped => true

/-- Pure boundary progression, the only transition that consumes a stop request. -/
def atAttemptBoundary {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (achieved stopping : Bool) : BoundaryDecision plan :=
  if stopping then .stopped
  else if !achieved then
    if ha : cursor.attempt.val + 1 < plan.attempts.toNat then
      .continue { cursor with attempt := ⟨cursor.attempt.val + 1, ha⟩ }
    else nextGoal
  else nextGoal
where
  /-- Goal advancement uses the same cycle rule after achievement and attempt exhaustion. -/
  nextGoal : BoundaryDecision plan :=
    if hg : cursor.goal.val + 1 < plan.goals.val then
      .continue ⟨cursor.cycle, ⟨cursor.goal.val + 1, hg⟩, ⟨0, plan.positiveAttempts⟩⟩
    else
      let cycle := saturatingIncrement64 cursor.cycle
      if plan.cycles != 0 && cycle ≥ plan.cycles then .complete
      else .continue ⟨cycle, ⟨0, by have := cursor.goal.isLt; omega⟩, ⟨0, plan.positiveAttempts⟩⟩

/-- A raised stop is consumed at this boundary regardless of goal outcome or remaining budget. -/
theorem atAttemptBoundary_stop {size : Nat} {plan : CampaignPlan size} (cursor : CampaignCursor plan)
    (achieved : Bool) : atAttemptBoundary cursor achieved true = .stopped := rfl

/-- Empty finite campaigns have no cursor and need no repeated empty-loop execution. -/
def CampaignPlan.initial {size : Nat} (plan : CampaignPlan size) : BoundaryDecision plan :=
  if hg : 0 < plan.goals.val then
    .continue ⟨0, ⟨0, hg⟩, ⟨0, plan.positiveAttempts⟩⟩
  else .complete

/-- Empty campaign completion is possible only with a finite cycle budget. -/
theorem CampaignPlan.empty_finite {size : Nat} (plan : CampaignPlan size) (h : plan.goals.val = 0) :
    plan.cycles.toNat ≠ 0 := by have := plan.productive; omega

/-- The three load outcomes that govern future write authority. -/
inductive CheckpointAdmission where
  /-- The image was accepted. -/
  | loaded
  /-- No image existed. -/
  | missing
  /-- An existing image was refused. -/
  | refused
  deriving DecidableEq

/-- A path can be written only with a positive schedule and admitted image status. -/
structure WritableCheckpoint where
  private mk ::
  /-- Receiving path, retained from admission rather than supplied at a write site. -/
  path : System.FilePath
  /-- Positive attempt interval; zero is a load-only policy. -/
  interval : UInt32
  /-- The schedule never divides by zero. -/
  positive : 0 < interval.toNat
  /-- Periodic phase is bounded by this capability's own interval. -/
  phase : Fin interval.toNat

/-- Refused images and disabled schedules produce no write capability. -/
def WritableCheckpoint.admit (path : System.FilePath) (interval : UInt32) (status : CheckpointAdmission) :
    Option WritableCheckpoint :=
  match status with
  | .refused => none
  | .loaded | .missing => if h : 0 < interval.toNat then some ⟨path, interval, h, ⟨0, h⟩⟩ else none

/-- Advance exactly one completed attempt without a saturating lifetime counter. -/
def WritableCheckpoint.advance (capability : WritableCheckpoint) : WritableCheckpoint :=
  { capability with phase := ⟨(capability.phase.val + 1) % capability.interval.toNat,
      Nat.mod_lt _ capability.positive⟩ }

/-- Periodic phase is exactly modular arithmetic over its positive interval. -/
theorem WritableCheckpoint.advance_phase (capability : WritableCheckpoint) :
    capability.advance.phase.val = (capability.phase.val + 1) % capability.interval.toNat := rfl

/-- Mathematical iteration uses the same phase update as every native attempt boundary. -/
def WritableCheckpoint.advanceBy (capability : WritableCheckpoint) : Nat → WritableCheckpoint
  | 0 => capability
  | count + 1 => capability.advance.advanceBy count

/-- Every finite attempt prefix preserves the selected interval. -/
theorem WritableCheckpoint.advanceBy_interval (capability : WritableCheckpoint) (count : Nat) :
    (capability.advanceBy count).interval = capability.interval := by
  induction count generalizing capability with
  | zero => rfl
  | succ count ih => exact ih capability.advance

/-- Arbitrarily long prefixes remain periodic, independently of reporting counter saturation. -/
theorem WritableCheckpoint.advanceBy_phase (capability : WritableCheckpoint) (count : Nat) :
    (capability.advanceBy count).phase.val =
      (capability.phase.val + count) % capability.interval.toNat := by
  induction count generalizing capability with
  | zero => exact (Nat.mod_eq_of_lt capability.phase.isLt).symm
  | succ count ih =>
    simp only [advanceBy, ih, advance, Nat.mod_add_mod]
    congr 1
    omega

/-- Final boundaries accelerate only an already admitted checkpoint write. -/
def WritableCheckpoint.due (capability : WritableCheckpoint) (closing : Bool) : Bool :=
  closing || capability.phase.val == 0

/-- Save scheduling consumes the actual execution decision and advanced periodic phase. -/
def WritableCheckpoint.dueAt {size : Nat} {plan : CampaignPlan size}
    (capability : WritableCheckpoint) (decision : BoundaryDecision plan) : Bool :=
  capability.due decision.closing

/-- Every closing execution boundary schedules its armed writer at every periodic phase. -/
theorem WritableCheckpoint.closing_due {size : Nat} {plan : CampaignPlan size}
    (capability : WritableCheckpoint) (decision : BoundaryDecision plan)
    (closing : decision.closing = true) : capability.dueAt decision = true := by
  simp [dueAt, due, closing]

/-- Stop schedules the armed writer independently of outcome, cursor and periodic phase. -/
theorem WritableCheckpoint.stop_due {size : Nat} {plan : CampaignPlan size}
    (capability : WritableCheckpoint) (cursor : CampaignCursor plan)
    (achieved : Bool) : capability.dueAt (atAttemptBoundary cursor achieved true) = true := by
  simp [atAttemptBoundary_stop, dueAt, BoundaryDecision.closing, due]

/-- No amount of stopping or schedule progress can re-enable a refused image. -/
theorem WritableCheckpoint.refused (path : System.FilePath) (interval : UInt32) :
    admit path interval .refused = none := rfl

end Acorn.Host
