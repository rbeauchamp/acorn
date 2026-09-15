/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Demon
import Acorn.Agreement

/-!
# Bounded lifetime observations

The durable record and process-local pending returns are separate. All updates
consume observations; no policy reads this record. Counters saturate, histories
have fixed shapes, and each pending return belongs to its prediction horizon.
The record summarizes the experienced stream. File serialization belongs to
the persistence owner.
-/
set_option maxRecDepth 4096

namespace Acorn.Lifetime
open Features
open Acorn.FeatureConstants

/-- Saturating addition shared by lifetime counters. -/
def addCount (left right : UInt64) : UInt64 :=
  (min (left.toNat + right.toNat) (2^64 - 1)).toUInt64

/-- Saturating arithmetic has its exact natural-number interpretation. -/
theorem addCount_exact (left right : UInt64) :
    (addCount left right).toNat = min (left.toNat + right.toNat) (2^64 - 1) := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right (left.toNat + right.toNat) (2^64 - 1)
  omega

/-- Fixed logarithmic history index, including the zero clock. -/
def historyBin (step : UInt64) : Fin historyBins :=
  ⟨min step.toNat.log2 (historyBins - 1), by have := Nat.min_le_right step.toNat.log2 63; change min step.toNat.log2 63 < 64; omega⟩

/-- Eight exact cycles followed by logarithmic buckets and a saturated tail. -/
def cycleBin (cycle : UInt64) : Fin cycleBins :=
  if h : cycle.toNat < exactCycles then ⟨cycle.toNat, by simp only [exactCycles, cycleBins] at *; omega⟩
  else ⟨min (exactCycles + (cycle.toNat - exactCycles + 1).log2) (cycleBins - 1), by
    have := Nat.min_le_right (exactCycles + (cycle.toNat - exactCycles + 1).log2) (cycleBins - 1); simp only [cycleBins] at *; omega⟩

/-- Closed scalar kinds own the reading bound; callers cannot widen it. -/
inductive Quantity where
  /-- Environment reward. -/
  | reward
  /-- Squared prediction error at the receiving horizon. -/
  | squaredError (discount : Discount)
  deriving DecidableEq

/-- Signed settled error uses the current twice-horizon envelope. -/
def errorBound (discount : Discount) : Binary32 :=
  Agreement.errorEnvelope discount

/-- The receiving scalar kind determines its machine bound. -/
def Quantity.bound : Quantity → Binary32
  | .reward => .one
  | .squaredError discount => (errorBound discount).mul (errorBound discount)

/-- Every reading is projected under its closed finite envelope. -/
def Quantity.range (quantity : Quantity) : Interval32 :=
  ⟨.zero, quantity.bound, by decide,
    by cases quantity with
       | reward => decide
       | squaredError discount => cases discount <;> decide,
    by cases quantity with
       | reward => decide
       | squaredError discount => cases discount <;> decide⟩

/-- Stored signed settled-error domain. -/
def errorRange (discount : Discount) : Symmetric32 where
  range := ⟨(errorBound discount).negate, errorBound discount,
    by cases discount <;> decide, by cases discount <;> decide,
    by cases discount <;> decide⟩
  symmetric := rfl
  zeroLegal := by cases discount <;> decide

/-- Current binary64 total cap, derived from the count and immutable quantity. -/
def maximumSum (quantity : Quantity) (count : UInt64) : Binary64 :=
  (Binary64.ofUInt64 count).mul (Conversion.widen quantity.bound)

/-- A total's precise stored invariant, including the empty record. -/
def LegalSum (quantity : Quantity) (count : UInt64) (sum : Binary64) : Prop :=
  sum.Finite ∧ 0 ≤ sum.key ∧ sum.key ≤ (maximumSum quantity count).key ∧
    (count = 0 → sum.key = 0)

instance (quantity : Quantity) (count : UInt64) (sum : Binary64) :
    Decidable (LegalSum quantity count sum) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Exact source update expression over stored words. -/
def sumUpdate (quantity : Quantity) (count : UInt64) (sum : Binary64) (value : Binary32) :
    UInt64 × Binary64 :=
  let count := addCount count 1
  let value := quantity.range.saturate value
  let sum := sum.add (Conversion.widen value)
  let bound := maximumSum quantity count
  (count, if bound.less sum then bound else sum)

/-- Every total comes from legal durable admission or the exact current write.
This provenance is erased; it is not a retained observation history. -/
inductive SumAdmitted (quantity : Quantity) : UInt64 → Binary64 → Prop where
  /-- Durable reconstruction is identity and requires the receiving numeric invariant. -/
  | durable (count : UInt64) (sum : Binary64) (legal : LegalSum quantity count sum) :
      SumAdmitted quantity count sum
  /-- A write may use the receiving bound or a narrower closed quantity. -/
  | observation (count : UInt64) (sum : Binary64) (value : Binary32) (written : Quantity)
      (bound : written.bound.key ≤ quantity.bound.key) (prior : SumAdmitted quantity count sum) :
      SumAdmitted quantity (sumUpdate written count sum value).1 (sumUpdate written count sum value).2

/-- Exact-count machine total with all admission and write paths recorded in its type. -/
structure SumCount (quantity : Quantity) where
  /-- Saturating observation count. -/
  count : UInt64
  /-- Ordered binary64 sum. -/
  sum : Binary64
  /-- Erased evidence for the actual admission/write path. -/
  admitted : SumAdmitted quantity count sum

/-- The zero record has no observations. -/
def SumCount.initial (quantity : Quantity) : SumCount quantity :=
  ⟨0, ⟨0⟩, .durable 0 ⟨0⟩ (by cases quantity with
    | reward => decide
    | squaredError discount => cases discount <;> decide)⟩

/-- Admit a durable total without modifying either word. -/
def SumCount.admit (quantity : Quantity) (count : UInt64) (sum : Binary64) :
    Option (SumCount quantity) :=
  if h : LegalSum quantity count sum then some ⟨count, sum, .durable count sum h⟩ else none

/-- Update under a closed narrower reading envelope, retaining the source cap. -/
def SumCount.observeAs {quantity : Quantity} (state : SumCount quantity) (written : Quantity)
    (bound : written.bound.key ≤ quantity.bound.key) (value : Binary32) : SumCount quantity :=
  let next := sumUpdate written state.count state.sum value
  ⟨next.1, next.2, .observation state.count state.sum value written bound state.admitted⟩

/-- One live write uses the receiving quantity's own envelope. -/
def SumCount.observe {quantity : Quantity} (state : SumCount quantity) (value : Binary32) :
    SumCount quantity := state.observeAs quantity (Int.le_refl _) value

/-- Every observation retains the exact ordered computation. -/
theorem SumCount.observe_exact {quantity : Quantity} (state : SumCount quantity) (value : Binary32) :
    ((state.observe value).count, (state.observe value).sum) =
      sumUpdate quantity state.count state.sum value := rfl

/-- Goal aggregates store the count relation at every write. -/
structure GoalTotals where
  /-- Completed attempts. -/
  attempts : UInt64
  /-- Achieved attempts. -/
  successes : UInt64
  /-- Total completed-attempt steps. -/
  steps : UInt64
  /-- Success is a subset of attempts. -/
  successesBound : successes.toNat ≤ attempts.toNat
  /-- Empty records cannot contain steps. -/
  emptySteps : attempts = 0 → steps = 0

/-- No completed goal attempts. -/
def GoalTotals.initial : GoalTotals := ⟨0, 0, 0, by decide, fun _ => rfl⟩

/-- One completed attempt writes its counts together. -/
def GoalTotals.observe (state : GoalTotals) (steps : UInt64) (achieved : Bool) : GoalTotals :=
  ⟨addCount state.attempts 1, addCount state.successes (if achieved then 1 else 0),
    addCount state.steps steps, by
      rw [addCount_exact, addCount_exact]
      have := state.successesBound
      cases achieved <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · change min (state.successes.toNat + 0) _ ≤ min (state.attempts.toNat + 1) _; omega
      · change min (state.successes.toNat + 1) _ ≤ min (state.attempts.toNat + 1) _; omega,
    by
      intro empty
      have h := congrArg UInt64.toNat empty
      rw [addCount_exact] at h
      change min (state.attempts.toNat + 1) (2^64 - 1) = 0 at h
      omega⟩

/-- Current three-reason option episode totals. -/
structure OptionEpisodes where
  /-- Episode starts. -/
  started : UInt64
  /-- Completed episode durations. -/
  duration : UInt64
  /-- Goal, duration and interruption endings, in that order. -/
  reasons : Vector UInt64 3

/-- Completed episodes are derived from the same reason counters. -/
def OptionEpisodes.completed (state : OptionEpisodes) : UInt64 :=
  state.reasons.toList.foldl addCount 0

/-- No option episode has started. -/
def OptionEpisodes.initial : OptionEpisodes := ⟨0, 0, Vector.replicate _ 0⟩

/-- Record one actual invocation. -/
def OptionEpisodes.start (state : OptionEpisodes) : OptionEpisodes :=
  { state with started := addCount state.started 1 }

/-- Record one consumed activation and its reason atomically. -/
def OptionEpisodes.finish (state : OptionEpisodes) (duration : UInt32) (reason : Fin 3) :
    OptionEpisodes :=
  { state with
    duration := addCount state.duration (UInt64.ofNat duration.toNat)
    reasons := state.reasons.set reason.val (addCount state.reasons[reason.val] 1) reason.isLt }

/-- Episode counts agree with the outstanding invocation, even after counter saturation. -/
def OptionEpisodes.Valid (state : OptionEpisodes) (active : Bool) : Prop :=
  state.completed.toNat ≤ state.started.toNat ∧
    (state.completed = 0 → state.duration = 0) ∧
    (active = true → state.completed.toNat < state.started.toNat ∨ state.started.toNat = 2^64 - 1)

/-- The three reason counters determine their saturating completed total exactly. -/
theorem OptionEpisodes.completed_exact (state : OptionEpisodes) :
    state.completed.toNat = min
      ((state.reasons[0]).toNat + (state.reasons[1]).toNat + (state.reasons[2]).toNat) (2^64 - 1) := by
  have expanded : state.reasons = #v[state.reasons[0], state.reasons[1], state.reasons[2]] := by
    apply Vector.ext
    intro index bound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl
  unfold OptionEpisodes.completed
  rw [expanded]
  change (addCount (addCount (addCount 0 state.reasons[0]) state.reasons[1]) state.reasons[2]).toNat =
    min (state.reasons[0].toNat + state.reasons[1].toNat + state.reasons[2].toNat) (2^64 - 1)
  simp only [addCount_exact]
  change min (min (min (0 + (state.reasons[0]).toNat) (2^64 - 1) +
    (state.reasons[1]).toNat) (2^64 - 1) + (state.reasons[2]).toNat) (2^64 - 1) = _
  have := (state.reasons[0]).toNat_lt
  omega

/-- Starting an invocation does not change any completed episode. -/
theorem OptionEpisodes.start_completed (state : OptionEpisodes) :
    state.start.completed = state.completed := rfl

/-- One consumed activation increments the derived completed total exactly once. -/
theorem OptionEpisodes.finish_completed (state : OptionEpisodes) (duration : UInt32) (reason : Fin 3) :
    (state.finish duration reason).completed.toNat = min (state.completed.toNat + 1) (2^64 - 1) := by
  rw [completed_exact, completed_exact]
  rcases reason with ⟨reason, bound⟩
  have cases : reason = 0 ∨ reason = 1 ∨ reason = 2 := by omega
  rcases cases with rfl | rfl | rfl <;>
    simp only [OptionEpisodes.finish, Vector.getElem_set, ↓reduceIte, Nat.reduceEqDiff,
      addCount_exact, UInt64.reduceToNat] <;> omega

/-- No invocation has ended or remains active at cold initialization. -/
theorem OptionEpisodes.initial_valid : OptionEpisodes.initial.Valid false := by
  exact ⟨by decide, fun _ => rfl, by intro impossible; contradiction⟩

/-- Start uses the same saturating counter and reserves one outstanding completion. -/
theorem OptionEpisodes.start_valid (state : OptionEpisodes) (valid : state.Valid false) :
    state.start.Valid true := by
  rcases valid with ⟨completed, empty, _⟩
  refine ⟨?_, empty, ?_⟩
  · change state.completed.toNat ≤ (addCount state.started 1).toNat
    rw [addCount_exact]
    have := state.started.toNat_lt
    change state.completed.toNat ≤ min (state.started.toNat + 1) (2^64 - 1)
    omega
  · intro _
    change state.completed.toNat < (addCount state.started 1).toNat ∨
      (addCount state.started 1).toNat = 2^64 - 1
    rw [addCount_exact]
    change state.completed.toNat < min (state.started.toNat + 1) (2^64 - 1) ∨
      min (state.started.toNat + 1) (2^64 - 1) = 2^64 - 1
    omega

/-- Finish consumes exactly the outstanding invocation; empty totals cannot acquire duration. -/
theorem OptionEpisodes.finish_valid (state : OptionEpisodes) (valid : state.Valid true)
    (duration : UInt32) (reason : Fin 3) : (state.finish duration reason).Valid false := by
  refine ⟨?_, ?_, by intro impossible; contradiction⟩
  · rw [finish_completed]
    change min (state.completed.toNat + 1) (2^64 - 1) ≤ state.started.toNat
    have room := valid.2.2 rfl
    omega
  · intro zero
    have h := congrArg UInt64.toNat zero
    rw [finish_completed] at h
    change min (state.completed.toNat + 1) (2^64 - 1) = 0 at h
    omega

/-- Complete scalar payload of one actual option ending. -/
structure EpisodeEnd where
  /-- Stable option slot. -/
  slot : Fin Acorn.FeatureConstants.skillCount
  /-- Consumed activation duration. -/
  duration : UInt32
  /-- Closed goal/duration/interruption reason. -/
  reason : Fin 3

/-- Endings are recorded before starts, including replacement in the same slot. -/
def recordOptions (options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount)
    (ended : Option EpisodeEnd) (started : Option (Fin Acorn.FeatureConstants.skillCount)) :
    Vector OptionEpisodes Acorn.FeatureConstants.skillCount :=
  let options := match ended with
    | none => options
    | some event => options.set event.slot.val
        (options[event.slot.val].finish event.duration event.reason) event.slot.isLt
  match started with
  | none => options
  | some slot => options.set slot.val options[slot.val].start slot.isLt

/-- Each slot's observations carry the outstanding invocation owned by exclusive occupancy. -/
def OptionsValid (options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount)
    (active : Option (Fin Acorn.FeatureConstants.skillCount)) : Prop :=
  ∀ slot : Fin Acorn.FeatureConstants.skillCount, options[slot.val].Valid (active == some slot)

/-- Completing the active slot leaves all slots with no outstanding invocation. -/
theorem options_finish_valid (options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount)
    (event : EpisodeEnd) (valid : OptionsValid options (some event.slot)) :
    OptionsValid (options.set event.slot.val
      (options[event.slot.val].finish event.duration event.reason) event.slot.isLt) none := by
  intro slot
  by_cases same : event.slot = slot
  · subst slot
    simpa using (options[event.slot.val].finish_valid (by simpa using valid event.slot)
      event.duration event.reason)
  · have different : event.slot.val ≠ slot.val := fun equality => same (Fin.ext equality)
    have unequal : (event.slot == slot) = false := Bool.eq_false_iff.mpr (fun h => same (beq_iff_eq.mp h))
    simpa [Vector.getElem_set, different, unequal] using valid slot

/-- Beginning one slot reserves exactly one outstanding completion. -/
theorem options_start_valid (options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount)
    (started : Fin Acorn.FeatureConstants.skillCount) (valid : OptionsValid options none) :
    OptionsValid (options.set started.val options[started.val].start started.isLt) (some started) := by
  intro slot
  by_cases same : started = slot
  · subst slot
    simpa using (options[started.val].start_valid (by simpa using valid started))
  · have different : started.val ≠ slot.val := fun equality => same (Fin.ext equality)
    have unequal : (started == slot) = false := Bool.eq_false_iff.mpr (fun h => same (beq_iff_eq.mp h))
    simpa [Vector.getElem_set, different, unequal] using valid slot

/-- Pending empirical returns contain raw transient arithmetic, never learner input. -/
structure PendingPrediction (discount : Discount) where
  /-- Completed observations of this pending return. -/
  age : Fin (maxSettlement + 1)
  /-- Prediction being evaluated. -/
  prediction : Prediction discount
  /-- Ordered current return. -/
  returnSum : Binary32
  /-- Next cumulant multiplier. -/
  discountPower : Binary32
  /-- Clock at the prediction's capture. -/
  startedAt : UInt64

/-- Capturing a forecast consumes no outcome; its first multiplier is exactly one. -/
def PendingPrediction.initial {discount : Discount} (clock : UInt64)
    (prediction : Prediction discount) : PendingPrediction discount :=
  ⟨⟨0, by decide⟩, prediction, .zero, .one, clock⟩

/-- First machine horizon reaching the declared one-percent residual, capped at 600.
The loop is bounded diagnostic accounting, never certified agent re-execution. -/
@[irreducible] def settlementHorizon (discount : Discount) : Fin (maxSettlement + 1) :=
  ((List.finRange maxSettlement).foldl (fun (state : Binary32 × Fin (maxSettlement + 1)) step =>
    if (⟨Acorn.FeatureConstants.settleRemainingBits⟩ : Binary32).less state.1 then
      (state.1.mul discount.gamma, ⟨step.val + 1, by have := step.isLt; omega⟩)
    else state) (.one, 0)).2

/-- One horizon-indexed durable prediction record. -/
structure DemonDurable (discount : Discount) where
  /-- Settled squared-error total at this horizon. -/
  squaredError : SumCount (.squaredError discount)
  /-- Last settled empirical return. -/
  lastReturn : Prediction discount
  /-- Last signed error under the same horizon. -/
  lastError : Bounded32 (errorRange discount).range

/-- Empty horizon-indexed prediction record. -/
def DemonDurable.initial (discount : Discount) : DemonDurable discount :=
  ⟨SumCount.initial _, Prediction.project _ .zero,
    Bounded32.projectSymmetric (errorRange discount) .zero⟩

/-- Pending samples have fixed capacity, independent of elapsed lifetime. -/
structure DemonStats (discount : Discount) where
  /-- The durable projection. -/
  durable : DemonDurable discount
  /-- Twenty-six possible overlapping sampled returns, each owned by this channel. -/
  pending : Vector (Option (PendingPrediction discount)) pendingSamples
  /-- Current-process exact agreement; it shares this channel's pending bank. -/
  agreement : Agreement.Channel discount
  /-- Compute the immutable settlement horizon once, with its exact owner linkage. -/
  settleAfter : { value : Fin (maxSettlement + 1) // value = settlementHorizon discount }

/-- Restore only durable observations; process-local futures begin empty. -/
def DemonStats.restore {discount : Discount} (durable : DemonDurable discount) : DemonStats discount :=
  ⟨durable, Vector.replicate _ none, Agreement.Channel.empty discount, ⟨settlementHorizon discount, rfl⟩⟩

/-- Initial prediction accounting contains no invented pending observation. -/
def DemonStats.initial (discount : Discount) : DemonStats discount :=
  .restore (DemonDurable.initial discount)

/-- Exact outstanding sufficient-record count, without reading any raw history. -/
def DemonStats.pendingCount {discount : Discount} (state : DemonStats discount) : Nat :=
  state.pending.toList.countP Option.isSome

/-- Discard unavailable futures, preserving settled evidence and counting censorship. -/
def DemonStats.censor {discount : Discount} (state : DemonStats discount) : DemonStats discount :=
  { state with
    agreement := state.agreement.censor state.pendingCount
    pending := Vector.replicate _ none }

/-- A completed return's raw squared error and original history bucket. -/
structure Settlement where
  /-- Count-bound input before projection. -/
  squared : Binary32
  /-- Bucket belonging to the sample start, not its completion. -/
  bucket : Fin historyBins

/-- Advance one pending return in exact multiply/add/multiply order. -/
def PendingPrediction.advance {discount : Discount} (sample : PendingPrediction discount)
    (cumulant : Binary32) : PendingPrediction discount :=
  { sample with
    returnSum := sample.returnSum.add (sample.discountPower.mul cumulant)
    discountPower := sample.discountPower.mul discount.gamma
    age := ⟨min (sample.age.val + 1) maxSettlement, by
      have := Nat.min_le_right (sample.age.val + 1) maxSettlement; omega⟩ }

/-- Settle one pending return without changing the meaning of any raw error word. -/
def DemonStats.advanceSlot {discount : Discount} (state : DemonStats discount)
    (slot : Fin pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    DemonStats discount × Option Settlement := Id.run do
  match state.pending.get slot with
  | none => return (state, none)
  | some sample =>
    let sample := sample.advance cumulant
    if sample.age.val ≥ state.settleAfter.val.val then
      let error := sample.prediction.value.sub sample.returnSum
      let squared := error.mul error
      let total := state.durable.squaredError.observe squared
      let durable : DemonDurable discount :=
        ⟨total, Prediction.project discount sample.returnSum,
          Bounded32.projectSymmetric (errorRange discount) error⟩
      let agreement := state.agreement.settle sample.prediction.value sample.returnSum
        sample.discountPower sample.age.val sample.startedAt clock
      return (⟨durable, state.pending.set slot.val none slot.isLt, agreement, state.settleAfter⟩,
        some ⟨squared, historyBin sample.startedAt⟩)
    else return ({ state with pending := state.pending.set slot.val (some sample) slot.isLt }, none)

/-- Start at the fixed cadence in the first free slot, after all existing returns advanced. -/
def DemonStats.start {discount : Discount} (state : DemonStats discount)
    (clock : UInt64) (prediction : Prediction discount) : DemonStats discount :=
  if clock.toNat % settleStride = 0 then
    match (List.finRange pendingSamples).find? (fun slot => (state.pending.get slot).isNone) with
    | none => { state with agreement := { state.agreement with
        fault := state.agreement.fault.or (some .invalid) } }
    | some slot =>
      let sample := PendingPrediction.initial clock prediction
      { state with pending := state.pending.set slot.val (some sample) slot.isLt }
  else state

/-- Update a shared error-history bin under the currently settling channel's cap.
The stored domain remains the widest channel; the narrower per-write cap is retained. -/
def observeHistory (state : SumCount (.squaredError .g99)) (discount : Discount)
    (value : Binary32) : SumCount (.squaredError .g99) :=
  state.observeAs (.squaredError discount) (by cases discount <;> decide) value

/-- One slot transition with its separate durable-history projection. -/
def DemonStats.visit {discount : Discount}
    (current : DemonStats discount × Vector (SumCount (.squaredError .g99)) historyBins)
    (slot : Fin pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    DemonStats discount × Vector (SumCount (.squaredError .g99)) historyBins :=
  let (next, settled) := current.1.advanceSlot slot cumulant clock
  let bins := match settled with
    | none => current.2
    | some sample =>
      let bin := observeHistory (current.2.get sample.bucket) discount sample.squared
      current.2.set sample.bucket.val bin sample.bucket.isLt
  (next, bins)

/-- Slot traversal is shared by execution and the pending-bank correspondence proof. -/
@[irreducible] def DemonStats.advanceSlots {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) historyBins)
    (clock : UInt64) (cumulant : Binary32) (slots : List (Fin pendingSamples)) :
    DemonStats discount × Vector (SumCount (.squaredError .g99)) historyBins :=
  slots.foldl (fun current slot => DemonStats.visit current slot cumulant clock) (state, history)

/-- Advance each slot exactly once, then install at most one new sample.
The scratch fold carries no variable-length record of the experienced stream. -/
def DemonStats.observe {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) historyBins)
    (clock : UInt64) (cumulant : Binary32) (prediction : Prediction discount) :
    DemonStats discount × Vector (SumCount (.squaredError .g99)) historyBins :=
  let (state, history) := state.advanceSlots history clock cumulant (List.finRange pendingSamples)
  (state.start clock prediction, history)

/-- Prediction accounting has exactly the current immutable horizon layout. -/
inductive DemonRecords : List Discount → Type where
  /-- Empty channel tail. -/
  | nil : DemonRecords []
  /-- One channel and the remaining ordered channels. -/
  | cons {discount : Discount} {rest : List Discount}
      (head : DemonStats discount) (tail : DemonRecords rest) : DemonRecords (discount :: rest)

/-- Build every zero prediction record in canonical channel order. -/
def DemonRecords.initial : (discounts : List Discount) → DemonRecords discounts
  | [] => .nil
  | discount :: rest => .cons (DemonStats.initial discount) (DemonRecords.initial rest)

/-- End a process's available continuation without manufacturing terminal cumulants. -/
def DemonRecords.censor {discounts : List Discount} : DemonRecords discounts → DemonRecords discounts
  | .nil => .nil
  | .cons head tail => .cons head.censor tail.censor

/-- A discontinuous or exhausted core clock invalidates the entire comparable population. -/
def DemonRecords.fail {discounts : List Discount} (fault : Agreement.Fault) :
    DemonRecords discounts → DemonRecords discounts
  | .nil => .nil
  | .cons head tail => .cons
      { head with agreement := { head.agreement with fault := head.agreement.fault.or (some fault) } }
      (tail.fail fault)

/-- Settle every channel in canonical order on the same shared history. -/
def DemonRecords.observe {discounts : List Discount} (state : DemonRecords discounts)
    (history : Vector (SumCount (.squaredError .g99)) historyBins) (clock : UInt64)
    (cumulants : Cumulants discounts) (predictions : PredictionCache discounts) :
    DemonRecords discounts × Vector (SumCount (.squaredError .g99)) historyBins :=
  match state, cumulants, predictions with
  | .nil, .nil, .nil => (.nil, history)
  | .cons head tail, .cons _ cumulant cumulants, .cons prediction predictions => Id.run do
    let (head, history) := head.observe history clock cumulant prediction
    let (tail, history) := tail.observe history clock cumulants predictions
    return (.cons head tail, history)

/-- Every question contributes one entry in its compiler-owned horizon layout. -/
def DemonRecords.agreementRatios {discounts : List Discount} :
    DemonRecords discounts → List (Option Agreement.Ratio)
  | .nil => []
  | .cons head tail => head.agreement.ratio :: tail.agreementRatios

/-- Equal-question agreement is absent until all channels supply evidence. -/
def DemonRecords.agreementRatio {discounts : List Discount} (state : DemonRecords discounts) :
    Option Agreement.Ratio :=
  (Agreement.aggregateAll state.agreementRatios).bind Agreement.Aggregate.ratio

/-- The fold cannot omit a question or insert an extra channel. -/
theorem DemonRecords.agreementRatios_length {discounts : List Discount} (state : DemonRecords discounts) :
    state.agreementRatios.length = discounts.length := by
  induction state with
  | nil => rfl
  | cons head tail ih => simpa only [agreementRatios, List.length_cons] using congrArg (· + 1) ih

/-- One bounded cumulative process-session history point. -/
structure AgreementPoint where
  /-- Agent lifetime clock when the cumulative value was observed. -/
  clock : UInt64
  /-- Exact ratio of the cumulative equal-question mean squared discrepancy. -/
  ratio : Agreement.Ratio

/-- Complete fixed-memory lifetime state, outside the learned decision path. -/
structure Stats (discounts : List Discount) where
  /-- Lifetime task reward. -/
  reward : SumCount .reward
  /-- Task-family reward totals. -/
  rewardByFamily : Vector (SumCount .reward) 4
  /-- Logarithmic lifetime reward history. -/
  rewardHistory : Vector (SumCount .reward) historyBins
  /-- Horizon-indexed prediction records and pending returns. -/
  demons : DemonRecords discounts
  /-- Shared settled-error history. -/
  errorHistory : Vector (SumCount (.squaredError .g99)) historyBins
  /-- One episode record per option. -/
  options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount
  /-- Task-family attempt totals. -/
  goals : Vector GoalTotals 4
  /-- Task-family by cycle-window totals. -/
  goalCycles : Vector (Vector GoalTotals cycleBins) 4
  /-- First evaluated clock in this core process, independently of checkpoint age. -/
  agreementStarted : Option UInt64
  /-- Cumulative snapshots in the existing bounded logarithmic clock buckets. -/
  agreementHistory : Vector (Option AgreementPoint) historyBins
  /-- Last consumed core clock, distinct from any telemetry sequence or browser cursor. -/
  agreementLastClock : Option UInt64
  /-- A completed process cannot continue its evaluator without a fresh session. -/
  agreementStopped : Bool

/-- Complete zero lifetime state for every admitted prediction layout. -/
def Stats.initial (discounts : List Discount) : Stats discounts :=
  ⟨SumCount.initial _, Vector.replicate _ (SumCount.initial _),
    Vector.replicate _ (SumCount.initial _), DemonRecords.initial discounts,
    Vector.replicate _ (SumCount.initial _), Vector.replicate _ OptionEpisodes.initial,
    Vector.replicate _ GoalTotals.initial, Vector.replicate _ (Vector.replicate _ GoalTotals.initial),
    some 0, Vector.replicate _ none, some 0, false⟩

/-- Record one delivered environment reward at the agent's current clock. -/
def Stats.recordEnvironment {discounts : List Discount} (state : Stats discounts)
    (clock : UInt64) (family : Fin 4) (value : Binary32) : Stats discounts := Id.run do
  let reward := state.reward.observe value
  let familyReward := (state.rewardByFamily.get family).observe value
  let bucket := historyBin clock
  let historyReward := (state.rewardHistory.get bucket).observe value
  return { state with
    reward
    rewardByFamily := state.rewardByFamily.set family.val familyReward family.isLt
    rewardHistory := state.rewardHistory.set bucket.val historyReward bucket.isLt }

/-- Prediction accounting consumes current outputs, never recomputed future values. -/
def Stats.recordDemons {discounts : List Discount} (state : Stats discounts) (clock : UInt64)
    (cumulants : Cumulants discounts) (predictions : PredictionCache discounts) : Stats discounts := Id.run do
  if state.agreementStopped then return state
  let demons := if clock.toNat = Agreement.countLimit then state.demons.censor.fail .saturated else
    match state.agreementLastClock with
    | none => state.demons
    | some last => if clock.toNat = last.toNat + 1 then state.demons else state.demons.censor.fail .invalid
  let (demons, history) := demons.observe state.errorHistory clock cumulants predictions
  let agreementHistory := if clock.toNat % settleStride = 0 then
    let point := demons.agreementRatio.map (fun ratio => AgreementPoint.mk clock ratio)
    state.agreementHistory.set (historyBin clock).val point (historyBin clock).isLt
    else state.agreementHistory
  return { state with
    demons := demons
    errorHistory := history
    agreementStarted := state.agreementStarted.or (some clock)
    agreementLastClock := some clock
    agreementHistory := agreementHistory }

/-- Prediction observation, including refusal after Stop, cannot change option episodes. -/
theorem Stats.recordDemons_options {discounts : List Discount} (state : Stats discounts)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts) :
    (state.recordDemons clock cumulants predictions).options = state.options := by
  cases stopped : state.agreementStopped <;> simp [recordDemons, stopped]

/-- A stopped process retains observed totals and releases every unavailable future. -/
def Stats.censor {discounts : List Discount} (state : Stats discounts) : Stats discounts :=
  { state with demons := state.demons.censor, agreementStopped := true }

/-- Task completion changes exactly its family and cycle-window aggregates. -/
def Stats.recordAttempt {discounts : List Discount} (state : Stats discounts)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) : Stats discounts :=
  let bucket := cycleBin cycle
  let familyCycles := state.goalCycles.get family
  { state with
    goals := state.goals.set family.val ((state.goals.get family).observe steps achieved) family.isLt
    goalCycles := state.goalCycles.set family.val
      (familyCycles.set bucket.val ((familyCycles.get bucket).observe steps achieved) bucket.isLt) family.isLt }

/-- Durable prediction records contain no pending sample. -/
inductive DurableDemons : List Discount → Type where
  /-- Empty channel tail. -/
  | nil : DurableDemons []
  /-- Current channel's durable values and remaining ordered channels. -/
  | cons {discount : Discount} {rest : List Discount}
      (head : DemonDurable discount) (tail : DurableDemons rest) : DurableDemons (discount :: rest)

/-- Read the durable projection in the same horizon order. -/
def DemonRecords.durable {discounts : List Discount} : DemonRecords discounts → DurableDemons discounts
  | .nil => .nil
  | .cons head tail => .cons head.durable tail.durable

/-- Restore the durable channel values with every pending bank empty. -/
def DurableDemons.restore {discounts : List Discount} : DurableDemons discounts → DemonRecords discounts
  | .nil => .nil
  | .cons head tail => .cons (DemonStats.restore head) tail.restore

/-- Censoring cannot alter any checkpoint-persistent prediction statistic. -/
theorem DemonRecords.censor_durable {discounts : List Discount} (state : DemonRecords discounts) :
    state.censor.durable = state.durable := by
  induction state with
  | nil => rfl
  | cons head tail ih => simp [DemonRecords.censor, DemonRecords.durable, DemonStats.censor, ih]

/-- Cold restoration preserves every durable prediction field. -/
theorem DurableDemons.restore_durable {discounts : List Discount} (state : DurableDemons discounts) :
    state.restore.durable = state := by
  induction state with
  | nil => rfl
  | cons head tail ih => simp [restore, DemonRecords.durable, DemonStats.restore, ih]

/-- Complete durable lifetime projection; fixed shapes match the observation owner. -/
structure Durable (discounts : List Discount) where
  /-- Lifetime task reward. -/
  reward : SumCount .reward
  /-- Task-family reward totals. -/
  rewardByFamily : Vector (SumCount .reward) 4
  /-- Logarithmic lifetime reward history. -/
  rewardHistory : Vector (SumCount .reward) historyBins
  /-- Settled prediction records, without pending futures. -/
  demons : DurableDemons discounts
  /-- Shared settled-error history. -/
  errorHistory : Vector (SumCount (.squaredError .g99)) historyBins
  /-- One episode record per option. -/
  options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount
  /-- Task-family attempt totals. -/
  goals : Vector GoalTotals 4
  /-- Task-family by cycle-window totals. -/
  goalCycles : Vector (Vector GoalTotals cycleBins) 4

/-- Read only the durable fields; this operation never advances accounting. -/
def Stats.durable {discounts : List Discount} (state : Stats discounts) : Durable discounts :=
  ⟨state.reward, state.rewardByFamily, state.rewardHistory, state.demons.durable,
    state.errorHistory, state.options, state.goals, state.goalCycles⟩

/-- Clear every process-local pending sample and retain the complete durable record. -/
def Durable.restore {discounts : List Discount} (state : Durable discounts) : Stats discounts :=
  ⟨state.reward, state.rewardByFamily, state.rewardHistory, state.demons.restore,
    state.errorHistory, state.options, state.goals, state.goalCycles,
    none, Vector.replicate _ none, none, false⟩

/-- Durable restoration preserves the complete projection, for every admitted record. -/
theorem Durable.restore_durable {discounts : List Discount} (state : Durable discounts) :
    state.restore.durable = state := by
  cases state
  simp [Durable.restore, Stats.durable, DurableDemons.restore_durable]

/-- Process finalization changes no field in the durable lifetime projection. -/
theorem Stats.censor_durable {discounts : List Discount} (state : Stats discounts) :
    state.censor.durable = state.durable := by
  simp [Stats.censor, Stats.durable, DemonRecords.censor_durable]

/-- Finalization permanently refuses further observations in this process state. -/
theorem Stats.censor_no_observation {discounts : List Discount} (state : Stats discounts)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts) :
    state.censor.recordDemons clock cumulants predictions = state.censor := by
  simp [Stats.recordDemons, Stats.censor]

end Acorn.Lifetime
