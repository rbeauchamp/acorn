/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.State
import Acorn.FeatureConstants

/-!
# Exact process-session discrepancy accounting

The descriptive agreement convention is Acorn's definition, not a measure of
world knowledge. Binary32 operands are decoded in units of their minimum
subnormal, so subtraction, squaring and accumulation need no floating rounding.
The count and total carry finite bounds; exhaustion is an explicit non-score.
These sufficient statistics contain no observations that could be replayed.
-/
namespace Acorn.Agreement

/-- Binary32's minimum positive subnormal fixes the common integer unit. -/
def unitExponent : Nat := 149

/-- Exact unsigned significand in minimum-subnormal units. Exceptional words
must be refused by the receiving admission boundary. -/
def magnitudeUnits (value : Binary32) : Nat :=
  let exponent := value.magnitude / 2^23
  let fraction := value.magnitude % 2^23
  if exponent = 0 then fraction else (2^23 + fraction) * 2^(exponent - 1)

/-- Signed dyadic coordinate; both zero encodings have coordinate zero. -/
def units (value : Binary32) : Int :=
  if value.negative then -(magnitudeUnits value : Int) else magnitudeUnits value

/-- Exact squared discrepancy of the two encoded operands. -/
def squaredUnits (forecast outcome : Binary32) : Nat :=
  (units forecast - units outcome).natAbs ^ 2

/-- A receiving envelope admits a sample unchanged or refuses it. -/
def admitSquared (envelope : Nat) (forecast outcome : Binary32) : Option (Fin (envelope^2 + 1)) :=
  if forecast.Finite ∧ outcome.Finite then
    if h : squaredUnits forecast outcome < envelope^2 + 1 then
      some ⟨squaredUnits forecast outcome, h⟩
    else none
  else none

/-- Successful admission preserves every bit of the exact squared discrepancy. -/
theorem admitSquared_exact (envelope : Nat) (forecast outcome : Binary32)
    (sample : Fin (envelope^2 + 1))
    (admitted : admitSquared envelope forecast outcome = some sample) :
    sample.val = squaredUnits forecast outcome := by
  unfold admitSquared at admitted
  split at admitted
  · split at admitted
    · cases admitted
      rfl
    · contradiction
  · contradiction

/-- Finite count limit, shared with the core's unsigned lifetime clock. -/
def countLimit : Nat := 2^64 - 1

/-- Exact finite sufficient statistic. Its legal population is part of its type. -/
structure Total (envelope : Nat) where
  /-- Number of settled forecasts. -/
  count : Fin (countLimit + 1)
  /-- Sum of squared dyadic discrepancies. -/
  sum : Nat
  /-- Every constructor and write retains the population-derived bound. -/
  bounded : sum ≤ count.val * envelope^2

/-- A new process has no evidence, including when learned state is restored. -/
def Total.empty (envelope : Nat) : Total envelope :=
  ⟨⟨0, by decide⟩, 0, Nat.zero_le _⟩

/-- Exact addition while the count has room; exhaustion does not alter the mean. -/
def Total.observe {envelope : Nat} (total : Total envelope)
    (sample : Fin (envelope^2 + 1)) : Option (Total envelope) :=
  if room : total.count.val + 1 < countLimit + 1 then
    some ⟨⟨total.count.val + 1, room⟩, total.sum + sample.val, by
      have sampleBound : sample.val ≤ envelope^2 := by have := sample.isLt; omega
      have added := Nat.add_le_add total.bounded sampleBound
      simpa [Nat.add_mul] using added⟩
  else none

/-- An admitted write increments the population and adds the exact discrepancy. -/
theorem Total.observe_exact {envelope : Nat} (total next : Total envelope)
    (sample : Fin (envelope^2 + 1)) (written : total.observe sample = some next) :
    next.count.val = total.count.val + 1 ∧ next.sum = total.sum + sample.val := by
  unfold observe at written
  split at written
  · cases written
    exact ⟨rfl, rfl⟩
  · contradiction

/-- No empty population can carry a nonzero total. -/
theorem Total.empty_sum {envelope : Nat} (total : Total envelope)
    (empty : total.count.val = 0) : total.sum = 0 := by
  have := total.bounded
  simp only [empty, Nat.zero_mul] at this
  omega

/-- Storage is bounded independently of the process lifetime. -/
theorem Total.storage_bound {envelope : Nat} (total : Total envelope) :
    total.sum ≤ countLimit * envelope^2 :=
  Nat.le_trans total.bounded (Nat.mul_le_mul_right _ (by have := total.count.isLt; omega))

/-- An exact normalized squared-error ratio, with a strictly positive scale. -/
structure Ratio where
  /-- Exact numerator. -/
  numerator : Nat
  /-- Exact denominator. -/
  denominator : Nat
  /-- Missing evidence cannot be represented by a zero denominator. -/
  positive : 0 < denominator
  /-- Admission establishes the normalized unit interval. -/
  bounded : numerator ≤ denominator

/-- Admit an exact unit-interval ratio without changing either integer. -/
def Ratio.admit (numerator denominator : Nat) : Option Ratio :=
  if positive : 0 < denominator then
    if bounded : numerator ≤ denominator then some ⟨numerator, denominator, positive, bounded⟩
    else none
  else none

/-- Exact larger ratio, used for deterministic population-wide error allowances. -/
def Ratio.maximum (left right : Ratio) : Ratio :=
  if left.numerator * right.denominator ≤ right.numerator * left.denominator then right else left

/-- Empty evidence is absent rather than a perfect score. -/
def Total.ratio {envelope : Nat} (total : Total envelope) : Option Ratio :=
  if positive : 0 < total.count.val * envelope^2 then
    some ⟨total.sum, total.count.val * envelope^2, positive, total.bounded⟩
  else none

/-- Integer display precision only; it is neither a window nor smoothing. -/
def displayScale : Nat := 1000000

/-- Downward-rounded normalized RMSE in millionths, using exact integer division
and square root. The mathematical correspondence is proved separately. -/
def Ratio.errorUnits (ratio : Ratio) : Nat :=
  (ratio.numerator * displayScale^2 / ratio.denominator).sqrt

/-- Complement in millionths; 100 points corresponds to `displayScale`. -/
def Ratio.agreementUnits (ratio : Ratio) : Nat := displayScale - ratio.errorUnits

/-- Upward-rounded deterministic allowance, separate from the point estimate. -/
def Ratio.upperUnits (ratio : Ratio) : Nat :=
  (ratio.numerator * displayScale + ratio.denominator - 1) / ratio.denominator

/-- Point-scale text preserves exact endpoint meanings despite finite display precision. -/
def Ratio.agreementText (ratio : Ratio) : String :=
  if ratio.numerator = 0 then "100.00"
  else if ratio.numerator = ratio.denominator then "0.00"
  else
    let units := ratio.agreementUnits
    if ratio.numerator * 100000000 < ratio.denominator then ">99.99"
    else if ratio.denominator * 99980001 < ratio.numerator * 100000000 then "<0.01"
    else
      let hundredths := (units / 100) % 100
      toString (units / 10000) ++ "." ++
        (if hundredths < 10 then "0" else "") ++ toString hundredths

/-- Nonnegative numerator accumulation for an equal-question mean. -/
structure Aggregate where
  /-- Questions included exactly once. -/
  questions : Nat
  /-- Sum numerator under the shared denominator. -/
  numerator : Nat
  /-- Product of included positive denominators. -/
  denominator : Nat
  /-- The common denominator remains positive. -/
  positive : 0 < denominator
  /-- Each question contributes at most one. -/
  bounded : numerator ≤ questions * denominator

/-- No question has been included. -/
def Aggregate.empty : Aggregate := ⟨0, 0, 1, by decide, by decide⟩

/-- Add a whole question, irrespective of its sample count. -/
def Aggregate.add (aggregate : Aggregate) (ratio : Ratio) : Aggregate :=
  ⟨aggregate.questions + 1,
    aggregate.numerator * ratio.denominator + ratio.numerator * aggregate.denominator,
    aggregate.denominator * ratio.denominator,
    Nat.mul_pos aggregate.positive ratio.positive, by
      have left := Nat.mul_le_mul_right ratio.denominator aggregate.bounded
      have right := Nat.mul_le_mul_right aggregate.denominator ratio.bounded
      have both := Nat.add_le_add left right
      change _ ≤ (aggregate.questions + 1) * (aggregate.denominator * ratio.denominator)
      rw [Nat.add_mul, Nat.one_mul]
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using both⟩

/-- Equal-question RMS uses the mean squared error, not mean agreement. -/
def Aggregate.ratio (aggregate : Aggregate) : Option Ratio :=
  if positive : 0 < aggregate.questions * aggregate.denominator then
    some ⟨aggregate.numerator, aggregate.questions * aggregate.denominator,
      positive, aggregate.bounded⟩
  else none

/-- Missing channels propagate through the whole aggregate. -/
def aggregateAll : List (Option Ratio) → Option Aggregate
  | [] => some .empty
  | none :: _ => none
  | some head :: tail => (aggregateAll tail).map (·.add head)

/-- A missing channel never becomes a zero-error contribution. -/
theorem aggregateAll_missing (tail : List (Option Ratio)) :
    aggregateAll (none :: tail) = none := rfl

/-- Closed forecast/return discrepancy scale, shared with lifetime diagnostics. -/
def errorEnvelope (discount : Discount) : Binary32 :=
  (Binary32.ofUInt64 2).mul discount.horizon

/-- Exact scale in the same units as the discrepancies. -/
def envelopeUnits (discount : Discount) : Nat := magnitudeUnits (errorEnvelope discount)

/-- The analytic binary32 return-rounding allowance in exact least-subnormal units. -/
def returnRoundingUnits (steps : Nat) : Nat :=
  steps * 2^(unitExponent - 14) + steps * (steps + 1) * 2^(unitExponent - 24)

/-- Accumulated power-rounding allowance in the same exact units. -/
def powerRoundingUnits (steps : Nat) : Nat := steps * 2^(unitExponent - 23)

/-- Independent deterministic truncation and arithmetic allowances, normalized by the envelope. -/
structure Precision where
  /-- Unseen discounted tail; not a confidence interval. -/
  tail : Ratio
  /-- Executed finite-return rounding; no projection is applied. -/
  rounding : Ratio

/-- Retain bounds covering every settled population member. -/
def Precision.merge (left right : Precision) : Precision :=
  ⟨left.tail.maximum right.tail, left.rounding.maximum right.rounding⟩

/-- Derive truncation from the shared pending power with its rounding allowance.
No second power loop, trajectory traversal, or floating conversion is needed. -/
def precision (discount : Discount) (steps : Nat) (power : Binary32) : Option Precision := do
  if !power.Finite || steps > FeatureConstants.maxSettlement then none else
    let envelope := envelopeUnits discount
    let tail ← Ratio.admit
      ((magnitudeUnits power + powerRoundingUnits steps) * 2^unitExponent)
      ((2^unitExponent - magnitudeUnits discount.gamma) * envelope)
    let rounding ← Ratio.admit (returnRoundingUnits steps) envelope
    return ⟨tail, rounding⟩

/-- Arithmetic failure is sticky for this process's comparable population. -/
inductive Fault where
  /-- A finite-word or envelope admission failed. -/
  | invalid
  /-- Finite accounting capacity was exhausted. -/
  | saturated
  deriving DecidableEq

/-- Actual endpoint range; no count implies consecutive or independent samples. -/
structure ClockRange where
  /-- Earliest included clock. -/
  first : UInt64
  /-- Latest included clock. -/
  last : UInt64
  /-- Endpoints cannot be reversed. -/
  ordered : first.toNat ≤ last.toNat

/-- Include one clock without assuming telemetry delivery order. -/
def ClockRange.include (range : Option ClockRange) (clock : UInt64) : ClockRange :=
  match range with
  | none => ⟨clock, clock, Nat.le_refl _⟩
  | some range =>
    if before : clock.toNat < range.first.toNat then
      ⟨clock, range.last, Nat.le_trans (Nat.le_of_lt before) range.ordered⟩
    else if after : range.last.toNat < clock.toNat then
      ⟨range.first, clock, Nat.le_trans range.ordered (Nat.le_of_lt after)⟩
    else range

/-- Process-local sufficient statistics; no durable constructor imports past totals. -/
structure Channel (discount : Discount) where
  /-- Exact discrepancy sum and finite count. -/
  total : Total (envelopeUnits discount)
  /-- Unavailable arithmetic remains visible. -/
  fault : Option Fault
  /-- Actual start clocks of settled forecasts. -/
  starts : Option ClockRange
  /-- Actual settlement clocks. -/
  settlements : Option ClockRange
  /-- Futures explicitly discarded without pretending they terminated. -/
  censored : Fin (countLimit + 1)
  /-- Bounds covering the current process's settled population. -/
  precision : Option Precision

/-- Empty process-session evaluator, independent of restored learner state. -/
def Channel.empty (discount : Discount) : Channel discount :=
  ⟨.empty _, none, none, none, ⟨0, by decide⟩, none⟩

/-- Count unavailable futures exactly, or enter explicit capacity exhaustion. -/
def Channel.censor {discount : Discount} (channel : Channel discount) (count : Nat) : Channel discount :=
  if room : channel.censored.val + count < countLimit + 1 then
    { channel with censored := ⟨channel.censored.val + count, room⟩ }
  else { channel with fault := channel.fault.or (some .saturated) }

/-- Settle one shared pending record, refusing illegal operands or exhausted counts. -/
def Channel.settle {discount : Discount} (channel : Channel discount)
    (forecast outcome power : Binary32) (steps : Nat) (started settled : UInt64) : Channel discount :=
  if channel.fault.isSome then channel else
  if started.toNat ≥ settled.toNat then { channel with fault := some .invalid } else
  match admitSquared (envelopeUnits discount) forecast outcome, Agreement.precision discount steps power with
  | none, _ | _, none => { channel with fault := some .invalid }
  | some sample, some precision => match channel.total.observe sample with
    | none => { channel with fault := some .saturated }
    | some total =>
      { channel with
        total := total
        precision := some (channel.precision.map (·.merge precision) |>.getD precision)
        starts := some (ClockRange.include channel.starts started)
        settlements := some (ClockRange.include channel.settlements settled) }

/-- Invalid or saturated arithmetic never becomes a numeric score. -/
def Channel.ratio {discount : Discount} (channel : Channel discount) : Option Ratio :=
  if channel.fault.isSome then none else channel.total.ratio

/-- No score can escape a recorded arithmetic failure. -/
theorem Channel.fault_no_score {discount : Discount} (channel : Channel discount)
    (fault : Fault) (failed : channel.fault = some fault) : channel.ratio = none := by
  simp [Channel.ratio, failed]

end Acorn.Agreement
