import Acorn.State
import Acorn.FeatureConstants

namespace Acorn.Agreement

def unitExponent : Nat := 149

def magnitudeUnits (value : Binary32) : Nat :=
  let exponent := value.magnitude / 2^23
  let fraction := value.magnitude % 2^23
  if exponent = 0 then fraction else (2^23 + fraction) * 2^(exponent - 1)

def units (value : Binary32) : Int :=
  if value.Negative then -(magnitudeUnits value : Int) else magnitudeUnits value

def squaredUnits (forecast outcome : Binary32) : Nat :=
  (units forecast - units outcome).natAbs ^ 2

def admitSquared (envelope : Nat) (forecast outcome : Binary32) : Option (Fin (envelope^2 + 1)) :=
  if forecast.Finite ∧ outcome.Finite then
    if h : squaredUnits forecast outcome < envelope^2 + 1 then
      some ⟨squaredUnits forecast outcome, h⟩
    else none
  else none

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

def countLimit : Nat := 2^64 - 1

structure Total (envelope : Nat) where
  count : Fin (countLimit + 1)
  sum : Nat
  bounded : sum ≤ count.val * envelope^2

def Total.empty (envelope : Nat) : Total envelope :=
  ⟨⟨0, by decide⟩, 0, Nat.zero_le _⟩

def Total.observe {envelope : Nat} (total : Total envelope)
    (sample : Fin (envelope^2 + 1)) : Option (Total envelope) :=
  if room : total.count.val + 1 < countLimit + 1 then
    some ⟨⟨total.count.val + 1, room⟩, total.sum + sample.val, by
      have sampleBound : sample.val ≤ envelope^2 := by have := sample.isLt; omega
      have added := Nat.add_le_add total.bounded sampleBound
      simpa [Nat.add_mul] using added⟩
  else none

theorem Total.observe_exact {envelope : Nat} (total next : Total envelope)
    (sample : Fin (envelope^2 + 1)) (written : total.observe sample = some next) :
    next.count.val = total.count.val + 1 ∧ next.sum = total.sum + sample.val := by
  unfold observe at written
  split at written
  · cases written
    exact ⟨rfl, rfl⟩
  · contradiction

theorem Total.empty_sum {envelope : Nat} (total : Total envelope)
    (empty : total.count.val = 0) : total.sum = 0 := by
  have := total.bounded
  simp only [empty, Nat.zero_mul] at this
  omega

theorem Total.storage_bound {envelope : Nat} (total : Total envelope) :
    total.sum ≤ countLimit * envelope^2 :=
  Nat.le_trans total.bounded (Nat.mul_le_mul_right _ (by have := total.count.isLt; omega))

structure Ratio where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator
  bounded : numerator ≤ denominator

def Ratio.admit (numerator denominator : Nat) : Option Ratio :=
  if positive : 0 < denominator then
    if bounded : numerator ≤ denominator then some ⟨numerator, denominator, positive, bounded⟩
    else none
  else none

def Ratio.maximum (left right : Ratio) : Ratio :=
  if left.numerator * right.denominator ≤ right.numerator * left.denominator then right else left

def Total.ratio {envelope : Nat} (total : Total envelope) : Option Ratio :=
  if positive : 0 < total.count.val * envelope^2 then
    some ⟨total.sum, total.count.val * envelope^2, positive, total.bounded⟩
  else none

def displayScale : Nat := 1000000

def Ratio.errorUnits (ratio : Ratio) : Nat :=
  (ratio.numerator * displayScale^2 / ratio.denominator).sqrt

def Ratio.agreementUnits (ratio : Ratio) : Nat := displayScale - ratio.errorUnits

def Ratio.upperUnits (ratio : Ratio) : Nat :=
  (ratio.numerator * displayScale + ratio.denominator - 1) / ratio.denominator

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

structure Aggregate where
  questions : Nat
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator
  bounded : numerator ≤ questions * denominator

def Aggregate.empty : Aggregate := ⟨0, 0, 1, by decide, by decide⟩

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

def Aggregate.ratio (aggregate : Aggregate) : Option Ratio :=
  if positive : 0 < aggregate.questions * aggregate.denominator then
    some ⟨aggregate.numerator, aggregate.questions * aggregate.denominator,
      positive, aggregate.bounded⟩
  else none

def aggregateAll : List (Option Ratio) → Option Aggregate
  | [] => some .empty
  | none :: _ => none
  | some head :: tail => (aggregateAll tail).map (·.add head)

theorem aggregateAll_missing (tail : List (Option Ratio)) :
    aggregateAll (none :: tail) = none := rfl

def errorEnvelope (discount : Discount) : Binary32 :=
  (Binary32.ofUInt64 2).mul discount.horizon

def envelopeUnits (discount : Discount) : Nat := magnitudeUnits (errorEnvelope discount)

def returnRoundingUnits (steps : Nat) : Nat :=
  steps * 2^(unitExponent - 14) + steps * (steps + 1) * 2^(unitExponent - 24)

def powerRoundingUnits (steps : Nat) : Nat := steps * 2^(unitExponent - 23)

structure Precision where
  tail : Ratio
  rounding : Ratio

def Precision.merge (left right : Precision) : Precision :=
  ⟨left.tail.maximum right.tail, left.rounding.maximum right.rounding⟩

def precision (discount : Discount) (steps : Nat) (power : Binary32) : Option Precision := do
  if !power.Finite || steps > FeatureConstants.maxSettlement then none else
    let envelope := envelopeUnits discount
    let tail ← Ratio.admit
      ((magnitudeUnits power + powerRoundingUnits steps) * 2^unitExponent)
      ((2^unitExponent - magnitudeUnits discount.gamma) * envelope)
    let rounding ← Ratio.admit (returnRoundingUnits steps) envelope
    return ⟨tail, rounding⟩

inductive Fault where
  | invalid
  | saturated
  deriving DecidableEq

structure ClockRange where
  first : UInt64
  last : UInt64
  ordered : first.toNat ≤ last.toNat

def ClockRange.include (range : Option ClockRange) (clock : UInt64) : ClockRange :=
  match range with
  | none => ⟨clock, clock, Nat.le_refl _⟩
  | some range =>
    if before : clock.toNat < range.first.toNat then
      ⟨clock, range.last, Nat.le_trans (Nat.le_of_lt before) range.ordered⟩
    else if after : range.last.toNat < clock.toNat then
      ⟨range.first, clock, Nat.le_trans range.ordered (Nat.le_of_lt after)⟩
    else range

structure Channel (discount : Discount) where
  total : Total (envelopeUnits discount)
  fault : Option Fault
  starts : Option ClockRange
  settlements : Option ClockRange
  censored : Fin (countLimit + 1)
  precision : Option Precision

def Channel.empty (discount : Discount) : Channel discount :=
  ⟨.empty _, none, none, none, ⟨0, by decide⟩, none⟩

def Channel.censor {discount : Discount} (channel : Channel discount) (count : Nat) : Channel discount :=
  if room : channel.censored.val + count < countLimit + 1 then
    { channel with censored := ⟨channel.censored.val + count, room⟩ }
  else { channel with fault := channel.fault.or (some .saturated) }

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

def Channel.ratio {discount : Discount} (channel : Channel discount) : Option Ratio :=
  if channel.fault.isSome then none else channel.total.ratio

theorem Channel.fault_no_score {discount : Discount} (channel : Channel discount)
    (fault : Fault) (failed : channel.fault = some fault) : channel.ratio = none := by
  simp [Channel.ratio, failed]

end Acorn.Agreement
