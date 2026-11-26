import Acorn.Demon
import Acorn.Agreement

set_option maxRecDepth 4096

namespace Acorn.Lifetime
open Features
open Acorn.FeatureConstants

def addCount (left right : UInt64) : UInt64 :=
  (min (left.toNat + right.toNat) (2^64 - 1)).toUInt64

theorem addCount_exact (left right : UInt64) :
    (addCount left right).toNat = min (left.toNat + right.toNat) (2^64 - 1) := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right (left.toNat + right.toNat) (2^64 - 1)
  omega

def historyBin (step : UInt64) : Fin historyBins :=
  ⟨min step.toNat.log2 (historyBins - 1), by have := Nat.min_le_right step.toNat.log2 63; change min step.toNat.log2 63 < 64; omega⟩

def cycleBin (cycle : UInt64) : Fin cycleBins :=
  if h : cycle.toNat < exactCycles then ⟨cycle.toNat, by simp only [exactCycles, cycleBins] at *; omega⟩
  else ⟨min (exactCycles + (cycle.toNat - exactCycles + 1).log2) (cycleBins - 1), by
    have := Nat.min_le_right (exactCycles + (cycle.toNat - exactCycles + 1).log2) (cycleBins - 1); simp only [cycleBins] at *; omega⟩

inductive Quantity where
  | reward
  | squaredError (discount : Discount)
  deriving DecidableEq

def errorBound (discount : Discount) : Binary32 :=
  Agreement.errorEnvelope discount

def Quantity.bound : Quantity → Binary32
  | .reward => .one
  | .squaredError discount => (errorBound discount).mul (errorBound discount)

def Quantity.range (quantity : Quantity) : Interval32 :=
  ⟨.zero, quantity.bound, by decide,
    by cases quantity with
       | reward => decide
       | squaredError discount => cases discount <;> decide,
    by cases quantity with
       | reward => decide
       | squaredError discount => cases discount <;> decide⟩

def errorRange (discount : Discount) : Symmetric32 where
  range := ⟨(errorBound discount).negate, errorBound discount,
    by cases discount <;> decide, by cases discount <;> decide,
    by cases discount <;> decide⟩
  symmetric := rfl
  zeroLegal := by cases discount <;> decide

def maximumSum (quantity : Quantity) (count : UInt64) : Binary64 :=
  (Binary64.ofUInt64 count).mul (Conversion.widen quantity.bound)

def LegalSum (quantity : Quantity) (count : UInt64) (sum : Binary64) : Prop :=
  sum.Finite ∧ 0 ≤ sum.key ∧ sum.key ≤ (maximumSum quantity count).key ∧
    (count = 0 → sum.key = 0)

instance (quantity : Quantity) (count : UInt64) (sum : Binary64) :
    Decidable (LegalSum quantity count sum) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def sumUpdate (quantity : Quantity) (count : UInt64) (sum : Binary64) (value : Binary32) :
    UInt64 × Binary64 :=
  let count := addCount count 1
  let value := quantity.range.saturate value
  let sum := sum.add (Conversion.widen value)
  let bound := maximumSum quantity count
  (count, if bound.Less sum then bound else sum)

inductive SumAdmitted (quantity : Quantity) : UInt64 → Binary64 → Prop where
  | durable (count : UInt64) (sum : Binary64) (legal : LegalSum quantity count sum) :
      SumAdmitted quantity count sum
  | observation (count : UInt64) (sum : Binary64) (value : Binary32) (written : Quantity)
      (bound : written.bound.key ≤ quantity.bound.key) (prior : SumAdmitted quantity count sum) :
      SumAdmitted quantity (sumUpdate written count sum value).1 (sumUpdate written count sum value).2

structure SumCount (quantity : Quantity) where
  count : UInt64
  sum : Binary64
  admitted : SumAdmitted quantity count sum

def SumCount.initial (quantity : Quantity) : SumCount quantity :=
  ⟨0, ⟨0⟩, .durable 0 ⟨0⟩ (by cases quantity with
    | reward => decide
    | squaredError discount => cases discount <;> decide)⟩

def SumCount.admit (quantity : Quantity) (count : UInt64) (sum : Binary64) :
    Option (SumCount quantity) :=
  if h : LegalSum quantity count sum then some ⟨count, sum, .durable count sum h⟩ else none

def SumCount.observeAs {quantity : Quantity} (state : SumCount quantity) (written : Quantity)
    (bound : written.bound.key ≤ quantity.bound.key) (value : Binary32) : SumCount quantity :=
  let next := sumUpdate written state.count state.sum value
  ⟨next.1, next.2, .observation state.count state.sum value written bound state.admitted⟩

def SumCount.observe {quantity : Quantity} (state : SumCount quantity) (value : Binary32) :
    SumCount quantity := state.observeAs quantity (Int.le_refl _) value

theorem SumCount.observe_exact {quantity : Quantity} (state : SumCount quantity) (value : Binary32) :
    ((state.observe value).count, (state.observe value).sum) =
      sumUpdate quantity state.count state.sum value := rfl

structure GoalTotals where
  attempts : UInt64
  successes : UInt64
  steps : UInt64
  successesBound : successes.toNat ≤ attempts.toNat
  emptySteps : attempts = 0 → steps = 0

def GoalTotals.initial : GoalTotals := ⟨0, 0, 0, by decide, fun _ => rfl⟩

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

structure OptionEpisodes where
  started : UInt64
  duration : UInt64
  reasons : Vector UInt64 3

def OptionEpisodes.completed (state : OptionEpisodes) : UInt64 :=
  state.reasons.toList.foldl addCount 0

def OptionEpisodes.initial : OptionEpisodes := ⟨0, 0, Vector.replicate _ 0⟩

def OptionEpisodes.start (state : OptionEpisodes) : OptionEpisodes :=
  { state with started := addCount state.started 1 }

def OptionEpisodes.finish (state : OptionEpisodes) (duration : UInt32) (reason : Fin 3) :
    OptionEpisodes :=
  { state with
    duration := addCount state.duration (UInt64.ofNat duration.toNat)
    reasons := state.reasons.set reason.val (addCount state.reasons[reason.val] 1) reason.isLt }

def OptionEpisodes.Valid (state : OptionEpisodes) (active : Bool) : Prop :=
  state.completed.toNat ≤ state.started.toNat ∧
    (state.completed = 0 → state.duration = 0) ∧
    (active = true → state.completed.toNat < state.started.toNat ∨ state.started.toNat = 2^64 - 1)

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

theorem OptionEpisodes.start_completed (state : OptionEpisodes) :
    state.start.completed = state.completed := rfl

theorem OptionEpisodes.finish_completed (state : OptionEpisodes) (duration : UInt32) (reason : Fin 3) :
    (state.finish duration reason).completed.toNat = min (state.completed.toNat + 1) (2^64 - 1) := by
  rw [completed_exact, completed_exact]
  rcases reason with ⟨reason, bound⟩
  have cases : reason = 0 ∨ reason = 1 ∨ reason = 2 := by omega
  rcases cases with rfl | rfl | rfl <;>
    simp only [OptionEpisodes.finish, Vector.getElem_set, ↓reduceIte, Nat.reduceEqDiff,
      addCount_exact, UInt64.reduceToNat] <;> omega

theorem OptionEpisodes.initial_valid : OptionEpisodes.initial.Valid false := by
  exact ⟨by decide, fun _ => rfl, by intro impossible; contradiction⟩

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

structure EpisodeEnd where
  slot : Fin Acorn.FeatureConstants.skillCount
  duration : UInt32
  reason : Fin 3

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

def OptionsValid (options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount)
    (active : Option (Fin Acorn.FeatureConstants.skillCount)) : Prop :=
  ∀ slot : Fin Acorn.FeatureConstants.skillCount, options[slot.val].Valid (active == some slot)

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

structure PendingPrediction (discount : Discount) where
  age : Fin (maxSettlement + 1)
  prediction : Prediction discount
  returnSum : Binary32
  discountPower : Binary32
  startedAt : UInt64

def PendingPrediction.initial {discount : Discount} (clock : UInt64)
    (prediction : Prediction discount) : PendingPrediction discount :=
  ⟨⟨0, by decide⟩, prediction, .zero, .one, clock⟩

@[irreducible] def settlementHorizon (discount : Discount) : Fin (maxSettlement + 1) :=
  ((List.finRange maxSettlement).foldl (fun (state : Binary32 × Fin (maxSettlement + 1)) step =>
    if (⟨Acorn.FeatureConstants.settleRemainingBits⟩ : Binary32).less state.1 then
      (state.1.mul discount.gamma, ⟨step.val + 1, by have := step.isLt; omega⟩)
    else state) (.one, 0)).2

structure DemonDurable (discount : Discount) where
  squaredError : SumCount (.squaredError discount)
  lastReturn : Prediction discount
  lastError : Bounded32 (errorRange discount).range

def DemonDurable.initial (discount : Discount) : DemonDurable discount :=
  ⟨SumCount.initial _, Prediction.project _ .zero,
    Bounded32.projectSymmetric (errorRange discount) .zero⟩

structure DemonStats (discount : Discount) where
  durable : DemonDurable discount
  pending : Vector (Option (PendingPrediction discount)) pendingSamples
  agreement : Agreement.Channel discount
  settleAfter : { value : Fin (maxSettlement + 1) // value = settlementHorizon discount }

def DemonStats.restore {discount : Discount} (durable : DemonDurable discount) : DemonStats discount :=
  ⟨durable, Vector.replicate _ none, Agreement.Channel.empty discount, ⟨settlementHorizon discount, rfl⟩⟩

def DemonStats.initial (discount : Discount) : DemonStats discount :=
  .restore (DemonDurable.initial discount)

def DemonStats.pendingCount {discount : Discount} (state : DemonStats discount) : Nat :=
  state.pending.toList.countP Option.isSome

def DemonStats.censor {discount : Discount} (state : DemonStats discount) : DemonStats discount :=
  { state with
    agreement := state.agreement.censor state.pendingCount
    pending := Vector.replicate _ none }

structure Settlement where
  squared : Binary32
  bucket : Fin historyBins

def PendingPrediction.advance {discount : Discount} (sample : PendingPrediction discount)
    (cumulant : Binary32) : PendingPrediction discount :=
  { sample with
    returnSum := sample.returnSum.add (sample.discountPower.mul cumulant)
    discountPower := sample.discountPower.mul discount.gamma
    age := ⟨min (sample.age.val + 1) maxSettlement, by
      have := Nat.min_le_right (sample.age.val + 1) maxSettlement; omega⟩ }

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

def observeHistory (state : SumCount (.squaredError .g99)) (discount : Discount)
    (value : Binary32) : SumCount (.squaredError .g99) :=
  state.observeAs (.squaredError discount) (by cases discount <;> decide) value

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

@[irreducible] def DemonStats.advanceSlots {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) historyBins)
    (clock : UInt64) (cumulant : Binary32) (slots : List (Fin pendingSamples)) :
    DemonStats discount × Vector (SumCount (.squaredError .g99)) historyBins :=
  slots.foldl (fun current slot => DemonStats.visit current slot cumulant clock) (state, history)

def DemonStats.observe {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) historyBins)
    (clock : UInt64) (cumulant : Binary32) (prediction : Prediction discount) :
    DemonStats discount × Vector (SumCount (.squaredError .g99)) historyBins :=
  let (state, history) := state.advanceSlots history clock cumulant (List.finRange pendingSamples)
  (state.start clock prediction, history)

inductive DemonRecords : List Discount → Type where
  | nil : DemonRecords []
  | cons {discount : Discount} {rest : List Discount}
      (head : DemonStats discount) (tail : DemonRecords rest) : DemonRecords (discount :: rest)

def DemonRecords.initial : (discounts : List Discount) → DemonRecords discounts
  | [] => .nil
  | discount :: rest => .cons (DemonStats.initial discount) (DemonRecords.initial rest)

def DemonRecords.censor {discounts : List Discount} : DemonRecords discounts → DemonRecords discounts
  | .nil => .nil
  | .cons head tail => .cons head.censor tail.censor

def DemonRecords.fail {discounts : List Discount} (fault : Agreement.Fault) :
    DemonRecords discounts → DemonRecords discounts
  | .nil => .nil
  | .cons head tail => .cons
      { head with agreement := { head.agreement with fault := head.agreement.fault.or (some fault) } }
      (tail.fail fault)

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

def DemonRecords.agreementRatios {discounts : List Discount} :
    DemonRecords discounts → List (Option Agreement.Ratio)
  | .nil => []
  | .cons head tail => head.agreement.ratio :: tail.agreementRatios

def DemonRecords.agreementRatio {discounts : List Discount} (state : DemonRecords discounts) :
    Option Agreement.Ratio :=
  (Agreement.aggregateAll state.agreementRatios).bind Agreement.Aggregate.ratio

theorem DemonRecords.agreementRatios_length {discounts : List Discount} (state : DemonRecords discounts) :
    state.agreementRatios.length = discounts.length := by
  induction state with
  | nil => rfl
  | cons head tail ih => simpa only [agreementRatios, List.length_cons] using congrArg (· + 1) ih

structure AgreementPoint where
  clock : UInt64
  ratio : Agreement.Ratio

structure Stats (discounts : List Discount) where
  reward : SumCount .reward
  rewardByFamily : Vector (SumCount .reward) 4
  rewardHistory : Vector (SumCount .reward) historyBins
  demons : DemonRecords discounts
  errorHistory : Vector (SumCount (.squaredError .g99)) historyBins
  options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount
  goals : Vector GoalTotals 4
  goalCycles : Vector (Vector GoalTotals cycleBins) 4
  agreementStarted : Option UInt64
  agreementHistory : Vector (Option AgreementPoint) historyBins
  agreementLastClock : Option UInt64
  agreementStopped : Bool

def Stats.initial (discounts : List Discount) : Stats discounts :=
  ⟨SumCount.initial _, Vector.replicate _ (SumCount.initial _),
    Vector.replicate _ (SumCount.initial _), DemonRecords.initial discounts,
    Vector.replicate _ (SumCount.initial _), Vector.replicate _ OptionEpisodes.initial,
    Vector.replicate _ GoalTotals.initial, Vector.replicate _ (Vector.replicate _ GoalTotals.initial),
    some 0, Vector.replicate _ none, some 0, false⟩

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

theorem Stats.recordDemons_live {discounts : List Discount} (state : Stats discounts)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts)
    (live : state.agreementStopped = false) :
    (state.recordDemons clock cumulants predictions).agreementLastClock = some clock := by
  simp [recordDemons, live]

theorem Stats.recordDemons_stopped {discounts : List Discount} (state : Stats discounts)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts)
    (stopped : state.agreementStopped = true) :
    state.recordDemons clock cumulants predictions = state := by
  simp [recordDemons, stopped]

theorem Stats.recordDemons_options {discounts : List Discount} (state : Stats discounts)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts) :
    (state.recordDemons clock cumulants predictions).options = state.options := by
  cases stopped : state.agreementStopped <;> simp [recordDemons, stopped]

def Stats.censor {discounts : List Discount} (state : Stats discounts) : Stats discounts :=
  { state with demons := state.demons.censor, agreementStopped := true }

def Stats.recordAttempt {discounts : List Discount} (state : Stats discounts)
    (family : Fin 4) (cycle steps : UInt64) (achieved : Bool) : Stats discounts :=
  let bucket := cycleBin cycle
  let familyCycles := state.goalCycles.get family
  { state with
    goals := state.goals.set family.val ((state.goals.get family).observe steps achieved) family.isLt
    goalCycles := state.goalCycles.set family.val
      (familyCycles.set bucket.val ((familyCycles.get bucket).observe steps achieved) bucket.isLt) family.isLt }

inductive DurableDemons : List Discount → Type where
  | nil : DurableDemons []
  | cons {discount : Discount} {rest : List Discount}
      (head : DemonDurable discount) (tail : DurableDemons rest) : DurableDemons (discount :: rest)

def DemonRecords.durable {discounts : List Discount} : DemonRecords discounts → DurableDemons discounts
  | .nil => .nil
  | .cons head tail => .cons head.durable tail.durable

def DurableDemons.restore {discounts : List Discount} : DurableDemons discounts → DemonRecords discounts
  | .nil => .nil
  | .cons head tail => .cons (DemonStats.restore head) tail.restore

theorem DemonRecords.censor_durable {discounts : List Discount} (state : DemonRecords discounts) :
    state.censor.durable = state.durable := by
  induction state with
  | nil => rfl
  | cons head tail ih => simp [DemonRecords.censor, DemonRecords.durable, DemonStats.censor, ih]

theorem DurableDemons.restore_durable {discounts : List Discount} (state : DurableDemons discounts) :
    state.restore.durable = state := by
  induction state with
  | nil => rfl
  | cons head tail ih => simp [restore, DemonRecords.durable, DemonStats.restore, ih]

structure Durable (discounts : List Discount) where
  reward : SumCount .reward
  rewardByFamily : Vector (SumCount .reward) 4
  rewardHistory : Vector (SumCount .reward) historyBins
  demons : DurableDemons discounts
  errorHistory : Vector (SumCount (.squaredError .g99)) historyBins
  options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount
  goals : Vector GoalTotals 4
  goalCycles : Vector (Vector GoalTotals cycleBins) 4

def Stats.durable {discounts : List Discount} (state : Stats discounts) : Durable discounts :=
  ⟨state.reward, state.rewardByFamily, state.rewardHistory, state.demons.durable,
    state.errorHistory, state.options, state.goals, state.goalCycles⟩

def Durable.restore {discounts : List Discount} (state : Durable discounts) : Stats discounts :=
  ⟨state.reward, state.rewardByFamily, state.rewardHistory, state.demons.restore,
    state.errorHistory, state.options, state.goals, state.goalCycles,
    none, Vector.replicate _ none, none, false⟩

theorem Durable.restore_durable {discounts : List Discount} (state : Durable discounts) :
    state.restore.durable = state := by
  cases state
  simp [Durable.restore, Stats.durable, DurableDemons.restore_durable]

theorem Stats.censor_durable {discounts : List Discount} (state : Stats discounts) :
    state.censor.durable = state.durable := by
  simp [Stats.censor, Stats.durable, DemonRecords.censor_durable]

theorem Stats.censor_no_observation {discounts : List Discount} (state : Stats discounts)
    (clock : UInt64) (cumulants : Cumulants discounts) (predictions : PredictionCache discounts) :
    state.censor.recordDemons clock cumulants predictions = state.censor := by
  simp [Stats.recordDemons, Stats.censor]

end Acorn.Lifetime
