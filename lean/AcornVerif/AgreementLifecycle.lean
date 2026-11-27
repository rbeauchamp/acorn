import AcornVerif.AgreementTelemetryPrecision
import Acorn.Handcrafted.Cumulants

namespace AcornVerif.AgreementLifecycle
open Acorn Acorn.Lifetime

private theorem vector_get {α : Type} {n : Nat} (values : Vector α n) (index : Fin n) :
    values.get index = values[index.val] := rfl

theorem advanceSlot_selected {discount : Discount} (state : DemonStats discount)
    (slot : Fin Acorn.FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    (state.advanceSlot slot cumulant clock).1.pending.get slot =
      match state.pending.get slot with
      | none => none
      | some sample => if (sample.advance cumulant).age.val ≥ state.settleAfter.val.val then none
          else some (sample.advance cumulant) := by
  cases present : state.pending.get slot with
  | none => simp [DemonStats.advanceSlot, present]
  | some sample =>
    by_cases complete : (sample.advance cumulant).age.val ≥ state.settleAfter.val.val <;>
      simp [DemonStats.advanceSlot, present, complete, vector_get]

theorem advanceSlot_other {discount : Discount} (state : DemonStats discount)
    (slot other : Fin Acorn.FeatureConstants.pendingSamples) (different : other ≠ slot)
    (cumulant : Binary32) (clock : UInt64) :
    (state.advanceSlot slot cumulant clock).1.pending.get other = state.pending.get other := by
  have unequal : other.val ≠ slot.val := fun same => different (Fin.ext same)
  cases present : state.pending.get slot with
  | none => simp [DemonStats.advanceSlot, present]
  | some sample =>
    by_cases complete : (sample.advance cumulant).age.val ≥ state.settleAfter.val.val <;>
      simp [DemonStats.advanceSlot, present, complete, vector_get, Ne.symm unequal]

theorem advanceSlot_horizon {discount : Discount} (state : DemonStats discount)
    (slot : Fin Acorn.FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    (state.advanceSlot slot cumulant clock).1.settleAfter = state.settleAfter := by
  cases present : state.pending.get slot with
  | none => simp [DemonStats.advanceSlot, present]
  | some sample =>
    by_cases complete : (sample.advance cumulant).age.val ≥ state.settleAfter.val.val <;>
      simp [DemonStats.advanceSlot, present, complete]

theorem advanceSlot_age {discount : Discount} (state : DemonStats discount)
    (slot : Fin Acorn.FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64)
    (sample : PendingPrediction discount)
    (retained : (state.advanceSlot slot cumulant clock).1.pending.get slot = some sample) :
    sample.age.val < Acorn.FeatureConstants.maxSettlement := by
  rw [advanceSlot_selected] at retained
  cases present : state.pending.get slot with
  | none => simp [present] at retained
  | some prior =>
    simp only [present] at retained
    split at retained
    · contradiction
    · cases retained
      have := state.settleAfter.val.isLt
      omega

theorem visit_first {discount : Discount}
    (current : DemonStats discount × Vector (SumCount (.squaredError .g99))
      Acorn.FeatureConstants.historyBins)
    (slot : Fin Acorn.FeatureConstants.pendingSamples) (cumulant : Binary32) (clock : UInt64) :
    (DemonStats.visit current slot cumulant clock).1 =
      (current.1.advanceSlot slot cumulant clock).1 := rfl

private theorem advanceSlots_cons {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulant : Binary32)
    (head : Fin Acorn.FeatureConstants.pendingSamples)
    (tail : List (Fin Acorn.FeatureConstants.pendingSamples)) :
    state.advanceSlots history clock cumulant (head :: tail) =
      (DemonStats.visit (state, history) head cumulant clock).1.advanceSlots
        (DemonStats.visit (state, history) head cumulant clock).2 clock cumulant tail := by
  unfold DemonStats.advanceSlots
  rfl

theorem advanceSlots_unvisited {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulant : Binary32)
    (slots : List (Fin Acorn.FeatureConstants.pendingSamples))
    (target : Fin Acorn.FeatureConstants.pendingSamples) (absent : target ∉ slots) :
    (state.advanceSlots history clock cumulant slots).1.pending.get target =
      state.pending.get target := by
  induction slots generalizing state history with
  | nil => simp [DemonStats.advanceSlots]
  | cons head tail ih =>
    simp only [List.mem_cons, not_or] at absent
    rw [advanceSlots_cons]
    rw [ih _ _ absent.2, visit_first, advanceSlot_other _ _ _ absent.1]

theorem advanceSlots_once {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulant : Binary32)
    (slots : List (Fin Acorn.FeatureConstants.pendingSamples)) (unique : slots.Nodup)
    (target : Fin Acorn.FeatureConstants.pendingSamples) (member : target ∈ slots) :
    (state.advanceSlots history clock cumulant slots).1.pending.get target =
      (state.advanceSlot target cumulant clock).1.pending.get target := by
  induction slots generalizing state history with
  | nil => contradiction
  | cons head tail ih =>
    have nodup := List.nodup_cons.mp unique
    rw [advanceSlots_cons]
    by_cases same : target = head
    · subst target
      rw [advanceSlots_unvisited _ _ _ _ _ _ nodup.1, visit_first]
    · have tailMember : target ∈ tail := (List.mem_cons.mp member).resolve_left same
      rw [ih _ _ nodup.2 tailMember, advanceSlot_selected, visit_first,
        advanceSlot_other _ _ _ same, advanceSlot_horizon]
      exact (advanceSlot_selected state target cumulant clock).symm

theorem fullBank_once {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulant : Binary32) (target : Fin Acorn.FeatureConstants.pendingSamples) :
    (state.advanceSlots history clock cumulant
      (List.finRange Acorn.FeatureConstants.pendingSamples)).1.pending.get target =
      (state.advanceSlot target cumulant clock).1.pending.get target := by
  apply advanceSlots_once
  · exact List.nodup_finRange _
  · exact List.mem_finRange target

theorem start_cases {discount : Discount} (state : DemonStats discount) (clock : UInt64)
    (prediction : Prediction discount) (target : Fin Acorn.FeatureConstants.pendingSamples)
    (sample : PendingPrediction discount)
    (present : (state.start clock prediction).pending.get target = some sample) :
    sample = PendingPrediction.initial clock prediction ∨
      state.pending.get target = some sample := by
  unfold DemonStats.start at present
  split at present
  · cases found : (List.finRange Acorn.FeatureConstants.pendingSamples).find?
        (fun slot => (state.pending.get slot).isNone) with
    | none => simp only [found] at present; exact Or.inr present
    | some slot =>
      simp only [found] at present
      by_cases same : slot = target
      · subst target
        have equality : some (PendingPrediction.initial clock prediction) = some sample := by
          simpa only [vector_get, Vector.getElem_set_self] using present
        exact Or.inl (Option.some.inj equality).symm
      · have unequal : slot.val ≠ target.val := fun sameValue => same (Fin.ext sameValue)
        apply Or.inr
        simpa only [vector_get, Vector.getElem_set, unequal, ite_false] using present
  · exact Or.inr present

theorem observe_cases {discount : Discount} (state : DemonStats discount)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulant : Binary32) (prediction : Prediction discount)
    (target : Fin Acorn.FeatureConstants.pendingSamples) (sample : PendingPrediction discount)
    (present : (state.observe history clock cumulant prediction).1.pending.get target =
      some sample) :
    sample = PendingPrediction.initial clock prediction ∨
      ∃ prior, state.pending.get target = some prior ∧ sample = prior.advance cumulant ∧
        sample.age.val < Acorn.FeatureConstants.maxSettlement := by
  have capture := start_cases
    (state.advanceSlots history clock cumulant
      (List.finRange Acorn.FeatureConstants.pendingSamples)).1
    clock prediction target sample present
  rcases capture with fresh | retained
  · exact Or.inl fresh
  · rw [fullBank_once] at retained
    have age := advanceSlot_age state target cumulant clock sample retained
    rw [advanceSlot_selected] at retained
    cases prior : state.pending.get target with
    | none => simp [prior] at retained
    | some value =>
      simp only [prior] at retained
      split at retained
      · contradiction
      · cases retained
        exact Or.inr ⟨value, rfl, rfl, age⟩

def Captured {discount : Discount} (sample : PendingPrediction discount) : Prop :=
  ∃ inputs : List Binary32, inputs.length = sample.age.val ∧
    (∀ word ∈ inputs, word.Finite ∧ 0 ≤ AcornVerif.CurrentArithmetic.numerical32 word ∧
      AcornVerif.CurrentArithmetic.numerical32 word ≤ 1) ∧
    sample = inputs.foldl PendingPrediction.advance
      (PendingPrediction.initial sample.startedAt sample.prediction)

theorem captured_initial {discount : Discount} (clock : UInt64) (prediction : Prediction discount) :
    Captured (PendingPrediction.initial clock prediction) := by
  refine ⟨[], rfl, ?_, rfl⟩
  simp

theorem captured_advance {discount : Discount} (sample : PendingPrediction discount)
    (captured : Captured sample) (young : sample.age.val < Acorn.FeatureConstants.maxSettlement)
    (cumulant : Binary32)
    (legal : cumulant.Finite ∧ 0 ≤ AcornVerif.CurrentArithmetic.numerical32 cumulant ∧
      AcornVerif.CurrentArithmetic.numerical32 cumulant ≤ 1) :
    Captured (sample.advance cumulant) := by
  obtain ⟨inputs, count, signals, correspondence⟩ := captured
  refine ⟨inputs ++ [cumulant], ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, count, PendingPrediction.advance]
    exact (Nat.min_eq_left (Nat.succ_le_of_lt young)).symm
  · intro word member
    rcases List.mem_append.mp member with old | new
    · exact signals word old
    · simpa only [List.mem_singleton.mp new] using legal
  · change sample.advance cumulant =
      (inputs ++ [cumulant]).foldl PendingPrediction.advance
        (PendingPrediction.initial sample.startedAt sample.prediction)
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← correspondence]

def BankInvariant {discount : Discount} (state : DemonStats discount) : Prop :=
  ∀ slot sample, state.pending.get slot = some sample →
    Captured sample ∧ sample.age.val < Acorn.FeatureConstants.maxSettlement

theorem restore_invariant {discount : Discount} (durable : DemonDurable discount) :
    BankInvariant (DemonStats.restore durable) := by
  intro slot sample present
  simp [DemonStats.restore, vector_get] at present

theorem censor_invariant {discount : Discount} (state : DemonStats discount) :
    BankInvariant state.censor := by
  intro slot sample present
  simp [DemonStats.censor, vector_get] at present

theorem observe_invariant {discount : Discount} (state : DemonStats discount)
    (invariant : BankInvariant state)
    (history : Vector (SumCount (.squaredError .g99)) Acorn.FeatureConstants.historyBins)
    (clock : UInt64) (cumulant : Binary32) (prediction : Prediction discount)
    (legal : cumulant.Finite ∧ 0 ≤ AcornVerif.CurrentArithmetic.numerical32 cumulant ∧
      AcornVerif.CurrentArithmetic.numerical32 cumulant ≤ 1) :
    BankInvariant (state.observe history clock cumulant prediction).1 := by
  intro target sample present
  rcases observe_cases state history clock cumulant prediction target sample present with
    fresh | old
  · subst sample
    exact ⟨captured_initial clock prediction, by
      change 0 < Acorn.FeatureConstants.maxSettlement
      decide⟩
  · obtain ⟨prior, pending, rfl, young⟩ := old
    have before := invariant target prior pending
    exact ⟨captured_advance prior before.1 before.2 cumulant legal, young⟩

theorem captured_available {discount : Discount} (sample : PendingPrediction discount)
    (captured : Captured sample) :
    (Agreement.admitSquared (Agreement.envelopeUnits discount)
      sample.prediction.value sample.returnSum).isSome = true := by
  obtain ⟨inputs, count, signals, correspondence⟩ := captured
  have room : inputs.length ≤ Acorn.FeatureConstants.maxSettlement := by
    have := sample.age.isLt
    omega
  have available := AgreementReturn.captured_admission discount sample.startedAt sample.prediction
    inputs room signals
  rw [← correspondence] at available
  exact available

theorem captured_precision_available {discount : Discount} (sample : PendingPrediction discount)
    (captured : Captured sample) :
    (Agreement.precision discount sample.age.val sample.discountPower).isSome = true := by
  obtain ⟨inputs, count, signals, correspondence⟩ := captured
  have room : inputs.length ≤ Acorn.FeatureConstants.maxSettlement := by
    have := sample.age.isLt
    omega
  have tracked := AgreementReturn.fold_tracks inputs
    (PendingPrediction.initial sample.startedAt sample.prediction) 0 0 1
    (by simpa using room) signals
    (AgreementReturn.initial_tracks discount sample.startedAt sample.prediction)
    (by simp [AgreementReturn.IdealBound])
  simp only [Nat.zero_add] at tracked
  rw [← correspondence, count] at tracked
  exact AgreementTelemetryPrecision.precision_available _ _ _ _ _
    (by have := sample.age.isLt; omega) tracked.1 tracked.2

theorem settlement_squared_available {discount : Discount} (state : DemonStats discount)
    (invariant : BankInvariant state) (slot : Fin Acorn.FeatureConstants.pendingSamples)
    (sample : PendingPrediction discount) (pending : state.pending.get slot = some sample)
    (cumulant : Binary32)
    (legal : cumulant.Finite ∧ 0 ≤ AcornVerif.CurrentArithmetic.numerical32 cumulant ∧
      AcornVerif.CurrentArithmetic.numerical32 cumulant ≤ 1) :
    (Agreement.admitSquared (Agreement.envelopeUnits discount)
      (sample.advance cumulant).prediction.value
      (sample.advance cumulant).returnSum).isSome = true :=
  captured_available _ (captured_advance sample (invariant slot sample pending).1
    (invariant slot sample pending).2 cumulant legal)

theorem settlement_available {discount : Discount} (state : DemonStats discount)
    (invariant : BankInvariant state) (slot : Fin Acorn.FeatureConstants.pendingSamples)
    (sample : PendingPrediction discount) (pending : state.pending.get slot = some sample)
    (cumulant : Binary32)
    (legal : cumulant.Finite ∧ 0 ≤ AcornVerif.CurrentArithmetic.numerical32 cumulant ∧
      AcornVerif.CurrentArithmetic.numerical32 cumulant ≤ 1) :
    (Agreement.admitSquared (Agreement.envelopeUnits discount)
      (sample.advance cumulant).prediction.value
      (sample.advance cumulant).returnSum).isSome = true ∧
    (Agreement.precision discount (sample.advance cumulant).age.val
      (sample.advance cumulant).discountPower).isSome = true := by
  exact ⟨settlement_squared_available state invariant slot sample pending cumulant legal,
    captured_precision_available _ (captured_advance sample (invariant slot sample pending).1
      (invariant slot sample pending).2 cumulant legal)⟩

theorem current_cumulant_legal (signal : Handcrafted.Cumulant) (obs : Host.Observation)
    (reward : Binary32) :
    (signal.eval obs reward).Finite ∧
      0 ≤ AcornVerif.CurrentArithmetic.numerical32 (signal.eval obs reward) ∧
      AcornVerif.CurrentArithmetic.numerical32 (signal.eval obs reward) ≤ 1 := by
  rcases signal.indicator obs reward with zero | one
  · rw [zero]
    exact ⟨by decide, by decide, by decide⟩
  · rw [one]
    have value : AcornVerif.CurrentArithmetic.numerical32 Binary32.one = 1 := by
      change (1 : ℚ) * 8388608 * 2^(-23 : Int) = 1
      norm_num
    exact ⟨by decide, by rw [value]; norm_num, by rw [value]⟩

theorem current_inventory_unique : Handcrafted.cumulantOrder.Nodup := List.nodup_finRange _

end AcornVerif.AgreementLifecycle
