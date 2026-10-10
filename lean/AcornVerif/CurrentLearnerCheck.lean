/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentLearner
import Acorn.FeatureConsumers

/-!
# The invariant check of a stored learner

`NumericState.resumable` decides, on a learner's stored words, the schedule invariant of the
learner's capacity theorem, `ScheduleInv` (`resumable_iff`). A learner read back from a
checkpoint image is admitted by that check, so every learner that `ManagedAdmission` admits
still satisfies the invariant (`CurrentFeatureConsumers.managed_schedule`): the provenance a
managed learner carries gives core safety, unique eligibility and phase-specific readiness,
whatever its origin.
-/
namespace AcornVerif.CurrentLearnerCheck
open Acorn Acorn.Features AcornVerif.CurrentLearner AcornVerif.CurrentArithmetic
open AcornVerif.CurrentOrder

variable {config : Acorn.Config} {dimension : Dimension}

/-- A seen slot leaves the builder unchanged. -/
theorem add_seen (builder : UniqueBuilder dimension) (index : FeatIdx dimension)
    (seen : index ∈ builder.reversed) : builder.add index = builder := by
  unfold UniqueBuilder.add
  rw [dite_eq_left (by simpa [builder.exact] using seen)]

/-- An unseen slot is prepended. -/
theorem add_unseen (builder : UniqueBuilder dimension) (index : FeatIdx dimension)
    (unseen : index ∉ builder.reversed) :
    (builder.add index).reversed = index :: builder.reversed := by
  unfold UniqueBuilder.add
  rw [dite_eq_right (by simpa [builder.exact] using unseen)]

/-- A fold adds at most one slot per element. -/
theorem fold_length_le : ∀ (indices : List (FeatIdx dimension)) (builder : UniqueBuilder dimension),
    (indices.foldl UniqueBuilder.add builder).reversed.length ≤
      builder.reversed.length + indices.length
  | [], builder => by simp
  | index :: rest, builder => by
    rw [List.foldl_cons]
    by_cases seen : index ∈ builder.reversed
    · rw [add_seen builder index seen]
      have := fold_length_le rest builder
      simp only [List.length_cons]
      omega
    · have tail := fold_length_le rest (builder.add index)
      rw [add_unseen builder index seen] at tail
      simp only [List.length_cons] at tail ⊢
      omega

/-- A fold keeps every element exactly when no element repeats and none was seen before. -/
theorem fold_length : ∀ (indices : List (FeatIdx dimension)) (builder : UniqueBuilder dimension),
    (indices.foldl UniqueBuilder.add builder).reversed.length =
        builder.reversed.length + indices.length ↔
      indices.Nodup ∧ ∀ index ∈ indices, index ∉ builder.reversed
  | [], builder => by simp
  | index :: rest, builder => by
    rw [List.foldl_cons]
    by_cases seen : index ∈ builder.reversed
    · rw [add_seen builder index seen]
      have bound := fold_length_le rest builder
      constructor
      · intro same
        simp only [List.length_cons] at same
        omega
      · intro ⟨_, unseen⟩
        exact absurd seen (unseen index List.mem_cons_self)
    · have tail := fold_length rest (builder.add index)
      rw [add_unseen builder index seen] at tail
      simp only [List.length_cons] at tail ⊢
      rw [show builder.reversed.length + (rest.length + 1) =
        builder.reversed.length + 1 + rest.length by omega, tail]
      simp only [List.mem_cons, not_or, List.nodup_cons]
      constructor
      · rintro ⟨fresh, apart⟩
        refine ⟨⟨fun member => (apart index member).1 rfl, fresh⟩, fun other inside => ?_⟩
        rcases inside with rfl | member
        · exact seen
        · exact (apart other member).2
      · rintro ⟨⟨absent, fresh⟩, unseen⟩
        exact ⟨fresh, fun other member =>
          ⟨fun same => absent (same ▸ member), unseen other (.inr member)⟩⟩

/-- The builder of a list keeps every element exactly when no element repeats. -/
theorem presence_nodup (indices : List (FeatIdx dimension)) :
    (indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)).reversed.length =
      indices.length ↔ indices.Nodup := by
  have kept := fold_length indices (UniqueBuilder.empty dimension)
  simp only [UniqueBuilder.empty, List.length_nil, Nat.zero_add, List.not_mem_nil,
    not_false_eq_true, implies_true, and_true] at kept
  exact kept

/-- A slot is flagged by the builder of a list exactly when it is in the list. -/
theorem presence_seen (indices : List (FeatIdx dimension)) (index : FeatIdx dimension) :
    (indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)).seen[index.val] = true ↔
      index ∈ indices := by
  rw [(indices.foldl UniqueBuilder.add (UniqueBuilder.empty dimension)).exact, decide_eq_true_iff]
  have kept := mem_unique indices index
  simp only [unique, UniqueBuilder.finish, List.mem_reverse] at kept
  exact kept

/-- The nine-word test is the zero register vector of the support invariant. -/
theorem clearAt_iff (state : NumericState config dimension) (index : FeatIdx dimension) :
    state.clearAt index = true ↔ registers state index = Vector.replicate 9 Binary32.zero := by
  unfold NumericState.clearAt registers
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨z, zDelta⟩, zBar⟩, lastAlpha⟩, deltaWeight⟩, h⟩, hOld⟩, hTemp⟩, p⟩
    rw [z, zDelta, zBar, lastAlpha, deltaWeight, h, hOld, hTemp, p]
    rfl
  · intro same
    have entry := fun (position : Nat) (inside : position < 9) =>
      congrArg (fun words : Vector Binary32 9 => words[position]'inside) same
    exact ⟨⟨⟨⟨⟨⟨⟨⟨entry 0 (by decide), entry 1 (by decide)⟩, entry 2 (by decide)⟩,
      entry 3 (by decide)⟩, entry 4 (by decide)⟩, entry 5 (by decide)⟩, entry 6 (by decide)⟩,
      entry 7 (by decide)⟩, entry 8 (by decide)⟩

/-- The stored word of five has the value five. -/
theorem five_value : numerical32 (⟨0x40a00000⟩ : Binary32) = 5 := by
  change (1 : ℚ) * 10485760 * (2 : ℚ) ^ (-21 : Int) = 5
  norm_num

/-- Positive zero has the value zero. -/
theorem zero_value : numerical32 Binary32.zero = 0 := by decide

/-- The interval of a reference word is the reference invariant. -/
theorem reference_iff (word : Binary32) :
    referenceRange.Contains word ↔ ReferenceLegal word := by
  unfold Interval32.Contains ReferenceLegal
  constructor
  · rintro ⟨finite, lower, upper⟩
    refine ⟨finite, ?_, ?_⟩
    · have := (numerical32_order Binary32.zero word (by decide) finite).mpr lower
      rwa [zero_value] at this
    · have := (numerical32_order word ⟨0x40a00000⟩ finite (by decide)).mpr upper
      rwa [five_value] at this
  · rintro ⟨finite, lower, upper⟩
    refine ⟨finite, ?_, ?_⟩
    · exact (numerical32_order Binary32.zero word (by decide) finite).mp
        (by rw [zero_value]; exact lower)
    · exact (numerical32_order word ⟨0x40a00000⟩ finite (by decide)).mp
        (by rw [five_value]; exact upper)

/-- **The stored-word check is the schedule invariant.** For every learner state and phase,
`NumericState.resumable` accepts exactly the states that satisfy `ScheduleInv`: support,
legal pruning references, unique eligibility and, under a permitted second loop, readiness. -/
theorem resumable_iff (state : NumericState config dimension) (phase : Bool) :
    state.resumable phase = true ↔ ScheduleInv state phase := by
  have eligible : ∀ index : FeatIdx dimension,
      index ∈ state.transient.eligible ↔ index ∈ state.transient.eligible.toList :=
    fun index => Array.mem_toList_iff.symm
  unfold NumericState.resumable ScheduleInv CoreInv Supported ReferencesLegal Ready
  simp only [Bool.and_eq_true, beq_iff_eq, presence_nodup, List.all_eq_true, List.mem_finRange,
    true_implies, Bool.or_eq_true, presence_seen, clearAt_iff, decide_eq_true_eq, reference_iff,
    Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨⟨unique, slots⟩, ready⟩
    refine ⟨⟨fun index absent => ?_, fun index => (slots index).2⟩, unique, fun permitted => ?_⟩
    · rcases (slots index).1 with member | clear
      · exact absurd ((eligible index).mpr member) absent
      · exact clear
    · refine ⟨unique, fun index member => ?_⟩
      rcases ready with free | nonzero
      · rw [permitted] at free
        cases free
      · exact nonzero index ((eligible index).mp member)
  · rintro ⟨⟨support, references⟩, unique, ready⟩
    refine ⟨⟨unique, fun index => ⟨?_, references index⟩⟩, ?_⟩
    · by_cases member : index ∈ state.transient.eligible.toList
      · exact .inl member
      · exact .inr (support index (fun inside => member ((eligible index).mp inside)))
    · cases phase with
      | false => exact .inl rfl
      | true =>
        exact .inr fun index member => (ready rfl).2 index ((eligible index).mpr member)

end AcornVerif.CurrentLearnerCheck
