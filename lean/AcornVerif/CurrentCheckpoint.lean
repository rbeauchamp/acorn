/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Size
import AcornVerif.CurrentLifetime
import AcornVerif.CurrentLearner

/-!
# Current checkpoint admission and installation laws

These statements concern the actual format-14 parser, writer, legal-state
constructors and full-agent restoration. The laws describe parsing, serialization
and pure restoration. Native persistence relies on the filesystem and OS.
-/
namespace AcornVerif.CurrentCheckpoint
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime

/-- Legal stored totals survive durable admission with both words unchanged. -/
theorem sum_roundtrip {quantity : Quantity} (record : SumCount quantity) :
    admitSum quantity (sumWords record) = some record := by
  simp [admitSum, sumWords, SumCount.admit, CurrentLifetime.stored_sum_legal record]

/-- Goal admission preserves every already-legal count triple. -/
theorem goal_roundtrip (record : GoalTotals) : admitGoal (goalWords record) = some record := by
  have valid : record.successes.toNat ≤ record.attempts.toNat ∧ (record.attempts = 0 →
    record.steps = 0) :=
    ⟨record.successesBound, record.emptySteps⟩
  unfold admitGoal goalWords
  rw [dif_pos valid]

/-- Mapping a word projection and its partial inverse covers all vector positions. -/
theorem vector_roundtrip {α β : Type} {count : Nat} (encode : α → β) (admit : β → Option α)
    (inverse : ∀ value, admit (encode value) = some value) (values : Vector α count) :
    (values.map encode).mapM admit = some values := by
  simp only [Vector.mapM_map]
  have same : admit ∘ encode = fun value => some value := funext inverse
  rw [same]
  simpa using (Vector.mapM_pure (m := Option) (xs := values) id)

/-- Prepending preserves column order in the actual vector storage. -/
theorem prepend_toList {α : Type} {count : Nat} (head : α) (tail : Vector α count) :
    (prepend head tail).toList = head :: tail.toList := by
  unfold prepend
  rw [Vector.toList_cast]
  change (#v[head] ++ tail).toList = head :: tail.toList
  simp

/-- Each horizon validates exactly its own three durable columns. -/
theorem demons_roundtrip {discounts : List Discount} (records : DurableDemons discounts) :
    admitDemons discounts (demonColumns records).sums.toList
      (demonColumns records).returns.toList (demonColumns records).errors.toList = some records :=
        by
  induction records with
  | nil => rfl
  | cons head tail ih =>
    simp [demonColumns, prepend_toList, admitDemons, sum_roundtrip,
      Prediction.admit, Bounded32.admit_self, ih]

/-- Every field of an admitted durable lifetime record survives serialization admission. -/
theorem lifetime_roundtrip (record : Durable demonLayout) (valid : OptionsValid record.options
  none) :
    admitLifetime (lifetimeWords record) = some record := by
  simp only [admitLifetime, lifetimeWords,
    sum_roundtrip, vector_roundtrip sumWords (admitSum .reward) sum_roundtrip,
    vector_roundtrip sumWords (admitSum (.squaredError .g99)) sum_roundtrip,
    vector_roundtrip goalWords admitGoal goal_roundtrip,
    vector_roundtrip (fun row : Vector GoalTotals Acorn.FeatureConstants.cycleBins => row.map
      goalWords)
      (fun row : Vector GoalWords Acorn.FeatureConstants.cycleBins => row.mapM admitGoal)
      (vector_roundtrip goalWords admitGoal goal_roundtrip), demons_roundtrip]
  simp [valid]

/-- The exact receiver identity and supported-profile header is admitted without normalization. -/
theorem header_roundtrip (construction : AgentConstruction)
    (image : AgentImage construction.config construction.criterion construction.dimension)
    (supported : construction.profile.checkpointSupported = true) :
    admitHeader construction (imagePayload construction image).header = .ok image.gain := by
  have units : construction.config.units.count.toUInt32.toNat = construction.config.units.count :=
    Nat.mod_eq_of_lt (by have := construction.config.units.bounded; omega)
  have gain : RewardRate.admit image.gain.value = some image.gain := Bounded32.admit_self image.gain
  simp [admitHeader, imagePayload, supported, gain, units]
  rfl

/-- Raw feature words reconstruct the exact saved progress, objectives and primary image. -/
theorem feature_roundtrip (construction : AgentConstruction)
    (image : AgentImage construction.config construction.criterion construction.dimension) :
    FeatureImage.admit construction.config construction.criterion construction.dimension
      ⟨construction.config.seed, construction.config.tilings,
        construction.config.units.count.toUInt32.toUInt16,
       construction.dimension.capacity.toUInt32, construction.criterion.tag.toUInt32.toUInt8,
       image.features.progress.clock, image.features.progress.words,
       image.features.assignments.map (Assignment.words construction.dimension),
       image.features.primary, image.features.pending⟩ = some image.features := by
  have units : construction.config.units.count.toUInt32.toUInt16.toNat =
    construction.config.units.count := by
    have := construction.config.units.bounded
    change (construction.config.units.count % 2^32) % 2^16 = construction.config.units.count
    omega
  have capacity : construction.dimension.capacity.toUInt32.toNat = construction.dimension.capacity
    :=
    Nat.mod_eq_of_lt construction.dimension.wordBound
  have criterion : construction.criterion.tag.toUInt32.toUInt8 = construction.criterion.tag := by
    cases construction.criterion <;> rfl
  simp only [FeatureImage.admit, units, capacity, criterion]
  simp only [bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [Progress.words_roundtrip]
  simp only [bind, Option.bind]
  rw [vector_roundtrip _ _ (Assignment.words_roundtrip construction.dimension)]

/-- Full admission preserves every typed image, including both signed-zero encodings. -/
theorem image_roundtrip (construction : AgentConstruction)
    (image : AgentImage construction.config construction.criterion construction.dimension)
    (supported : construction.profile.checkpointSupported = true) :
    admitPayload construction (imagePayload construction image) = .ok image := by
  unfold admitPayload
  rw [header_roundtrip construction image supported]
  simp only [bind, Except.bind]
  have lifetime := lifetime_roundtrip image.lifetime image.episodes
  cases pending : image.features.pending <;>
    simp only [imagePayload, pending, Bool.false_eq_true, ↓reduceIte]
  all_goals
    simp only [pure, Except.pure, transcriptWords]
    have feature := feature_roundtrip construction image
    simp only [pending] at feature
    rw [feature, lifetime]
    simp [image.episodes]

/-- Every raw primary weight passes through the receiving rule at its exact index. -/
theorem restored_weight {config : Acorn.Config} {dimension : Dimension}
    (receiver : Managed config dimension) (image : KnowledgeImage dimension)
    (index : FeatIdx dimension) :
    ((receiver.restore image).state.weights.get index).value =
      (Weight.project config.rule (image.weights.get index)).value := by
  change ((receiver.state.restoreWeights image.weights.toList).weights.get index).value = _
  rw [CurrentLearner.restore_weights_get]
  simp [index.isLt, Vector.get]

/-- Every raw log step size uses the receiving learner's immutable rails. -/
theorem restored_beta {config : Acorn.Config} {dimension : Dimension}
    (receiver : Managed config dimension) (image : KnowledgeImage dimension)
    (index : FeatIdx dimension) :
    ((receiver.restore image).state.beta.get index).value =
      (LogStepSize.project receiver.state.rails (image.beta.get index)).value := by
  change (((receiver.state.restoreWeights image.weights.toList).restoreLogStepSizes
    image.beta.toList).beta.get index).value = _
  rw [CurrentLearner.restore_beta_get]
  simp [index.isLt, Vector.get]
  rfl

/-- Both legal signed-zero encodings and all other stored weight words stay warm. -/
theorem saved_weight_identity {config : Acorn.Config} {dimension : Dimension}
    (source receiver : Managed config dimension) (index : FeatIdx dimension) :
    ((receiver.restore (knowledge source)).state.weights.get index).value =
      (source.state.weights.get index).value := by
  rw [restored_weight]
  simp only [knowledge, Vector.get, Vector.toArray_map, Array.getElem_map]
  exact config.rule.domain.symmetric_project_identity _ (weight_legal _)

/-- Equal immutable configurations give identical receiver bounds for every saved beta. -/
theorem saved_beta_identity {config : Acorn.Config} {dimension : Dimension}
    (source receiver : Managed config dimension) (index : FeatIdx dimension) :
    ((receiver.restore (knowledge source)).state.beta.get index).value =
      (source.state.beta.get index).value := by
  rw [restored_beta]
  simp only [knowledge, Vector.get, Vector.toArray_map, Array.getElem_map]
  have legal := (source.state.beta.get index).legal
  have admitted : receiver.state.rails.range.Contains (source.state.beta.get index).value := by
    refine ⟨legal.1, ?_, ?_⟩
    · rw [receiver.state.rails.lowerIdentity, ← source.state.rails.lowerIdentity]
      exact legal.2.1
    · rw [receiver.state.rails.upperIdentity, ← source.state.rails.upperIdentity]
      exact legal.2.2
  exact receiver.state.rails.range.saturate_identity _ admitted

/-- Restoring knowledge clears all nine transient register arrays and their aggregates. -/
theorem restored_transient {config : Acorn.Config} {dimension : Dimension}
    (receiver : Managed config dimension) (image : KnowledgeImage dimension) :
    (receiver.restore image).state.transient = TransientState.zero dimension := rfl

/-- The preflight header decoder consumes the same header emitted by the complete writer. -/
theorem encoded_header (dimension : Dimension) (payload : Payload dimension) :
    ∃ rest, headerCodec.decode ((encode dimension payload).drop magic.length) = some
      (payload.header, rest) := by
  simp only [Checkpoint.encode, payloadCodec, Codec.iso, Codec.pair, List.append_assoc,
    List.drop_left]
  rw [headerCodec.roundtrip]
  exact ⟨_, rfl⟩

/-- All encoded payloads contain the minimum magic, header and checksum framing. -/
theorem encoded_minimum (dimension : Dimension) (payload : Payload dimension) :
    72 ≤ (encode dimension payload).length := by
  rw [encoded_size]
  simp only [payloadBytes]
  omega

/-- The actual complete-candidate loader round-trips every admitted typed image. -/
theorem candidate_roundtrip (construction : AgentConstruction)
    (image : AgentImage construction.config construction.criterion construction.dimension)
    (supported : construction.profile.checkpointSupported = true) :
    loadCandidate construction (encode construction.dimension (imagePayload construction image)) =
      .ok image := by
  have large := encoded_minimum construction.dimension (imagePayload construction image)
  obtain ⟨rest, header⟩ := encoded_header construction.dimension (imagePayload construction image)
  have magicOk : (encode construction.dimension (imagePayload construction image)).take
    magic.length = magic := by
    simp [Checkpoint.encode, List.append_assoc]
  unfold loadCandidate
  simp only [show ¬(encode construction.dimension (imagePayload construction image)).length < 72
    by omega,
    decide_false, magicOk, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, header]
  rw [header_roundtrip construction image supported]
  simp only [bind, Except.bind, roundtrip]
  exact image_roundtrip construction image supported

/-- Saving any supported agent and loading into a matching receiver reaches exactly the
existing cold restoration, without requiring equality of their transient state. -/
theorem save_load (construction : AgentConstruction) (source receiver : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    ∃ restored, receiver.restore (snapshotImage construction source) = some restored ∧
      load construction receiver (encode construction.dimension (snapshot construction source)) =
        .ok restored := by
  have existsRestore : ∃ restored, receiver.restore (snapshotImage construction source) = some
    restored := by
    simp [Agent.restore, supported]
  obtain ⟨restored, restore⟩ := existsRestore
  refine ⟨restored, restore, ?_⟩
  unfold load snapshot
  rw [candidate_roundtrip construction (snapshotImage construction source) supported]
  simp only [bind, Except.bind]
  rw [restore]
  rfl

end AcornVerif.CurrentCheckpoint
