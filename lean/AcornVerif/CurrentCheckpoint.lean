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

These statements concern the actual format-18 parser, writer, legal-state
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
  rw [dite_eq_left valid]

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
theorem header_roundtrip (construction : AgentConstruction) (image : construction.Image)
    (supported : construction.profile.checkpointSupported = true) :
    admitHeader construction (imagePayload construction image).header = .ok image.image.gain := by
  have units : construction.config.units.count.toUInt32.toNat = construction.config.units.count :=
    Nat.mod_eq_of_lt (by have := construction.config.units.bounded; omega)
  have gain : RewardRate.admit image.image.gain.value = some image.image.gain :=
    Bounded32.admit_self image.image.gain
  simp [admitHeader, imagePayload, supported, gain, units]
  rfl

/-- Raw feature words reconstruct the exact saved progress, objectives and primary image. -/
theorem feature_roundtrip (construction : AgentConstruction)
    (image : AgentImage Grid.interface construction.config construction.criterion
      construction.dimension) :
    FeatureImage.admit construction.config construction.criterion construction.dimension
      ⟨construction.config.seed, construction.config.tilings,
        construction.config.units.count.toUInt32.toUInt16,
       construction.dimension.capacity.toUInt32, construction.criterion.tag.toUInt32.toUInt8,
       image.features.progress.clock, (testerWords image.features.progress).progress,
       image.features.assignments.map (Assignment.words construction.dimension),
       image.features.primary⟩ = some image.features := by
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
  rw [show (testerWords image.features.progress).progress = image.features.progress.words from rfl,
    Progress.words_roundtrip]
  simp only [bind, Option.bind]
  rw [vector_roundtrip _ _ (Assignment.words_roundtrip construction.dimension)]
  simp [(Assignment.distinct_iff _).mpr image.features.distinct]

/-- Full admission preserves every image of a construction, including both signed-zero
encodings: the admission of the payload of an image is that image. -/
theorem image_roundtrip (construction : AgentConstruction) (image : construction.Image)
    (supported : construction.profile.checkpointSupported = true) :
    admitPayload construction (imagePayload construction image) = .ok image := by
  unfold admitPayload
  rw [header_roundtrip construction image supported]
  simp only [bind, Except.bind]
  have lifetime := lifetime_roundtrip image.image.lifetime image.image.episodes
  simp only [imagePayload, pure, Except.pure]
  have feature := feature_roundtrip construction image.image
  rw [feature, lifetime]
  simp [image.image.episodes]

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
  simp only [knowledge, Vector.get, Vector.toArray_map, Array.getElem_map, Weight.project_eq]
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

/-- The actual complete-candidate loader round-trips every image of a construction. -/
theorem candidate_roundtrip (construction : AgentConstruction) (image : construction.Image)
    (supported : construction.profile.checkpointSupported = true) :
    loadCandidate construction
        (encode construction.dimension (imagePayload construction image)) = .ok image := by
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
    ∃ restored : construction.State,
      receiver.agent.restore (snapshotImage construction source).image = some restored.agent ∧
      load construction receiver (encode construction.dimension (snapshot construction source)) =
        .ok restored := by
  have existsRestore : ∃ next,
      receiver.agent.restore (snapshotImage construction source).image = some next := by
    simp [Agent.restore, supported]
  obtain ⟨next, restore⟩ := existsRestore
  have candidate := candidate_roundtrip construction (snapshotImage construction source) supported
  have typed := receiver.restore_agent (snapshotImage construction source)
  rw [restore] at typed
  unfold load snapshot
  rw [candidate]
  cases restored : receiver.restore (snapshotImage construction source) with
  | none =>
    rw [restored] at typed
    cases typed
  | some state =>
    rw [restored] at typed
    refine ⟨state, ?_, ?_⟩
    · rw [restore]
      exact (congrArg some (Option.some.inj typed)).symm
    · simp only [bind, Except.bind, restored]
      rfl

/-- **A save writes the order word of the state's own construction.** For every
construction, state and byte list: when `saveBytes` returns the bytes, the header codec
reads from them a header whose order word is the stored word of the construction's order
(`StepOrder.Stored`). `saveBytes` takes the state of a construction and no order word;
`Store.save` writes these bytes. -/
theorem saved_header (construction : AgentConstruction) (state : construction.State)
    (bytes : List UInt8) (saved : saveBytes construction state = .ok bytes) :
    ∃ header rest, headerCodec.decode (bytes.drop magic.length) = some (header, rest) ∧
      StepOrder.Stored header.order construction.order := by
  unfold saveBytes at saved
  split at saved
  · cases saved
    obtain ⟨rest, decoded⟩ := encoded_header construction.dimension (snapshot construction state)
    exact ⟨_, rest, decoded, (StepOrder.tag_stored _ _).mp rfl⟩
  · cases saved

/-- **Bytes that one construction saved are admitted by a second only under the same
order.** For every two constructions, every state of the first, byte list and image of
the second: when the first saves the bytes and the loader of the second admits them, the
two step orders are equal. The statement is about bytes that a save of this project
wrote; a file is not authenticated, so an edit of its order word is outside it. -/
theorem saved_admitted_order (saver receiver : AgentConstruction) (state : saver.State)
    (bytes : List UInt8) (image : receiver.Image)
    (saved : saveBytes saver state = .ok bytes)
    (loaded : loadCandidate receiver bytes = .ok image) : receiver.order = saver.order := by
  obtain ⟨written, rest, wrote, stamped⟩ := saved_header saver state bytes saved
  obtain ⟨read, tail, gain, decoded, admitted⟩ := loadCandidate_header receiver bytes image loaded
  rw [wrote] at decoded
  cases decoded
  exact StepOrder.stored_injective _ _ _ admitted.order stamped

/-- **A relabel of an image in memory is an edit of the order word.** For every profile,
criterion, planning selection, feature configuration and dimension, every two step
orders and every image of the construction of the first order: the payload of the same
durable data as an image of the construction of the second order is the payload of the
image with its order word replaced by the word of the second order, and with no other
change. The statement names the constructor of the image, which a definition outside the
owning modules cannot do; it says what such a definition would make. -/
theorem relabeled_payload (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (config : Features.Config) (dimension : Dimension)
    (first second : StepOrder)
    (image : (AgentConstruction.mk profile criterion planning first config dimension).Image) :
    imagePayload ⟨profile, criterion, planning, second, config, dimension⟩ ⟨image.image⟩ =
      { imagePayload ⟨profile, criterion, planning, first, config, dimension⟩ image with
        header := { (imagePayload ⟨profile, criterion, planning, first, config, dimension⟩
          image).header with order := second.tag } } := rfl

/-- **The second construction admits that edited payload, and returns the relabeled
image.** For the same arguments and a profile that has a resumable image: the admission
of the payload with the replaced order word, by the construction of the second order,
returns the image with the same durable data. So a relabeled image in memory is the value
that the second construction gets from the first construction's payload after an edit of
the order word. No predicate on the durable data separates the two. The statement is for
a profile that has a resumable image; for another profile no payload is admitted. -/
theorem relabeled_admitted (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (config : Features.Config) (dimension : Dimension)
    (first second : StepOrder)
    (image : (AgentConstruction.mk profile criterion planning first config dimension).Image)
    (supported : profile.checkpointSupported = true) :
    admitPayload ⟨profile, criterion, planning, second, config, dimension⟩
        { imagePayload ⟨profile, criterion, planning, first, config, dimension⟩ image with
          header := { (imagePayload ⟨profile, criterion, planning, first, config, dimension⟩
            image).header with order := second.tag } } =
      .ok ⟨image.image⟩ := by
  rw [← relabeled_payload profile criterion planning config dimension first second image]
  exact image_roundtrip ⟨profile, criterion, planning, second, config, dimension⟩
    ⟨image.image⟩ supported

/-- **The loader of the second construction admits the bytes of that edited payload.**
For the same arguments and a profile that has a resumable image: the complete-candidate
loader of the construction of the second order, on the encoding of the payload with the
replaced order word, returns the image with the same durable data. The encoding has the
checksum of the edited payload: a checkpoint file is not authenticated, so a writer that
replaces the order word can write that checksum. -/
theorem relabeled_loaded (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (config : Features.Config) (dimension : Dimension)
    (first second : StepOrder)
    (image : (AgentConstruction.mk profile criterion planning first config dimension).Image)
    (supported : profile.checkpointSupported = true) :
    loadCandidate ⟨profile, criterion, planning, second, config, dimension⟩
        (encode dimension
          { imagePayload ⟨profile, criterion, planning, first, config, dimension⟩ image with
            header := { (imagePayload ⟨profile, criterion, planning, first, config, dimension⟩
              image).header with order := second.tag } }) =
      .ok ⟨image.image⟩ := by
  rw [← relabeled_payload profile criterion planning config dimension first second image]
  exact candidate_roundtrip ⟨profile, criterion, planning, second, config, dimension⟩
    ⟨image.image⟩ supported

end AcornVerif.CurrentCheckpoint
