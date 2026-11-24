import Acorn.Host.Checkpoint.Size
import AcornVerif.CurrentImage

namespace AcornVerif.CurrentCheckpoint
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime

theorem header_roundtrip (construction : AgentConstruction) (image : construction.Image)
    (supported : construction.profile.checkpointSupported = true) :
    admitHeader construction (imagePayload construction image).header =
      .ok image.image.control.average.rate := by
  have units : construction.config.units.count.toUInt32.toNat = construction.config.units.count :=
    Nat.mod_eq_of_lt (by have := construction.config.units.bounded; omega)
  have gain : RewardRate.admit image.image.control.average.rate.value =
      some image.image.control.average.rate :=
    Bounded32.admit_self image.image.control.average.rate
  have resumable : construction.profile.Resumable :=
    construction.profile.checkpoint_iff.mp supported
  simp [admitHeader, imagePayload, supported, resumable, gain, units]
  rfl

theorem image_roundtrip (construction : AgentConstruction) (image : construction.Image)
    (supported : construction.profile.checkpointSupported = true) :
    admitPayload construction (imagePayload construction image) = .ok image := by
  have decoded := (CurrentImage.imageFormat_exact construction).lawful image []
  rw [List.append_nil] at decoded
  unfold admitPayload
  rw [header_roundtrip construction image supported]
  simp only [bind, Except.bind]
  simp only [imagePayload] at decoded ⊢
  rw [decoded]
  simp [pure, Except.pure]

theorem encoded_header (payload : Payload) :
    ∃ rest, headerCodec.decode ((encode payload).drop magic.length) =
      some (payload.header, rest) := by
  simp only [Checkpoint.encode, Payload.signed, List.append_assoc, List.drop_left]
  rw [headerCodec.roundtrip]
  exact ⟨_, rfl⟩

theorem encoded_minimum (payload : Payload) : 72 ≤ (encode payload).length := by
  rw [encoded_size]
  omega

theorem candidate_roundtrip (construction : AgentConstruction) (image : construction.Image)
    (supported : construction.profile.checkpointSupported = true) :
    loadCandidate construction (encode (imagePayload construction image)) = .ok image := by
  have large := encoded_minimum (imagePayload construction image)
  obtain ⟨rest, header⟩ := encoded_header (imagePayload construction image)
  have magicOk : (encode (imagePayload construction image)).take magic.length = magic := by
    simp [Checkpoint.encode, List.append_assoc]
  unfold loadCandidate
  simp only [show ¬(encode (imagePayload construction image)).length < 72 by omega,
    decide_false, magicOk, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    header]
  rw [header_roundtrip construction image supported]
  simp only [bind, Except.bind, roundtrip]
  exact image_roundtrip construction image supported

theorem load_saved (construction : AgentConstruction) (receiver state : construction.State)
    (bytes : List UInt8) (saved : saveBytes construction state = .ok bytes) :
    load construction receiver bytes = .ok state := by
  unfold saveBytes at saved
  split at saved
  · rename_i supported
    cases saved
    have candidate : loadCandidate construction (encode (snapshot construction state)) =
        .ok (stateImage construction state) :=
      candidate_roundtrip construction (stateImage construction state) supported
    unfold load
    split
    · rename_i error refused
      rw [candidate] at refused
      cases refused
    · rename_i image admitted
      have same : stateImage construction state = image := by
        rw [candidate] at admitted
        exact Except.ok.inj admitted
      subst same
      obtain ⟨restored, found, agent⟩ := AgentConstruction.State.restore_exact receiver
        (stateImage construction state) ⟨_, admitted⟩ supported
      rw [found]
      exact congrArg Except.ok (AgentConstruction.State.ext agent)
  · cases saved

theorem save_load (construction : AgentConstruction) (receiver state : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    load construction receiver (encode (snapshot construction state)) = .ok state :=
  load_saved construction receiver state _ (save_supported construction state supported)

theorem resume_saved (construction : AgentConstruction) (receiver state : construction.State)
    (bytes : List UInt8) (saved : saveBytes construction state = .ok bytes) :
    resume construction receiver bytes = .ok state.beginSession := by
  unfold resume
  rw [load_saved construction receiver state bytes saved]
  rfl

theorem resume_records (construction : AgentConstruction) (receiver state : construction.State)
    (bytes : List UInt8) (saved : saveBytes construction state = .ok bytes) :
    ∃ resumed, resume construction receiver bytes = .ok resumed ∧
      resumed.agent = state.agent.beginSession ∧
      ∀ clock cumulants predictions,
        (resumed.agent.control.lifetime.recordDemons clock cumulants
          predictions).agreementLastClock = some clock :=
  ⟨state.beginSession, resume_saved construction receiver state bytes saved, rfl,
    fun clock cumulants predictions =>
      Lifetime.Stats.recordDemons_live _ clock cumulants predictions rfl⟩

theorem saved_header (construction : AgentConstruction) (state : construction.State)
    (bytes : List UInt8) (saved : saveBytes construction state = .ok bytes) :
    ∃ header rest, headerCodec.decode (bytes.drop magic.length) = some (header, rest) ∧
      StepOrder.Stored header.order construction.order := by
  unfold saveBytes at saved
  split at saved
  · cases saved
    obtain ⟨rest, decoded⟩ := encoded_header (snapshot construction state)
    exact ⟨_, rest, decoded, (StepOrder.tag_stored _ _).mp rfl⟩
  · cases saved

theorem saved_admitted_order (saver receiver : AgentConstruction) (state : saver.State)
    (bytes : List UInt8) (image : receiver.Image)
    (saved : saveBytes saver state = .ok bytes)
    (loaded : loadCandidate receiver bytes = .ok image) : receiver.order = saver.order := by
  obtain ⟨written, rest, wrote, stamped⟩ := saved_header saver state bytes saved
  obtain ⟨read, tail, gain, decoded, admitted⟩ := loadCandidate_header receiver bytes image loaded
  rw [wrote] at decoded
  cases decoded
  exact StepOrder.stored_injective _ _ _ admitted.order stamped

theorem imageFormat_encode (construction : AgentConstruction) (image : construction.Image) :
    (imageFormat construction).encode image =
      (agentImageFormat Grid.interface construction.profile construction.config
        construction.criterion construction.dimension).encode image.image := by
  unfold imageFormat Format.map Format.filterMap
  rfl

theorem relabeled_payload (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (config : Features.Config) (dimension : Dimension)
    (first second : StepOrder)
    (image : (AgentConstruction.mk profile criterion planning first config dimension).Image) :
    imagePayload ⟨profile, criterion, planning, second, config, dimension⟩ ⟨image.image⟩ =
      { imagePayload ⟨profile, criterion, planning, first, config, dimension⟩ image with
        header := { (imagePayload ⟨profile, criterion, planning, first, config, dimension⟩
          image).header with order := second.tag } } := by
  unfold imagePayload
  rw [imageFormat_encode, imageFormat_encode]

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

theorem relabeled_loaded (profile : FeatureProfile) (criterion : Criterion)
    (planning : PlanningSelection) (config : Features.Config) (dimension : Dimension)
    (first second : StepOrder)
    (image : (AgentConstruction.mk profile criterion planning first config dimension).Image)
    (supported : profile.checkpointSupported = true) :
    loadCandidate ⟨profile, criterion, planning, second, config, dimension⟩
        (encode
          { imagePayload ⟨profile, criterion, planning, first, config, dimension⟩ image with
            header := { (imagePayload ⟨profile, criterion, planning, first, config, dimension⟩
              image).header with order := second.tag } }) =
      .ok ⟨image.image⟩ := by
  rw [← relabeled_payload profile criterion planning config dimension first second image]
  exact candidate_roundtrip ⟨profile, criterion, planning, second, config, dimension⟩
    ⟨image.image⟩ supported

theorem loader_reaches (construction : AgentConstruction)
    (agent : Agent Grid.interface construction.profile construction.config
      construction.criterion construction.dimension construction.planning)
    (supported : construction.profile.checkpointSupported = true) : construction.Reached agent :=
  .loaded (candidate_roundtrip construction ⟨agent.image⟩ supported)

theorem unresumable_unloaded (construction : AgentConstruction) (bytes : List UInt8)
    (image : construction.Image) (unsupported : construction.profile.checkpointSupported = false) :
    loadCandidate construction bytes ≠ .ok image := by
  intro loaded
  obtain ⟨header, rest, gain, _, admitted⟩ := loadCandidate_header construction bytes image loaded
  have supported := (FeatureProfile.checkpoint_iff _).mpr admitted.supported
  rw [unsupported] at supported
  cases supported

theorem previous_generation_unloaded (construction : AgentConstruction) (bytes : List UInt8)
    (header : Header) (rest : List UInt8)
    (decoded : headerCodec.decode (bytes.drop magic.length) = some (header, rest))
    (previous : header.version < 21) (image : construction.Image) :
    loadCandidate construction bytes ≠ .ok image := by
  intro loaded
  obtain ⟨found, _, _, again, admitted⟩ := loadCandidate_header construction bytes image loaded
  rw [decoded, Option.some.injEq, Prod.mk.injEq] at again
  obtain ⟨rfl, -⟩ := again
  rw [admitted.version] at previous
  exact absurd previous (by decide)

theorem u32_small (word : UInt32) (small : word.toNat < 256) :
    u32Codec.encode word = [UInt8.ofNat word.toNat, 0, 0, 0] := by
  simp [u32Codec, Codec.iso, wordCodec, encodeNat, Nat.div_eq_of_lt small]

theorem order_bytes (payload : Payload) :
    ∃ before after, ∀ word : UInt32,
      { payload with header := { payload.header with order := word } }.signed =
        before ++ u32Codec.encode word ++ after := by
  refine ⟨u32Codec.encode payload.header.version ++ u32Codec.encode payload.header.capacity ++
      u32Codec.encode payload.header.learners ++ u64Codec.encode payload.header.seed ++
      u64Codec.encode payload.header.clock ++ u32Codec.encode payload.header.criterion ++
      binary32Codec.encode payload.header.gain ++ u64Codec.encode payload.header.tilings ++
      u32Codec.encode payload.header.units ++ u32Codec.encode payload.header.supported,
    payload.body, fun word => ?_⟩
  simp only [Payload.signed, headerCodec, Codec.iso, Codec.pair, List.append_assoc]

theorem order_edit_refused (payload : Payload) (word : UInt32)
    (differs : word ≠ payload.header.order) (small : word.toNat < 256)
    (stored : payload.header.order.toNat < 256) :
    decode (magic ++ { payload with header := { payload.header with order := word } }.signed ++
      u64Codec.encode (Rng.fnv payload.signed)) = none := by
  have separated : Rng.fnv payload.signed ≠
      Rng.fnv { payload with header := { payload.header with order := word } }.signed := by
    obtain ⟨before, after, bytes⟩ := order_bytes payload
    have original : payload.signed = before ++ u32Codec.encode payload.header.order ++ after :=
      bytes payload.header.order
    intro same
    rw [original, bytes word, u32_small _ stored, u32_small _ small] at same
    simp only [List.append_assoc, List.cons_append, List.nil_append] at same
    have low := congrArg UInt8.toNat (Rng.fnv_byte before _ _ _ same)
    simp only [UInt8.toNat_ofNat'] at low
    have words : word.toNat = payload.header.order.toNat := by omega
    exact differs (UInt32.toNat_inj.mp words)
  rw [decode_frame, ite_eq_right separated]

theorem loadCandidate_decoded (construction : AgentConstruction) (bytes : List UInt8)
    (image : construction.Image) (loaded : loadCandidate construction bytes = .ok image) :
    ∃ payload, decode bytes = some payload := by
  unfold loadCandidate at loaded
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at loaded
  split at loaded
  · cases loaded
  · cases decoded : headerCodec.decode (bytes.drop magic.length) with
    | none =>
      rw [decoded] at loaded
      cases loaded
    | some found =>
      rw [decoded] at loaded
      dsimp only at loaded
      cases admitted : admitHeader construction found.1 with
      | error refusal =>
        rw [admitted] at loaded
        cases loaded
      | ok gain =>
        rw [admitted] at loaded
        dsimp only at loaded
        cases framed : decode bytes with
        | none =>
          rw [framed] at loaded
          cases loaded
        | some payload => exact ⟨payload, rfl⟩

theorem order_edit_unloaded (construction : AgentConstruction) (payload : Payload)
    (word : UInt32) (differs : word ≠ payload.header.order) (small : word.toNat < 256)
    (stored : payload.header.order.toNat < 256) (image : construction.Image) :
    loadCandidate construction (magic ++
        { payload with header := { payload.header with order := word } }.signed ++
      u64Codec.encode (Rng.fnv payload.signed)) ≠ .ok image := by
  intro loaded
  obtain ⟨decoded, framed⟩ := loadCandidate_decoded construction _ image loaded
  rw [order_edit_refused payload word differs small stored] at framed
  cases framed

theorem relabeled_unloaded (construction : AgentConstruction) (payload : Payload)
    (saved replaced : StepOrder) (word : payload.header.order = saved.tag)
    (other : replaced ≠ saved) (image : construction.Image) :
    loadCandidate construction (magic ++
        { payload with header := { payload.header with order := replaced.tag } }.signed ++
      u64Codec.encode (Rng.fnv payload.signed)) ≠ .ok image :=
  order_edit_unloaded construction payload replaced.tag
    (by rw [word]; exact fun same => other (StepOrder.tag_injective _ _ same))
    replaced.tag_small (by rw [word]; exact saved.tag_small) image

end AcornVerif.CurrentCheckpoint
