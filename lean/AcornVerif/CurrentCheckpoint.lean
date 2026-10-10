/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Size
import AcornVerif.CurrentImage

/-!
# The exact save and restore

These statements concern the executed format-19 writer, frame, admission and loader and the
agent's restore. Loading the bytes that a save of a state writes returns that state, every
field of its agent included (`load_saved`), for every state of every construction of a
resumable profile. The proof composes three exact layers: the image format reads exactly the
encodings of agent images (`CurrentImage.imageFormat_exact`), the header codec and frame
read back the header, body and checksum they write (`Checkpoint.roundtrip`), and the restore
replaces every field of the receiver (`Agent.restore_exact`).

What stays trusted: native file IO (`Store.save` writes the byte list as a byte array,
`loadFile` reads it back through `readBounded`), the runtime and the OS. The byte layer,
encoding and decoding between values and `List UInt8`, is proved here; the conversion between
that list and the `ByteArray` of a file is the structure's own field. A file is not
authenticated: the checksum detects accidental mutation only.
-/
namespace AcornVerif.CurrentCheckpoint
open Acorn Acorn.Checkpoint Acorn.Features Acorn.Handcrafted Acorn.Lifetime

/-- The exact receiver identity and supported-profile header is admitted without normalization. -/
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

/-- **Payload admission returns the image whose payload it reads.** For every construction of
a resumable profile and every image of it. -/
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

/-- The preflight header decoder consumes the same header emitted by the complete writer. -/
theorem encoded_header (payload : Payload) :
    ∃ rest, headerCodec.decode ((encode payload).drop magic.length) =
      some (payload.header, rest) := by
  simp only [Checkpoint.encode, Payload.signed, List.append_assoc, List.drop_left]
  rw [headerCodec.roundtrip]
  exact ⟨_, rfl⟩

/-- All encoded payloads contain the minimum magic, header and checksum framing. -/
theorem encoded_minimum (payload : Payload) : 72 ≤ (encode payload).length := by
  rw [encoded_size]
  omega

/-- The actual complete-candidate loader returns every image of a construction from its
encoded payload. -/
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

/-- **Loading a saved state returns the state that was saved.** For every construction, every
receiver and every state of it, and every byte list: when `saveBytes` writes the bytes,
`load` returns exactly the saved state, every field of its agent: learners and their
transient registers, option models, off-policy questions, primitive credit, the rate
schedule, every process-local reference and every lifetime observation. The receiver's
state does not matter. -/
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
      simp only [AgentConstruction.State.restore, supported, ↓reduceIte]
      exact congrArg Except.ok (AgentConstruction.State.ext rfl)
  · cases saved

/-- A supported construction's save writes bytes, so `load_saved` applies to every state of
it. -/
theorem save_load (construction : AgentConstruction) (receiver state : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    load construction receiver (encode (snapshot construction state)) = .ok state :=
  load_saved construction receiver state _ (save_supported construction state supported)

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
    obtain ⟨rest, decoded⟩ := encoded_header (snapshot construction state)
    exact ⟨_, rest, decoded, (StepOrder.tag_stored _ _).mp rfl⟩
  · cases saved

/-- **Bytes that one construction saved are admitted by a second only under the same
order.** For every two constructions, every state of the first, byte list and image of the
second: when the first saves the bytes and the loader of the second admits them, the two
step orders are equal. The statement is about bytes that a save of this project wrote; a
file is not authenticated, so an edit of its order word is outside it. -/
theorem saved_admitted_order (saver receiver : AgentConstruction) (state : saver.State)
    (bytes : List UInt8) (image : receiver.Image)
    (saved : saveBytes saver state = .ok bytes)
    (loaded : loadCandidate receiver bytes = .ok image) : receiver.order = saver.order := by
  obtain ⟨written, rest, wrote, stamped⟩ := saved_header saver state bytes saved
  obtain ⟨read, tail, gain, decoded, admitted⟩ := loadCandidate_header receiver bytes image loaded
  rw [wrote] at decoded
  cases decoded
  exact StepOrder.stored_injective _ _ _ admitted.order stamped

/-- The image format of a construction writes the agent image of the image. -/
theorem imageFormat_encode (construction : AgentConstruction) (image : construction.Image) :
    (imageFormat construction).encode image =
      (agentImageFormat Grid.interface construction.profile construction.config
        construction.criterion construction.dimension).encode image.image := by
  unfold imageFormat Format.map Format.filterMap
  rfl

/-- **A relabel of an image in memory is an edit of the order word.** For every profile,
criterion, planning selection, feature configuration and dimension, every two step
orders and every image of the construction of the first order: the payload of the same
agent image as an image of the construction of the second order is the payload of the
image with its order word replaced by the word of the second order, and with no other
change. The statement names the public constructor of the image, which every module can
apply. -/
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

/-- **The second construction admits that edited payload, and returns the relabeled
image.** For the same arguments and a profile that has a resumable image: the admission
of the payload with the replaced order word, by the construction of the second order,
returns the image with the same agent image. No predicate on the agent separates the two.
The statement is for a profile that has a resumable image; for another profile no payload
is admitted. -/
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
replaced order word, returns the image with the same agent image. The encoding has the
checksum of the edited payload: a checkpoint file is not authenticated, so a writer that
replaces the order word can write that checksum. -/
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

/-- **The loader of a resumable construction reaches every agent of it.** For every
construction of a resumable profile and every agent of its type, the construction reaches the
agent: the loader admits the encoding of the agent's image under the construction's own
header (`candidate_roundtrip`). So the reachability that a state carries does not separate
the agents of two orders through the checkpoint: a relabel of a state of another order
goes through bytes that this construction's loader admits, which a save of the other order
does not write (`saved_admitted_order`) and an edit of the order word with its checksum does
(`relabeled_loaded`). -/
theorem loader_reaches (construction : AgentConstruction)
    (agent : Agent Grid.interface construction.profile construction.config
      construction.criterion construction.dimension construction.planning)
    (supported : construction.profile.checkpointSupported = true) : construction.Reached agent :=
  .loaded (candidate_roundtrip construction ⟨agent.image⟩ supported)

/-- **A profile without a resumable image admits no bytes.** For every construction whose
profile is not resumable, every byte list and every image, the loader does not return the
image: header admission refuses the profile. So every agent such a construction reaches is
reached from the cold state by its own steps and observation writes. -/
theorem unresumable_unloaded (construction : AgentConstruction) (bytes : List UInt8)
    (image : construction.Image) (unsupported : construction.profile.checkpointSupported = false) :
    loadCandidate construction bytes ≠ .ok image := by
  intro loaded
  obtain ⟨header, rest, gain, _, admitted⟩ := loadCandidate_header construction bytes image loaded
  have supported := (FeatureProfile.checkpoint_iff _).mpr admitted.supported
  rw [unsupported] at supported
  cases supported

/-- A stored word below 256 is its low byte and three zero bytes. -/
theorem u32_small (word : UInt32) (small : word.toNat < 256) :
    u32Codec.encode word = [UInt8.ofNat word.toNat, 0, 0, 0] := by
  simp [u32Codec, Codec.iso, wordCodec, encodeNat, Nat.div_eq_of_lt small]

/-- The signed bytes of a payload are one prefix and one suffix around the four bytes of
its order word, whatever that word is. -/
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

/-- **An edit of the order word alone does not decode.** For every payload and word that
differs from the payload's order word, both below 256: the file bytes of the payload with the
order word replaced and the checksum word of the original payload are refused by the frame
decoder. The stored words of the step orders are below 256 (`StepOrder.tag`), and two of
them differ in one byte, which the checksum separates (`Rng.fnv_byte`). An edit that also
writes the checksum of the edited bytes is outside this statement and is admitted
(`relabeled_loaded`): the checksum detects a mutation and authenticates nothing. -/
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

/-- A loaded candidate decoded as a complete frame. -/
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

/-- **No loader admits an edit of the order word alone.** For every construction, every
payload and every word that differs from the payload's order word, both below 256: the
loader of the construction returns no image for the file bytes of the payload with the order
word replaced and the checksum word of the original payload. So a file whose order word
alone was changed to the word of another order is refused by the loader of every order. -/
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

/-- **A file whose order word alone is replaced by the word of another order is refused.**
For every receiving construction, every payload whose order word is the stored word of one
order, and every other order: the loader returns no image for the file bytes of the payload
with the order word replaced by the word of the other order and the checksum word of the
original payload. The receiving construction is arbitrary, so the loader of the other order
refuses the file as well. -/
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
