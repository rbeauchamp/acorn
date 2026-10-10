/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Frame
import Acorn.Host.Checkpoint.Image

/-!
# Receiver-bound checkpoint admission

Parsing has no receiver write capability. Exact header identity, including the step
order the image was saved under, is admitted first; the body is then read as the exact
image of an agent of the receiving construction (`imageFormat`), which admits every stored
word in its own domain and the invariants of every learner and of the agent. No word is
projected or repaired: an image is admitted whole or refused.
-/
namespace Acorn.Checkpoint
open Features Handcrafted Lifetime

/-- Explicit file, identity, profile and numeric refusal domains. -/
inductive Error where
  /-- Magic or minimum header framing is absent. -/
  | notACheckpoint
  /-- Unsupported layout or invariant generation. -/
  | version (found expected : UInt32)
  /-- The receiving Bellman criterion differs. -/
  | criterion (found expected : UInt32)
  /-- Feature capacity or complete primary count differs. -/
  | shape (foundCapacity expectedCapacity foundLearners expectedLearners : UInt32)
  /-- Feature seed differs. -/
  | seed (found expected : UInt64)
  /-- Sensory tilings or initial bank capacity differs. -/
  | representation
  /-- The image was saved under a different step order than the receiver declares. -/
  | order (found expected : UInt32)
  /-- This profile has no resumable image. -/
  | unsupportedPolicy
  /-- Length, checksum or image admission failed. -/
  | corrupt
  /-- The image is longer than the receiving construction's read limit (`maximumBytes`), so
  no file of it is written. -/
  | oversized
  deriving DecidableEq, Repr

/-- The currently supported generation. Every earlier generation is refused with its word:
an image of generation 18 or earlier holds no option model, off-policy question, primitive
credit, rate schedule or process-local reference, so no load of it could return the agent
that was saved. -/
def formatVersion : UInt32 := Acorn.FeatureConstants.checkpointFormatVersion.toUInt32

/-- Header validation precedes large shape-dependent decoding. -/
def admitHeader (construction : AgentConstruction) (header : Header) : Except Error RewardRate := do
  if header.version != formatVersion then throw (.version header.version formatVersion)
  let criterion := construction.criterion.tag.toUInt32
  if header.criterion != criterion then throw (.criterion header.criterion criterion)
  let some gain := RewardRate.admit header.gain | throw .corrupt
  let capacity := construction.dimension.capacity.toUInt32
  let learners := primaryCount.toUInt32
  if header.capacity != capacity || header.learners != learners then
    throw (.shape header.capacity capacity header.learners learners)
  if header.seed != construction.config.seed then throw (.seed header.seed construction.config.seed)
  if !construction.profile.checkpointSupported || header.supported != 1 then throw .unsupportedPolicy
  if header.tilings != construction.config.tilings || header.units.toNat != construction.config.units.count then
    throw .representation
  if header.order != construction.order.tag then throw (.order header.order construction.order.tag)
  return gain

/-- The complete specification of header admission: every condition under which a header
is the header of an image that the receiving construction admits, with the reward rate it
yields. Each field is stated on the stored words and on the typed values, and calls no
function that the admission executes: the words are numerals, the receiver's choices are
its constructors, and the reward rate is the returned typed value. -/
structure HeaderAdmitted (construction : AgentConstruction) (header : Header)
    (gain : RewardRate) : Prop where
  /-- The format generation is 19. -/
  version : header.version = 19
  /-- The criterion word is the word of the receiver's criterion: 0 for the discounted
  criterion and 1 for the differential one. -/
  criterion : (header.criterion = 0 ∧ construction.criterion = .discounted) ∨
    (header.criterion = 1 ∧ construction.criterion = .differential)
  /-- The returned rate holds the stored reward-rate word. A rate is a word of the reward
  range by its type, so a stored word outside that range has no rate. -/
  gain : gain.value = header.gain
  /-- The stored capacity has the value of the receiver's weight space. -/
  capacity : header.capacity.toNat = construction.dimension.capacity
  /-- The stored learner count is 51: 9 primitive learners, 4 meta learners, 3 times 9
  option learners and 11 demon learners. -/
  learners : header.learners = 51
  /-- The feature salt is the receiver's. -/
  seed : header.seed = construction.config.seed
  /-- The receiving profile is the full learned profile with the declared rate, which is
  the one profile that has a resumable image. -/
  supported : construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
    construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned
  /-- The image was saved by a profile that has a resumable image. -/
  policy : header.supported = 1
  /-- The tiling count is the receiver's. -/
  tilings : header.tilings = construction.config.tilings
  /-- The stored unit capacity has the value of the receiver's. -/
  units : header.units.toNat = construction.config.units.count
  /-- The step order word is the stored word of the receiver's order. -/
  order : StepOrder.Stored header.order construction.order

/-- The checks of header admission in the terms the implementation writes them. This is
a step of the proof of `admitHeader_iff`; the specification is `HeaderAdmitted`. -/
theorem admitHeader_checks (construction : AgentConstruction) (header : Header)
    (gain : RewardRate) :
    admitHeader construction header = .ok gain ↔
      header.version = formatVersion ∧
        header.criterion = construction.criterion.tag.toUInt32 ∧
        RewardRate.admit header.gain = some gain ∧
        header.capacity = construction.dimension.capacity.toUInt32 ∧
        header.learners = primaryCount.toUInt32 ∧
        header.seed = construction.config.seed ∧
        construction.profile.checkpointSupported = true ∧
        header.supported = 1 ∧
        header.tilings = construction.config.tilings ∧
        header.units.toNat = construction.config.units.count ∧
        header.order = construction.order.tag := by
  constructor
  · intro admitted
    unfold admitHeader at admitted
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
      at admitted
    repeat' split at admitted
    all_goals first
      | (cases admitted; done)
      | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all)
  · rintro ⟨version, criterion, admittedGain, capacity, learners, seed, supported, policy,
      tilings, units, order⟩
    simp [admitHeader, version, criterion, admittedGain, capacity, learners, seed, supported,
      policy, tilings, units, order, pure, Except.pure]

/-- **Header admission is exactly its specification.** For every construction, header
and reward rate, the executed admission returns the rate exactly when the header meets
every condition of `HeaderAdmitted`. -/
theorem admitHeader_iff (construction : AgentConstruction) (header : Header) (gain : RewardRate) :
    admitHeader construction header = .ok gain ↔ HeaderAdmitted construction header gain := by
  rw [admitHeader_checks]
  constructor
  · rintro ⟨version, criterion, admittedGain, capacity, learners, seed, supported, policy,
      tilings, units, order⟩
    exact
      { version := version
        criterion := by
          cases chosen : construction.criterion with
          | discounted =>
            rw [chosen] at criterion
            exact .inl ⟨criterion, rfl⟩
          | differential =>
            rw [chosen] at criterion
            exact .inr ⟨criterion, rfl⟩
        gain := (Bounded32.admit_exact _ _ _ admittedGain).1
        capacity := by
          rw [capacity]
          exact Nat.mod_eq_of_lt construction.dimension.wordBound
        learners := learners
        seed := seed
        supported := (FeatureProfile.checkpoint_iff _).mp supported
        policy := policy
        tilings := tilings
        units := units
        order := (StepOrder.tag_stored _ _).mp order.symm }
  · intro specified
    refine ⟨specified.version, ?_, ?_, ?_, specified.learners, specified.seed,
      (FeatureProfile.checkpoint_iff _).mpr specified.supported, specified.policy,
      specified.tilings, specified.units, ((StepOrder.tag_stored _ _).mpr specified.order).symm⟩
    · rcases specified.criterion with ⟨word, chosen⟩ | ⟨word, chosen⟩ <;> rw [word, chosen] <;> rfl
    · rw [← specified.gain]
      exact Bounded32.admit_self gain
    · apply UInt32.toNat_inj.mp
      rw [specified.capacity]
      exact (Nat.mod_eq_of_lt construction.dimension.wordBound).symm

/-- **An admitted header was saved under the receiver's step order.** For every
construction and header, header admission succeeds only when the stored order word is
the stored word of the receiver's order; `StepOrder.stored_injective` makes the two
orders one. -/
theorem admitHeader_order (construction : AgentConstruction) (header : Header) (gain : RewardRate)
    (admitted : admitHeader construction header = .ok gain) :
    StepOrder.Stored header.order construction.order :=
  ((admitHeader_iff construction header gain).mp admitted).order

/-- Read the body as the exact image of an agent of the receiving construction: the whole
body is the image's encoding, and the header's clock and reward-rate words are the image's
own. This is where this project makes an image of a construction from bytes. The order word
it compares with the receiving construction is the word of the payload's own header
(`admitHeader`); it takes no order word beside the payload. -/
@[noinline] def admitPayload (construction : AgentConstruction) (payload : Payload) :
    Except Error construction.Image := do
  let _ ← admitHeader construction payload.header
  match (imageFormat construction).decode payload.body with
  | none => throw .corrupt
  | some (image, rest) =>
    if rest = [] ∧
        image.image.control.runtime.lifecycle.representation.progress.clock =
          payload.header.clock ∧
        image.image.control.average.rate.value = payload.header.gain then
      return image
    else throw .corrupt

/-- Decode a complete candidate under the immutable receiver context. -/
@[noinline] def loadCandidate (construction : AgentConstruction) (bytes : List UInt8) :
    Except Error construction.Image := do
  if bytes.length < 72 || bytes.take magic.length != magic then throw .notACheckpoint
  let some (header, _) := headerCodec.decode (bytes.drop magic.length) | throw .notACheckpoint
  let _ ← admitHeader construction header
  let some payload := decode bytes | throw .corrupt
  admitPayload construction payload

/-- **A candidate is admitted only from bytes whose own header the receiver admits.**
For every construction, byte list and image: when the loader returns the image, the
header that the header codec reads from those bytes is admitted for the construction
(`HeaderAdmitted`). In particular the order word in the bytes is the word of the
receiving construction's order. The loader takes no order word from its caller. -/
theorem loadCandidate_header (construction : AgentConstruction) (bytes : List UInt8)
    (image : construction.Image) (loaded : loadCandidate construction bytes = .ok image) :
    ∃ header rest gain, headerCodec.decode (bytes.drop magic.length) = some (header, rest) ∧
      HeaderAdmitted construction header gain := by
  unfold loadCandidate at loaded
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at loaded
  split at loaded
  · cases loaded
  · cases decoded : headerCodec.decode (bytes.drop magic.length) with
    | none =>
      rw [decoded] at loaded
      cases loaded
    | some found =>
      obtain ⟨header, rest⟩ := found
      rw [decoded] at loaded
      dsimp only at loaded
      cases admitted : admitHeader construction header with
      | error refusal =>
        rw [admitted] at loaded
        cases loaded
      | ok gain =>
        exact ⟨header, rest, gain, rfl, (admitHeader_iff construction header gain).mp admitted⟩

end Acorn.Checkpoint
