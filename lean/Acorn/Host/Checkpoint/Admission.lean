import Acorn.Host.Checkpoint.Frame
import Acorn.Host.Checkpoint.Image

namespace Acorn.Checkpoint
open Features Handcrafted Lifetime

inductive Error where
  | notACheckpoint
  | version (found expected : UInt32)
  | criterion (found expected : UInt32)
  | shape (foundCapacity expectedCapacity foundLearners expectedLearners : UInt32)
  | seed (found expected : UInt64)
  | representation
  | order (found expected : UInt32)
  | unsupportedPolicy
  | corrupt
  | oversized
  deriving DecidableEq, Repr

def formatVersion : UInt32 := Acorn.FeatureConstants.checkpointFormatVersion.toUInt32

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

structure HeaderAdmitted (construction : AgentConstruction) (header : Header)
    (gain : RewardRate) : Prop where
  version : header.version = 21
  criterion : (header.criterion = 0 ∧ construction.criterion = .discounted) ∨
    (header.criterion = 1 ∧ construction.criterion = .differential)
  gain : gain.value = header.gain
  capacity : header.capacity.toNat = construction.dimension.capacity
  learners : header.learners = 51
  seed : header.seed = construction.config.seed
  supported : construction.profile.mode = .final ∧ construction.profile.credit = .perStep ∧
    construction.profile.rate = .declared ∧ construction.profile.subtasks = .learned
  policy : header.supported = 1
  tilings : header.tilings = construction.config.tilings
  units : header.units.toNat = construction.config.units.count
  order : StepOrder.Stored header.order construction.order

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

theorem admitHeader_order (construction : AgentConstruction) (header : Header) (gain : RewardRate)
    (admitted : admitHeader construction header = .ok gain) :
    StepOrder.Stored header.order construction.order :=
  ((admitHeader_iff construction header gain).mp admitted).order

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

@[noinline] def loadCandidate (construction : AgentConstruction) (bytes : List UInt8) :
    Except Error construction.Image := do
  if bytes.length < 72 || bytes.take magic.length != magic then throw .notACheckpoint
  let some (header, _) := headerCodec.decode (bytes.drop magic.length) | throw .notACheckpoint
  let _ ← admitHeader construction header
  let some payload := decode bytes | throw .corrupt
  admitPayload construction payload

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
