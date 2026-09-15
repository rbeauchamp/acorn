/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Frame

/-!
# Receiver-bound checkpoint admission

Parsing has no receiver write capability. Exact header identity, all durable
numeric domains, assignments and transcript are admitted before the complete
image reaches `Agent.restore`. The primary image contains raw words by design:
installation applies each immutable receiving learner's projection.
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
  /-- This profile's process state has no resumable format-14 image. -/
  | unsupportedPolicy
  /-- Length, checksum, assignment, transcript or durable numeric admission failed. -/
  | corrupt
  deriving DecidableEq, Repr

/-- The currently supported generation; older generations are explicitly refused. -/
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
  return gain

/-- Goals enter through their complete count relation, without repair or clamping. -/
def admitGoal (words : GoalWords) : Option GoalTotals :=
  if valid : words.2.1.toNat ≤ words.1.toNat ∧ (words.1 = 0 → words.2.2 = 0) then
    some ⟨words.1, words.2.1, words.2.2, valid.1, valid.2⟩
  else none

/-- A total uses the receiving quantity's closed numeric rule. -/
def admitSum (quantity : Quantity) (words : SumWords) : Option (SumCount quantity) :=
  SumCount.admit quantity words.1 words.2

/-- The three column lists are consumed in lockstep with the current demon layout. -/
def admitDemons : (discounts : List Discount) → List SumWords → List Binary32 → List Binary32 →
    Option (DurableDemons discounts)
  | [], [], [], [] => some .nil
  | discount :: rest, sum :: sums, value :: values, error :: errors => do
    let sum ← admitSum (.squaredError discount) sum
    let value ← Prediction.admit discount value
    let error ← Bounded32.admit (errorRange discount).range error
    let tail ← admitDemons rest sums values errors
    some (.cons ⟨sum, value, error⟩ tail)
  | _, _, _, _ => none

/-- Episode admission is decidable over the full stored word domain. -/
instance (record : OptionEpisodes) (active : Bool) : Decidable (record.Valid active) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- All slots are checked before any full-agent image is constructed. -/
instance (options : Vector OptionEpisodes Acorn.FeatureConstants.skillCount)
    (active : Option (Fin Acorn.FeatureConstants.skillCount)) : Decidable (OptionsValid options active) :=
  inferInstanceAs (Decidable (∀ _slot : Fin Acorn.FeatureConstants.skillCount, _))

/-- Every lifetime total, bound and settled value is admitted in its own semantic domain. -/
def admitLifetime (raw : LifetimeWords) : Option (Durable demonLayout) := do
  let reward ← admitSum .reward raw.reward
  let family ← raw.rewardByFamily.mapM (admitSum .reward)
  let history ← raw.rewardHistory.mapM (admitSum .reward)
  let demons ← admitDemons demonLayout raw.squaredErrors.toList raw.returns.toList raw.errors.toList
  let errorHistory ← raw.errorHistory.mapM (admitSum (.squaredError .g99))
  let goals ← raw.goals.mapM admitGoal
  let cycles ← raw.goalCycles.mapM (fun row => row.mapM admitGoal)
  if OptionsValid raw.options none then
    some ⟨reward, family, history, demons, errorHistory, raw.options, goals, cycles⟩
  else none

/-- Complete-candidate construction: no failed admission can install a field. -/
@[noinline] def admitPayload (construction : AgentConstruction) (payload : Payload construction.dimension) :
    Except Error (AgentImage construction.config construction.criterion construction.dimension) := do
  let gain ← admitHeader construction payload.header
  let pending ← match payload.header.pending with
    | 0 => pure false
    | 1 => pure true
    | _ => throw .corrupt
  let raw : RawFeatureImage construction.dimension demonLayout :=
    ⟨payload.header.seed, payload.header.tilings, payload.header.units.toUInt16,
      payload.header.capacity, payload.header.criterion.toUInt8, payload.header.clock,
      payload.events.val, payload.assignments, payload.primary, pending⟩
  let some features := FeatureImage.admit construction.config construction.criterion construction.dimension raw
    | throw .corrupt
  let some lifetime := admitLifetime payload.lifetime | throw .corrupt
  if valid : OptionsValid lifetime.options none then return ⟨features, gain, lifetime, valid⟩
  else throw .corrupt

/-- Decode a complete candidate under the immutable receiver context. -/
@[noinline] def loadCandidate (construction : AgentConstruction) (bytes : List UInt8) :
    Except Error (AgentImage construction.config construction.criterion construction.dimension) := do
  if bytes.length < 72 || bytes.take magic.length != magic then throw .notACheckpoint
  let some (header, _) := headerCodec.decode (bytes.drop magic.length) | throw .notACheckpoint
  let _ ← admitHeader construction header
  let some payload := decode construction.dimension bytes | throw .corrupt
  admitPayload construction payload

/-- Only the successful candidate branch invokes the existing cold restore. -/
@[noinline] def load (construction : AgentConstruction) (receiver : construction.State) (bytes : List UInt8) :
    Except Error construction.State := do
  let image ← loadCandidate construction bytes
  let some restored := receiver.restore image | throw .unsupportedPolicy
  return restored

/-- An explicit return of the unchanged state on refusal, with the error preserved. -/
def loadKeeping (construction : AgentConstruction) (receiver : construction.State) (bytes : List UInt8) :
    construction.State × Option Error :=
  match load construction receiver bytes with
  | .error error => (receiver, some error)
  | .ok restored => (restored, none)

/-- Arbitrary rejected byte streams cannot return a partially changed receiver. -/
theorem load_nonmutation (construction : AgentConstruction) (receiver : construction.State)
    (bytes : List UInt8) (error : Error) (rejected : load construction receiver bytes = .error error) :
    loadKeeping construction receiver bytes = (receiver, some error) := by
  simp [loadKeeping, rejected]

end Acorn.Checkpoint
