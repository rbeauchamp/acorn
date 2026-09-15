/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Features

/-!
# Bounded replacement history

The clock saturates while learning may continue. Replacement admission requires
both unused transcript capacity and a strictly newer timestamp. Restoration
establishes structural legality, not reachability under a learning stream.
-/
namespace Acorn.Features

/-- An event can name only a unit in its receiving bank. -/
structure Event (config : Config) where
  /-- Owned lifetime timestamp. -/
  step : UInt64
  /-- Bank position, never a free-standing unchecked word. -/
  unit : Fin config.units.count
  deriving DecidableEq

/-- Complete structural transcript predicate, independent of any learning claim. -/
def LegalHistory (config : Config) (clock : UInt64) (events : List (Event config)) : Prop :=
  events.length ≤ config.units.count ∧
    events.Pairwise (fun a b => a.step.toNat < b.step.toNat) ∧
    ∀ event ∈ events, event.step.toNat ≤ clock.toNat

instance (config : Config) (clock : UInt64) (events : List (Event config)) :
    Decidable (LegalHistory config clock events) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Clock and transcript are admitted and replaced together. -/
structure Progress (config : Config) where
  /-- Saturating lifetime word. -/
  clock : UInt64
  /-- Chronological replacement sequence. -/
  events : List (Event config)
  /-- Capacity, chronology and clock bounds belong to the stored state. -/
  legal : LegalHistory config clock events

/-- Initial representation has no replacement history. -/
def Progress.empty (config : Config) : Progress config := ⟨0, [], by simp [LegalHistory]⟩

/-- Last representable lifetime. -/
def maxClock : Nat := 2 ^ 64 - 1

/-- Saturation avoids overflow and timestamp reuse. -/
def advanceClock (clock : UInt64) : UInt64 := (min (clock.toNat + 1) maxClock).toUInt64

/-- The executed word constructor represents the saturated integer exactly. -/
theorem advanceClock_exact (clock : UInt64) :
    (advanceClock clock).toNat = min (clock.toNat + 1) maxClock := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right (clock.toNat + 1) maxClock
  unfold maxClock at *
  omega

/-- Clock advancement never invalidates an admitted event. -/
theorem advanceClock_monotone (clock : UInt64) : clock.toNat ≤ (advanceClock clock).toNat := by
  rw [advanceClock_exact]
  have := clock.toNat_lt
  unfold maxClock
  omega

/-- Advance only the owned clock; every retained event remains legal. -/
def Progress.advance {config : Config} (progress : Progress config) : Progress config :=
  ⟨advanceClock progress.clock, progress.events, progress.legal.1, progress.legal.2.1,
    fun event member => Nat.le_trans (progress.legal.2.2 event member)
      (advanceClock_monotone progress.clock)⟩

/-- One new event has room exactly when capacity and strict chronology permit it. -/
def Progress.CanRecord {config : Config} (progress : Progress config) : Prop :=
  progress.events.length < config.units.count ∧
    ∀ event ∈ progress.events, event.step.toNat < progress.clock.toNat

instance {config : Config} (progress : Progress config) : Decidable progress.CanRecord :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Append with authority derived from this exact progress state. -/
def Progress.record {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) (room : progress.CanRecord) : Progress config :=
  { clock := progress.clock
    events := progress.events ++ [⟨progress.clock, unit⟩]
    legal := by
      refine ⟨by have := room.1; simp only [List.length_append, List.length_singleton]; omega, ?_, ?_⟩
      · rw [List.pairwise_append]
        exact ⟨progress.legal.2.1, by simp,
          fun event member next hn => by
            have hn : next = ⟨progress.clock, unit⟩ := by simpa using hn
            subst next
            exact room.2 event member⟩
      · intro event member
        rcases List.mem_append.mp member with old | new
        · exact progress.legal.2.2 event old
        · have same : event = ⟨progress.clock, unit⟩ := by simpa using new
          subst event
          exact Nat.le_refl _ }

/-- Capacity refusal leaves the same progress state, rather than truncating history. -/
def Progress.tryRecord {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) : Option (Progress config) :=
  if room : progress.CanRecord then some (progress.record unit room) else none

/-- Exact refusal criterion, for every bank size and legal progress state. -/
theorem tryRecord_refuses {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) :
    progress.tryRecord unit = none ↔ ¬ progress.CanRecord := by
  simp [Progress.tryRecord]

/-- Success records precisely one event at the owner's timestamp. -/
theorem record_events {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) (room : progress.CanRecord) :
    (progress.record unit room).events = progress.events ++ [⟨progress.clock, unit⟩] := rfl

/-- No second retirement can use the same clock, irrespective of unit choice. -/
theorem record_excludes_same_clock {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) (room : progress.CanRecord) :
    ¬ (progress.record unit room).CanRecord := by
  intro h
  have impossible := h.2 ⟨progress.clock, unit⟩ (by simp [Progress.record])
  exact Nat.lt_irrefl _ impossible

/-- A full transcript stays unable to record after any clock advance. -/
theorem full_refuses {config : Config} (progress : Progress config)
    (full : progress.events.length = config.units.count) : ¬ progress.CanRecord := by
  intro room
  have := room.1
  omega

/-- Saturation is a fixed point of the executing clock operation. -/
theorem advanceClock_saturated (clock : UInt64) (saturated : clock.toNat = maxClock) :
    advanceClock clock = clock := by
  apply UInt64.toNat.inj
  rw [advanceClock_exact, saturated]
  omega

/-- Once a saturated timestamp is recorded, no future number of clock advances
can admit another replacement, even if transcript slots remain. -/
theorem saturated_record_refuses_forever {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) (room : progress.CanRecord)
    (saturated : progress.clock.toNat = maxClock) (steps : Nat) :
    ¬ (Nat.repeat Progress.advance steps (progress.record unit room)).CanRecord := by
  have fixed : (progress.record unit room).advance = progress.record unit room := by
    have clockFixed := advanceClock_saturated progress.clock saturated
    simp only [Progress.advance, Progress.record, clockFixed]
  have identity : Nat.repeat Progress.advance steps (progress.record unit room) =
      progress.record unit room := by
    induction steps with
    | zero => rfl
    | succ n ih => simp [Nat.repeat, ih, fixed]
  rw [identity]
  exact record_excludes_same_clock progress unit room

/-- A replacement consumes exactly one bounded transcript slot. -/
theorem record_count {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) (room : progress.CanRecord) :
    (progress.record unit room).events.length = progress.events.length + 1 := by
  simp [Progress.record]

/-- Exact bank-relative event-word admission. -/
def Event.admit (config : Config) (raw : UInt64 × UInt16) : Option (Event config) :=
  if h : raw.2.toNat < config.units.count then some ⟨raw.1, ⟨raw.2.toNat, h⟩⟩ else none

/-- An admitted unit has an exact durable UInt16 representation. -/
def Event.words {config : Config} (event : Event config) : UInt64 × UInt16 :=
  (event.step, event.unit.val.toUInt16)

/-- Serialization loses neither the unit number nor the timestamp. -/
theorem Event.words_roundtrip {config : Config} (event : Event config) :
    Event.admit config event.words = some event := by
  have bound : event.unit.val < 2 ^ 16 := by
    have := event.unit.isLt
    have := config.units.bounded
    omega
  have exactWord : event.unit.val.toUInt16.toNat = event.unit.val := Nat.mod_eq_of_lt bound
  simp only [Event.admit, Event.words, exactWord, event.unit.isLt, ↓reduceDIte]

/-- Pairwise chronology makes the latest entry sufficient for admission. -/
theorem Progress.newest_suffices {config : Config} (progress : Progress config)
    (event : Event config) (latest : progress.events.getLast? = some event) :
    (∀ old ∈ progress.events, old.step.toNat < progress.clock.toNat) ↔
      event.step.toNat < progress.clock.toNat := by
  constructor
  · intro all
    exact all event (List.mem_of_getLast? latest)
  · intro newer old member
    have ordered := progress.legal.2.1
    have last := List.getLast?_eq_some_iff.mp latest
    obtain ⟨earlierEvents, equality⟩ := last
    rw [equality] at ordered member
    rcases List.mem_append.mp member with earlier | last
    · have cross := (List.pairwise_append.mp ordered).2.2 old earlier event (by simp)
      exact Nat.lt_trans cross newer
    · have same : old = event := by simpa using last
      simpa [same] using newer

/-- Structural admission never alters timestamps, unit identities, or event order. -/
def Progress.admit (config : Config) (clock : UInt64) (raw : List (UInt64 × UInt16)) :
    Option (Progress config) := do
  let events ← raw.mapM (Event.admit config)
  if legal : LegalHistory config clock events then some ⟨clock, events, legal⟩ else none

/-- The canonical word image preserves all event positions. -/
def Progress.words {config : Config} (progress : Progress config) : List (UInt64 × UInt16) :=
  progress.events.map Event.words

/-- Every typed event sequence survives exact raw-word admission. -/
theorem events_words_roundtrip {config : Config} (events : List (Event config)) :
    (events.map Event.words).mapM (Event.admit config) = some events := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp [Event.words_roundtrip, ih]

/-- Raw restoration of a legal transcript preserves its complete stored identity. -/
theorem Progress.words_roundtrip {config : Config} (progress : Progress config) :
    Progress.admit config progress.clock progress.words = some progress := by
  simp only [Progress.admit, Progress.words, events_words_roundtrip]
  simp [progress.legal]

/-- An already decoded image is accepted exactly when all stored invariants hold. -/
def Progress.admitEvents (config : Config) (clock : UInt64) (events : List (Event config)) :
    Option (Progress config) :=
  if legal : LegalHistory config clock events then some ⟨clock, events, legal⟩ else none

/-- A legal receiver's own structural image round-trips exactly. -/
theorem admitEvents_roundtrip {config : Config} (progress : Progress config) :
    Progress.admitEvents config progress.clock progress.events = some progress := by
  simp [Progress.admitEvents, progress.legal]

/-- Exact chronological reconstruction from the original bank. -/
def rebuild (shape : PatchShape) (config : Config) (events : List (Event config)) : Bank shape config :=
  events.foldl (fun bank event => bank.replace event.unit) (Bank.initial shape config)

/-- Chronological replay extends the same generator and replaces the same unit. -/
theorem rebuild_append (shape : PatchShape) (config : Config)
    (events : List (Event config)) (event : Event config) :
    rebuild shape config (events ++ [event]) = (rebuild shape config events).replace event.unit := by
  simp [rebuild, List.foldl_append]

/-- The live bank and its compact reconstruction image cannot disagree. -/
structure Representation (shape : PatchShape) (config : Config) where
  /-- Stored clock and transcript. -/
  progress : Progress config
  /-- Native bank storage. -/
  bank : Bank shape config
  /-- Erased correspondence, checked at construction, replacement and load. -/
  identity : bank = rebuild shape config progress.events

/-- Fresh representation. -/
def Representation.initial (shape : PatchShape) (config : Config) : Representation shape config :=
  ⟨Progress.empty config, Bank.initial shape config, rfl⟩

/-- Restoration reconstructs identity by construction, never by a hash check. -/
def Representation.restore (shape : PatchShape) {config : Config} (progress : Progress config) :
    Representation shape config := ⟨progress, rebuild shape config progress.events, rfl⟩

/-- Time advancement changes no representation identity. -/
def Representation.advance {shape : PatchShape} {config : Config}
    (representation : Representation shape config) : Representation shape config :=
  ⟨representation.progress.advance, representation.bank, representation.identity⟩

/-- One admitted replacement links the executing bank to the appended transcript. -/
def Representation.replace {shape : PatchShape} {config : Config}
    (representation : Representation shape config) (unit : Fin config.units.count)
    (room : representation.progress.CanRecord) : Representation shape config :=
  ⟨representation.progress.record unit room, representation.bank.replace unit, by
    rw [record_events, rebuild_append, representation.identity]⟩

/-- A cache is indexed by the exact receiver bank and supplied opaque observation.
Changing banks cannot silently reinterpret old active features as a fresh encoding. -/
structure EncodingFrame (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) where
  /-- Materialized learner input. -/
  active : SwiftTd.ActiveSet dimension
  /-- Erased execution correspondence. -/
  fresh : active = encode dimension bank words patch

/-- Construct a frame by executing the current encoder once. -/
def EncodingFrame.compute (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    EncodingFrame dimension bank words patch := ⟨encode dimension bank words patch, rfl⟩

end Acorn.Features
