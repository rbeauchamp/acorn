/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Features

/-!
# Durable tester and generator state

Every unit carries its generator origin, its birth clock and its running
contribution utility. The bank is rebuilt from the origins, so the stored state
is `O(units)` for any number of replacements. The clock and the lifetime
replacement count saturate while learning may continue. Restoration establishes
structural legality, not reachability under a learning stream.
-/
namespace Acorn.Features

/-- An event can name only a unit in its receiving bank. -/
structure Event (config : Config) where
  /-- Owned lifetime timestamp. -/
  step : UInt64
  /-- Bank position, never a free-standing unchecked word. -/
  unit : Fin config.units.count
  deriving DecidableEq

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

/-- Clock advancement never invalidates an admitted birth or event. -/
theorem advanceClock_monotone (clock : UInt64) : clock.toNat ≤ (advanceClock clock).toNat := by
  rw [advanceClock_exact]
  have := clock.toNat_lt
  unfold maxClock
  omega

/-- Saturation is a fixed point of the executing clock operation. -/
theorem advanceClock_saturated (clock : UInt64) (saturated : clock.toNat = maxClock) :
    advanceClock clock = clock := by
  apply UInt64.toNat.inj
  rw [advanceClock_exact, saturated]
  omega

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

/-- Contribution utilities are finite and nonnegative at storage. -/
def utilityRange : Interval32 where
  lower := .zero
  upper := ⟨0x7f7fffff⟩
  lowerFinite := by decide
  upperFinite := by decide
  ordered := by decide

/-- A stored contribution utility. -/
abbrev Utility := Bounded32 utilityRange

/-- A generated unit starts with zero utility. -/
def Utility.zero : Utility := ⟨.zero, by decide⟩

/-- Dohare et al. (2024), arXiv:2306.13812v3, eq. (2), p. 19:
`c ← η·c + (1 − η)·|h|·Σ_k |w_k|`, where `contribution` is `|h|·Σ_k |w_k|`.
The write saturates through the utility range, so every stored word is finite
and nonnegative whatever the machine arithmetic returns. -/
def Utility.update (tester : Tester) (utility : Utility) (contribution : Binary32) : Utility :=
  Bounded32.project utilityRange
    ((tester.decay.mul utility.value).add (tester.complement.mul contribution))

/-- One unit's durable tester state. -/
structure UnitState where
  /-- Generator state its projection was drawn from. -/
  origin : UInt64
  /-- Clock at generation; the unit's age is the clock minus this word. -/
  birth : UInt64
  /-- Running contribution utility. -/
  utility : Utility

/-- Raw per-unit words: origin, birth and utility bits. -/
abbrev UnitWords := UInt64 × UInt64 × Binary32

/-- Exact per-unit words. -/
def UnitState.words (unit : UnitState) : UnitWords := (unit.origin, unit.birth, unit.utility.value)

/-- Utility words are admitted by identity or refused; origins and births are total. -/
def UnitState.admit (raw : UnitWords) : Option UnitState :=
  (Bounded32.admit utilityRange raw.2.2).map fun utility => ⟨raw.1, raw.2.1, utility⟩

/-- Every stored unit survives its own words. -/
theorem UnitState.words_roundtrip (unit : UnitState) : UnitState.admit unit.words = some unit := by
  simp [UnitState.admit, UnitState.words, Bounded32.admit_self]

/-- The stored latest event, if any, is no later than the clock. -/
def Recent {config : Config} (clock : UInt64) : Option (Event config) → Prop
  | none => True
  | some event => event.step.toNat ≤ clock.toNat

instance {config : Config} (clock : UInt64) (last : Option (Event config)) :
    Decidable (Recent clock last) := by
  cases last <;> unfold Recent <;> infer_instance

/-- A later clock keeps the latest event legal. -/
theorem Recent.mono {config : Config} {clock later : UInt64} {last : Option (Event config)}
    (recent : Recent clock last) (monotone : clock.toNat ≤ later.toNat) : Recent later last := by
  cases last with
  | none => trivial
  | some event => exact Nat.le_trans recent monotone

/-- Clock, generator, per-unit tester state and accrued credit are admitted and
replaced together. -/
structure Progress (config : Config) where
  /-- Saturating lifetime word. -/
  clock : UInt64
  /-- Generator continuation for the next replacement. -/
  stream : UInt64
  /-- Every unit's origin, birth and utility. -/
  units : Vector UnitState config.units.count
  /-- Accrued eligible-unit steps not yet spent on a replacement. -/
  credit : Fin config.tester.period
  /-- Saturating lifetime replacement count. -/
  replaced : UInt64
  /-- The latest replacement. -/
  last : Option (Event config)
  /-- No unit is born after the clock, so every age is a natural number. -/
  born : ∀ unit : Fin config.units.count, units[unit.val].birth.toNat ≤ clock.toNat
  /-- The latest replacement is no later than the clock. -/
  recent : Recent clock last

/-- Every initial unit is born at clock zero with zero utility. -/
def Progress.initial (config : Config) : Progress config :=
  ⟨0, initialStream config,
    Vector.ofFn fun unit => ⟨(initialOrigins config)[unit.val], 0, Utility.zero⟩,
    ⟨0, config.tester.positive⟩, 0, none, by simp, trivial⟩

/-- Advance only the owned clock; every birth and event remains legal. -/
def Progress.advance {config : Config} (progress : Progress config) : Progress config :=
  { progress with
    clock := advanceClock progress.clock
    born := fun unit => Nat.le_trans (progress.born unit) (advanceClock_monotone progress.clock)
    recent := progress.recent.mono (advanceClock_monotone progress.clock) }

/-- Advancing keeps every unit and the credit, and saturates the clock. -/
theorem Progress.advance_fields {config : Config} (progress : Progress config) :
    progress.advance.units = progress.units ∧ progress.advance.credit = progress.credit ∧
      progress.advance.clock = advanceClock progress.clock := by
  unfold Progress.advance
  exact ⟨rfl, rfl, rfl⟩

/-- Every unit's generator origin. -/
def Progress.origins {config : Config} (progress : Progress config) :
    Vector UInt64 config.units.count :=
  progress.units.map (·.origin)

/-- Replace one unit: its projection is drawn at the generator continuation, its
age restarts at the current clock and its utility at zero, and the lifetime
count and latest event record the replacement. -/
def Progress.replace {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) : Progress config where
  clock := progress.clock
  stream := progress.stream + projectionStride
  units := progress.units.set unit.val ⟨progress.stream, progress.clock, Utility.zero⟩ unit.isLt
  credit := progress.credit
  replaced := advanceClock progress.replaced
  last := some ⟨progress.clock, unit⟩
  born := by
    intro other
    by_cases same : unit.val = other.val
    · simp [same]
    · simp only [Vector.getElem_set_ne _ _ same]
      exact progress.born other
  recent := Nat.le_refl _

/-- Replacement records its unit's origin at the old continuation. -/
theorem Progress.replace_origins {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) :
    (progress.replace unit).origins = progress.origins.set unit.val progress.stream unit.isLt := by
  simp [Progress.origins, Progress.replace, Vector.map_set]

/-- Replacement keeps the clock and the accrued credit. -/
theorem Progress.replace_counters {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) :
    (progress.replace unit).clock = progress.clock ∧ (progress.replace unit).credit = progress.credit := by
  unfold Progress.replace
  exact ⟨rfl, rfl⟩

/-- A replaced unit is born at the current clock. -/
theorem Progress.replace_birth {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) :
    (progress.replace unit).units[unit.val].birth = progress.clock := by
  simp [Progress.replace]

/-- Replacement leaves every other unit's state unchanged. -/
theorem Progress.replace_other {config : Config} (progress : Progress config)
    (unit other : Fin config.units.count) (different : unit.val ≠ other.val) :
    (progress.replace unit).units[other.val] = progress.units[other.val] := by
  simp [Progress.replace, Vector.getElem_set_ne _ _ different]

/-- Write every unit's utility from its index and prior state, keeping origins and births. -/
def Progress.rescore {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) : Progress config :=
  { progress with
    units := Vector.ofFn fun unit =>
      { progress.units[unit.val] with utility := utility unit progress.units[unit.val] }
    born := fun unit => by simpa using progress.born unit }

/-- Rescoring keeps every birth. -/
theorem Progress.rescore_birth {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) (unit : Fin config.units.count) :
    (progress.rescore utility).units[unit.val].birth = progress.units[unit.val].birth := by
  simp [Progress.rescore]

/-- Rescoring keeps the clock and the credit. -/
theorem Progress.rescore_counters {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) :
    (progress.rescore utility).clock = progress.clock ∧
      (progress.rescore utility).credit = progress.credit := by
  unfold Progress.rescore
  exact ⟨rfl, rfl⟩

/-- Rescoring keeps every origin. -/
theorem Progress.rescore_origins {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) :
    (progress.rescore utility).origins = progress.origins := by
  ext index bound
  simp [Progress.rescore, Progress.origins]

/-- Replace the accrued credit. -/
def Progress.withCredit {config : Config} (progress : Progress config)
    (credit : Fin config.tester.period) : Progress config :=
  { progress with credit }

/-- A credit write keeps every unit and the clock. -/
theorem Progress.withCredit_fields {config : Config} (progress : Progress config)
    (credit : Fin config.tester.period) :
    (progress.withCredit credit).units = progress.units ∧
      (progress.withCredit credit).clock = progress.clock ∧
      (progress.withCredit credit).credit = credit := by
  unfold Progress.withCredit
  exact ⟨rfl, rfl, rfl⟩

/-- Raw latest-event words: tag (zero absent, one present), step and unit. -/
abbrev LastWords := UInt32 × UInt64 × UInt16

/-- The canonical latest-event words. -/
def lastWords {config : Config} : Option (Event config) → LastWords
  | none => (0, 0, 0)
  | some event => (1, event.words)

/-- Absence has one encoding; presence admits a bank-relative event; other tags are refused. -/
def admitLast (config : Config) (raw : LastWords) : Option (Option (Event config)) :=
  if raw = (0, 0, 0) then some none
  else if raw.1 = 1 then (Event.admit config raw.2).map some
  else none

/-- Every latest event survives its words. -/
theorem admitLast_roundtrip {config : Config} (last : Option (Event config)) :
    admitLast config (lastWords last) = some last := by
  cases last with
  | none => rfl
  | some event =>
    have tag : ((1 : UInt32), event.words) ≠ (0, 0, 0) := by
      simp [Prod.ext_iff]
    simp [admitLast, lastWords, tag, Event.words_roundtrip]

/-- Raw durable tester words apart from the clock, which the header carries. -/
structure ProgressWords where
  /-- Generator continuation. -/
  stream : UInt64
  /-- Accrued credit. -/
  credit : UInt32
  /-- Lifetime replacement count. -/
  replaced : UInt64
  /-- Latest replacement. -/
  last : LastWords
  /-- Every unit's words, in bank order. -/
  units : List UnitWords

/-- The canonical word image of every stored field. -/
def Progress.words {config : Config} (progress : Progress config) : ProgressWords :=
  ⟨progress.stream, progress.credit.val.toUInt32, progress.replaced, lastWords progress.last,
    progress.units.toList.map UnitState.words⟩

/-- Admission accepts exactly the stored invariants: one entry per unit, legal
utilities, credit below the period, no birth or event after the clock. It never
clamps or repairs a word. -/
def Progress.admit (config : Config) (clock : UInt64) (raw : ProgressWords) :
    Option (Progress config) := do
  let units ← raw.units.mapM UnitState.admit
  let last ← admitLast config raw.last
  if shape : units.length = config.units.count ∧ raw.credit.toNat < config.tester.period then
    let units : Vector UnitState config.units.count := ⟨units.toArray, by simpa using shape.1⟩
    if legal : (∀ unit : Fin config.units.count, units[unit.val].birth.toNat ≤ clock.toNat) ∧
        Recent clock last then
      some ⟨clock, raw.stream, units, ⟨raw.credit.toNat, shape.2⟩, raw.replaced, last,
        legal.1, legal.2⟩
    else none
  else none

/-- Every per-unit word list survives admission. -/
theorem units_words_roundtrip (units : List UnitState) :
    (units.map UnitState.words).mapM UnitState.admit = some units := by
  induction units with
  | nil => rfl
  | cons unit rest ih => simp [UnitState.words_roundtrip, ih]

/-- Raw restoration of a legal state preserves its complete stored identity. -/
theorem Progress.words_roundtrip {config : Config} (progress : Progress config) :
    Progress.admit config progress.clock progress.words = some progress := by
  have credit : progress.credit.val.toUInt32.toNat = progress.credit.val := by
    have := progress.credit.isLt
    have := config.tester.bounded
    exact Nat.mod_eq_of_lt (by omega)
  have shape : progress.units.toList.length = config.units.count ∧
      progress.credit.val.toUInt32.toNat < config.tester.period := by
    simp [credit]
  have units : (⟨progress.units.toList.toArray, by simp⟩ : Vector UnitState config.units.count) =
      progress.units := by
    ext index bound
    simp
  simp only [Progress.admit, Progress.words, units_words_roundtrip, admitLast_roundtrip,
    bind, Option.bind, units, credit]
  split
  · split
    · rfl
    · rename_i absent
      exact absurd ⟨progress.born, progress.recent⟩ absent
  · rename_i absent
    exact absurd ⟨by simp, progress.credit.isLt⟩ absent

/-- The live bank and its origins cannot disagree. -/
structure Representation (shape : PatchShape) (config : Config) where
  /-- Stored clock, generator and tester state. -/
  progress : Progress config
  /-- Native bank storage. -/
  bank : Bank shape config
  /-- Erased correspondence, checked at construction, replacement and load. -/
  identity : bank = Bank.build shape progress.origins progress.stream

/-- The initial units' origins are the initial bank's origins. -/
theorem Progress.initial_origins (config : Config) :
    (Progress.initial config).origins = initialOrigins config := by
  ext index bound
  simp [Progress.initial, Progress.origins]

/-- Fresh representation. -/
def Representation.initial (shape : PatchShape) (config : Config) : Representation shape config :=
  ⟨Progress.initial config, Bank.initial shape config, by
    rw [Progress.initial_origins] <;> rfl⟩

/-- Restoration reconstructs the bank by construction, never by a hash check. -/
def Representation.restore (shape : PatchShape) {config : Config} (progress : Progress config) :
    Representation shape config := ⟨progress, Bank.build shape progress.origins progress.stream, rfl⟩

/-- Time advancement changes no representation identity. -/
def Representation.advance {shape : PatchShape} {config : Config}
    (representation : Representation shape config) : Representation shape config :=
  ⟨representation.progress.advance, representation.bank, representation.identity⟩

/-- Utility writes leave the bank and its origins unchanged. -/
def Representation.rescore {shape : PatchShape} {config : Config}
    (representation : Representation shape config)
    (utility : Fin config.units.count → UnitState → Utility) : Representation shape config :=
  ⟨representation.progress.rescore utility, representation.bank, by
    rw [Progress.rescore_origins]
    exact representation.identity⟩

/-- Credit writes leave the bank and its origins unchanged. -/
def Representation.withCredit {shape : PatchShape} {config : Config}
    (representation : Representation shape config) (credit : Fin config.tester.period) :
    Representation shape config :=
  ⟨representation.progress.withCredit credit, representation.bank, representation.identity⟩

/-- One replacement links the executing bank to the recorded origin. -/
def Representation.replace {shape : PatchShape} {config : Config}
    (representation : Representation shape config) (unit : Fin config.units.count) :
    Representation shape config :=
  ⟨representation.progress.replace unit, representation.bank.replace unit, by
    rw [representation.identity, Bank.build_replace, Progress.replace_origins] <;> rfl⟩

/-- A cache is indexed by the exact receiver bank and supplied opaque observation.
Changing banks cannot silently reinterpret old active features as a fresh encoding.
The unit outputs the tester reads are the same outputs the encoding used. -/
structure EncodingFrame (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) where
  /-- Every unit's binary output on this input. -/
  units : Vector Bool config.units.count
  /-- Erased output correspondence. -/
  freshUnits : units = bank.activations patch
  /-- Materialized learner input. -/
  active : SwiftTd.ActiveSet dimension
  /-- Erased execution correspondence. -/
  fresh : active = encode dimension bank words patch

/-- Construct a frame by executing the unit outputs and the encoder once. -/
def EncodingFrame.compute (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    EncodingFrame dimension bank words patch :=
  let units := bank.activations patch
  ⟨units, rfl, encodeWith dimension config words units, rfl⟩

end Acorn.Features
