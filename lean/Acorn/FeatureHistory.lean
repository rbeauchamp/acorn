import Acorn.Features

namespace Acorn.Features

structure Event (config : Config) where
  step : UInt64
  unit : Fin config.units.count
  deriving DecidableEq

def maxClock : Nat := 2 ^ 64 - 1

def advanceClock (clock : UInt64) : UInt64 := (min (clock.toNat + 1) maxClock).toUInt64

theorem advanceClock_exact (clock : UInt64) :
    (advanceClock clock).toNat = min (clock.toNat + 1) maxClock := by
  apply Nat.mod_eq_of_lt
  have := Nat.min_le_right (clock.toNat + 1) maxClock
  unfold maxClock at *
  omega

theorem advanceClock_monotone (clock : UInt64) : clock.toNat ≤ (advanceClock clock).toNat := by
  rw [advanceClock_exact]
  have := clock.toNat_lt
  unfold maxClock
  omega

theorem advanceClock_saturated (clock : UInt64) (saturated : clock.toNat = maxClock) :
    advanceClock clock = clock := by
  apply UInt64.toNat.inj
  rw [advanceClock_exact, saturated]
  omega

def Event.admit (config : Config) (raw : UInt64 × UInt16) : Option (Event config) :=
  if h : raw.2.toNat < config.units.count then some ⟨raw.1, ⟨raw.2.toNat, h⟩⟩ else none

def Event.words {config : Config} (event : Event config) : UInt64 × UInt16 :=
  (event.step, event.unit.val.toUInt16)

theorem Event.words_roundtrip {config : Config} (event : Event config) :
    Event.admit config event.words = some event := by
  have bound : event.unit.val < 2 ^ 16 := by
    have := event.unit.isLt
    have := config.units.bounded
    omega
  have exactWord : event.unit.val.toUInt16.toNat = event.unit.val := Nat.mod_eq_of_lt bound
  simp only [Event.admit, Event.words, exactWord, event.unit.isLt, ↓reduceDIte]

theorem Event.admit_words {config : Config} (raw : UInt64 × UInt16) (event : Event config)
    (admitted : Event.admit config raw = some event) : raw = event.words := by
  unfold Event.admit at admitted
  split at admitted
  · cases admitted
    simp [Event.words]
  · contradiction

def utilityRange : Interval32 where
  lower := .zero
  upper := ⟨0x7f7fffff⟩
  lowerFinite := by decide
  upperFinite := by decide
  ordered := by decide

abbrev Utility := Bounded32 utilityRange

def Utility.zero : Utility := ⟨.zero, by decide⟩

def Utility.update (tester : Tester) (utility : Utility) (contribution : Binary32) : Utility :=
  Bounded32.project utilityRange
    ((tester.decay.mul utility.value).add (tester.complement.mul contribution))

structure UnitState where
  origin : UInt64
  birth : UInt64
  utility : Utility

abbrev UnitWords := UInt64 × UInt64 × Binary32

def UnitState.words (unit : UnitState) : UnitWords := (unit.origin, unit.birth, unit.utility.value)

def UnitState.admit (raw : UnitWords) : Option UnitState :=
  (Bounded32.admit utilityRange raw.2.2).map fun utility => ⟨raw.1, raw.2.1, utility⟩

theorem UnitState.words_roundtrip (unit : UnitState) : UnitState.admit unit.words = some unit := by
  simp [UnitState.admit, UnitState.words, Bounded32.admit_self]

theorem UnitState.admit_words (raw : UnitWords) (unit : UnitState)
    (admitted : UnitState.admit raw = some unit) : raw = unit.words := by
  unfold UnitState.admit at admitted
  cases legal : Bounded32.admit utilityRange raw.2.2 with
  | none =>
    rw [legal] at admitted
    contradiction
  | some utility =>
    rw [legal] at admitted
    cases admitted
    rw [UnitState.words, (Bounded32.admit_exact _ _ _ legal).1]

def Recent {config : Config} (clock : UInt64) : Option (Event config) → Prop
  | none => True
  | some event => event.step.toNat ≤ clock.toNat

instance {config : Config} (clock : UInt64) (last : Option (Event config)) :
    Decidable (Recent clock last) := by
  cases last <;> unfold Recent <;> infer_instance

theorem Recent.mono {config : Config} {clock later : UInt64} {last : Option (Event config)}
    (recent : Recent clock last) (monotone : clock.toNat ≤ later.toNat) : Recent later last := by
  cases last with
  | none => trivial
  | some event => exact Nat.le_trans recent monotone

structure Progress (config : Config) where
  clock : UInt64
  stream : UInt64
  units : Vector UnitState config.units.count
  credit : Fin config.tester.period
  replaced : UInt64
  last : Option (Event config)
  born : ∀ unit : Fin config.units.count, units[unit.val].birth.toNat ≤ clock.toNat
  recent : Recent clock last

def Progress.initial (config : Config) : Progress config :=
  ⟨0, initialStream config,
    Vector.ofFn fun unit => ⟨(initialOrigins config)[unit.val], 0, Utility.zero⟩,
    ⟨0, config.tester.positive⟩, 0, none, by simp, trivial⟩

def Progress.advance {config : Config} (progress : Progress config) : Progress config :=
  { progress with
    clock := advanceClock progress.clock
    born := fun unit => Nat.le_trans (progress.born unit) (advanceClock_monotone progress.clock)
    recent := progress.recent.mono (advanceClock_monotone progress.clock) }

theorem Progress.advance_fields {config : Config} (progress : Progress config) :
    progress.advance.units = progress.units ∧ progress.advance.credit = progress.credit ∧
      progress.advance.clock = advanceClock progress.clock := by
  unfold Progress.advance
  exact ⟨rfl, rfl, rfl⟩

def Progress.origins {config : Config} (progress : Progress config) :
    Vector UInt64 config.units.count :=
  progress.units.map (·.origin)

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

theorem Progress.replace_origins {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) :
    (progress.replace unit).origins = progress.origins.set unit.val progress.stream unit.isLt := by
  simp [Progress.origins, Progress.replace, Vector.map_set]

theorem Progress.replace_counters {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) :
    (progress.replace unit).clock = progress.clock ∧ (progress.replace unit).credit = progress.credit := by
  unfold Progress.replace
  exact ⟨rfl, rfl⟩

theorem Progress.replace_birth {config : Config} (progress : Progress config)
    (unit : Fin config.units.count) :
    (progress.replace unit).units[unit.val].birth = progress.clock := by
  simp [Progress.replace]

theorem Progress.replace_other {config : Config} (progress : Progress config)
    (unit other : Fin config.units.count) (different : unit.val ≠ other.val) :
    (progress.replace unit).units[other.val] = progress.units[other.val] := by
  simp [Progress.replace, Vector.getElem_set_ne _ _ different]

def Progress.rescore {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) : Progress config :=
  { progress with
    units := Vector.ofFn fun unit =>
      { progress.units[unit.val] with utility := utility unit progress.units[unit.val] }
    born := fun unit => by simpa using progress.born unit }

theorem Progress.rescore_birth {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) (unit : Fin config.units.count) :
    (progress.rescore utility).units[unit.val].birth = progress.units[unit.val].birth := by
  simp [Progress.rescore]

theorem Progress.rescore_counters {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) :
    (progress.rescore utility).clock = progress.clock ∧
      (progress.rescore utility).credit = progress.credit := by
  unfold Progress.rescore
  exact ⟨rfl, rfl⟩

theorem Progress.rescore_origins {config : Config} (progress : Progress config)
    (utility : Fin config.units.count → UnitState → Utility) :
    (progress.rescore utility).origins = progress.origins := by
  ext index bound
  simp [Progress.rescore, Progress.origins]

def Progress.withCredit {config : Config} (progress : Progress config)
    (credit : Fin config.tester.period) : Progress config :=
  { progress with credit }

theorem Progress.withCredit_fields {config : Config} (progress : Progress config)
    (credit : Fin config.tester.period) :
    (progress.withCredit credit).units = progress.units ∧
      (progress.withCredit credit).clock = progress.clock ∧
      (progress.withCredit credit).credit = credit := by
  unfold Progress.withCredit
  exact ⟨rfl, rfl, rfl⟩

abbrev LastWords := UInt32 × UInt64 × UInt16

def lastWords {config : Config} : Option (Event config) → LastWords
  | none => (0, 0, 0)
  | some event => (1, event.words)

def admitLast (config : Config) (raw : LastWords) : Option (Option (Event config)) :=
  if raw = (0, 0, 0) then some none
  else if raw.1 = 1 then (Event.admit config raw.2).map some
  else none

theorem admitLast_roundtrip {config : Config} (last : Option (Event config)) :
    admitLast config (lastWords last) = some last := by
  cases last with
  | none => rfl
  | some event =>
    have tag : ((1 : UInt32), event.words) ≠ (0, 0, 0) := by
      simp [Prod.ext_iff]
    simp [admitLast, lastWords, tag, Event.words_roundtrip]

theorem admitLast_words {config : Config} (raw : LastWords) (last : Option (Event config))
    (admitted : admitLast config raw = some last) : raw = lastWords last := by
  unfold admitLast at admitted
  split at admitted
  · rename_i absent
    cases admitted
    exact absent
  · split at admitted
    · rename_i present
      cases found : Event.admit config raw.2 with
      | none =>
        rw [found] at admitted
        contradiction
      | some event =>
        rw [found] at admitted
        cases admitted
        show raw = (1, event.words)
        rw [← Event.admit_words raw.2 event found, ← present]
    · contradiction

structure ProgressWords where
  stream : UInt64
  credit : UInt32
  replaced : UInt64
  last : LastWords
  units : List UnitWords

def Progress.words {config : Config} (progress : Progress config) : ProgressWords :=
  ⟨progress.stream, progress.credit.val.toUInt32, progress.replaced, lastWords progress.last,
    progress.units.toList.map UnitState.words⟩

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

theorem units_words_roundtrip (units : List UnitState) :
    (units.map UnitState.words).mapM UnitState.admit = some units := by
  induction units with
  | nil => rfl
  | cons unit rest ih => simp [UnitState.words_roundtrip, ih]

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

theorem units_admit_words : ∀ (raw : List UnitWords) (units : List UnitState),
    raw.mapM UnitState.admit = some units → raw = units.map UnitState.words
  | [], units, admitted => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at admitted
    subst admitted
    rfl
  | word :: words, units, admitted => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at admitted
    obtain ⟨unit, first, rest, others, built⟩ := admitted
    subst built
    rw [List.map_cons, ← UnitState.admit_words word unit first,
      ← units_admit_words words rest others]

theorem Progress.admit_words {config : Config} (clock : UInt64) (raw : ProgressWords)
    (progress : Progress config) (admitted : Progress.admit config clock raw = some progress) :
    clock = progress.clock ∧ raw = progress.words := by
  obtain ⟨stream, credit, replaced, lastRaw, unitsRaw⟩ := raw
  unfold Progress.admit at admitted
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at admitted
  obtain ⟨units, unitsAdmitted, last, lastAdmitted, built⟩ := admitted
  split at built
  · split at built
    · cases built
      have unitsWords := units_admit_words unitsRaw units unitsAdmitted
      have lastWords := admitLast_words lastRaw last lastAdmitted
      subst unitsWords lastWords
      have creditWord : credit.toNat.toUInt32 = credit :=
        UInt32.toNat_inj.mp (Nat.mod_eq_of_lt credit.toNat_lt)
      refine ⟨rfl, ?_⟩
      simp [Progress.words, creditWord]
    · contradiction
  · contradiction

structure Representation (shape : PatchShape) (config : Config) where
  progress : Progress config
  bank : Bank shape config
  identity : bank = Bank.build shape progress.origins progress.stream

theorem Progress.initial_origins (config : Config) :
    (Progress.initial config).origins = initialOrigins config := by
  ext index bound
  simp [Progress.initial, Progress.origins]

def Representation.initial (shape : PatchShape) (config : Config) : Representation shape config :=
  ⟨Progress.initial config, Bank.initial shape config, by
    rw [Progress.initial_origins] <;> rfl⟩

def Representation.restore (shape : PatchShape) {config : Config} (progress : Progress config) :
    Representation shape config := ⟨progress, Bank.build shape progress.origins progress.stream, rfl⟩

def Representation.advance {shape : PatchShape} {config : Config}
    (representation : Representation shape config) : Representation shape config :=
  ⟨representation.progress.advance, representation.bank, representation.identity⟩

def Representation.rescore {shape : PatchShape} {config : Config}
    (representation : Representation shape config)
    (utility : Fin config.units.count → UnitState → Utility) : Representation shape config :=
  ⟨representation.progress.rescore utility, representation.bank, by
    rw [Progress.rescore_origins]
    exact representation.identity⟩

def Representation.withCredit {shape : PatchShape} {config : Config}
    (representation : Representation shape config) (credit : Fin config.tester.period) :
    Representation shape config :=
  ⟨representation.progress.withCredit credit, representation.bank, representation.identity⟩

def Representation.replace {shape : PatchShape} {config : Config}
    (representation : Representation shape config) (unit : Fin config.units.count) :
    Representation shape config :=
  ⟨representation.progress.replace unit, representation.bank.replace unit, by
    rw [representation.identity, Bank.build_replace, Progress.replace_origins] <;> rfl⟩

structure EncodingFrame (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) where
  units : Vector Bool config.units.count
  freshUnits : units = bank.activations patch
  active : SwiftTd.ActiveSet dimension
  fresh : active = encode dimension bank words patch

def EncodingFrame.computeCosted (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    Costed (EncodingFrame dimension bank words patch) := do
  let units ← Costed.attach (bank.activationsCosted patch)
  let active ← Costed.attach (encodeWithCosted dimension config words units.val)
  Costed.pure ⟨units.val, units.property, active.val, by
    rw [active.property, units.property]
    rfl⟩

def EncodingFrame.compute (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    EncodingFrame dimension bank words patch :=
  (EncodingFrame.computeCosted dimension bank words patch).val

theorem EncodingFrame.compute_def (dimension : Dimension) {shape : PatchShape} {config : Config}
    (bank : Bank shape config) (words : List SensorWord) (patch : Patch shape) :
    EncodingFrame.compute dimension bank words patch =
      ⟨bank.activations patch, rfl,
        encodeWith dimension config words (bank.activations patch), rfl⟩ := rfl

end Acorn.Features
