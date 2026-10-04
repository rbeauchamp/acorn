/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Regula.Contract
import Regula.Decision
import Acorn.Agreement
import Acorn.FeatureRanking
import Acorn.Host.Campaign
import Acorn.Host.Checkpoint.Admission
import Acorn.Host.Cli
import Acorn.Host.Viewer.ControlRequest
import Acorn.Host.Viewer.GoalProtocol
import Acorn.Host.Viewer.WorldMemory

/-!
# Registered decisions of the executing library

A decision is a function whose result accepts or refuses its input: an admission, a parser or
a validity test. Each registration below is a `Regula.ExecutableContract` about the executing
definition itself, with the kind its proof establishes: `Regula.Decides` states that the
function accepts exactly the inputs that satisfy the written specification, with one accepted
and one refused input as witnesses. `@[regula_decision]` then makes that contract a
requirement of the function, so removing the contract while the function stays registered
fails the Regula audit.

Three groups are registered.

* Decisions of independent arguments carry a kind and the registration. A function of several
  arguments is decided on their product through `Function.uncurry`.
* A decision procedure whose result type is `Decidable _` carries both directions in its type,
  so it is registered with no contract.
* An admission whose result type depends on an argument, such as `Bounded32.admit`, has no
  kind: a kind is stated about a function between two fixed types. Its refusal theorem is
  registered as an ordinary requirement, which the audit reports with no kind, and the
  function carries no `@[regula_decision]` registration.

A contract whose proof needs the proof library is stated in `AcornVerif.Decisions`. Regula
counts only a contract of the function's own library toward a registration, so such a function
is not registered here.

No kind says that a specification is the intended one, that every caller acts on the verdict,
or which value an accepting result carries. Exactness of the accepted value is stated by the
theorems beside each definition.

This module declares theorems and two specification predicates, and no executing definition.
No executable and no other module imports it, so the registration attribute's module, which
imports Lean's elaborator, is linked into no native entry point.
-/

namespace Acorn.Decisions
open Features Handcrafted

/-- A two-way decision from an acceptance equivalence about the function, an input that
satisfies the specification and one that does not. -/
private theorem decides.{u, v} {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
    {f : α → ρ} (iff : ∀ x, accepts (f x) ↔ spec x) (holds : ∃ x, spec x)
    (fails : ∃ x, ¬spec x) : Regula.Decides accepts spec f :=
  .of_iff iff (holds.elim fun x satisfied => ⟨x, (iff x).mpr satisfied⟩)
    (fails.elim fun x unsatisfied => ⟨x, fun accepted => unsatisfied ((iff x).mp accepted)⟩)

/-- A refusal theorem read as the acceptance equivalence it determines. -/
private theorem accepts_iff_not.{u} {α : Type u} {refusal : Prop} {result : Option α}
    (refuses : result = none ↔ refusal) : result.isSome = true ↔ ¬refusal := by
  rw [Option.isSome_iff_ne_none]
  exact not_congr refuses

/-- An admission that is one test accepts exactly when the tested condition holds. -/
private theorem dite_isSome.{u} {α : Type u} {condition : Prop} [Decidable condition]
    (accept : condition → α) :
    (if holds : condition then some (accept holds) else none).isSome = true ↔ condition := by
  split <;> simp_all

/-! ## Machine comparisons -/

/-- NaN classification accepts exactly the words whose magnitude exceeds infinity's
(`Binary32.isNaN_eq_magnitude`). -/
theorem binary32_nan : Regula.ExecutableContract Binary32.isNaN
    (Regula.Decides (· = true) (fun word : Binary32 => word.magnitude > 0x7f800000)) :=
  ⟨decides
    (fun word => by
      show word.isNaN = true ↔ _
      rw [Binary32.isNaN_eq_magnitude]
      exact decide_eq_true_iff)
    ⟨⟨0x7fc00000⟩, by decide⟩ ⟨.zero, by decide⟩⟩

attribute [regula_decision] Binary32.isNaN

/-- Zero classification accepts exactly the words with signed key zero
(`Binary32.isZero_eq_key`). -/
theorem binary32_zero : Regula.ExecutableContract Binary32.isZero
    (Regula.Decides (· = true) (fun word : Binary32 => word.key = 0)) :=
  ⟨decides
    (fun word => by
      show word.isZero = true ↔ _
      rw [Binary32.isZero_eq_key]
      exact decide_eq_true_iff)
    ⟨.zero, by decide⟩ ⟨⟨0x3f800000⟩, by decide⟩⟩

attribute [regula_decision] Binary32.isZero

/-- Strict word comparison accepts exactly two non-NaN words in strict signed-key order
(`Binary32.less_eq_key`). -/
theorem binary32_less : Regula.ExecutableContract Binary32.less (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.isNaN = false ∧ words.2.isNaN = false ∧ words.1.key < words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.less words.2 = true ↔ _
      rw [Binary32.less_eq_key]
      simp [and_assoc])
    ⟨(.zero, ⟨0x3f800000⟩), by decide⟩ ⟨(.zero, .zero), by decide⟩⟩

attribute [regula_decision] Binary32.less

/-- Non-strict word comparison accepts exactly two non-NaN words in signed-key order
(`Binary32.lessOrEqual_eq_key`). -/
theorem binary32_less_or_equal : Regula.ExecutableContract Binary32.lessOrEqual (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.isNaN = false ∧ words.2.isNaN = false ∧ words.1.key ≤ words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.lessOrEqual words.2 = true ↔ _
      rw [Binary32.lessOrEqual_eq_key]
      simp [and_assoc])
    ⟨(.zero, .zero), by decide⟩ ⟨(⟨0x3f800000⟩, .zero), by decide⟩⟩

attribute [regula_decision] Binary32.lessOrEqual

/-- Numeric word equality accepts exactly two non-NaN words with equal signed keys
(`Binary32.numericallyEqual_eq_key`). -/
theorem binary32_equal : Regula.ExecutableContract Binary32.numericallyEqual (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.isNaN = false ∧ words.2.isNaN = false ∧ words.1.key = words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.numericallyEqual words.2 = true ↔ _
      rw [Binary32.numericallyEqual_eq_key]
      simp [and_assoc])
    ⟨(.zero, .zero), by decide⟩ ⟨(⟨0x3f800000⟩, .zero), by decide⟩⟩

attribute [regula_decision] Binary32.numericallyEqual

/-- The magnitude test accepts exactly a word whose magnitude field is the given constant
(`Binary32.magnitudeEq_exact`). -/
theorem binary32_magnitude : Regula.ExecutableContract Binary32.magnitudeEq (fun test =>
    Regula.Decides (· = true)
      (fun input : Binary32 × UInt32 => input.1.magnitude = input.2.toNat)
      (Function.uncurry test)) :=
  ⟨decides
    (fun input => by
      show input.1.magnitudeEq input.2 = true ↔ _
      rw [Binary32.magnitudeEq_exact]
      exact beq_iff_eq)
    ⟨(.zero, 0), by decide⟩ ⟨(.zero, 1), by decide⟩⟩

attribute [regula_decision] Binary32.magnitudeEq

/-- Binary64 NaN classification accepts exactly the words whose magnitude exceeds
infinity's. -/
theorem binary64_nan : Regula.ExecutableContract Binary64.isNaN
    (Regula.Decides (· = true) (fun word : Binary64 => word.magnitude > 0x7ff0000000000000)) :=
  ⟨decides (fun _ => decide_eq_true_iff)
    ⟨⟨0x7ff8000000000000⟩, by decide⟩ ⟨⟨0⟩, by decide⟩⟩

attribute [regula_decision] Binary64.isNaN

/-- Strict binary64 comparison accepts exactly two non-NaN words in strict signed-key order
(`Binary64.less_eq_key`). -/
theorem binary64_less : Regula.ExecutableContract Binary64.less (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary64 × Binary64 =>
        words.1.isNaN = false ∧ words.2.isNaN = false ∧ words.1.key < words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.less words.2 = true ↔ _
      rw [Binary64.less_eq_key]
      simp [and_assoc])
    ⟨(⟨0⟩, ⟨0x3ff0000000000000⟩), by decide⟩ ⟨(⟨0⟩, ⟨0⟩), by decide⟩⟩

attribute [regula_decision] Binary64.less

/-! ## Machine-state admission -/

/-- Interval admission accepts exactly the finite ordered endpoint pairs
(`Interval32.interval_admit_refuses`). -/
theorem interval_admit : Regula.ExecutableContract Interval32.admit (fun admit =>
    Regula.Decides (·.isSome = true)
      (fun endpoints : Binary32 × Binary32 =>
        endpoints.1.Finite ∧ endpoints.2.Finite ∧ endpoints.1.key ≤ endpoints.2.key)
      (Function.uncurry admit)) :=
  ⟨decides
    (fun endpoints => (accepts_iff_not
      (Interval32.interval_admit_refuses endpoints.1 endpoints.2)).trans Classical.not_not)
    ⟨(.zero, .zero), by decide⟩ ⟨(⟨0x7fc00000⟩, .zero), by decide⟩⟩

attribute [regula_decision] Interval32.admit

/-- Reward-rate admission accepts exactly the words of the reward-rate interval
(`Bounded32.admit_refuses`). -/
theorem reward_rate_admit : Regula.ExecutableContract RewardRate.admit
    (Regula.Decides (·.isSome = true) rewardRange.Contains) :=
  ⟨decides
    (fun raw => (accepts_iff_not (Bounded32.admit_refuses rewardRange raw)).trans
      Classical.not_not)
    ⟨.zero, by decide⟩ ⟨⟨0x7fc00000⟩, by decide⟩⟩

attribute [regula_decision] RewardRate.admit

/-- The word positivity test accepts exactly the words with a positive signed key
(`Binary32.keyPositive_exact`). -/
theorem key_positive : Regula.ExecutableContract Binary32.keyPositive
    (Regula.Decides (· = true) (fun word : Binary32 => 0 < word.key)) :=
  ⟨decides Binary32.keyPositive_exact ⟨⟨0x3f800000⟩, by decide⟩ ⟨.zero, by decide⟩⟩

attribute [regula_decision] Binary32.keyPositive

/-- Bonus admission accepts exactly the positive words of the Demon-0 prediction range. Every
held bonus is one of them (`Bonus.admit_self`). -/
theorem bonus_admit : Regula.ExecutableContract Bonus.admit
    (Regula.Decides (·.isSome = true)
      (fun raw : Binary32 => Discount.g99.predictionRange.Contains raw ∧ 0 < raw.key)) :=
  ⟨decides
    (fun raw => by
      show (Bonus.admit raw).isSome = true ↔ _
      unfold Bonus.admit Prediction.admit Bounded32.admit
      by_cases legal : Discount.g99.predictionRange.Contains raw
      · by_cases positive : 0 < raw.key <;> simp [legal, positive, Bonus.ofWeight]
      · simp [legal])
    ⟨⟨0x3f800000⟩, by decide⟩ ⟨.zero, by decide⟩⟩

attribute [regula_decision] Bonus.admit

/-- Unit-state admission accepts exactly the words whose utility lies in the utility range.
Every stored unit is admitted from its own words (`UnitState.words_roundtrip`). -/
theorem unit_state_admit : Regula.ExecutableContract UnitState.admit
    (Regula.Decides (·.isSome = true)
      (fun raw : UnitWords => utilityRange.Contains raw.2.2)) :=
  ⟨decides
    (fun raw => by
      show (UnitState.admit raw).isSome = true ↔ _
      rw [UnitState.admit, Option.isSome_map]
      exact (accepts_iff_not (Bounded32.admit_refuses utilityRange raw.2.2)).trans
        Classical.not_not)
    ⟨(0, 0, .zero), by decide⟩ ⟨(0, 0, ⟨0x7fc00000⟩), by decide⟩⟩

attribute [regula_decision] UnitState.admit

/-- Checked clock advancement accepts exactly the pairs whose sum fits the 64-bit word
(`Word.clock_advance_refuses`). -/
theorem clock_advance : Regula.ExecutableContract Word.advanceClock (fun advance =>
    Regula.Decides (·.isSome = true)
      (fun words : UInt64 × UInt64 => words.1.toNat + words.2.toNat < 2 ^ 64)
      (Function.uncurry advance)) :=
  ⟨decides
    (fun words => (accepts_iff_not (Word.clock_advance_refuses words.1 words.2)).trans
      Nat.not_le)
    ⟨(0, 0), by decide⟩ ⟨(0xffffffffffffffff, 1), by decide⟩⟩

attribute [regula_decision] Word.advanceClock

/-- Ratio admission accepts exactly a numerator bounded by a positive denominator. -/
theorem ratio_admit : Regula.ExecutableContract Agreement.Ratio.admit (fun admit =>
    Regula.Decides (·.isSome = true)
      (fun parts : Nat × Nat => 0 < parts.2 ∧ parts.1 ≤ parts.2) (Function.uncurry admit)) :=
  ⟨decides
    (fun parts => by
      show (Agreement.Ratio.admit parts.1 parts.2).isSome = true ↔ _
      unfold Agreement.Ratio.admit
      by_cases positive : 0 < parts.2 <;> by_cases bounded : parts.1 ≤ parts.2 <;>
        simp [positive, bounded])
    ⟨(0, 1), by decide⟩ ⟨(0, 0), by decide⟩⟩

attribute [regula_decision] Agreement.Ratio.admit

/-! ## Agent construction and checkpoint admission -/

/-- Agent construction accepts exactly a nonzero tiling word, a bank of one to 65535 units
and a capacity exponent below 32 (`AgentConstruction.admit_iff`). -/
theorem agent_construction_admit :
    Regula.ExecutableContract AgentConstruction.admit (fun admit =>
      Regula.Decides (·.isSome = true)
        (fun input : (((((FeatureProfile × Criterion) × PlanningSelection) × UInt64) × UInt64) ×
            Nat) × Nat =>
          0 < input.1.1.2.toNat ∧ 0 < input.1.2 ∧ input.1.2 ≤ 65535 ∧ input.2 < 32)
        (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
          (Function.uncurry (Function.uncurry admit))))))) :=
  ⟨decides
    (fun input => AgentConstruction.admit_iff input.1.1.1.1.1.1 input.1.1.1.1.1.2
      input.1.1.1.1.2 input.1.1.1.2 input.1.1.2 input.1.2 input.2)
    ⟨((((((⟨.final, .perStep, .declared, .learned⟩, .discounted), .expectation), 0), 1), 1), 0),
      by decide⟩
    ⟨((((((⟨.final, .perStep, .declared, .learned⟩, .discounted), .expectation), 0), 0), 1), 0),
      by decide⟩⟩

attribute [regula_decision] AgentConstruction.admit

/-- The resumable-profile test accepts exactly the profile with all four checkpointed
discriminants (`FeatureProfile.checkpoint_iff`). -/
theorem checkpoint_supported : Regula.ExecutableContract FeatureProfile.checkpointSupported
    (Regula.Decides (· = true) (fun profile : FeatureProfile =>
      profile.mode = .final ∧ profile.credit = .perStep ∧ profile.rate = .declared ∧
        profile.subtasks = .learned)) :=
  ⟨decides FeatureProfile.checkpoint_iff ⟨⟨.final, .perStep, .declared, .learned⟩, by decide⟩
    ⟨⟨.frozen, .perStep, .declared, .learned⟩, by decide⟩⟩

attribute [regula_decision] FeatureProfile.checkpointSupported

/-- Goal-total admission accepts exactly the triples whose successes do not exceed their
attempts and whose steps are zero when no attempt completed. -/
theorem goal_admit : Regula.ExecutableContract Checkpoint.admitGoal
    (Regula.Decides (·.isSome = true) (fun words : Checkpoint.GoalWords =>
      words.2.1.toNat ≤ words.1.toNat ∧ (words.1 = 0 → words.2.2 = 0))) :=
  ⟨decides (fun _ => dite_isSome _) ⟨(0, 0, 0), by decide⟩ ⟨(0, 1, 0), by decide⟩⟩

attribute [regula_decision] Checkpoint.admitGoal

/-- The specification of header admission, over a receiving construction and a header: the
header's generation, criterion, shape, seed and representation are the receiver's, the
receiver's profile is resumable and marked so, and the reward rate lies in its interval. -/
def HeaderMatches (input : AgentConstruction × Checkpoint.Header) : Prop :=
  input.2.version = Checkpoint.formatVersion ∧
    input.2.criterion = input.1.criterion.tag.toUInt32 ∧
    rewardRange.Contains input.2.gain ∧
    input.2.capacity = input.1.dimension.capacity.toUInt32 ∧
    input.2.learners = Checkpoint.primaryCount.toUInt32 ∧
    input.2.seed = input.1.config.seed ∧
    input.1.profile.checkpointSupported = true ∧
    input.2.supported = 1 ∧
    input.2.tilings = input.1.config.tilings ∧
    input.2.units.toNat = input.1.config.units.count

/-- Header admission returns a reward rate exactly for a header that matches its receiver. -/
private theorem admitHeader_isOk (construction : AgentConstruction) (header : Checkpoint.Header) :
    (Checkpoint.admitHeader construction header).isOk = true ↔
      HeaderMatches (construction, header) := by
  unfold HeaderMatches
  by_cases version : header.version = Checkpoint.formatVersion
  case neg => simp [Checkpoint.admitHeader, Except.isOk, Except.toBool, bind, Except.bind, version]
  by_cases criterion : header.criterion = construction.criterion.tag.toUInt32
  case neg =>
    simp [Checkpoint.admitHeader, Except.isOk, Except.toBool, bind, Except.bind, pure,
      Except.pure, version, criterion]
  by_cases gain : rewardRange.Contains header.gain
  case neg =>
    have refused : RewardRate.admit header.gain = none :=
      (Bounded32.admit_refuses rewardRange header.gain).mpr gain
    simp [Checkpoint.admitHeader, Except.isOk, Except.toBool, version, criterion, gain, refused]
  have admitted : RewardRate.admit header.gain = some ⟨header.gain, gain⟩ := by
    simp [RewardRate.admit, Bounded32.admit, gain]
  by_cases capacity : header.capacity = construction.dimension.capacity.toUInt32 <;>
    by_cases learners : header.learners = Checkpoint.primaryCount.toUInt32 <;>
    by_cases seed : header.seed = construction.config.seed <;>
    by_cases supported : construction.profile.checkpointSupported = true <;>
    by_cases flag : header.supported = 1 <;>
    by_cases tilings : header.tilings = construction.config.tilings <;>
    by_cases units : header.units.toNat = construction.config.units.count <;>
    simp [Checkpoint.admitHeader, Except.isOk, Except.toBool, bind, Except.bind, pure,
      Except.pure, version, criterion, gain, admitted, capacity, learners, seed, supported, flag,
      tilings, units]

/-- Header admission accepts exactly the headers that name the receiving construction's
generation, criterion, shape, seed, resumable profile and representation, with a reward rate
in its interval. -/
theorem header_admit : Regula.ExecutableContract Checkpoint.admitHeader (fun admit =>
    Regula.Decides (·.isOk = true) HeaderMatches (Function.uncurry admit)) :=
  ⟨decides (fun input => admitHeader_isOk input.1 input.2)
    ⟨(AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation,
        ⟨Checkpoint.formatVersion, Acorn.FeatureConstants.defaultWeightSpace.toUInt32,
          Checkpoint.primaryCount.toUInt32, 0, 0, 0, .zero,
          Acorn.FeatureConstants.defaultTilings.toUInt64,
          Acorn.FeatureConstants.defaultImprintUnits.toUInt32, 1⟩),
      by unfold HeaderMatches; decide⟩
    ⟨(AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation,
        ⟨Checkpoint.formatVersion + 1, 0, 0, 0, 0, 0, .zero, 0, 0, 0⟩),
      fun matched => absurd matched.1 (by decide)⟩⟩

attribute [regula_decision] Checkpoint.admitHeader

/-- A decoded fixed-width word is the encoding of its value, followed by the returned
suffix. -/
private theorem decodeNat_written (width : Nat) (bytes : List UInt8) (value : Nat)
    (rest : List UInt8) (decoded : Checkpoint.decodeNat width bytes = some (value, rest)) :
    bytes = Checkpoint.encodeNat width value ++ rest := by
  induction width generalizing bytes value rest with
  | zero =>
    simp only [Checkpoint.decodeNat, Option.some.injEq, Prod.mk.injEq] at decoded
    simp [Checkpoint.encodeNat, decoded.2]
  | succ width ih =>
    cases bytes with
    | nil => simp [Checkpoint.decodeNat, Checkpoint.byteCodec] at decoded
    | cons digit bytes =>
      simp only [Checkpoint.decodeNat, Checkpoint.byteCodec, bind, Option.bind] at decoded
      cases highEq : Checkpoint.decodeNat width bytes with
      | none => simp [highEq] at decoded
      | some high =>
        simp only [highEq, Option.some.injEq, Prod.mk.injEq] at decoded
        have tail := ih bytes high.1 high.2 highEq
        have small := digit.toNat_lt
        have quotient : value / 256 = high.1 := by omega
        have low : UInt8.ofNat value = digit := by
          apply UInt8.toNat_inj.mp
          show value % 256 = digit.toNat
          omega
        rw [Checkpoint.encodeNat, low, quotient, List.cons_append, ← decoded.2, ← tail]

/-- Fixed-width word decoding accepts exactly the encodings of a word below the width's
bound, followed by any suffix (`Checkpoint.nat_roundtrip`, `Checkpoint.decodeNat_bound`). -/
theorem nat_decode : Regula.ExecutableContract Checkpoint.decodeNat (fun decode =>
    Regula.Decides (·.isSome = true)
      (fun input : Nat × List UInt8 => ∃ value suffix, value < 256 ^ input.1 ∧
        input.2 = Checkpoint.encodeNat input.1 value ++ suffix)
      (Function.uncurry decode)) :=
  ⟨{ sound := fun input accepted => by
       obtain ⟨⟨value, rest⟩, decoded⟩ := Option.isSome_iff_exists.mp accepted
       exact ⟨value, rest, Checkpoint.decodeNat_bound _ _ _ _ decoded,
         decodeNat_written _ _ _ _ decoded⟩
     accepted := ⟨(0, []), rfl⟩
     complete := fun input ⟨value, suffix, bound, written⟩ => by
       show (Checkpoint.decodeNat input.1 input.2).isSome = true
       rw [written, Checkpoint.nat_roundtrip _ _ bound]
       rfl
     refused := ⟨(1, []), by decide⟩ }⟩

attribute [regula_decision] Checkpoint.decodeNat

/-- Write-capability admission accepts exactly a positive interval with no refused image
(`Host.WritableCheckpoint.refused`). -/
theorem writable_checkpoint_admit :
    Regula.ExecutableContract Host.WritableCheckpoint.admit (fun admit =>
      Regula.Decides (·.isSome = true)
        (fun input : (System.FilePath × UInt32) × Host.CheckpointAdmission =>
          input.2 ≠ .refused ∧ 0 < input.1.2.toNat)
        (Function.uncurry (Function.uncurry admit))) :=
  ⟨decides
    (fun ⟨⟨path, interval⟩, status⟩ => by
      show (Host.WritableCheckpoint.admit path interval status).isSome = true ↔
        status ≠ .refused ∧ 0 < interval.toNat
      cases status <;> by_cases positive : 0 < interval.toNat <;>
        simp [Host.WritableCheckpoint.admit, positive])
    ⟨((⟨""⟩, 1), .loaded), by decide⟩ ⟨((⟨""⟩, 1), .refused), by decide⟩⟩

attribute [regula_decision] Host.WritableCheckpoint.admit

/-- The public resumable-profile test accepts exactly the ranked profile. It agrees with the
constructed profile's test (`Host.research_resumable`). -/
theorem profile_resumable : Regula.ExecutableContract Host.ResearchProfile.resumable
    (Regula.Decides (· = true) (fun profile : Host.ResearchProfile => profile = .ranked)) :=
  ⟨decides (fun profile => by cases profile <;> simp [Host.ResearchProfile.resumable])
    ⟨.ranked, rfl⟩ ⟨.primitive, by decide⟩⟩

attribute [regula_decision] Host.ResearchProfile.resumable

/-! ## Host admission and parsing -/

/-- Coordinate admission accepts exactly the signed 64-bit integers
(`Host.Coordinate.checked_none`). -/
theorem coordinate_checked : Regula.ExecutableContract Host.Coordinate.checked
    (Regula.Decides (·.isSome = true)
      (fun value : Int => -(2 ^ 63) ≤ value ∧ value < 2 ^ 63)) :=
  ⟨decides
    (fun value => (accepts_iff_not (Host.Coordinate.checked_none value)).trans
      Classical.not_not)
    ⟨0, by decide⟩ ⟨2 ^ 63, by decide⟩⟩

attribute [regula_decision] Host.Coordinate.checked

/-- Custom world admission accepts exactly a positive side and a nonzero day length. -/
theorem world_config_admit : Regula.ExecutableContract Host.WorldConfig.admit
    (Regula.Decides (·.isOk = true) (fun raw : Host.RawWorldConfig =>
      0 < raw.side.val ∧ 0 < raw.dayLength.toNat)) :=
  ⟨decides
    (fun raw => by
      show (Host.WorldConfig.admit raw).isOk = true ↔ _
      unfold Host.WorldConfig.admit
      by_cases side : 0 < raw.side.val <;> by_cases day : 0 < raw.dayLength.toNat <;>
        simp [side, day, Except.isOk, Except.toBool])
    ⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide⟩
    ⟨⟨0, ⟨0, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide⟩⟩

attribute [regula_decision] Host.WorldConfig.admit

/-- Standard world admission accepts exactly a side within the supported interval
(`Host.WorldConfig.standard_bounds`). -/
theorem world_config_standard :
    Regula.ExecutableContract Host.WorldConfig.standard (fun standard =>
      Regula.Decides (·.isOk = true)
        (fun input : UInt64 × Host.Coordinate =>
          (Acorn.FeatureConstants.worldMinSide : Int) ≤ input.2.val ∧
            input.2.val ≤ (Acorn.FeatureConstants.worldMaxSide : Int))
        (Function.uncurry standard)) :=
  ⟨decides
    (fun input => by
      show (Host.WorldConfig.standard input.1 input.2).isOk = true ↔ _
      unfold Host.WorldConfig.standard
      by_cases low : input.2.val < Acorn.FeatureConstants.worldMinSide
      · simp [low, Except.isOk, Except.toBool] <;> omega
      · by_cases high : input.2.val > Acorn.FeatureConstants.worldMaxSide
        · simp [low, high, Except.isOk, Except.toBool] <;> omega
        · simp [low, high, Except.isOk, Except.toBool] <;> omega)
    ⟨(0, ⟨64, by decide⟩), by decide⟩ ⟨(0, ⟨63, by decide⟩), by decide⟩⟩

attribute [regula_decision] Host.WorldConfig.standard

/-- The raw area product is accepted exactly when it is a signed 64-bit integer
(`Host.RawWorldConfig.area_exact`). -/
theorem world_area : Regula.ExecutableContract Host.RawWorldConfig.area
    (Regula.Decides (·.isSome = true) (fun raw : Host.RawWorldConfig =>
      -(2 ^ 63) ≤ raw.side.val * raw.side.val ∧ raw.side.val * raw.side.val < 2 ^ 63)) :=
  ⟨decides (fun raw => coordinate_checked.evidence.iff (raw.side.val * raw.side.val))
    ⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide⟩
    ⟨⟨0, ⟨2 ^ 62, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide⟩⟩

attribute [regula_decision] Host.RawWorldConfig.area

/-- Energy spending accepts exactly a cost within the balance (`Host.Energy.spend_balance`). -/
theorem energy_spend : Regula.ExecutableContract Host.Energy.spend (fun spend =>
    Regula.Decides (·.isSome = true)
      (fun input : Host.Energy × Nat => input.2 ≤ input.1.val) (Function.uncurry spend)) :=
  ⟨decides
    (fun input => by
      show (Host.Energy.spend input.1 input.2).isSome = true ↔ _
      unfold Host.Energy.spend
      split <;> simp_all)
    ⟨(Host.Energy.new 0, 0), Nat.zero_le _⟩ ⟨(Host.Energy.new 0, 1), by decide⟩⟩

attribute [regula_decision] Host.Energy.spend

/-- The raw energy cost is accepted exactly when the product fits 32 bits
(`Host.Action.rawEnergyCost_exact`). -/
theorem raw_energy_cost : Regula.ExecutableContract Host.Action.rawEnergyCost (fun cost =>
    Regula.Decides (·.isSome = true)
      (fun input : Host.Action × UInt32 =>
        (if input.1 == .harvest then Acorn.FeatureConstants.harvestCost else 1) *
          input.2.toNat < 2 ^ 32)
      (Function.uncurry cost)) :=
  ⟨decides
    (fun input => by
      show (Host.Action.rawEnergyCost input.1 input.2).isSome = true ↔ _
      unfold Host.Action.rawEnergyCost
      dsimp only
      split <;> simp_all)
    ⟨(.wait, 0), by decide⟩ ⟨(.harvest, 0xffffffff), by decide⟩⟩

attribute [regula_decision] Host.Action.rawEnergyCost

/-- Crafting accepts exactly an unowned tool whose recipe the inventory covers
(`Host.Inventory.craft_exact`). -/
theorem inventory_craft : Regula.ExecutableContract Host.Inventory.craft (fun craft =>
    Regula.Decides (·.isOk = true)
      (fun input : Host.Inventory × Host.Craftable =>
        input.1.owns input.2 = false ∧ input.2.recipe.1 ≤ input.1.wood.toNat ∧
          input.2.recipe.2 ≤ input.1.stone.toNat)
      (Function.uncurry craft)) :=
  ⟨decides
    (fun ⟨inventory, tool⟩ => by
      show (inventory.craft tool).isOk = true ↔ inventory.owns tool = false ∧
        tool.recipe.1 ≤ inventory.wood.toNat ∧ tool.recipe.2 ≤ inventory.stone.toNat
      rcases recipe : tool.recipe with ⟨wood, stone⟩
      by_cases owned : inventory.owns tool = true
      · simp [Host.Inventory.craft, owned, Except.isOk, Except.toBool]
      · by_cases short : inventory.wood.toNat < wood
        · simp [Host.Inventory.craft, recipe, owned, short, Except.isOk, Except.toBool] <;>
            omega
        · by_cases shortStone : inventory.stone.toNat < stone
          · simp [Host.Inventory.craft, recipe, owned, short, shortStone, Except.isOk,
              Except.toBool] <;> omega
          · simp [Host.Inventory.craft, recipe, owned, short, shortStone, Except.isOk,
              Except.toBool] <;> omega)
    ⟨(⟨100, 100, 0, 0, false, false⟩, .axe), by decide⟩
    ⟨(⟨0, 0, 0, 0, true, false⟩, .axe), by decide⟩⟩

attribute [regula_decision] Host.Inventory.craft

/-- Step-total aggregation accepts exactly a total and an outcome whose step sum fits 64 bits
(`Host.addOutcomeSteps_exact`). -/
theorem outcome_steps : Regula.ExecutableContract Host.addOutcomeSteps (fun add =>
    Regula.Decides (·.isOk = true)
      (fun input : UInt64 × Host.GoalOutcome => input.1.toNat + input.2.steps.toNat < 2 ^ 64)
      (Function.uncurry add)) :=
  ⟨decides
    (fun input => by
      show (Host.addOutcomeSteps input.1 input.2).isOk = true ↔ _
      have advance := clock_advance.evidence.iff (input.1, input.2.steps)
      unfold Host.addOutcomeSteps
      cases next : Word.advanceClock input.1 input.2.steps <;>
        simp_all [Function.uncurry, Except.isOk, Except.toBool])
    ⟨(0, ⟨0, 0, 0, 0, false, .zero, ⟨.zero, .zero, .zero⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩),
      by decide⟩
    ⟨(0xffffffffffffffff,
        ⟨0, 0, 0, 1, false, .zero, ⟨.zero, .zero, .zero⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩),
      by decide⟩⟩

attribute [regula_decision] Host.addOutcomeSteps

/-- The unaided enterability test accepts exactly the terrain that is neither water nor
mountain. -/
theorem tile_walkable : Regula.ExecutableContract Host.TileKind.walkable
    (Regula.Decides (· = true)
      (fun kind : Host.TileKind => kind ≠ .water ∧ kind ≠ .mountain)) :=
  ⟨decides (fun kind => by cases kind <;> simp [Host.TileKind.walkable])
    ⟨.grass, by decide⟩ ⟨.water, by decide⟩⟩

attribute [regula_decision] Host.TileKind.walkable

/-- Planning-selection parsing accepts exactly the two canonical spellings
(`PlanningSelection.parse_accepted`). -/
theorem planning_parse : Regula.ExecutableContract PlanningSelection.parse
    (Regula.Decides (·.isSome = true)
      (fun text => ∃ selection, text = PlanningSelection.name selection)) :=
  ⟨.of_roundtrip (fun selection => (PlanningSelection.parse_accepted _ selection).mpr rfl)
    (fun text selection parsed =>
      ((PlanningSelection.parse_accepted text selection).mp parsed).symm)
    .expectation (unwritten := "") rfl⟩

attribute [regula_decision] PlanningSelection.parse

/-- The command-line planning value is accepted exactly when the shared parser accepts it. -/
private theorem planningValue_isOk (text : String) :
    (Host.Cli.planningValue text).isOk = (PlanningSelection.parse text).isSome := by
  unfold Host.Cli.planningValue
  cases PlanningSelection.parse text <;> rfl

/-- Command-line planning admission accepts exactly the two canonical spellings, through the
shared parser and with no substitution. -/
theorem planning_value : Regula.ExecutableContract Host.Cli.planningValue
    (Regula.Decides (·.isOk = true)
      (fun text => ∃ selection, text = PlanningSelection.name selection)) :=
  ⟨decides
    (fun text => by
      show (Host.Cli.planningValue text).isOk = true ↔ _
      rw [planningValue_isOk]
      exact planning_parse.evidence.iff text)
    planning_parse.evidence.toDecidesSoundly.satisfiable
    planning_parse.evidence.toDecidesCompletely.refutable⟩

attribute [regula_decision] Host.Cli.planningValue

/-- Planning admission from an argument list accepts exactly an absent option or one
canonical spelling (`Host.Cli.planningSelection_absent`,
`Host.Cli.planningSelection_provided`). A missing value is refused. -/
theorem planning_selection : Regula.ExecutableContract Host.Cli.planningSelection
    (Regula.Decides (·.isOk = true) (fun arguments : List String =>
      Host.Cli.value arguments "--planning" = .ok none ∨
        ∃ selection, Host.Cli.value arguments "--planning" =
          .ok (some (PlanningSelection.name selection)))) :=
  ⟨decides
    (fun arguments => by
      show (Host.Cli.planningSelection arguments).isOk = true ↔ _
      cases found : Host.Cli.value arguments "--planning" with
      | error refusal =>
        simp [Host.Cli.planningSelection, found, Except.isOk, Except.toBool, bind, Except.bind]
      | ok text =>
        cases text with
        | none =>
          simp [Host.Cli.planningSelection_absent arguments found, Except.isOk, Except.toBool]
        | some text =>
          rw [Host.Cli.planningSelection_provided arguments text found, planningValue_isOk]
          constructor
          · intro accepted
            obtain ⟨selection, written⟩ := (planning_parse.evidence.iff text).mp accepted
            exact .inr ⟨selection, by rw [written]⟩
          · rintro (absent | ⟨selection, provided⟩)
            · cases absent
            · have written : text = PlanningSelection.name selection := by simpa using provided
              exact (planning_parse.evidence.iff text).mpr ⟨selection, written⟩)
    ⟨[], .inl rfl⟩
    ⟨["--planning"], fun spec => by
      have found : Host.Cli.value ["--planning"] "--planning" =
          .error (.missing "--planning") := rfl
      rw [found] at spec
      simp at spec⟩⟩

attribute [regula_decision] Host.Cli.planningSelection

/-- Checkpoint-status parsing accepts exactly the five emitted status lines
(`Host.CheckpointStatus.roundtrip`). -/
theorem checkpoint_status_parse : Regula.ExecutableContract Host.CheckpointStatus.parse
    (Regula.Decides (·.isSome = true)
      (fun line => ∃ status : Host.CheckpointStatus, line = status.line)) :=
  ⟨.of_roundtrip Host.CheckpointStatus.roundtrip
    (fun line status parsed => by
      unfold Host.CheckpointStatus.parse at parsed
      split at parsed <;> cases parsed <;> rfl)
    .saved (unwritten := "") rfl⟩

attribute [regula_decision] Host.CheckpointStatus.parse

/-! ## Viewer protocol admission -/

open Host.Viewer

/-- Goal-family decoding accepts exactly the five emitted family codes
(`Host.Viewer.goalKind_roundtrip`). -/
theorem goal_kind_decode : Regula.ExecutableContract decodeGoalKind
    (Regula.Decides (·.isSome = true) (fun code => ∃ kind : GoalKind, code = kind.code)) :=
  ⟨.of_roundtrip goalKind_roundtrip
    (fun _ _ decoded => by simpa using List.find?_some decoded)
    none (unwritten := 5) rfl⟩

attribute [regula_decision] decodeGoalKind

/-- Goal-item decoding accepts exactly the emitted item codes
(`Host.Viewer.goalItem_roundtrip`). -/
theorem goal_item_decode : Regula.ExecutableContract decodeGoalItem
    (Regula.Decides (·.isSome = true) (fun code => ∃ item : GoalItem, code = item.code)) :=
  ⟨.of_roundtrip goalItem_roundtrip
    (fun _ _ decoded => by simpa using List.find?_some decoded)
    none (unwritten := 1000) rfl⟩

attribute [regula_decision] decodeGoalItem

/-- Line extension accepts exactly a line below the line capacity
(`LineBytes.append_exact`). -/
theorem line_append : Regula.ExecutableContract LineBytes.append (fun append =>
    Regula.Decides (·.isSome = true)
      (fun input : LineBytes × UInt8 => input.1.bytes.size < lineCapacity)
      (Function.uncurry append)) :=
  ⟨decides (fun _ => dite_isSome _) ⟨(.empty, 0), by decide⟩
    ⟨(⟨⟨Array.replicate lineCapacity 0⟩, by simp [ByteArray.size]⟩, 0),
      by simp [ByteArray.size]⟩⟩

attribute [regula_decision] LineBytes.append

/-- Output admission accepts exactly the running or stopping phase of the same generation
(`Phase.archiving_rejects`). -/
theorem phase_accepts : Regula.ExecutableContract Phase.accepts (fun test =>
    Regula.Decides (· = true)
      (fun input : Phase × UInt64 => input.1 = .running input.2 ∨ input.1 = .stopping input.2)
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨phase, generation⟩ => by
      show phase.accepts generation = true ↔ phase = .running generation ∨
        phase = .stopping generation
      cases phase <;> simp [Phase.accepts])
    ⟨(.running 0, 0), .inl rfl⟩ ⟨(.idle, 0), by decide⟩⟩

attribute [regula_decision] Phase.accepts

/-- Map-cell admission accepts exactly the unseen marker and the eight terrain codes. -/
theorem map_cell_admit : Regula.ExecutableContract MapCell.admit
    (Regula.Decides (·.isSome = true) (fun byte : UInt8 => byte = 255 ∨ byte.toNat < 8)) :=
  ⟨decides
    (fun byte => by
      show (MapCell.admit byte).isSome = true ↔ _
      unfold MapCell.admit
      by_cases unseen : byte = 255
      · simp [unseen]
      · by_cases terrain : byte.toNat < 8 <;> simp [unseen, terrain])
    ⟨255, by decide⟩ ⟨8, by decide⟩⟩

attribute [regula_decision] MapCell.admit

/-- Capture attribution accepts exactly the captures that name the published run and agent
epoch. -/
theorem capture_matches : Regula.ExecutableContract Capture.matches (fun test =>
    Regula.Decides (· = true)
      (fun input : Capture × Identity =>
        input.1.run = input.2.run ∧ input.1.epoch = input.2.agentEpoch)
      (Function.uncurry test)) :=
  ⟨decides (fun input => by simp [Function.uncurry, Capture.matches])
    ⟨(⟨0, 0, 0, 0, 0, false⟩, ⟨0, 0, 0⟩), by decide⟩
    ⟨(⟨1, 0, 0, 0, 0, false⟩, ⟨0, 0, 0⟩), by decide⟩⟩

attribute [regula_decision] Capture.matches

/-- Control-body admission accepts exactly the bodies within the declared byte bound. -/
theorem control_body : Regula.ExecutableContract controlBody
    (Regula.Decides (·.isSome = true)
      (fun bytes : ByteArray => bytes.size ≤ controlBodyCapacity)) :=
  ⟨decides (fun _ => dite_isSome _) ⟨ByteArray.empty, Nat.zero_le _⟩
    ⟨⟨Array.replicate 1025 0⟩, by simp [ByteArray.size, controlBodyCapacity]⟩⟩

attribute [regula_decision] controlBody

/-- The specification of wire-line admission: the text fits the line capacity in bytes and
holds neither newline character. -/
def WireLine (text : String) : Prop :=
  text.utf8ByteSize ≤ lineCapacity ∧ text.contains '\n' = false ∧ text.contains '\r' = false

/-- The wire-line test is its byte and delimiter specification (`WireText.byte_bound`,
`WireText.delimiter_bound`). -/
private theorem wireTextLegal_iff (text : String) : wireTextLegal text = true ↔ WireLine text := by
  simp [wireTextLegal, WireLine, and_assoc]

/-- The wire-line test accepts exactly the texts within the line capacity that hold neither
newline character. -/
theorem wire_text_legal : Regula.ExecutableContract wireTextLegal
    (Regula.Decides (· = true) WireLine) :=
  ⟨.of_iff wireTextLegal_iff ⟨"", by simp [wireTextLegal, lineCapacity]⟩
    ⟨"\n", by simp [wireTextLegal, lineCapacity]⟩⟩

attribute [regula_decision] wireTextLegal

/-- Wire-text admission accepts exactly the texts the wire-line test accepts. -/
theorem wire_text : Regula.ExecutableContract wireText
    (Regula.Decides (·.isSome = true) WireLine) :=
  ⟨.of_iff (fun text => (dite_isSome _).trans (wireTextLegal_iff text))
    ⟨"", (dite_isSome _).mpr (by simp [wireTextLegal, lineCapacity])⟩
    ⟨"\n", fun accepted =>
      absurd ((dite_isSome _).mp accepted) (by simp [wireTextLegal, lineCapacity])⟩⟩

attribute [regula_decision] wireText

/-- Folding the byte differences of a list against itself leaves the accumulator unchanged. -/
private theorem difference_self (bytes : List UInt8) (difference : UInt8) :
    (bytes.zip bytes).foldl (fun (difference : UInt8) pair => difference ||| (pair.1 ^^^ pair.2))
      difference = difference := by
  induction bytes generalizing difference with
  | nil => rfl
  | cons byte rest ih => simp [ih]

/-- The token comparison accepts exactly equal tokens. -/
private theorem tokenMatches_iff (received expected : String) :
    tokenMatches received expected = true ↔ received = expected := by
  constructor
  · intro matched
    unfold tokenMatches at matched
    split at matched
    · exact absurd matched Bool.false_ne_true
    · simp only [Bool.and_eq_true, beq_iff_eq] at matched
      exact matched.2
  · rintro rfl
    simp [tokenMatches, difference_self]

/-- The control-token comparison accepts exactly a received token equal to the expected one.
The kind states the verdict only; it says nothing of the comparison's timing. -/
theorem token_matches : Regula.ExecutableContract tokenMatches (fun test =>
    Regula.Decides (· = true) (fun tokens : String × String => tokens.1 = tokens.2)
      (Function.uncurry test)) :=
  ⟨decides (fun tokens => tokenMatches_iff tokens.1 tokens.2) ⟨("", ""), rfl⟩
    ⟨("", "a"), by decide⟩⟩

attribute [regula_decision] tokenMatches

/-- Control authorization accepts exactly a JSON POST whose token is nonempty and equal to
the expected token and whose declared length is the admitted body's size. -/
theorem control_authorizes : Regula.ExecutableContract ControlHeaders.authorizes (fun test =>
    Regula.Decides (· = true)
      (fun input : (ControlHeaders × String) × ControlBody =>
        input.1.1.method = "POST" ∧ input.1.1.mediaType = "application/json" ∧
          input.1.2.isEmpty = false ∧ input.1.1.token = input.1.2 ∧
          input.1.1.length = some input.2.val.size)
      (Function.uncurry (Function.uncurry test))) :=
  ⟨decides
    (fun input => by
      simp [Function.uncurry, ControlHeaders.authorizes, tokenMatches_iff, and_assoc])
    ⟨((⟨"POST", "application/json", "a", some 0⟩, "a"), ⟨ByteArray.empty, Nat.zero_le _⟩),
      by decide⟩
    ⟨((⟨"GET", "application/json", "a", some 0⟩, "a"), ⟨ByteArray.empty, Nat.zero_le _⟩),
      fun authorized => absurd authorized.1 (by decide)⟩⟩

attribute [regula_decision] ControlHeaders.authorizes

/-! ## Decision procedures

Each result is a `Decidable` value: an accepting result carries a proof of the decided
proposition and a refusing result a proof of its negation, so no contract is registered. -/

attribute [regula_decision] Interval32.orderedDecidable Binary32.positiveDecidable

/-! ## Admissions with a dependent result type

The result type of each function below is indexed by an argument: the receiving interval, the
value rule, the feature dimension or the action count. A decision kind is stated about a
function between two fixed types, so none applies. The refusal theorem beside each definition
is registered as an ordinary requirement, reported with no kind. -/

/-- Bounded admission refuses exactly the words outside the receiving interval
(`Bounded32.admit_refuses`). -/
theorem bounded_admit : Regula.ExecutableContract Bounded32.admit (fun admit =>
    ∀ (range : Interval32) (raw : Binary32), admit range raw = none ↔ ¬range.Contains raw) :=
  ⟨Bounded32.admit_refuses⟩

/-- Weight admission refuses exactly the words outside the receiving rule's domain
(`weight_admit_refuses`). -/
theorem weight_admit : Regula.ExecutableContract Weight.admit (fun admit =>
    ∀ (rule : ValueRule) (raw : Binary32),
      admit rule raw = none ↔ ¬rule.domain.range.Contains raw) :=
  ⟨weight_admit_refuses⟩

/-- Feature-index admission refuses exactly the words at or beyond the receiving capacity
(`feature_index_admit_refuses`). -/
theorem feature_index_admit : Regula.ExecutableContract FeatIdx.admit (fun admit =>
    ∀ (dimension : Dimension) (word : UInt32),
      admit dimension word = none ↔ dimension.capacity ≤ word.toNat) :=
  ⟨feature_index_admit_refuses⟩

/-- Action admission refuses exactly the indices outside the action space
(`Action.admit_none`). -/
theorem action_admit : Regula.ExecutableContract Action.admit (fun admit =>
    ∀ actions raw : Nat, admit actions raw = none ↔ actions ≤ raw) :=
  ⟨Action.admit_none⟩

end Acorn.Decisions
